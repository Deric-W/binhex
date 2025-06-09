//! Utilities for reading RLE compressed streams

// The read module is part of binhex (https://github.com/Deric-W/binhex)
// Copyright (C) 2021  Eric Wolf
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, version 3.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.
// SPDX-License-Identifier: GPL-3.0-only

use super::RUN_DELIMITER;
use core::cmp::min;
use core::convert::TryInto;
use core::default::Default;
use core::num::NonZeroU8;
use memchr::memchr;
use std::collections::TryReserveError;
use std::io::{BufRead, Error as IoError, ErrorKind, Read, Result as IoResult};
use thiserror::Error;

/// Error produced by [`Decoder`] when receiving invalid data.
#[derive(Error, Debug)]
pub enum DecoderError {
    #[error("non-zero run without a byte at start")]
    OrphanedRun,

    #[error("expected byte specifying the length of a run, received eof")]
    UnexpectedEof,
}

#[derive(Clone, Copy, Default, Debug)]
enum DecoderState {
    /// The decoder has not produced any data yet.
    #[default]
    Empty,

    /// The decoder produced some data, with its last byte being recorded.
    Written(u8),

    /// The decoder received a delimiter (possibly after producing some data).
    Delimiter(Option<u8>),

    /// A run  with a non zero length is being produced.
    Run(u8, NonZeroU8),
}

/// Decoder of the compression used by BinHex 4.
///
/// BinHex 4 files use a RLE compression described [here](https://files.stairways.com/other/binhex-40-specs-info.txt)
/// which can be decoded using this type.
/// At first the compressed input is passed to the [`Decoder::decode`] method
/// until all has been consumed.
/// Then [`Decoder::drain`] is called until the internal state is consumed.
///
/// # Incremental Decoding
///
/// The [`Decoder::decode`] does not require access to the whole input at once,
/// allowing for it to be read in chunks to reduce the required memory.
///
/// # Buffering
///
/// [`Decoder`] maintains an internal fixed size buffer for storing state between
/// calls to its methods.
/// While this buffer consists only of around three bytes it may represent output up
/// to 255 bytes long and therefore has to be consumed by calling [`Decoder::drain`]
/// for guaranteeing a successful decoding.
#[derive(Clone, Default, Debug)]
pub struct Decoder {
    state: DecoderState,
}

impl Decoder {
    /// Creates a new `Decoder` with an initial state.
    ///
    /// # Examples
    ///
    /// ```
    /// use binhex::rle::Decoder;
    ///
    /// let decoder = Decoder::new();
    /// ```
    pub fn new() -> Self {
        Decoder::default()
    }

    /// Decompress a portion of the input.
    ///
    /// This method is passed a portion of the input and a buffer for the decoded output.
    /// It will fill the output buffer as much as it can and return the number of input
    /// bytes consumed and output bytes produced.
    ///
    /// Should the whole decoded output not fit in the output buffer it will only consume
    /// a part of it and expects the caller to call it again with the rest of the input
    /// buffer (and possible more input data) until the whole input has been consumed.
    ///
    /// Should the input begin with a run which is not an escaped delimiter an [`DecoderError`]
    /// will be produced instead without changing the internal state.
    pub fn decode(
        &mut self,
        mut input: &[u8],
        mut output: &mut [u8],
    ) -> Result<(usize, usize), DecoderError> {
        let input_length = input.len();
        let output_length = output.len();
        let mut state = self.state;
        loop {
            match state {
                DecoderState::Empty => match input {
                    [RUN_DELIMITER, rest @ ..] => {
                        state = DecoderState::Delimiter(None);
                        input = rest;
                    }
                    [byte, rest @ ..] if !output.is_empty() => {
                        output[0] = *byte;
                        state = DecoderState::Written(*byte);
                        input = rest;
                        output = &mut output[1..];
                    }
                    _ => break,
                },
                DecoderState::Written(byte) => match read_run(byte, input, output) {
                    Some((new_state, read, written)) => {
                        state = new_state;
                        input = &input[read..];
                        output = &mut output[written..];
                    }
                    None => break,
                },
                DecoderState::Delimiter(written) => match input {
                    [length, rest @ ..] if *length > 0 => {
                        let written = written.ok_or(DecoderError::OrphanedRun)?;
                        // first byte already written, subtract it
                        state = match NonZeroU8::new(length - 1) {
                            Some(new_length) => DecoderState::Run(written, new_length),
                            None => DecoderState::Written(written),
                        };
                        input = rest;
                    }
                    // a run with a length of zero is an escaped run delimiter byte
                    [0, rest @ ..] if !output.is_empty() => {
                        output[0] = RUN_DELIMITER;
                        state = DecoderState::Written(RUN_DELIMITER);
                        input = rest;
                        output = &mut output[1..];
                    }
                    _ => break,
                },
                DecoderState::Run(byte, length) if !output.is_empty() => {
                    let (new_state, consumed) = consume_run(byte, length, output);
                    state = new_state;
                    output = &mut output[consumed..];
                }
                DecoderState::Run(_, _) => break,
            }
        }
        self.state = state;
        Ok((input_length - input.len(), output_length - output.len()))
    }

    /// Finish decompressing the buffered input.
    ///
    /// After all input has been consumed by [`Decoder::decode`] there may be state
    /// left in the decoder.
    /// To inform it that the input has ended this function has to be called to produce
    /// the rest of the decoded output until it produced zero bytes
    /// (assuming the output buffer would be able to store more).
    ///
    /// Should the placement of the end violate the compression format an [`DecoderError`]
    /// will be produced instead without changing the internal state.
    pub fn drain(&mut self, output: &mut [u8]) -> Result<usize, DecoderError> {
        match self.state {
            DecoderState::Empty | DecoderState::Written(_) => Ok(0),
            DecoderState::Delimiter(_) => Err(DecoderError::UnexpectedEof),
            DecoderState::Run(byte, length) => {
                let (state, consumed) = consume_run(byte, length, output);
                self.state = state;
                Ok(consumed)
            }
        }
    }
}

/// Process as much data as possible until a rle run,
/// returning any progress made.
fn read_run(written: u8, input: &[u8], output: &mut [u8]) -> Option<(DecoderState, usize, usize)> {
    // scan one more byte than output to check if it is an delimiter,
    // stopping at the end of the input
    let (longest_input, longest_output) = if input.len() > output.len() {
        (output.len() + 1, output.len())
    } else {
        (input.len(), input.len())
    };
    match memchr(RUN_DELIMITER, &input[..longest_input]) {
        Some(0) => Some((DecoderState::Delimiter(Some(written)), 1, 0)),
        Some(index) => {
            output[..index].copy_from_slice(&input[..index]);
            let state = DecoderState::Delimiter(Some(input[index - 1]));
            Some((state, index + 1, index))
        }
        None if longest_output > 0 => {
            output[..longest_output].copy_from_slice(&input[..longest_output]);
            let state = DecoderState::Written(input[longest_output - 1]);
            Some((state, longest_output, longest_output))
        }
        None => None,
    }
}

/// Consume a run of compressed bytes, returning the new state and number of bytes produced.
fn consume_run(byte: u8, length: NonZeroU8, output: &mut [u8]) -> (DecoderState, usize) {
    let consumed: u8 = min(length.get(), output.len().try_into().unwrap_or(u8::MAX));
    output[..consumed.into()].fill(byte);
    let state = match NonZeroU8::new(length.get() - consumed) {
        Some(new_length) => DecoderState::Run(byte, new_length),
        None => DecoderState::Written(byte),
    };
    (state, consumed.into())
}

/// Error produced by [`decode`] and [`decode_into`].
#[derive(Error, Debug)]
pub enum DecodeError {
    /// The used [`Decoder`] reported an error.
    #[error("error while decoding input data")]
    DecoderError(#[source] DecoderError),

    /// The buffer to hold the output data could not be resized
    /// to receive additional data.
    #[error("error while resizing the output buffer")]
    ReserveError(#[source] TryReserveError),
}

/// Decompress some input data, returning the produced output.
///
/// This function uses [`Decoder`] internally and is intended
/// to be used as a shortcut when the resulting data will fit into memory.
///
/// # Examples
///
/// ```
/// use binhex::rle::{RUN_DELIMITER, decode, DecodeError};
///
/// // with compressed runs
/// let output = decode(&[1u8, 2u8, RUN_DELIMITER, 2u8, 3u8]).unwrap();
/// assert_eq!(output, [1, 2, 2, 3]);
///
/// // with escaped delimiters
/// let output = decode(&[0x2Bu8, RUN_DELIMITER, 0x00u8, RUN_DELIMITER, 0x05u8]).unwrap();
/// assert_eq!(output, [0x2Bu8, 0x90u8, 0x90u8, 0x90u8, 0x90u8, 0x90u8]);
///
/// // with corrupted runs
/// let error = decode(&[0x42u8, RUN_DELIMITER]).unwrap_err();
/// assert!(matches!(error, DecodeError::DecoderError(_)));
/// ```
pub fn decode(input: &[u8]) -> Result<Vec<u8>, DecodeError> {
    let mut buf = Vec::new();
    decode_into(input, &mut buf)?;
    Ok(buf)
}

/// Variant of [`decode`] which appends to an existing buffer.
///
/// # Examples
///
/// ```
/// use binhex::rle::{RUN_DELIMITER, decode_into, DecodeError};
///
/// let mut output = vec![42];
/// decode_into(&[1u8, 2u8, RUN_DELIMITER, 2u8, 3u8], &mut output).unwrap();
///
/// assert_eq!(output, [42, 1, 2, 2, 3]);
/// ```
pub fn decode_into(mut input: &[u8], output: &mut Vec<u8>) -> Result<(), DecodeError> {
    let mut decoder = Decoder::new();
    let mut final_size = output.len();
    let mut buf: &mut [u8] = &mut [];
    while !input.is_empty() {
        if buf.is_empty() {
            buf = aquire_buf(output)?;
        }
        let (read, written) = decoder
            .decode(input, buf)
            .map_err(DecodeError::DecoderError)?;
        input = &input[read..];
        buf = &mut buf[written..];
        final_size += written;
    }
    loop {
        if buf.is_empty() {
            buf = aquire_buf(output)?;
        }
        let written = decoder.drain(buf).map_err(DecodeError::DecoderError)?;
        if written == 0 {
            break;
        }
        buf = &mut buf[written..];
        final_size += written;
    }
    output.truncate(final_size);
    Ok(())
}

fn aquire_buf(output: &mut Vec<u8>) -> Result<&mut [u8], DecodeError> {
    let old_len = output.len();
    output.try_reserve(64).map_err(DecodeError::ReserveError)?;
    // FIXME: use [MaybeUninit<u8>] when the required methods on slices are stabilised
    output.resize(output.capacity(), 0);
    Ok(&mut output[old_len..])
}

/// Wrapper which transparently applies [`Decoder`] to a [`BufRead`].
///
/// The internally used decoder maintains an internal state which can
/// cause data loss when the underlying reader is extracted before
/// everything has been read.
///
/// # Examples
///
/// ```
/// use std::io::{Read, ErrorKind};
/// use binhex::rle::{RUN_DELIMITER, Reader};
///
/// let mut buffer = Vec::with_capacity(6);
/// Reader::new(&[1u8, 2u8, RUN_DELIMITER, 2u8, 3u8][..]).read_to_end(&mut buffer).unwrap();
/// assert_eq!(buffer, [1, 2, 2, 3]);
///
/// // with escaped delimiters
/// buffer.clear();
/// Reader::new(&[0x2Bu8, RUN_DELIMITER, 0x00u8, RUN_DELIMITER, 0x05u8][..]).read_to_end(&mut buffer).unwrap();
/// assert_eq!(buffer, [0x2Bu8, 0x90u8, 0x90u8, 0x90u8, 0x90u8, 0x90u8]);
///
/// // with corrupted runs
/// let error = Reader::new(&[0x42u8, RUN_DELIMITER][..]).read_to_end(&mut buffer).unwrap_err();
/// assert_eq!(error.kind(), ErrorKind::UnexpectedEof);
/// ```
#[derive(Clone, Debug)]
pub struct Reader<R> {
    inner: R,
    decoder: Decoder,
    eof_reached: bool,
}

impl<R> Reader<R> {
    /// Creates a new [`Reader<R>`] with a default initial state.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::empty;
    /// use binhex::rle::Reader;
    ///
    /// let decoder = Reader::new(empty());
    /// ```
    pub fn new(inner: R) -> Self {
        Reader {
            inner,
            decoder: Decoder::default(),
            eof_reached: false,
        }
    }

    /// Gets a immutable reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader because doing
    /// so might result in corrupted data when reading from this reader.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{empty, Empty};
    /// use binhex::rle::Reader;
    ///
    /// let decoder = Reader::new(empty());
    /// let reader: &Empty = decoder.get_ref();
    /// ```
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    /// Gets a mutable reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader, see [`Reader::get_ref`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{empty, Empty};
    /// use binhex::rle::Reader;
    ///
    /// let mut decoder = Reader::new(empty());
    /// let mut reader: &mut Empty = decoder.get_mut();
    /// ```
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    /// Unwrap this [`Reader<R>`] and return the underlying reader.
    ///
    /// Note that data stored in the current state is lost.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{empty, Empty};
    /// use binhex::rle::Reader;
    ///
    /// let decoder = Reader::new(empty());
    /// let reader: Empty = decoder.into_inner();
    /// ```
    pub fn into_inner(self) -> R {
        self.inner
    }
}

impl<R: BufRead> Read for Reader<R> {
    fn read(&mut self, buf: &mut [u8]) -> IoResult<usize> {
        if self.eof_reached {
            let written = self
                .decoder
                .drain(buf)
                .map_err(|e| IoError::new(ErrorKind::UnexpectedEof, e))?;
            return Ok(written);
        }
        loop {
            let input = self.inner.fill_buf()?;
            if input.is_empty() {
                // consumed all input, drain decoder to prevent returning Ok(0) prematurely
                self.eof_reached = true;
                let written = self
                    .decoder
                    .drain(buf)
                    .map_err(|e| IoError::new(ErrorKind::UnexpectedEof, e))?;
                return Ok(written);
            } else {
                let (read, written) = self
                    .decoder
                    .decode(input, buf)
                    .map_err(|e| IoError::new(ErrorKind::InvalidData, e))?;
                self.inner.consume(read);
                // try to continue filling the buffer until we either write something
                // (if possible) or an error occurs, in which case no data is lost
                // since it will all be stored in the decoder
                if written != 0 || buf.is_empty() {
                    return Ok(written);
                }
            }
        }
    }
}
