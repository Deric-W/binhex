use std::default::Default;
use std::slice;
use std::io::{Read, ErrorKind, Result as IoResult};
use crate::rle::{RunState, RUN_DELIMITER};

/// Implementation of [`std::io::Read`] which transparently decompresses data from an underlying reader.
/// 
/// BinHex 4 files use a RLE compression described [here](https://files.stairways.com/other/binhex-40-specs-info.txt).
/// A `RleDecoder<R>` handles decompression by applying it transparently to reads from a underlying [`std::io::Read`] instance.
/// 
/// # Buffering
/// 
/// A `RleDecoder<R>` performs many short reads from the underlying reader, which can cause performance problems.
/// To prevent that, put a reader in a [`std::io::BufReader`] before wrapping it with this type.
/// 
/// # Examples
/// 
/// ```
/// use std::io::{Read, Result, ErrorKind};
/// use binhex::rle::RleDecoder;
/// 
/// let mut buffer = Vec::with_capacity(6);
/// RleDecoder::new(&[1u8, 2u8, 0x90u8, 2u8, 3u8][..]).read_to_end(&mut buffer).unwrap();
/// assert_eq!(buffer, [1, 2, 2, 3]);
/// 
/// // with escaped delimiters
/// buffer.clear();
/// RleDecoder::new(&[0x2Bu8, 0x90u8, 0x00u8, 0x90u8, 0x05u8][..]).read_to_end(&mut buffer).unwrap();
/// assert_eq!(buffer, [0x2Bu8, 0x90u8, 0x90u8, 0x90u8, 0x90u8, 0x90u8]);
/// 
/// // with corrupted runs
/// assert_eq!(RleDecoder::new(&[0x42u8, 0x90u8][..]).read_to_end(&mut buffer).err().unwrap().kind(), ErrorKind::UnexpectedEof);
/// ```
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct RleDecoder<R> {

    /// underlying reader providing data for decompression#
    inner: R,

    /// current state of the reader
    state: RunState
}

impl<R> RleDecoder<R> {
    /// Creates a new `RleDecoder<R>` with a default initial state, which is currently [`RunState::BEFORE`].
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::io::empty;
    /// use binhex::rle::RleDecoder;
    /// 
    /// let decoder = RleDecoder::new(empty());
    /// ``` 
    pub fn new(inner: R) -> RleDecoder<R> {
        RleDecoder::with_state(RunState::default(), inner)
    }

    /// Creates a new `RleDecoder<R>` with the specified initial state.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::io::empty;
    /// use binhex::rle::{RunState, RleDecoder};
    /// 
    /// let decoder = RleDecoder::with_state(RunState::BEFORE, empty());
    /// ```
    pub fn with_state(state: RunState, inner: R) -> RleDecoder<R> {
        RleDecoder {inner, state}
    }

    /// Returns the current state of this decoder.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::io::empty;
    /// use binhex::rle::{RunState, RleDecoder};
    /// 
    /// // maybe some data was already read from the reader
    /// let decoder = RleDecoder::with_state(RunState::IN(0x41, 4), empty());
    /// assert_eq!(decoder.state(), RunState::IN(0x41, 4));
    /// ```
    pub fn state(&self) -> RunState {
        self.state
    }

    /// Gets a imutable reference to the underlying reader.
    /// 
    /// It is inadvisable to directly read from the underlying reader because doing so might result in corrupted data when reading from the decoder.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::io::{empty, Empty};
    /// use binhex::rle::RleDecoder;
    /// 
    /// let decoder = RleDecoder::new(empty());
    /// let reader: &Empty = decoder.get_ref();
    /// ```
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    /// Gets a mutable reference to the underlying reader.
    /// 
    /// It is inadvisable to directly read from the underlying reader, see [`RleDecoder::get_ref`].
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::io::{empty, Empty};
    /// use binhex::rle::RleDecoder;
    /// 
    /// let mut decoder = RleDecoder::new(empty());
    /// let mut reader: &mut Empty = decoder.get_mut();
    /// ```
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    /// Unwrap this `RleDecoder<R>` and return the underlying reader.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::io::{empty, Empty};
    /// use binhex::rle::RleDecoder;
    /// 
    /// let decoder = RleDecoder::new(empty());
    /// let reader: Empty = decoder.into_inner();
    /// ```
    pub fn into_inner(self) -> R {
        self.inner
    }
}

impl<R: Read> RleDecoder<R> {
    /// Read a single byte from the underlying reader.
    /// 
    /// If this method returns `None` then nothing could be read.
    fn read_byte(&mut self) -> Option<IoResult<u8>> {
        let mut buf = 0;
        match self.inner.read(slice::from_mut(&mut buf)) {
            Ok(0)  => None,
            Ok(_)  => Some(Ok(buf)),
            Err(e) => Some(Err(e))
        }

    }

    /// Update the current state depending of the success of a write and return the number of bytes written.
    fn update_from_write(&mut self, byte: u8, count: u8, buf: &mut [u8]) -> usize {
        let (length, state) = RunState::from_write(byte, count, buf);
        self.state = state;
        length
    }

    /// Handle reading beginning with the delimiter.
    /// 
    /// If this method returns `None` then the buffer was too small to handle all possibilities and nothing was read.
    fn read_delimiter(&mut self, byte: u8, buf: &mut [u8]) -> Option<IoResult<usize>> {
        if buf.is_empty() {
            // dont read if the buf cant handle the possible byte
            None
        } else {
            match self.read_byte() {
                // try to complete the run
                Some(Ok(RUN_DELIMITER)) => match self.read_byte().unwrap_or(Err(ErrorKind::UnexpectedEof.into())) {
                    Ok(count) => Ok(self.update_from_write(byte, count, buf)),
                    Err(e)    => {
                        // remember that we already read the delimiter
                        self.state = RunState::LENGTH(byte);
                        Err(e)
                    }
                },
                // byte was not part of a run
                Some(Ok(b)) => {
                    // does not panic because the if protects against an empty buf
                    buf[0] = byte;
                    self.state = RunState::DELIMITER(b);
                    Ok(1)
                },
                Some(Err(e)) => Err(e),
                // if the last run contains no delimiter then its byte is not part of a `real` run
                None         => {
                    // does not panic because the if protects against an empty buf
                    buf[0] = byte;
                    self.state = RunState::BEFORE;
                    Ok(1)
                }
            }.into()
        }
    }
}

impl<R: Read> Read for RleDecoder<R> {
    fn read(&mut self, buf: &mut [u8]) -> IoResult<usize> {
        match self.state {
            // return Ok(0) instead of UnexpectedEof
            RunState::BEFORE => {
                self.read_byte().map_or(Ok(0), |result| {
                    match result {
                        Ok(byte) => self.read_delimiter(byte, buf).unwrap_or_else(
                            // remember that we already read the first byte of the run
                            || {self.state = RunState::DELIMITER(byte); Ok(0)}
                        ),
                        Err(e)   => Err(e)
                    }
                })
            },
            RunState::DELIMITER(byte) => self.read_delimiter(byte, buf).unwrap_or(Ok(0)),
            RunState::LENGTH(byte) => {
                self.read_byte()
                    .ok_or(ErrorKind::UnexpectedEof)?
                    .map(|count| self.update_from_write(byte, count, buf))
            },
            RunState::IN(byte, count) => Ok(self.update_from_write(byte, count, buf))
        }
    }
}