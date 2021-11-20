//! Utilities for reading RLE compressed files

use std::default::Default;
use std::slice;
use std::io::{Read, ErrorKind, Result as IoResult};
use crate::rle::RUN_DELIMITER;

/// State of a RLE run
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum RunState {
    /// nothing was read
    BEFORE,

    /// the byte to be expanded was read
    DELIMITER(u8),

    /// the delimiter between the byte and the length was read
    LENGTH(u8),

    /// byte, delimiter and length where read, run complete
    IN(u8, u8)
}

impl RunState {
    /// construct an instance dependig of the success of a full run write
    /// 
    /// # Arguments
    /// 
    /// * `byte` - the byte which the run expands
    /// * `count` - the length of the run
    /// * `buf` - buffer in which the run is to be expanded
    /// 
    /// # Return Value
    /// A tuple containing the number of bytes written and the resulting run state
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binhex::rle::read::RunState;
    /// 
    /// let mut buffer: [u8; 3] = [0; 3];
    /// 
    /// // buffer too small, state is not being reset
    /// assert_eq!(RunState::from_write(0x41, 3, &mut buffer[..1]), (1, RunState::IN(0x41, 2)));
    /// assert_eq!(&buffer, &[0x41, 0, 0]);
    /// 
    /// // all bytes fit in the buffer, the state is being reset
    /// assert_eq!(RunState::from_write(0x41, 3, &mut buffer), (3, RunState::BEFORE));
    /// assert_eq!(&buffer, &[0x41, 0x41, 0x41]);
    /// 
    /// // runs with a length of 0 are escaped delimiters
    /// assert_eq!(RunState::from_write(0xff, 0, &mut buffer), (1, RunState::DELIMITER(0x90)));
    /// assert_eq!(&buffer, &[0xff, 0x41, 0x41]);
    /// ```
	pub fn from_write(byte: u8, count: u8, buf: &mut [u8]) -> (usize, Self) {
		match buf {
			// no write = no state change
			[] => (0, Self::IN(byte, count)),

			// case for escaped delimiter
			[ref mut first, ..] if count == 0 => {
				*first = byte;
				(1, Self::DELIMITER(RUN_DELIMITER))
			},

			// base case for rle run
			_ => {
				let length: usize = count.into();
				match length.checked_sub(buf.len()) {
					// run fits in buffer
					Some(0) | None => {
						buf[..length].fill(byte);
						(length, Self::BEFORE)
					},

					// run does not fit in buffer
					Some(x) => {
						buf.fill(byte);
						(buf.len(), Self::IN(byte, x as u8))
					}
				}
			}
		}
	}
}

impl Default for RunState {
	fn default() -> Self {
		Self::BEFORE
	}
}


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
/// use binhex::rle::read::RleDecoder;
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

    /// underlying reader providing data for decompression
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
    /// use binhex::rle::read::RleDecoder;
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
    /// use binhex::rle::read::{RunState, RleDecoder};
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
    /// use binhex::rle::read::{RunState, RleDecoder};
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
    /// use binhex::rle::read::RleDecoder;
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
    /// use binhex::rle::read::RleDecoder;
    /// 
    /// let mut decoder = RleDecoder::new(empty());
    /// let mut reader: &mut Empty = decoder.get_mut();
    /// ```
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    /// Unwrap this `RleDecoder<R>` and return the underlying reader.
    /// 
    /// Note that data stored in the current state is lost.
    /// # Examples
    /// 
    /// ```
    /// use std::io::{empty, Empty};
    /// use binhex::rle::read::RleDecoder;
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

    /// Handle reading beginning with the length.
    fn read_length(&mut self, byte: u8, buf: &mut [u8]) -> IoResult<usize> {
        self.read_byte()
            .unwrap_or(Err(ErrorKind::UnexpectedEof.into()))
            .map(|count| self.update_from_write(byte, count, buf))
    }

    /// Handle reading beginning with the delimiter.
    fn read_delimiter(&mut self, byte: u8, buf: &mut [u8]) -> IoResult<usize> {
        if buf.is_empty() {
            // dont read if the buf cant handle the possible byte
            Ok(0)
        } else {
            match self.read_byte() {
                // try to complete the run
                Some(Ok(RUN_DELIMITER)) => {
                    // remember that we already read the delimiter
                    self.state = RunState::LENGTH(byte);
                    self.read_length(byte, buf)
                }
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
            }
        }
    }
}

impl<R: Read> Read for RleDecoder<R> {
    fn read(&mut self, buf: &mut [u8]) -> IoResult<usize> {
        match self.state {
            // return Ok(0) instead of UnexpectedEof
            RunState::BEFORE => self.read_byte().map_or(Ok(0), |result| {
                    match result {
                        Ok(byte) => {
                            // remember that we already read the first byte of the run
                            self.state = RunState::DELIMITER(byte);
                            self.read_delimiter(byte, buf)
                        },
                        Err(e)   => Err(e)
                    }
                }
            ),
            RunState::DELIMITER(byte) => self.read_delimiter(byte, buf),
            RunState::LENGTH(byte) => self.read_length(byte, buf),
            RunState::IN(byte, count) => Ok(self.update_from_write(byte, count, buf))
        }
    }
}