//! Utilities for the RLE compression used by BinHex 4 files

mod read;
pub use read::RleDecoder;

/// byte seperating the byte to be expanded and the length of a run
pub const RUN_DELIMITER: u8 = 0x90;

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
    /// use binhex::rle::RunState;
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