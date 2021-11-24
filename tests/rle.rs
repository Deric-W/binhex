use core::num::NonZeroU8;
use std::io::{Result as IoResult, Read, Write};
use binhex::rle::{read, write, RUN_DELIMITER};


/// Writer which always consumes a specified number of bytes
struct BrokenWriter {
    consume: usize
}

impl BrokenWriter {
    fn new(consume: usize) -> Self {
        BrokenWriter { consume }
    }
}

impl Write for BrokenWriter {
    fn write(&mut self, _buf: &[u8]) -> IoResult<usize> {
        Ok(self.consume)
    }

    fn flush(&mut self) -> IoResult<()> {
        Ok(())
    }
}


/// Check if the decoder handles zero length buffers
#[test]
fn read_delimiter_zero() {
    let buffer: [u8; 3] = [RUN_DELIMITER, 2, 3];
    let mut decoder = read::RleDecoder::with_state(read::RunState::Delimiter(1), &buffer[..]);
    assert_eq!(decoder.read(&mut []).unwrap(), 0);
    assert_eq!(decoder.into_inner(), &buffer[..]);
}

/// Check if the encoder prevents overflows
#[test]
fn write_run_overflow() {
    let mut buffer: [u8; 9] = [0; 9];
    let mut encoder = write::RleEncoder::new(&mut buffer[..]);
    assert_eq!(encoder.write(&[1; 300]).unwrap(), u8::MAX.into());
    assert_eq!(encoder.state(), write::RunState::Accumulate(1, NonZeroU8::new(u8::MAX).unwrap()));
    assert_eq!(encoder.write(&[2; 100]).unwrap(), 100);
    assert_eq!(encoder.write(&[2; 200]).unwrap(), 155);
    assert_eq!(encoder.write(&[2; 50]).unwrap(), 50);
    encoder.into_inner().unwrap();
    assert_eq!(&buffer, &[1, RUN_DELIMITER, 255, 2, RUN_DELIMITER, 255, 2, RUN_DELIMITER, 50]);
}

/// Check if the encoders state prevents overflows
#[test]
fn write_transition_overflow() {
    let mut encoder = write::RleEncoder::with_state(
        write::RunState::Accumulate(1, NonZeroU8::new(1).unwrap()),
        BrokenWriter::new(u8::MAX.into())
    );
    encoder.flush().unwrap();
    assert_eq!(encoder.state(), write::RunState::Before);
}

/// Check compression choices
#[test]
fn write_compression() {
    let mut buffer: [u8; 11] = [0; 11];
    let mut encoder = write::RleEncoder::new(&mut buffer[..]);
    assert_eq!(encoder.write(&[1; 2]).unwrap(), 2);
    assert_eq!(encoder.write(&[RUN_DELIMITER]).unwrap(), 1);
    assert_eq!(encoder.write(&[2; 4]).unwrap(), 4);
    assert_eq!(encoder.write(&[RUN_DELIMITER]).unwrap(), 1);
    assert_eq!(encoder.write(&[RUN_DELIMITER; 3]).unwrap(), 3);
    encoder.into_inner().unwrap();
    assert_eq!(&buffer, &[1, 1, RUN_DELIMITER, 0, 2, RUN_DELIMITER, 4, RUN_DELIMITER, 0, RUN_DELIMITER, 4]);
}

/// Check handling of Escape state
#[test]
fn write_escape() {
    let mut buffer: [u8; 7] = [RUN_DELIMITER, 0, 0, 0, 0, 0, 0];
    let mut encoder = write::RleEncoder::with_state(
        write::RunState::Escape(NonZeroU8::new(8).unwrap()),
        &mut buffer[1..]
    );
    // dont accumulate to escape 0
    assert_eq!(encoder.write(&[0; 4]).unwrap(), 4);
    assert_eq!(encoder.state(), write::RunState::Accumulate(0, NonZeroU8::new(4).unwrap()));
    encoder.into_inner().unwrap();
    assert_eq!(&buffer, &[RUN_DELIMITER, 0, RUN_DELIMITER, 8, 0, RUN_DELIMITER, 4]);
}
