use binhex::rle::{decode, write, DecodeError, Decoder, DecoderError, Reader, RUN_DELIMITER};
use core::num::NonZeroU8;
use std::fs::read;
use std::io::{BufRead, Read, Result as IoResult, Write};
use std::path::PathBuf;

macro_rules! python_binhex_test {
    ($name:ident: $compressed:literal, $uncompressed: literal) => {
        /// Test if decompressing a sample produced by Python's binhex module yields the same data.
        #[test]
        fn $name() {
            let sample_diretory: PathBuf = [env!("CARGO_MANIFEST_DIR"), "tests", "rle"]
                .iter()
                .collect();
            let mut compressed_path = sample_diretory.join("compressed");
            compressed_path.push($compressed);
            let mut uncompressed_path = sample_diretory.join("uncompressed");
            uncompressed_path.push($uncompressed);
            let compressed = read(&compressed_path)
                .expect(&format!("failed to read {}", compressed_path.display()));
            let uncompressed = read(&uncompressed_path)
                .expect(&format!("failed to read {}", uncompressed_path.display()));

            assert_eq!(decode(compressed.as_slice()).unwrap(), uncompressed);
        }
    };
}

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

/// Reader which provides its output one byte at a time.
struct ShortReader<'a> {
    output: &'a [u8],
}

impl<'a> ShortReader<'a> {
    fn new(output: &'a [u8]) -> Self {
        ShortReader { output }
    }
}

impl<'a> Read for ShortReader<'a> {
    fn read(&mut self, buf: &mut [u8]) -> IoResult<usize> {
        match self.output {
            [first, rest @ ..] if !buf.is_empty() => {
                buf[0] = *first;
                self.output = rest;
                Ok(1)
            }
            _ => Ok(0),
        }
    }
}

impl<'a> BufRead for ShortReader<'a> {
    fn fill_buf(&mut self) -> IoResult<&[u8]> {
        let produced = core::cmp::min(1, self.output.len());
        Ok(&self.output[..produced])
    }

    fn consume(&mut self, amount: usize) {
        self.output = &self.output[amount..];
    }
}

python_binhex_test! {
    decode_python_test_verbose: "test_verbose.bin", "test.bin"
}

python_binhex_test! {
    decode_python_test_compact: "test_compact.bin", "test.bin"
}

python_binhex_test! {
    decode_python_test_nested_runs: "nested_runs.bin", "nested_runs.bin"
}

/// Check if [`Decoder`] handles zero length buffers.
#[test]
fn decode_zero_output() {
    let input: [u8; 6] = [1, RUN_DELIMITER, 2, 3, RUN_DELIMITER, 2];
    let mut output = [42; 5];
    let mut decoder = Decoder::new();

    assert_eq!(decoder.decode(&input, &mut []).unwrap(), (0, 0));
    assert_eq!(decoder.decode(&input, &mut output[..1]).unwrap(), (3, 1));
    assert_eq!(decoder.decode(&input[3..], &mut []).unwrap(), (0, 0));
    assert_eq!(decoder.decode(&input[3..], &mut []).unwrap(), (0, 0));

    assert_eq!(
        decoder.decode(&input[3..], &mut output[1..3]).unwrap(),
        (3, 2)
    );
    assert_eq!(decoder.drain(&mut []).unwrap(), 0);
    assert_eq!(decoder.drain(&mut output[3..]).unwrap(), 1);
    assert_eq!(decoder.drain(&mut output[4..]).unwrap(), 0);

    assert_eq!(output, [1, 1, 3, 3, 42]);
}

/// Check if [`Decoder`] does correctly handle escaped bytes.
#[test]
fn decode_excaped_bytes() {
    let input: [u8; 8] = [
        RUN_DELIMITER,
        0,
        RUN_DELIMITER,
        3,
        RUN_DELIMITER,
        3,
        RUN_DELIMITER,
        0,
    ];

    let output = decode(&input).unwrap();
    assert_eq!(output, [RUN_DELIMITER; 6]);
}

/// Check if [`Decoder`] does report orphaned runs.
#[test]
fn test_orphaned_run() {
    let input: [u8; 2] = [RUN_DELIMITER, 42];

    assert!(matches!(
        decode(&input).unwrap_err(),
        DecodeError::DecoderError(DecoderError::OrphanedRun)
    ));
}

/// Check if [`Decoder`] does report unexpected eofs.
#[test]
fn test_unexpected_eof() {
    let input: [u8; 2] = [42, RUN_DELIMITER];

    assert!(matches!(
        decode(&input).unwrap_err(),
        DecodeError::DecoderError(DecoderError::UnexpectedEof)
    ));
}

/// Check if [`Reader::read`] does not produce `Ok(0)` prematurely.
#[test]
fn reader_drain_decoder() {
    let mut reader = Reader::new(ShortReader::new(&[1, RUN_DELIMITER, 2, 3]));
    let mut buf = Vec::with_capacity(3);

    assert_eq!(reader.read_to_end(&mut buf).unwrap(), 3);
    assert_eq!(buf, [1, 1, 3]);
}

/// Check if [`Reader::read`] handles an empty output buffer.
#[test]
fn reader_handle_empty_buffer() {
    let mut reader = Reader::new([1, RUN_DELIMITER, 2, 3].as_slice());
    let mut output: [u8; 4] = [42; 4];

    assert_eq!(reader.read(&mut []).unwrap(), 0);
    assert_eq!(reader.read(&mut output[..1]).unwrap(), 1);
    assert_eq!(reader.read(&mut []).unwrap(), 0);
    assert_eq!(reader.read(&mut output[1..2]).unwrap(), 1);
    assert_eq!(reader.read(&mut []).unwrap(), 0);
    assert_eq!(reader.read(&mut output[2..]).unwrap(), 1);

    assert_eq!(output, [1, 1, 3, 42]);
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
