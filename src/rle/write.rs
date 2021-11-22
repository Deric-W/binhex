//! Utilities for writing RLE compressed files

use crate::rle::RUN_DELIMITER;
use std::default::Default;
use std::error::Error;
use std::fmt;
use std::io::{Error as IoError, ErrorKind, Result as IoResult, Write};
use std::iter::Iterator;
use std::num::NonZeroU8;
use std::{mem, ptr};

/// State of a RLE run
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum RunState {
    /// Nothing is written for this run
    Before,

    /// The same as `Before`, but some bytes are ready to be written.
    ///
    /// The run length is not allowed to be zero
    /// to prevent confusion with escaped run delimiters.
    Accumulate(u8, NonZeroU8),

    /// A byte of a run needed escaping which has to be written.
    ///
    /// The run Length is not allowed to be zero
    /// to prevent confusion with escaped run delimiters.
    Escape(NonZeroU8),

    /// The run Delimiter needs to be written.
    ///
    /// The run Length is not allowed to be zero
    /// to prevent confusion with escaped run delimiters.
    Delimiter(NonZeroU8),

    /// the run length needs to be written
    ///
    /// The run length is allowed to be zero
    /// to allow escaped run delimiters.
    Length(u8)
}

impl RunState {
    /// Transition to next state depending on the success of a write.
    ///
    /// # Escaping
    ///
    /// Run delimiters appearing as literal or run bytes will be escaped
    /// by making them delimit a run with a length of zero as descibed
    /// [here](https://files.stairways.com/other/binhex-40-specs-info.txt).
    ///
    /// # Errors
    ///
    /// Errors produced by the writer are passed to the caller of this function,
    /// in which case nothing was written to the writer.
    /// If the writer returned Ok(0) `None` is returned to prevent confusion
    /// with errors originating from the writer.
    fn transition<W: Write>(self, mut writer: W) -> Option<IoResult<Self>> {
        match self {
            // nothing to write
            RunState::Before => Some(Ok(self)),
            // write escaped RUN_DELIMITER as literal
            RunState::Accumulate(RUN_DELIMITER, count) if count.get() < 2 => {
                match writer.write(&[RUN_DELIMITER, 0]) {
                    Ok(0) => None,
                    // escape the delimiter as a run of length 0
                    Ok(1) => Some(Ok(RunState::Length(0))),
                    Ok(_) => Some(Ok(RunState::Before)),
                    Err(e) => Some(Err(e))
                }
            }
            // write escaped RUN_DELIMITER as run
            RunState::Accumulate(RUN_DELIMITER, count) => {
                match writer.write(&[RUN_DELIMITER, 0, RUN_DELIMITER, count.get()]) {
                    Ok(0) => None,
                    Ok(1) => Some(Ok(RunState::Escape(count))),
                    Ok(2) => Some(Ok(RunState::Delimiter(count))),
                    Ok(3) => Some(Ok(RunState::Length(count.get()))),
                    Ok(_) => Some(Ok(RunState::Before)),
                    Err(e) => Some(Err(e))
                }
            }
            // write byte as literal(s)
            RunState::Accumulate(byte, count) if count.get() < 4 => {
                let buf: [u8; 3] = [byte; 3];
                let index: usize = count.get().into();
                match writer.write(&buf[..index]) {
                    Ok(0) => None,
                    Ok(n) => NonZeroU8::new(
                        // prevent overflow if n is somehow bigger than index
                        index.saturating_sub(n) as u8
                    )
                    .map_or(Some(Ok(RunState::Before)), |count| {
                        Some(Ok(RunState::Accumulate(byte, count)))
                    }),
                    Err(e) => Some(Err(e))
                }
            }
            // write byte as run
            RunState::Accumulate(byte, count) => Self::transition_run(byte, count, writer),
            // write escaped run
            RunState::Escape(count) => Self::transition_run(0, count, writer),
            // write delimiter
            RunState::Delimiter(count) => match writer.write(&[RUN_DELIMITER, count.get()]) {
                Ok(0) => None,
                Ok(1) => Some(Ok(RunState::Length(count.get()))),
                Ok(_) => Some(Ok(RunState::Before)),
                Err(e) => Some(Err(e))
            },
            // write length
            RunState::Length(count) => match writer.write(&[count]) {
                Ok(0) => None,
                Ok(_) => Some(Ok(RunState::Before)),
                Err(e) => Some(Err(e))
            },
        }
    }

    /// Helper function to reduce code duplication
    fn transition_run<W: Write>(
        byte: u8,
        count: NonZeroU8,
        mut writer: W,
    ) -> Option<IoResult<Self>> {
        match writer.write(&[byte, RUN_DELIMITER, count.get()]) {
            Ok(0) => None,
            Ok(1) => Some(Ok(RunState::Delimiter(count))),
            Ok(2) => Some(Ok(RunState::Length(count.get()))),
            Ok(_) => Some(Ok(RunState::Before)),
            Err(e) => Some(Err(e))
        }
    }
}

impl Default for RunState {
    fn default() -> RunState {
        RunState::Before
    }
}

/// An error returned by [`RleEncoder::into_inner()`] which combines an error that happend
/// while flushing the current state, and the rle encoder object which may be used to
/// recover from the condition.
///
/// # Examples
///
/// ```
/// use std::io::sink;
/// use binhex::rle::write::RleEncoder;
///
/// let mut encoder = RleEncoder::new(sink());
///
/// // after finishing writing
/// let writer = match encoder.into_inner() {
///     Ok(w) => w,
///     // In this case e is an IntoInnerError
///     Err(e) => panic!("failed to unwrap encoder")
/// };
/// ```
#[derive(Debug)]
pub struct IntoInnerError<W> {
    /// rle encoder instance which generated the error
    writer: W,

    /// error which caused the call to
    /// [`RleEncoder::into_inner()`] to fail
    error: IoError
}

impl<W> IntoInnerError<W> {
    /// create a new instance from the provided writer and error
    fn new(writer: W, error: IoError) -> IntoInnerError<W> {
        IntoInnerError { writer, error }
    }

    /// Returns a reference to the error which caused the
    /// call to [`RleEncoder::into_inner()`] to fail.
    ///
    /// This error was returned when attempting to flush the
    /// current state of the encoder.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::sink;
    /// use binhex::rle::write::RleEncoder;
    ///
    /// let mut encoder = RleEncoder::new(sink());
    ///
    /// // after finishing writing
    /// let writer = match encoder.into_inner() {
    ///     Ok(w) => w,
    ///     Err(e) => {
    ///         println!("{}", e.error());
    ///         panic!("failed to unwrap encoder")
    ///     }
    /// };
    /// ```
    pub fn error(&self) -> &IoError {
        &self.error
    }

    /// Consumes this [`IntoInnerError`] and returns the error
    /// which caused the call to [`RleEncoder::into_inner`] to fail.
    ///
    /// This takes ownership of the underlying error unlike [`IntoInnerError.error()`]
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{sink, ErrorKind};
    /// use binhex::rle::write::RleEncoder;
    ///
    /// let mut encoder = RleEncoder::new(sink());
    ///
    /// // after finishing writing
    /// let writer = match encoder.into_inner() {
    ///     Ok(w) => w,
    ///     Err(e) => {
    ///         match e.into_error().kind() {
    ///             ErrorKind::WriteZero => panic!("failed to write data"),
    ///             _ => panic!("something else happend")
    ///         }
    ///     }
    /// };
    /// ```
    pub fn into_error(self) -> IoError {
        self.error
    }

    /// Consumes this [`IntoInnerError`] and returns the
    /// rle encoder instance which generated the error.
    ///
    /// The returned instance can be used for error recovery,
    /// such as inspecting the current state or retry the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{sink, ErrorKind};
    /// use binhex::rle::write::RleEncoder;
    ///
    /// let mut encoder = RleEncoder::new(sink());
    ///
    /// // after finishing writing
    /// let writer = encoder.into_inner().unwrap_or_else(
    ///     |e| match e.into_inner().into_inner() {
    ///         Ok(w) => w,
    ///         Err(e) => panic!("into_inner failed a second time")
    ///     }
    /// );
    /// ```
    pub fn into_inner(self) -> W {
        self.writer
    }

    /// Consumes this [`IntoInnerError`] and returns both the
    /// error which caused the call to [`RleEncoder::into_inner`] to fail
    /// and the rle encoder instance which generated the error.
    ///
    /// This can be used for advanced error recovery.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::sink;
    /// use binhex::rle::write::RleEncoder;
    ///
    /// let mut encoder = RleEncoder::new(sink());
    ///
    /// // after finishing writing
    /// let writer = match encoder.into_inner() {
    ///     Ok(w) => w,
    ///     Err(e) => {
    ///         let (error, encoder) = e.into_parts();
    ///         println!("error while unwrapping encoder");
    ///         encoder.into_inner().expect("into inner failed a second time")
    ///     }
    /// };
    /// ```
    pub fn into_parts(self) -> (IoError, W) {
        (self.error, self.writer)
    }
}

impl<W> fmt::Display for IntoInnerError<W> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(
            formatter,
            "'{}' occured while flushing state in RleEncoder.into_inner",
            self.error()
        )
    }
}

impl<W: fmt::Debug> Error for IntoInnerError<W> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(self.error())
    }
}

impl<W> From<IntoInnerError<W>> for IoError {
    fn from(error: IntoInnerError<W>) -> IoError {
        error.into_error()
    }
}

/// Implementation of [`std::io::Write`] which transparently compresses data written to a wrapped writer.
///
/// BinHex 4 files use a RLE compression described [here](https://files.stairways.com/other/binhex-40-specs-info.txt).
/// A `RleEncoder<W>` handles compression by applying it transparently to writes to a underlying [`std::io::Write`] instance.
///
/// # Buffering
///
/// A `RleEncoder<W>` performs many short writes to the underlying writer, which can cause performance problems.
/// To prevent that, put a writer in a [`std::io::BufWriter`] before wrapping it with this type.
///
/// # Compression
///
/// The current run is buffered in memory to allow for compression where it would make sense.
/// This does not mean that this type consumes a significant amount of memory
/// (the run is stored as a tuple of two bytes), but allows for data loss if the buffered run is not flushed.
/// To prevent that, handle it like a [`std::io::BufWriter`].
///
/// # Short writes
/// 
/// This type may frequently process less data than requested (but never `Ok(0)`) even if
/// the underlying writer can handle more because the [`std::io::Write::write`]
/// method only knows success or failure and therefore has no concept for writes with an error.
///
/// While this is perfectly normal behavior it might confuse some bad implementations.
///
/// # Examples
///
/// ```
/// use std::io::{Write, Result, ErrorKind};
/// use std::num::NonZeroU8;
/// use binhex::rle::write::{RleEncoder, RunState};
///
/// let mut buffer = [0u8; 10];
/// {
///     let mut encoder = RleEncoder::new(&mut buffer[..]);
///
///     // normal bytes
///     encoder.write_all(&[1, 2, 2, 2, 2, 3]).unwrap();
///
///     // bytes which need escaping
///     encoder.write_all(&[0x2B, 0x90, 0x90, 0x90, 0x90, 0x90]).unwrap();
///
///     // the current run is buffered to allow for compression
///     // this can lead to short writes
///     assert_eq!(encoder.write(&[42, 42, 42, 1]).unwrap(), 3);
///
///     // buffer too small, accumulated run could not be flushed
///     assert_eq!(encoder.write(&[1]).unwrap(), 0);
///     assert_eq!(encoder.state(), RunState::Accumulate(42, NonZeroU8::new(3).unwrap()));
/// }
/// assert_eq!(buffer, [1, 2, 0x90, 4, 3, 0x2B, 0x90, 0x00, 0x90, 0x05]);
/// ```
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct RleEncoder<W: Write> {
    /// underlying writer receiving compressed data
    inner: W,

    /// current state of the writer
    state: RunState
}

impl<W: Write> RleEncoder<W> {
    /// Creates a new `RleEncoder<R>` with a default initial state, which is currently [`RunState::Before`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::sink;
    /// use binhex::rle::write::RleEncoder;
    ///
    /// let encoder = RleEncoder::new(sink());
    /// ```
    pub fn new(inner: W) -> RleEncoder<W> {
        RleEncoder::with_state(RunState::default(), inner)
    }

    /// Creates a new `RleEncoder<R>` with the specified initial state.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::sink;
    /// use binhex::rle::write::{RunState, RleEncoder};
    ///
    /// let encoder = RleEncoder::with_state(RunState::Before, sink());
    /// ```
    pub fn with_state(state: RunState, inner: W) -> RleEncoder<W> {
        RleEncoder { inner, state }
    }

    /// Returns the current state of this encoder.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::sink;
    /// use binhex::rle::write::{RunState, RleEncoder};
    ///
    /// // maybe some data was already written to the writer
    /// let encoder = RleEncoder::with_state(RunState::Length(4), sink());
    /// assert_eq!(encoder.state(), RunState::Length(4));
    /// ```
    pub fn state(&self) -> RunState {
        self.state
    }

    /// Gets a imutable reference to the underlying writer.
    ///
    /// It is inadvisable to directly write to the underlying writer because doing so might result in corrupted data when writing to the encoder.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{sink, Sink};
    /// use binhex::rle::write::RleEncoder;
    ///
    /// let encoder = RleEncoder::new(sink());
    /// let writer: &Sink = encoder.get_ref();
    /// ```
    pub fn get_ref(&self) -> &W {
        &self.inner
    }

    /// Gets a mutable reference to the underlying writer.
    ///
    /// It is inadvisable to directly write to the underlying writer, see [`RleEncoder::get_ref`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{sink, Sink};
    /// use binhex::rle::write::RleEncoder;
    ///
    /// let mut encoder = RleEncoder::new(sink());
    /// let writer: &mut Sink = encoder.get_mut();
    /// ```
    pub fn get_mut(&mut self) -> &mut W {
        &mut self.inner
    }

    /// Unwrap this `RleEncoder<R>` and return the underlying writer.
    ///
    /// The current state is flushed before returning the writer.
    ///
    /// # Errors
    ///
    /// An [`Err`] will be returned if an error occurs while flushing the state.
    ///
    /// In this case the encoder is returned too to allow for error handling.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{sink, Sink};
    /// use binhex::rle::write::RleEncoder;
    ///
    /// let encoder = RleEncoder::new(sink());
    /// let writer: Sink = encoder.into_inner().unwrap();
    /// ```
    pub fn into_inner(mut self) -> Result<W, IntoInnerError<Self>> {
        match self.flush_state() {
            Ok(()) => Ok(self.into_parts().0),
            Err(e) => Err(IntoInnerError::new(self, e)),
        }
    }

    /// Disassembles this `RleEncoder<W>`, returning the underlying writer and its current state.
    ///
    /// Note that this does not flush the current state.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::Write;
    /// use std::num::NonZeroU8;
    /// use binhex::rle::write::{RleEncoder, RunState};
    ///
    /// let mut buffer = [0; 2];
    ///
    /// let encoder = RleEncoder::with_state(RunState::Delimiter(NonZeroU8::new(4).unwrap()), &mut buffer[..]);
    /// let (writer, state) = encoder.into_parts();
    /// assert_eq!(writer.len(), 2);
    /// assert_eq!(state, RunState::Delimiter(NonZeroU8::new(4).unwrap()));
    /// ```
    pub fn into_parts(mut self) -> (W, RunState) {
        // SAFETY: forget(self) prevents double dropping inner
        let inner = unsafe { ptr::read(&mut self.inner) };
        let state = self.state;
        mem::forget(self);
        (inner, state)
    }

    /// like [`RleEncoder::flush`] but dont flushes the underlying writer
    pub fn flush_state(&mut self) -> IoResult<()> {
        // transition between states until there is
        // nothig more to write or we encounter an error
        while self.state != RunState::Before {
            // save states eagerly to prevent data corruption on panic
            self.state = self
                .state
                .transition(&mut self.inner)
                // incomplete writes will be treated as errors by flush
                .unwrap_or(Err(ErrorKind::WriteZero.into()))?
        }
        Ok(())
    }
}

impl<W: Write> Write for RleEncoder<W> {
    fn write(&mut self, buf: &[u8]) -> IoResult<usize> {
        match buf {
            // nothing to write
            [] => Ok(0),
            // add bytes to accumulator
            [first, ..] => match self.state {
                // add bytes to existing accumulation
                RunState::Accumulate(byte, count) if byte == *first && count.get() < u8::MAX => {
                    let count = count.get()
                        + buf
                            .iter()
                            .copied()
                            // prevent overflow
                            .take((u8::MAX - count.get()) as usize)
                            .take_while(|byte| byte == first)
                            .count() as u8;
                    debug_assert_ne!(count, 0);
                    // SAFETY: guard will never be zero since we guard against overflows
                    self.state =
                        RunState::Accumulate(*first, unsafe { NonZeroU8::new_unchecked(count) });
                    Ok(count as usize)
                }
                // flush state and create new accumulation
                _ => {
                    // like flush_state but dont treat empty writes as an error
                    while self.state != RunState::Before {
                        self.state = match self.state.transition(&mut self.inner) {
                            Some(Ok(state)) => state,
                            Some(Err(e)) => return Err(e),
                            None => return Ok(0)
                        }
                    }
                    let count = buf
                        .iter()
                        .copied()
                        // prevent overflow
                        .take(u8::MAX as usize)
                        .take_while(|byte| byte == first)
                        .count() as u8;
                    debug_assert_ne!(count, 0);
                    // SAFETY: the existence of first guarantees a non zero result
                    self.state =
                        RunState::Accumulate(*first, unsafe { NonZeroU8::new_unchecked(count) });
                    Ok(count as usize)
                }
            },
        }
    }

    fn flush(&mut self) -> IoResult<()> {
        // dont forget to flush the underlying writer too
        self.flush_state().and_then(|_| self.inner.flush())
    }
}

impl<W: Write> Drop for RleEncoder<W> {
    /// Flushes the state on drop to prevent data loss but ignores errors while doing so
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::io::Write;
    /// use binhex::rle::write::RleEncoder;
    /// 
    /// // buffer cant hold any data
    /// let mut buffer: [u8; 0] = [];
    /// {
    ///     let mut encoder = RleEncoder::new(&mut buffer[..]);
    ///     // data gets temporarily buffered
    ///     assert_eq!(encoder.write(&[1, 1, 1]).unwrap(), 3);
    /// }
    /// // data is lost since it cant be flushed
    /// ```
    fn drop(&mut self) {
        let _r = self.flush_state();
    }
}
