//! Utilities for the RLE compression used by BinHex 4 files

pub mod read;
pub mod write;

/// byte seperating the byte to be expanded and the length of a run
pub const RUN_DELIMITER: u8 = 0x90;
