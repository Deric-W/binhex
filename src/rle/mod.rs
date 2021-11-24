//! Utilities for the RLE compression used by BinHex 4 files
//! 
//! BinHex 4 files use a RLE compression described [here](https://files.stairways.com/other/binhex-40-specs-info.txt).
//! This module provides utilities for working with streams of data using that format.

// The rle module is part of binhex (https://github.com/Deric-W/binhex)
// Copyright (C) 2021  Eric Wolf
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, version 3.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.
// SPDX-License-Identifier: GPL-3.0-only

pub mod read;
pub mod write;

/// byte seperating the byte to be expanded and the length of a run
pub const RUN_DELIMITER: u8 = 0x90;
