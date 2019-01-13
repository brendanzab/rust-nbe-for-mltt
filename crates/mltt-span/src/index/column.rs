use std::ops;
use unicode_segmentation::UnicodeSegmentation;

use crate::{ByteIndex, ByteSize};

/// 0-based column number, in utf-8 characters
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ColumnIndex(usize);

impl ColumnIndex {
    pub fn from_str(src: &str, line_start_byte: ByteIndex, column_byte: ByteIndex) -> ColumnIndex {
        let line_src = &src[line_start_byte.to_usize()..column_byte.to_usize()];
        ColumnIndex::from(line_src.graphemes(true).count())
    }

    pub fn to_usize(self) -> usize {
        self.0
    }

    /// Convert to a byte size, based on a unicode string
    pub fn to_byte_size(self, line_src: &str) -> ByteSize {
        line_src
            .graphemes(true)
            .map(ByteSize::from_str)
            .fold(ByteSize::from(0), |acc, size| acc + size)
    }

    /// Convert to a byte index, based on a unicode string and a starting index
    pub fn to_byte_index(self, src: &str, line_start_byte: ByteIndex) -> ByteIndex {
        line_start_byte + self.to_byte_size(&src[line_start_byte.to_usize()..])
    }
}

impl From<usize> for ColumnIndex {
    fn from(src: usize) -> ColumnIndex {
        ColumnIndex(src)
    }
}

impl ops::Add<ColumnSize> for ColumnIndex {
    type Output = ColumnIndex;

    fn add(self, other: ColumnSize) -> ColumnIndex {
        ColumnIndex::from(self.to_usize() + other.to_usize())
    }
}

impl ops::AddAssign<ColumnSize> for ColumnIndex {
    fn add_assign(&mut self, other: ColumnSize) {
        self.0 += other.to_usize();
    }
}

impl ops::Sub<ColumnIndex> for ColumnIndex {
    type Output = ColumnSize;

    fn sub(self, other: ColumnIndex) -> ColumnSize {
        ColumnSize::from(self.to_usize() - other.to_usize())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ColumnSize(usize);

impl ColumnSize {
    pub fn to_usize(self) -> usize {
        self.0
    }
}

impl From<usize> for ColumnSize {
    fn from(src: usize) -> ColumnSize {
        ColumnSize(src)
    }
}

impl ops::Add<ColumnSize> for ColumnSize {
    type Output = ColumnSize;

    fn add(self, other: ColumnSize) -> ColumnSize {
        ColumnSize::from(self.to_usize() + other.to_usize())
    }
}

impl ops::AddAssign<ColumnSize> for ColumnSize {
    fn add_assign(&mut self, other: ColumnSize) {
        self.0 += other.to_usize();
    }
}
