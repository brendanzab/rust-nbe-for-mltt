use std::ops;

/// Byte index into a text string
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ByteIndex(usize);

impl ByteIndex {
    pub fn to_usize(self) -> usize {
        self.0
    }
}

impl From<usize> for ByteIndex {
    fn from(src: usize) -> ByteIndex {
        ByteIndex(src)
    }
}

impl ops::Add<ByteSize> for ByteIndex {
    type Output = ByteIndex;

    fn add(self, other: ByteSize) -> ByteIndex {
        ByteIndex::from(self.to_usize() + other.to_usize())
    }
}

impl ops::AddAssign<ByteSize> for ByteIndex {
    fn add_assign(&mut self, other: ByteSize) {
        self.0 += other.to_usize();
    }
}

impl ops::Sub<ByteIndex> for ByteIndex {
    type Output = ByteSize;

    fn sub(self, other: ByteIndex) -> ByteSize {
        ByteSize::from(self.to_usize() - other.to_usize())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ByteSize(usize);

impl ByteSize {
    pub fn from_char_utf8(ch: char) -> ByteSize {
        ByteSize::from(ch.len_utf8())
    }

    pub fn from_char_utf16(ch: char) -> ByteSize {
        ByteSize::from(ch.len_utf16())
    }

    pub fn from_str(s: &str) -> ByteSize {
        ByteSize::from(s.len())
    }

    pub fn to_usize(self) -> usize {
        self.0
    }
}

impl ops::Add<ByteSize> for ByteSize {
    type Output = ByteSize;

    fn add(self, other: ByteSize) -> ByteSize {
        ByteSize::from(self.to_usize() + other.to_usize())
    }
}

impl ops::AddAssign<ByteSize> for ByteSize {
    fn add_assign(&mut self, other: ByteSize) {
        self.0 += other.to_usize();
    }
}

impl From<usize> for ByteSize {
    fn from(src: usize) -> ByteSize {
        ByteSize(src)
    }
}

/// 0-based line number
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LineIndex(usize);

impl LineIndex {
    pub fn to_usize(self) -> usize {
        self.0
    }
}

impl From<usize> for LineIndex {
    fn from(src: usize) -> LineIndex {
        LineIndex(src)
    }
}

impl ops::Add<LineSize> for LineIndex {
    type Output = LineIndex;

    fn add(self, other: LineSize) -> LineIndex {
        LineIndex::from(self.to_usize() + other.to_usize())
    }
}

impl ops::AddAssign<LineSize> for LineIndex {
    fn add_assign(&mut self, other: LineSize) {
        self.0 += other.to_usize();
    }
}

impl ops::Sub<LineIndex> for LineIndex {
    type Output = LineSize;

    fn sub(self, other: LineIndex) -> LineSize {
        LineSize::from(self.to_usize() - other.to_usize())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LineSize(usize);

impl LineSize {
    pub fn to_usize(self) -> usize {
        self.0
    }
}

impl ops::Add<LineSize> for LineSize {
    type Output = LineSize;

    fn add(self, other: LineSize) -> LineSize {
        LineSize::from(self.to_usize() + other.to_usize())
    }
}

impl ops::AddAssign<LineSize> for LineSize {
    fn add_assign(&mut self, other: LineSize) {
        self.0 += other.to_usize();
    }
}

impl From<usize> for LineSize {
    fn from(src: usize) -> LineSize {
        LineSize(src)
    }
}

/// 0-based column number, in utf-8 characters
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ColumnIndex(usize);

impl ColumnIndex {
    pub fn from_str(src: &str, line_start_byte: ByteIndex, column_byte: ByteIndex) -> ColumnIndex {
        let line_src = &src[line_start_byte.to_usize()..column_byte.to_usize()];
        ColumnIndex::from(line_src.chars().count())
    }

    pub fn to_usize(self) -> usize {
        self.0
    }

    /// Convert to a byte size, based on a unicode string
    pub fn to_byte_size(self, line_src: &str) -> ByteSize {
        line_src
            .chars()
            .map(ByteSize::from_char_utf8)
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
