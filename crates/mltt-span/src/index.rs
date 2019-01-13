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

impl ops::Sub<ByteIndex> for ByteIndex {
    type Output = ByteSize;

    fn sub(self, other: ByteIndex) -> ByteSize {
        ByteSize::from(self.to_usize() - other.to_usize())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ByteSize(usize);

impl ByteSize {
    pub fn to_usize(self) -> usize {
        self.0
    }

    pub fn from_char_utf8(ch: char) -> ByteSize {
        ByteSize::from(ch.len_utf8())
    }

    pub fn from_char_utf16(ch: char) -> ByteSize {
        ByteSize::from(ch.len_utf16())
    }

    pub fn from_str(s: &str) -> ByteSize {
        ByteSize::from(s.len())
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

/// 0-based column number, in utf-8 characters
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ColumnIndex(usize);

impl ColumnIndex {
    pub fn to_usize(self) -> usize {
        self.0
    }
}

impl From<usize> for ColumnIndex {
    fn from(src: usize) -> ColumnIndex {
        ColumnIndex(src)
    }
}
