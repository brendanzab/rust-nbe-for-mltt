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
