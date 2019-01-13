use std::ops;

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
