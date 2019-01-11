use language_reporting;
use std::ops;

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

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    start: ByteIndex,
    end: ByteIndex,
}

impl Span {
    pub fn new(start: impl Into<ByteIndex>, end: impl Into<ByteIndex>) -> Span {
        let start = start.into();
        let end = end.into();

        assert!(end >= start);

        Span { start, end }
    }

    /// Gives an empty span at the start of a file.
    pub fn initial() -> Span {
        Span::new(0, 0)
    }

    /// Gives the "EOF" span for a file with the given text. This is an empty
    /// span pointing at the end.
    pub fn eof(text: &str) -> Span {
        let len = text.len();
        Span::new(len, len)
    }

    pub fn with_start(&self, start: impl Into<ByteIndex>) -> Span {
        Span::new(start, self.end())
    }

    pub fn with_end(&self, end: impl Into<ByteIndex>) -> Span {
        Span::new(self.start(), end)
    }

    pub fn start(&self) -> ByteIndex {
        self.start
    }

    pub fn end(&self) -> ByteIndex {
        self.end
    }

    pub fn contains(self, span: Span) -> bool {
        self.start() >= span.start() && self.end() < span.end()
    }

    pub fn contains_index(self, index: impl Into<ByteIndex>) -> bool {
        let index = index.into();
        self.start() <= index && index < self.end()
    }

    pub fn len(&self) -> ByteSize {
        self.end() - self.start()
    }
}

impl language_reporting::ReportingSpan for Span {
    fn with_start(&self, start: usize) -> Span {
        Span::with_start(self, ByteIndex::from(start))
    }

    fn with_end(&self, end: usize) -> Span {
        Span::with_end(self, ByteIndex::from(end))
    }

    fn start(&self) -> usize {
        Span::start(self).to_usize()
    }

    fn end(&self) -> usize {
        Span::end(self).to_usize()
    }
}
