use std::fmt;

use crate::{ByteIndex, ByteSize};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span<File> {
    file: File,
    start: ByteIndex,
    end: ByteIndex,
}

impl<File: Copy + PartialEq> Span<File> {
    pub fn new(file: File, start: impl Into<ByteIndex>, end: impl Into<ByteIndex>) -> Span<File> {
        let start = start.into();
        let end = end.into();

        assert!(end >= start);

        Span { file, start, end }
    }

    /// Gives an empty span at the start of a file.
    pub fn initial(file: File) -> Span<File> {
        Span::new(file, 0, 0)
    }

    pub fn from_str(file: File, s: &str) -> Span<File> {
        Span::new(file, 0, s.len())
    }

    pub fn with_start(&self, start: impl Into<ByteIndex>) -> Span<File> {
        Span::new(self.file(), start, self.end())
    }

    pub fn with_end(&self, end: impl Into<ByteIndex>) -> Span<File> {
        Span::new(self.file(), self.start(), end)
    }

    pub fn file(&self) -> File {
        self.file
    }

    pub fn start(&self) -> ByteIndex {
        self.start
    }

    pub fn end(&self) -> ByteIndex {
        self.end
    }

    pub fn contains(self, span: Span<File>) -> bool {
        self.file() == span.file() && self.start() >= span.start() && self.end() < span.end()
    }

    pub fn contains_index(self, index: impl Into<ByteIndex>) -> bool {
        let index = index.into();
        self.start() <= index && index < self.end()
    }

    pub fn len(&self) -> ByteSize {
        self.end() - self.start()
    }
}

impl<File: Copy + PartialEq + fmt::Debug> language_reporting::ReportingSpan for Span<File> {
    fn with_start(&self, start: usize) -> Span<File> {
        Span::with_start(self, ByteIndex::from(start))
    }

    fn with_end(&self, end: usize) -> Span<File> {
        Span::with_end(self, ByteIndex::from(end))
    }

    fn start(&self) -> usize {
        Span::start(self).to_usize()
    }

    fn end(&self) -> usize {
        Span::end(self).to_usize()
    }
}
