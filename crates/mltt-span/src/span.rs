use std::fmt;

use crate::{ByteIndex, ByteSize};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span<Source> {
    source: Source,
    start: ByteIndex,
    end: ByteIndex,
}

impl<Source: Copy> Span<Source> {
    pub fn new(
        source: Source,
        start: impl Into<ByteIndex>,
        end: impl Into<ByteIndex>,
    ) -> Span<Source> {
        let start = start.into();
        let end = end.into();

        assert!(end >= start);

        Span { source, start, end }
    }

    /// Gives an empty span at the start of a source.
    pub fn initial(source: Source) -> Span<Source> {
        Span::new(source, 0, 0)
    }

    pub fn from_str(source: Source, s: &str) -> Span<Source> {
        Span::new(source, 0, s.len())
    }

    pub fn with_source<NewSource: Copy>(&self, source: NewSource) -> Span<NewSource> {
        Span::new(source, self.start(), self.end())
    }

    pub fn with_start(&self, start: impl Into<ByteIndex>) -> Span<Source> {
        Span::new(self.source(), start, self.end())
    }

    pub fn with_end(&self, end: impl Into<ByteIndex>) -> Span<Source> {
        Span::new(self.source(), self.start(), end)
    }

    pub fn source(&self) -> Source {
        self.source
    }

    pub fn start(&self) -> ByteIndex {
        self.start
    }

    pub fn end(&self) -> ByteIndex {
        self.end
    }

    pub fn contains(self, span: Span<Source>) -> bool
    where
        Source: PartialEq,
    {
        self.source() == span.source() && self.start() >= span.start() && self.end() < span.end()
    }

    pub fn contains_index(self, index: impl Into<ByteIndex>) -> bool {
        let index = index.into();
        self.start() <= index && index < self.end()
    }

    pub fn len(&self) -> ByteSize {
        self.end() - self.start()
    }
}

impl<Source: Copy + fmt::Debug> language_reporting::ReportingSpan for Span<Source> {
    fn with_start(&self, start: usize) -> Span<Source> {
        Span::with_start(self, ByteIndex::from(start))
    }

    fn with_end(&self, end: usize) -> Span<Source> {
        Span::with_end(self, ByteIndex::from(end))
    }

    fn start(&self) -> usize {
        Span::start(self).to_usize()
    }

    fn end(&self) -> usize {
        Span::end(self).to_usize()
    }
}
