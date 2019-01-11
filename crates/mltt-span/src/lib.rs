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

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(usize);

impl FileId {
    pub fn to_usize(self) -> usize {
        self.0
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    file_id: FileId,
    start: ByteIndex,
    end: ByteIndex,
}

impl Span {
    pub fn new(file_id: FileId, start: impl Into<ByteIndex>, end: impl Into<ByteIndex>) -> Span {
        let start = start.into();
        let end = end.into();

        assert!(end >= start);

        Span {
            file_id,
            start,
            end,
        }
    }

    /// Gives an empty span at the start of a file.
    pub fn initial(file_id: FileId) -> Span {
        Span::new(file_id, 0, 0)
    }

    /// Gives the "EOF" span for a file with the given text. This is an empty
    /// span pointing at the end.
    pub fn eof(file_id: FileId, text: &str) -> Span {
        let len = text.len();
        Span::new(file_id, len, len)
    }

    pub fn with_start(&self, start: impl Into<ByteIndex>) -> Span {
        Span::new(self.file_id(), start, self.end())
    }

    pub fn with_end(&self, end: impl Into<ByteIndex>) -> Span {
        Span::new(self.file_id(), self.start(), end)
    }

    pub fn file_id(&self) -> FileId {
        self.file_id
    }

    pub fn start(&self) -> ByteIndex {
        self.start
    }

    pub fn end(&self) -> ByteIndex {
        self.end
    }

    pub fn contains(self, span: Span) -> bool {
        self.file_id() == span.file_id() && self.start() >= span.start() && self.end() < span.end()
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

#[derive(Debug, Clone)]
pub struct File {
    pub name: String,
    pub contents: String,
}

#[derive(Debug, Clone)]
pub struct Files {
    files: Vec<File>,
}

impl Files {
    pub fn new() -> Files {
        Files { files: Vec::new() }
    }

    pub fn add(&mut self, name: impl Into<String>, contents: impl Into<String>) -> FileId {
        let file_id = FileId(self.files.len());
        self.files.push(File {
            name: name.into(),
            contents: contents.into(),
        });
        file_id
    }

    pub fn byte_index(
        &self,
        file_id: FileId,
        line: impl Into<LineIndex>,
        column: impl Into<ColumnIndex>,
    ) -> Option<ByteIndex> {
        let source = &self[file_id].contents;
        let line = line.into();
        let column = column.into();
        let mut seen_lines = 0;
        let mut seen_bytes = 0;

        for (pos, _) in source.match_indices('\n') {
            if seen_lines == line.to_usize() {
                // FIXME: Column != byte width for larger unicode characters
                return Some(ByteIndex::from(seen_bytes + column.to_usize()));
            } else {
                seen_lines += 1;
                seen_bytes = pos + 1;
            }
        }

        None
    }

    pub fn location(
        &self,
        file_id: FileId,
        index: impl Into<ByteIndex>,
    ) -> Option<language_reporting::Location> {
        let source = &self[file_id].contents;
        let index = index.into();
        let mut seen_lines = 0;
        let mut seen_bytes = 0;

        for (pos, _) in source.match_indices('\n') {
            if pos > index.to_usize() {
                return Some(language_reporting::Location {
                    line: seen_lines,
                    column: index.to_usize() - seen_bytes,
                });
            } else {
                seen_lines += 1;
                seen_bytes = pos;
            }
        }

        None
    }

    pub fn line_span(&self, file_id: FileId, line: impl Into<LineIndex>) -> Option<Span> {
        let source = &self[file_id].contents;
        let line = line.into();
        let mut seen_lines = 0;
        let mut seen_bytes = 0;

        for (pos, _) in source.match_indices('\n') {
            if seen_lines >= line.to_usize() {
                return Some(Span::new(file_id, seen_bytes, pos));
            } else {
                seen_lines += 1;
                seen_bytes = pos + 1;
            }
        }

        None
    }

    pub fn source(&self, span: Span) -> Option<&str> {
        let source = &self[span.file_id()].contents;

        Some(&source[span.start().to_usize()..span.end().to_usize()])
    }
}

impl language_reporting::ReportingFiles for Files {
    type Span = Span;
    type FileId = FileId;

    fn file_id(&self, span: Span) -> FileId {
        span.file_id()
    }

    fn file_name(&self, file_id: FileId) -> language_reporting::FileName {
        language_reporting::FileName::Verbatim(self[file_id].name.clone())
    }

    fn byte_span(&self, file_id: FileId, from_index: usize, to_index: usize) -> Option<Span> {
        Some(Span::new(file_id, from_index, to_index)) // FIXME: Check file span?
    }

    fn byte_index(&self, file_id: FileId, line: usize, column: usize) -> Option<usize> {
        Files::byte_index(self, file_id, line, column).map(ByteIndex::to_usize)
    }

    fn location(&self, file_id: FileId, index: usize) -> Option<language_reporting::Location> {
        Files::location(self, file_id, index)
    }

    fn line_span(&self, file_id: FileId, line: usize) -> Option<Span> {
        Files::line_span(self, file_id, line)
    }

    fn source(&self, span: Span) -> Option<String> {
        Files::source(self, span).map(str::to_owned)
    }
}

impl ops::Index<FileId> for Files {
    type Output = File;

    fn index(&self, index: FileId) -> &File {
        &self.files[index.to_usize()]
    }
}
