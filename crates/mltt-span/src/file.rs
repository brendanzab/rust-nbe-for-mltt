use std::fmt;
use std::ops;

use crate::{ByteIndex, ColumnIndex, LineIndex, Location, Span};

/// A handle that points to a file in the database.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(usize);

impl fmt::Display for FileId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

/// A span in a file.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileSpan {
    file_id: FileId,
    span: Span,
}

impl FileSpan {
    pub fn new(file_id: FileId, span: Span) -> FileSpan {
        FileSpan { file_id, span }
    }

    pub fn file_id(&self) -> FileId {
        self.file_id
    }

    pub fn span(&self) -> Span {
        self.span
    }
}

impl language_reporting::ReportingSpan for FileSpan {
    fn with_start(&self, start: usize) -> FileSpan {
        FileSpan::new(self.file_id(), self.span().with_start(start))
    }

    fn with_end(&self, end: usize) -> FileSpan {
        FileSpan::new(self.file_id(), self.span().with_end(end))
    }

    fn start(&self) -> usize {
        self.span().start().to_usize()
    }

    fn end(&self) -> usize {
        self.span().end().to_usize()
    }
}

impl fmt::Debug for FileSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}:{:?}", self.file_id(), self.span)
    }
}

/// The contents of a file that is stored in the database.
#[derive(Debug, Clone)]
pub struct File {
    /// The id of the file in the database.
    id: FileId,
    /// The name of the file.
    name: String,
    /// The source code of the file.
    contents: String,
    /// The starting byte indices in the source code.
    line_starts: Vec<ByteIndex>,
}

impl File {
    /// Get the handle that points to this file.
    pub fn id(&self) -> FileId {
        self.id
    }

    /// Get the name of the file.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get a slice to the contents of the file.
    pub fn contents(&self) -> &str {
        &self.contents
    }

    /// Get a slice to the line start indices of the file.
    pub fn line_starts(&self) -> &[ByteIndex] {
        &self.line_starts
    }

    /// Get the span of the source of this file.
    pub fn span(&self) -> Span {
        Span::from_str(self.contents())
    }

    /// Get the file span of the source of this file.
    pub fn file_span(&self) -> FileSpan {
        FileSpan::new(self.id(), self.span())
    }
}

/// A database of source files.
#[derive(Debug, Clone)]
pub struct Files {
    files: Vec<File>,
}

impl Files {
    /// Create a new, empty database.
    pub fn new() -> Files {
        Files { files: Vec::new() }
    }

    /// Add a file to the database, returning the handle that can be used to refer to it again.
    pub fn add(&mut self, name: impl Into<String>, contents: impl Into<String>) -> FileId {
        let file_id = FileId(self.files.len());
        let contents = contents.into();

        // Pre-compute the line starting positions
        let line_starts = std::iter::once(0)
            .chain(contents.match_indices('\n').map(|(i, _)| i + 1))
            .chain(std::iter::once(contents.len()))
            .map(ByteIndex::from)
            .collect();

        // Add the file to the database
        self.files.push(File {
            id: file_id,
            name: name.into(),
            contents,
            line_starts,
        });

        file_id
    }

    pub fn byte_index(
        &self,
        file_id: FileId,
        line: impl Into<LineIndex>,
        column: impl Into<ColumnIndex>,
    ) -> Option<ByteIndex> {
        let file = &self[file_id];
        let line = line.into();
        let column = column.into();
        let line_start = *file.line_starts().get(line.to_usize())?;

        Some(column.to_byte_index(file.contents(), line_start))
    }

    pub fn line_span(&self, file_id: FileId, line: impl Into<LineIndex>) -> Option<FileSpan> {
        let file = &self[file_id];
        let line = line.into();
        let line_start = *file.line_starts().get(line.to_usize())?;
        let next_line_start = *file.line_starts().get(line.to_usize() + 1)?;

        Some(FileSpan::new(
            file_id,
            Span::new(line_start, next_line_start),
        ))
    }

    pub fn location(&self, file_id: FileId, byte: impl Into<ByteIndex>) -> Option<Location> {
        let file = &self[file_id];
        let byte = byte.into();
        let line_starts = file.line_starts();
        match line_starts.binary_search(&byte) {
            // Found the start of a line
            Ok(line) => Some(Location {
                line: LineIndex::from(line),
                column: ColumnIndex::from(0),
                byte,
            }),
            // Found something in the middle of a line
            Err(next_line) => {
                let line = LineIndex::from(next_line - 1);
                let line_start = line_starts[line.to_usize()];
                let column = ColumnIndex::from_str(file.contents(), line_start, byte)?;

                Some(Location { line, column, byte })
            },
        }
    }

    /// Return a slice of the source file, given a span.
    pub fn source(&self, span: FileSpan) -> Option<&str> {
        let start = span.span().start().to_usize();
        let end = span.span().end().to_usize();

        self[span.file_id()].contents.get(start..end)
    }
}

impl language_reporting::ReportingFiles for Files {
    type Span = FileSpan;
    type FileId = FileId;

    fn file_id(&self, span: FileSpan) -> FileId {
        span.file_id()
    }

    fn file_name(&self, file_id: FileId) -> language_reporting::FileName {
        language_reporting::FileName::Verbatim(self[file_id].name.clone())
    }

    fn byte_span(&self, file_id: FileId, from_index: usize, to_index: usize) -> Option<FileSpan> {
        let span = Span::new(from_index, to_index);
        if self[file_id].span().contains(span) {
            Some(FileSpan::new(file_id, span))
        } else {
            None
        }
    }

    fn byte_index(&self, file_id: FileId, line: usize, column: usize) -> Option<usize> {
        Files::byte_index(self, file_id, line, column).map(ByteIndex::to_usize)
    }

    fn line_span(&self, file_id: FileId, line: usize) -> Option<FileSpan> {
        Files::line_span(self, file_id, line)
    }

    fn location(&self, file_id: FileId, index: usize) -> Option<language_reporting::Location> {
        Files::location(self, file_id, index).map(Location::into)
    }

    fn source(&self, span: FileSpan) -> Option<String> {
        Files::source(self, span).map(str::to_owned)
    }
}

impl ops::Index<FileId> for Files {
    type Output = File;

    fn index(&self, index: FileId) -> &File {
        &self.files[index.0]
    }
}

#[cfg(test)]
mod test {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn line_starts() {
        let mut files = Files::new();
        let file_id = files.add("test", "foo\nbar\r\n\nbaz");

        assert_eq!(
            files[file_id].line_starts(),
            [
                ByteIndex::from(0),  // "foo\n"
                ByteIndex::from(4),  // "bar\r\n"
                ByteIndex::from(9),  // ""
                ByteIndex::from(10), // "baz"
                ByteIndex::from(13),
            ],
        );
    }

    #[test]
    fn location() {
        let mut files = Files::new();
        let file_id = files.add("test", "foo\nbar\r\n\nbaz");

        assert_eq!(
            files.location(file_id, 0),
            Some(Location {
                line: LineIndex::from(0),
                column: ColumnIndex::from(0),
                byte: ByteIndex::from(0),
            }),
        );

        assert_eq!(
            files.location(file_id, 7),
            Some(Location {
                line: LineIndex::from(1),
                column: ColumnIndex::from(3),
                byte: ByteIndex::from(7),
            }),
        );

        assert_eq!(
            files.location(file_id, 8),
            Some(Location {
                line: LineIndex::from(1),
                column: ColumnIndex::from(4),
                byte: ByteIndex::from(8),
            }),
        );

        assert_eq!(
            files.location(file_id, 9),
            Some(Location {
                line: LineIndex::from(2),
                column: ColumnIndex::from(0),
                byte: ByteIndex::from(9),
            }),
        );

        assert_eq!(files.location(file_id, 100), None);
    }

    #[test]
    fn line_span_sources() {
        let mut files = Files::new();
        let file_id = files.add("test", "foo\nbar\r\n\nbaz");

        let line_sources = (0..5)
            .map(|line| {
                let line_span = files.line_span(file_id, LineIndex::from(line))?;
                files.source(line_span)
            })
            .collect::<Vec<_>>();

        assert_eq!(
            line_sources,
            [
                Some("foo\n"),
                Some("bar\r\n"),
                Some("\n"),
                Some("baz"),
                None
            ],
        );
    }
}
