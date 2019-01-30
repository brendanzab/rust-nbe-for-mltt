use std::ops;

use crate::{ByteIndex, ByteSize, ColumnIndex, LineIndex, Location, Span};

/// A handle that points to a file in the database
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(usize);

/// A span in a file
pub type FileSpan = Span<FileId>;

fn line_starts(text: &str) -> Vec<ByteIndex> {
    let mut acc = ByteIndex::from(0);
    let end_index = ByteIndex::from(0) + ByteSize::from_str_len_utf8(text);
    text.lines()
        .map(|line_text| {
            let line_start = acc;
            acc += ByteSize::from_str_len_utf8(line_text);
            if text[acc.to_usize()..].starts_with("\r\n") {
                acc += ByteSize::from_str_len_utf8("\r\n");
            } else if text[acc.to_usize()..].starts_with("\n") {
                acc += ByteSize::from_str_len_utf8("\n");
            }
            line_start
        })
        .chain(std::iter::once(end_index))
        .collect()
}

/// The contents of a file that is stored in the database
#[derive(Debug, Clone)]
pub struct File {
    id: FileId,
    name: String,
    contents: String,
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
    pub fn span(&self) -> FileSpan {
        Span::from_str(self.id(), self.contents())
    }
}

/// A database of source file
#[derive(Debug, Clone)]
pub struct Files {
    files: Vec<File>,
}

impl Files {
    /// Create a new, empty database
    pub fn new() -> Files {
        Files { files: Vec::new() }
    }

    /// Add a file to the database, returning the handle that can be used to refer to it again
    pub fn add(&mut self, name: impl Into<String>, contents: impl Into<String>) -> FileId {
        let file_id = FileId(self.files.len());
        let contents = contents.into();
        let line_starts = line_starts(&contents);

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

    pub fn location(&self, file_id: FileId, byte: impl Into<ByteIndex>) -> Option<Location> {
        let file = &self[file_id];
        let byte = byte.into();
        let line_starts = file.line_starts();
        match line_starts.binary_search(&byte) {
            // Found the start of a line directly:
            Ok(line) => Some(Location {
                line: LineIndex::from(line),
                column: ColumnIndex::from(0),
                byte,
            }),
            Err(next_line) => {
                let line = LineIndex::from(next_line - 1);

                // Found something in the middle.
                let line_start = line_starts[line.to_usize()];

                // count utf-8 characters to find column
                let column = ColumnIndex::from_str(file.contents(), line_start, byte)?;

                Some(Location { line, column, byte })
            },
        }
    }

    pub fn line_span(&self, file_id: FileId, line: impl Into<LineIndex>) -> Option<FileSpan> {
        let file = &self[file_id];
        let line = line.into();
        let line_start = *file.line_starts().get(line.to_usize())?;
        let next_line_start = *file.line_starts().get(line.to_usize() + 1)?;

        Some(Span::new(file_id, line_start, next_line_start))
    }

    /// Return a slice of the source file, given a span
    pub fn source(&self, span: FileSpan) -> Option<&str> {
        let start = span.start().to_usize();
        let end = span.end().to_usize();

        self[span.source()].contents.get(start..end)
    }
}

impl language_reporting::ReportingFiles for Files {
    type Span = FileSpan;
    type FileId = FileId;

    fn file_id(&self, span: FileSpan) -> FileId {
        span.source()
    }

    fn file_name(&self, file_id: FileId) -> language_reporting::FileName {
        language_reporting::FileName::Verbatim(self[file_id].name.clone())
    }

    fn byte_span(&self, file_id: FileId, from_index: usize, to_index: usize) -> Option<FileSpan> {
        let file_span = self[file_id].span();
        let span = Span::new(file_id, from_index, to_index);

        if file_span.contains(span) {
            Some(span)
        } else {
            None
        }
    }

    fn byte_index(&self, file_id: FileId, line: usize, column: usize) -> Option<usize> {
        Files::byte_index(self, file_id, line, column).map(ByteIndex::to_usize)
    }

    fn location(&self, file_id: FileId, index: usize) -> Option<language_reporting::Location> {
        Files::location(self, file_id, index).map(|location| language_reporting::Location {
            line: location.line.to_usize(),
            column: location.column.to_usize(),
        })
    }

    fn line_span(&self, file_id: FileId, line: usize) -> Option<FileSpan> {
        Files::line_span(self, file_id, line)
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
        let file_id = files.add("test", "foo\nbar\r\nbaz");

        assert_eq!(
            files[file_id].line_starts(),
            [
                ByteIndex::from(0), // "foo\n"
                ByteIndex::from(4), // "bar\r\n"
                ByteIndex::from(9), // "baz"
                ByteIndex::from(12),
            ],
        );
    }

    #[test]
    fn location() {
        let mut files = Files::new();
        let file_id = files.add("test", "foo\nbar\r\nbaz");

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
        let file_id = files.add("test", "foo\nbar\r\nbaz");

        let line_sources = (0..4)
            .map(|line| {
                let line_span = files.line_span(file_id, LineIndex::from(line))?;
                files.source(line_span)
            })
            .collect::<Vec<_>>();

        assert_eq!(
            line_sources,
            [Some("foo\n"), Some("bar\r\n"), Some("baz"), None],
        );
    }
}
