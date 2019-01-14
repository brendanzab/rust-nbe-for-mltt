use std::ops;

use crate::{ByteIndex, ByteSize, ColumnIndex, LineIndex, LineSize, Location, Span};

/// A handle that points to a file in the database
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(usize);

/// A span in a file
pub type FileSpan = Span<FileId>;

/// The contents of a file that is stored in the database
#[derive(Debug, Clone)]
pub struct File {
    id: FileId,
    name: String,
    contents: String,
}

impl File {
    /// Get the handle that points to this file
    pub fn id(&self) -> FileId {
        self.id
    }

    /// Get the name of the file
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get a reference to the contents of the file
    pub fn contents(&self) -> &str {
        &self.contents
    }

    /// Get the span of the source of this file
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
        self.files.push(File {
            id: file_id,
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
        let mut current_line = LineIndex::from(0);
        let mut current_byte = ByteIndex::from(0);

        for (pos, _) in source.match_indices('\n') {
            let pos = ByteIndex::from(pos);
            if current_line >= line {
                return Some(column.to_byte_index(source, current_byte));
            } else {
                current_line += LineSize::from(1);
                current_byte = pos + ByteSize::from_char_len_utf8('\n');
            }
        }

        None
    }

    pub fn location(&self, file_id: FileId, byte: impl Into<ByteIndex>) -> Option<Location> {
        let source = &self[file_id].contents;
        let byte = byte.into();
        let mut current_line = LineIndex::from(0);
        let mut current_byte = ByteIndex::from(0);

        for (pos, _) in source.match_indices('\n') {
            let pos = ByteIndex::from(pos);
            if pos > byte {
                return Some(Location {
                    byte,
                    line: LineIndex::from(current_line),
                    column: ColumnIndex::from_str(source, byte, current_byte),
                });
            } else {
                current_line += LineSize::from(1);
                current_byte = pos;
            }
        }

        None
    }

    pub fn line_span(&self, file_id: FileId, line: impl Into<LineIndex>) -> Option<FileSpan> {
        let source = &self[file_id].contents;
        let line = line.into();
        let mut current_line = LineIndex::from(0);
        let mut current_byte = ByteIndex::from(0);

        for (pos, _) in source.match_indices('\n') {
            let pos = ByteIndex::from(pos);
            if current_line >= line {
                return Some(Span::new(file_id, current_byte, pos));
            } else {
                current_line += LineSize::from(1);
                current_byte = pos + ByteSize::from_char_len_utf8('\n');
            }
        }

        None
    }

    /// Return a slice of the source file, given a span
    pub fn source(&self, span: FileSpan) -> Option<&str> {
        let start = span.start().to_usize();
        let end = span.end().to_usize();

        Some(&self[span.source()].contents[start..end])
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
