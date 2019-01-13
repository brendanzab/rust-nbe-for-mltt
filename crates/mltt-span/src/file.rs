use std::ops;

use crate::{ByteIndex, ByteSize, ColumnIndex, LineIndex, LineSize, Location, Span};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(usize);

impl FileId {
    pub fn to_usize(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone)]
pub struct File {
    id: FileId,
    name: String,
    contents: String,
}

impl File {
    pub fn id(&self) -> FileId {
        self.id
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn contents(&self) -> &str {
        &self.contents
    }

    pub fn span(&self) -> Span<FileId> {
        Span::from_str(self.id(), self.contents())
    }
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
                current_byte = pos + ByteSize::from_char_utf8('\n');
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

    pub fn line_span(&self, file_id: FileId, line: impl Into<LineIndex>) -> Option<Span<FileId>> {
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
                current_byte = pos + ByteSize::from_char_utf8('\n');
            }
        }

        None
    }

    pub fn source(&self, span: Span<FileId>) -> Option<&str> {
        let start = span.start().to_usize();
        let end = span.end().to_usize();

        Some(&self[span.source()].contents[start..end])
    }
}

impl language_reporting::ReportingFiles for Files {
    type Span = Span<FileId>;
    type FileId = FileId;

    fn file_id(&self, span: Span<FileId>) -> FileId {
        span.source()
    }

    fn file_name(&self, file_id: FileId) -> language_reporting::FileName {
        language_reporting::FileName::Verbatim(self[file_id].name.clone())
    }

    fn byte_span(
        &self,
        file_id: FileId,
        from_index: usize,
        to_index: usize,
    ) -> Option<Span<FileId>> {
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

    fn line_span(&self, file_id: FileId, line: usize) -> Option<Span<FileId>> {
        Files::line_span(self, file_id, line)
    }

    fn source(&self, span: Span<FileId>) -> Option<String> {
        Files::source(self, span).map(str::to_owned)
    }
}

impl ops::Index<FileId> for Files {
    type Output = File;

    fn index(&self, index: FileId) -> &File {
        &self.files[index.to_usize()]
    }
}
