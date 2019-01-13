use std::ops;

use crate::{ByteIndex, ColumnIndex, LineIndex, Span};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(usize);

impl FileId {
    pub fn to_usize(self) -> usize {
        self.0
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

    pub fn line_span(&self, file_id: FileId, line: impl Into<LineIndex>) -> Option<Span<FileId>> {
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

    pub fn source(&self, span: Span<FileId>) -> Option<&str> {
        let source = &self[span.file()].contents;

        Some(&source[span.start().to_usize()..span.end().to_usize()])
    }
}

impl language_reporting::ReportingFiles for Files {
    type Span = Span<FileId>;
    type FileId = FileId;

    fn file_id(&self, span: Span<FileId>) -> FileId {
        span.file()
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
        Some(Span::new(file_id, from_index, to_index)) // FIXME: Check file span?
    }

    fn byte_index(&self, file_id: FileId, line: usize, column: usize) -> Option<usize> {
        Files::byte_index(self, file_id, line, column).map(ByteIndex::to_usize)
    }

    fn location(&self, file_id: FileId, index: usize) -> Option<language_reporting::Location> {
        Files::location(self, file_id, index)
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
