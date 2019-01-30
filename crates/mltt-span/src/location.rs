use crate::{ByteIndex, ColumnIndex, LineIndex};

/// A location in a source file.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    /// The line index in the source file.
    pub line: LineIndex,
    /// The column index in the source file.
    pub column: ColumnIndex,
    /// The byte index in the source file.
    pub byte: ByteIndex,
}

impl Into<language_reporting::Location> for Location {
    fn into(self) -> language_reporting::Location {
        language_reporting::Location {
            line: self.line.to_usize(),
            column: self.column.to_usize(),
        }
    }
}
