use crate::{ByteIndex, ColumnIndex, LineIndex};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    pub line: LineIndex,
    pub column: ColumnIndex,
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
