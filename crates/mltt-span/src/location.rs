use crate::{ByteIndex, ColumnIndex, LineIndex};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    pub line: LineIndex,
    pub column: ColumnIndex,
    pub byte: ByteIndex,
}
