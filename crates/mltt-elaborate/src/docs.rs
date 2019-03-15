use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_concrete::SpannedString;
use mltt_span::FileSpan;

/// Concatenate a bunch of lines of documentation into a single string, removing
/// comment prefixes if they are found.
pub fn concat(doc_lines: &[SpannedString<'_>]) -> String {
    let mut doc = String::new();
    for doc_line in doc_lines {
        // Strip the `||| ` or `|||` prefix left over from tokenization
        // We assume that each line of documentation has a trailing new line
        doc.push_str(match doc_line.value {
            doc_line if doc_line.starts_with("||| ") => &doc_line["||| ".len()..],
            doc_line if doc_line.starts_with("|||") => &doc_line["|||".len()..],
            doc_line => &doc_line[..],
        });
    }
    doc
}

/// Select the documentation from either the declaration or the definition,
/// returning an error if both are present.
pub fn merge(
    name: &SpannedString<'_>,
    decl_docs: &[SpannedString<'_>],
    defn_docs: &[SpannedString<'_>],
) -> Result<String, Diagnostic<FileSpan>> {
    match (decl_docs, defn_docs) {
        ([], []) => Ok("".to_owned()),
        (docs, []) => Ok(concat(docs)),
        ([], docs) => Ok(concat(docs)),
        (_, _) => Err(
            Diagnostic::new_error(format!("`{}` is already documented!", name.value))
                .with_label(
                    DiagnosticLabel::new_primary(doc_span(decl_docs).unwrap())
                        .with_message("the definition's documentation"),
                )
                .with_label(
                    DiagnosticLabel::new_secondary(doc_span(decl_docs).unwrap())
                        .with_message("the declaration's documentation"),
                ),
        ),
    }
}

pub fn doc_span(docs: &[SpannedString<'_>]) -> Option<FileSpan> {
    Some(FileSpan::merge(docs.first()?.span(), docs.last()?.span()))
}
