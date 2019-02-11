#![warn(rust_2018_idioms)]

extern crate proc_macro;

use heck::SnakeCase;
use std::fmt::Write;
use std::fs;
use std::path::{Path, PathBuf};

#[proc_macro]
pub fn generate_tests(_tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let mut result = String::new();

    // Get the base path of the tests, relative to the current directory
    let base_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    generate_tests_module(&mut result, &base_path);

    result.parse().unwrap()
}

/// Recursively generate nested modules in a way that reflects the structure of
/// the test directories
fn generate_tests_module(result: &mut dyn Write, base_path: &Path) {
    let mod_name = base_path.file_name().unwrap().to_str().unwrap();
    writeln!(result, "mod {} {{", mod_name.to_snake_case()).unwrap();

    let dir_entries = fs::read_dir(base_path)
        .unwrap_or_else(|err| panic!("failed to read dir `{}`: {}", base_path.display(), err))
        .map(|dir_entry| {
            dir_entry.unwrap_or_else(|err| {
                panic!("failed to read entry in `{}`: {}", base_path.display(), err)
            })
        });

    for dir_entry in dir_entries {
        if let Ok(metadata) = dir_entry.metadata() {
            if metadata.is_dir() {
                generate_tests_module(result, &dir_entry.path());
            } else if dir_entry.path().extension().and_then(|ext| ext.to_str()) == Some("mltt") {
                generate_test(result, &dir_entry.path());
            }
        }
    }

    writeln!(result, "}}").unwrap();
}

fn generate_test(result: &mut dyn Write, test_path: &Path) {
    let test_name_base = test_path.with_extension("");
    let test_name = test_name_base.file_name().unwrap().to_str().unwrap();

    writeln!(
        result,
        r#"#[test] fn {name}() {{ mltt_test_harness::run("{name}", "{path}"); }}"#,
        name = test_name.to_snake_case(),
        path = test_path.display(),
    )
    .unwrap();
}
