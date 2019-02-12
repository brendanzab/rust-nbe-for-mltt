use heck::SnakeCase;
use std::env;
use std::io::Write;
use std::fs::{self, File};
use std::path::{Path, PathBuf};

pub fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("tests.rs");
    let mut file = File::create(&dest_path).unwrap();

    // Get the base path of the tests, relative to the current directory
    let base_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    generate_tests_module(&mut file, &base_path, 0);
}

/// Recursively generate nested modules in a way that reflects the structure of
/// the test directories
fn generate_tests_module(result: &mut impl Write, base_path: &Path, indent: usize) {
    let mod_name = base_path.file_name().unwrap().to_str().unwrap();
    writeln!(
        result,
        "{:indent$}mod {mod_name} {{",
        "",
        indent = indent,
        mod_name = mod_name.to_snake_case(),
    ).unwrap();

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
                generate_tests_module(result, &dir_entry.path(), indent + 4);
            } else if dir_entry.path().extension().and_then(|ext| ext.to_str()) == Some("mltt") {
                generate_test(result, &dir_entry.path(), indent + 4);
            }
        }
    }

    writeln!(result, "}}").unwrap();
}

fn generate_test(result: &mut impl Write, test_path: &Path, indent: usize) {
    let test_name_base = test_path.with_extension("");
    let test_name = test_name_base.file_name().unwrap().to_str().unwrap();

    writeln!(
        result,
        r#"{:indent$}#[test] fn {name}() {{ mltt_test_harness::run("{name}", "{path}"); }}"#,
        "",
        indent = indent,
        name = test_name.to_snake_case(),
        path = test_path.display(),
    )
    .unwrap();
}
