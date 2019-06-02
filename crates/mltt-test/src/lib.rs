//! Integration tests for the MLTT language.

#![cfg(test)]

mod support;

mod samples {
    macro_rules! test {
        ($test_name:ident, $file_name:literal) => {
            #[test]
            fn $test_name() {
                $crate::support::run_sample($file_name);
            }
        };
    }

    test!(categories, "categories");
    test!(combinators, "combinators");
    test!(connectives, "connectives");
    test!(cumulativity, "cumulativity");
    test!(empty, "empty");
    test!(primitives, "primitives");
    test!(records, "records");
}

mod elaborate {
    mod check_fail {
        macro_rules! test {
            ($test_name:ident, $file_name:literal) => {
                #[test]
                fn $test_name() {
                    $crate::support::run_elaborate_check_fail($file_name);
                }
            };
        }

        mod literal_intro {
            mod int {
                mod u8 {
                    test!(dec_overflow, "literal-intro/int/u8/dec-overflow");
                    test!(dec_underflow, "literal-intro/int/u8/dec-underflow");
                }

                mod u16 {
                    test!(dec_overflow, "literal-intro/int/u16/dec-overflow");
                    test!(dec_underflow, "literal-intro/int/u16/dec-underflow");
                }
            }
        }

        mod record_intro {
            test!(superfluous_field, "record-intro/superfluous-field");
            test!(unexpected_field, "record-intro/unexpected-field");
        }
    }

    mod check_pass {
        macro_rules! test {
            ($test_name:ident, $file_name:literal) => {
                #[test]
                fn $test_name() {
                    $crate::support::run_elaborate_check_pass($file_name);
                }
            };
        }

        test!(if_, "if");
        test!(parens, "parens");
        test!(prim, "prim");

        mod case {
            test!(default_bind, "case/default-bind");
            test!(default, "case/default");
            test!(overlapping, "case/overlapping");
            test!(simple, "case/simple");
        }

        mod fun_intro {
            test!(explicit, "fun-intro/explicit");
            test!(implicit, "fun-intro/implicit");
            test!(instance, "fun-intro/instance");
        }

        mod literal_intro {
            mod int {
                mod s8 {
                    test!(bin_min, "literal-intro/int/s8/bin-min");
                    test!(bin_max, "literal-intro/int/s8/bin-max");
                    test!(dec_min, "literal-intro/int/s8/dec-min");
                    test!(dec_max, "literal-intro/int/s8/dec-max");
                    test!(oct_min, "literal-intro/int/s8/oct-min");
                    test!(oct_max, "literal-intro/int/s8/oct-max");
                    test!(hex_min, "literal-intro/int/s8/hex-min");
                    test!(hex_max, "literal-intro/int/s8/hex-max");
                }

                mod s16 {
                    test!(bin_min, "literal-intro/int/s16/bin-min");
                    test!(bin_max, "literal-intro/int/s16/bin-max");
                    test!(dec_min, "literal-intro/int/s16/dec-min");
                    test!(dec_max, "literal-intro/int/s16/dec-max");
                    test!(oct_min, "literal-intro/int/s16/oct-min");
                    test!(oct_max, "literal-intro/int/s16/oct-max");
                    test!(hex_min, "literal-intro/int/s16/hex-min");
                    test!(hex_max, "literal-intro/int/s16/hex-max");
                }

                mod s32 {
                    test!(bin_min, "literal-intro/int/s32/bin-min");
                    test!(bin_max, "literal-intro/int/s32/bin-max");
                    test!(dec_min, "literal-intro/int/s32/dec-min");
                    test!(dec_max, "literal-intro/int/s32/dec-max");
                    test!(oct_min, "literal-intro/int/s32/oct-min");
                    test!(oct_max, "literal-intro/int/s32/oct-max");
                    test!(hex_min, "literal-intro/int/s32/hex-min");
                    test!(hex_max, "literal-intro/int/s32/hex-max");
                }

                mod s64 {
                    test!(bin_min, "literal-intro/int/s64/bin-min");
                    test!(bin_max, "literal-intro/int/s64/bin-max");
                    test!(dec_min, "literal-intro/int/s64/dec-min");
                    test!(dec_max, "literal-intro/int/s64/dec-max");
                    test!(oct_min, "literal-intro/int/s64/oct-min");
                    test!(oct_max, "literal-intro/int/s64/oct-max");
                    test!(hex_min, "literal-intro/int/s64/hex-min");
                    test!(hex_max, "literal-intro/int/s64/hex-max");
                }

                mod u8 {
                    test!(bin_min, "literal-intro/int/u8/bin-min");
                    test!(bin_max, "literal-intro/int/u8/bin-max");
                    test!(dec_min, "literal-intro/int/u8/dec-min");
                    test!(dec_max, "literal-intro/int/u8/dec-max");
                    test!(oct_min, "literal-intro/int/u8/oct-min");
                    test!(oct_max, "literal-intro/int/u8/oct-max");
                    test!(hex_min, "literal-intro/int/u8/hex-min");
                    test!(hex_max, "literal-intro/int/u8/hex-max");
                    test!(samples, "literal-intro/int/u8/samples"); // TODO: Split up into separate tests
                }

                mod u16 {
                    test!(bin_min, "literal-intro/int/u16/bin-min");
                    test!(bin_max, "literal-intro/int/u16/bin-max");
                    test!(dec_min, "literal-intro/int/u16/dec-min");
                    test!(dec_max, "literal-intro/int/u16/dec-max");
                    test!(oct_min, "literal-intro/int/u16/oct-min");
                    test!(oct_max, "literal-intro/int/u16/oct-max");
                    test!(hex_min, "literal-intro/int/u16/hex-min");
                    test!(hex_max, "literal-intro/int/u16/hex-max");
                }

                mod u32 {
                    test!(bin_min, "literal-intro/int/u32/bin-min");
                    test!(bin_max, "literal-intro/int/u32/bin-max");
                    test!(dec_min, "literal-intro/int/u32/dec-min");
                    test!(dec_max, "literal-intro/int/u32/dec-max");
                    test!(oct_min, "literal-intro/int/u32/oct-min");
                    test!(oct_max, "literal-intro/int/u32/oct-max");
                    test!(hex_min, "literal-intro/int/u32/hex-min");
                    test!(hex_max, "literal-intro/int/u32/hex-max");
                }

                mod u64 {
                    test!(bin_min, "literal-intro/int/u64/bin-min");
                    test!(bin_max, "literal-intro/int/u64/bin-max");
                    test!(dec_min, "literal-intro/int/u64/dec-min");
                    test!(dec_max, "literal-intro/int/u64/dec-max");
                    test!(oct_min, "literal-intro/int/u64/oct-min");
                    test!(oct_max, "literal-intro/int/u64/oct-max");
                    test!(hex_min, "literal-intro/int/u64/hex-min");
                    test!(hex_max, "literal-intro/int/u64/hex-max");
                }
            }
        }

        mod record_intro {
            test!(dependent_pair, "record-intro/dependent-pair");
            test!(singleton, "record-intro/singleton");
            test!(singleton1, "record-intro/singleton1");
        }
    }

    mod synth_fail {
        macro_rules! test {
            ($test_name:ident, $file_name:literal) => {
                #[test]
                fn $test_name() {
                    $crate::support::run_elaborate_synth_fail($file_name);
                }
            };
        }

        mod fun_intro {
            test!(ambiguous, "fun-intro/ambiguous");
        }

        mod hole {
            test!(ambiguous, "hole/ambiguous");
        }

        mod let_ {
            test!(already_defined, "let/already-defined");
            test!(not_yet_declared, "let/not-yet-declared");
        }

        mod literal_intro {
            mod float {
                test!(float_ambiguous, "literal-intro/float/ambiguous");
            }

            mod int {
                test!(int_ambiguous, "literal-intro/int/ambiguous");
            }
        }

        mod prim {
            test!(ambiguous, "prim/ambiguous");
            test!(unknown, "prim/unknown");
        }

        mod record_elim {
            test!(field_not_found, "record-elim/field-not-found");
        }

        mod record_intro {
            test!(ambiguous, "record-intro/ambiguous");
        }

        mod universe {
            test!(overflow, "universe/overflow");
        }

        mod var {
            test!(overflow, "var/unbound");
        }
    }

    mod synth_pass {
        macro_rules! test {
            ($test_name:ident, $file_name:literal) => {
                #[test]
                fn $test_name() {
                    $crate::support::run_elaborate_synth_pass($file_name);
                }
            };
        }

        test!(parens, "parens");

        mod fun_elim {
            test!(explicit, "fun-elim/explicit");
            test!(implicit, "fun-elim/implicit");
            test!(implicit_insert_meta, "fun-elim/implicit-insert-meta");
            test!(instance, "fun-elim/instance");
        }

        mod fun_type {
            test!(param_group_1, "fun-type/param-group-1");
            test!(param_group_2, "fun-type/param-group-2");
        }

        mod fun_type_arrow {
            test!(term_term, "fun-type-arrow/term-term");
            test!(term_type, "fun-type-arrow/term-type");
            test!(term_type1, "fun-type-arrow/term-type1");
            test!(type_term, "fun-type-arrow/type-term");
            test!(type_type, "fun-type-arrow/type-type");
            test!(type1_term, "fun-type-arrow/type1-term");
        }

        mod let_ {
            test!(complicated, "let/complicated");
            test!(definition, "let/definition");
            test!(declaration_definition, "let/declaration-definition");
            test!(forward_declarations, "let/forward-declarations");
        }

        #[rustfmt::skip]
        mod literal_intro {
            mod char {
                test!(ascii, "literal-intro/char/ascii");
                test!(escape_ascii_lower_max, "literal-intro/char/escape-ascii-lower-max");
                test!(escape_ascii_upper_max, "literal-intro/char/escape-ascii-upper-max");
                test!(escape_simple_back_slash, "literal-intro/char/escape-simple-back-slash");
                test!(escape_simple_carriage_return, "literal-intro/char/escape-simple-carriage-return");
                test!(escape_simple_double_quote, "literal-intro/char/escape-simple-double-quote");
                test!(escape_simple_new_line, "literal-intro/char/escape-simple-new-line");
                test!(escape_simple_null, "literal-intro/char/escape-simple-null");
                test!(escape_simple_single_quote, "literal-intro/char/escape-simple-single-quote");
                test!(escape_simple_tab, "literal-intro/char/escape-simple-tab");
                test!(escape_unicode_lower_max, "literal-intro/char/escape-unicode-lower-max");
                test!(escape_unicode_upper_max, "literal-intro/char/escape-unicode-upper-max");
            }

            mod string {
                test!(ascii, "literal-intro/string/ascii");
                test!(escape_ascii_lower_max, "literal-intro/string/escape-ascii-lower-max");
                test!(escape_ascii_upper_max, "literal-intro/string/escape-ascii-upper-max");
                test!(escape_simple_back_slash, "literal-intro/string/escape-simple-back-slash");
                test!(escape_simple_carriage_return, "literal-intro/string/escape-simple-carriage-return");
                test!(escape_simple_double_quote, "literal-intro/string/escape-simple-double-quote");
                test!(escape_simple_new_line, "literal-intro/string/escape-simple-new-line");
                test!(escape_simple_null, "literal-intro/string/escape-simple-null");
                test!(escape_simple_single_quote, "literal-intro/string/escape-simple-single-quote");
                test!(escape_simple_tab, "literal-intro/string/escape-simple-tab");
                test!(escape_unicode_lower_max, "literal-intro/string/escape-unicode-lower-max");
                test!(escape_unicode_upper_max, "literal-intro/string/escape-unicode-upper-max");
                test!(escapes, "literal-intro/string/escapes");
            }
        }

        mod record_elim {
            test!(dependent_pair, "record-elim/dependent-pair");
            test!(singleton, "record-elim/singleton");
        }

        mod record_intro {
            test!(empty, "record-intro/empty");
        }

        mod record_type {
            test!(dependent_pair, "record-type/dependent-pair");
            test!(empty, "record-type/empty");
            test!(singleton, "record-type/singleton");
            test!(singleton1, "record-type/singleton1");
        }

        mod universe {
            test!(type_, "universe/type");
            test!(type0, "universe/type0");
            test!(type1, "universe/type1");
        }

        mod var {
            test!(bool, "var/bool");
            test!(false_, "var/false");
            test!(true_, "var/true");
            test!(char, "var/char");
            test!(f32, "var/f32");
            test!(f64, "var/f64");
            test!(s8, "var/s8");
            test!(s16, "var/s16");
            test!(s32, "var/s32");
            test!(s64, "var/s64");
            test!(string, "var/string");
            test!(u8, "var/u8");
            test!(u16, "var/u16");
            test!(u32, "var/u32");
            test!(u64, "var/u64");
        }
    }
}
