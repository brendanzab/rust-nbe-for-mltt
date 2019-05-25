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
    test!(forward_declarations, "forward-declarations");
    test!(literals, "literals");
    test!(let_expressions, "let-expressions");
    test!(primitives, "primitives");
    test!(records, "records");
}

mod elaborate {
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
            test!(implicit, "fun-intro/implicit");
            test!(explicit, "fun-intro/explicit");
        }

        mod literal_intro {
            mod u8 {
                test!(dec_min, "literal-intro/u8/dec-min");
                test!(dec_max, "literal-intro/u8/dec-max");
            }
        }

        mod record_intro {
            test!(singleton, "record-intro/singleton");
            test!(singleton1, "record-intro/singleton1");
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
            test!(implicit, "fun-elim/implicit");
            test!(explicit, "fun-elim/explicit");
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

        mod literal_intro {
            mod bool {
                test!(false_, "literal-intro/bool/false");
                test!(true_, "literal-intro/bool/true");
            }

            #[rustfmt::skip]
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

            #[rustfmt::skip]
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
            }
        }

        mod literal_type {
            test!(bool, "literal-type/bool");
            test!(char, "literal-type/char");
            test!(f32, "literal-type/f32");
            test!(f64, "literal-type/f64");
            test!(s8, "literal-type/s8");
            test!(s16, "literal-type/s16");
            test!(s32, "literal-type/s32");
            test!(s64, "literal-type/s64");
            test!(string, "literal-type/string");
            test!(u8, "literal-type/u8");
            test!(u16, "literal-type/u16");
            test!(u32, "literal-type/u32");
            test!(u64, "literal-type/u64");
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
    }
}
