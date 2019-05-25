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

        test!(case_default_bind, "case-default-bind");
        test!(case_default, "case-default");
        test!(case_overlapping, "case-overlapping");
        test!(case_simple, "case-simple");
        test!(fun_intro_implicit, "fun-intro-implicit");
        test!(fun_intro, "fun-intro");
        test!(literal_intro_u8_dec_min, "literal-intro-u8-dec-min");
        test!(literal_intro_u8_dec_max, "literal-intro-u8-dec-max");
        test!(if_, "if");
        test!(prim, "prim");
        test!(record_intro_singleton, "record-intro-singleton");
        test!(record_intro_singleton1, "record-intro-singleton1");
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

        test!(fun_elim_implicit, "fun-elim-implicit");
        test!(fun_elim, "fun-elim");
        test!(fun_type_param_group_1, "fun-type-param-group-1");
        test!(fun_type_param_group_2, "fun-type-param-group-2");
        test!(fun_type_term_term, "fun-type-term-term");
        test!(fun_type_term_type, "fun-type-term-type");
        test!(fun_type_term_type1, "fun-type-term-type1");
        test!(fun_type_type_term, "fun-type-type-term");
        test!(fun_type_type_type, "fun-type-type-type");
        test!(fun_type_type1_term, "fun-type-type1-term");
        test!(literal_intro_bool_false, "literal-intro-bool-false");
        test!(literal_intro_bool_true, "literal-intro-bool-true");
        test!(literal_intro_string, "literal-intro-string");
        test!(literal_type_bool, "literal-type-bool");
        test!(literal_type_char, "literal-type-char");
        test!(literal_type_f32, "literal-type-f32");
        test!(literal_type_f64, "literal-type-f64");
        test!(literal_type_s8, "literal-type-s8");
        test!(literal_type_s16, "literal-type-s16");
        test!(literal_type_s32, "literal-type-s32");
        test!(literal_type_s64, "literal-type-s64");
        test!(literal_type_string, "literal-type-string");
        test!(literal_type_u8, "literal-type-u8");
        test!(literal_type_u16, "literal-type-u16");
        test!(literal_type_u32, "literal-type-u32");
        test!(literal_type_u64, "literal-type-u64");
        test!(parens, "parens");
        test!(record_elim_dependent, "record-elim-dependent");
        test!(record_elim_singleton, "record-elim-singleton");
        test!(record_intro_empty, "record-intro-empty");
        test!(record_dependent, "record-type-dependent");
        test!(record_type_empty, "record-type-empty");
        test!(record_type_singleton, "record-type-singleton");
        test!(record_type_singleton1, "record-type-singleton1");
        test!(type_, "type");
        test!(type0, "type0");
        test!(type1, "type1");
    }
}
