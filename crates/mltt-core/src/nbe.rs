//! Normalization by evaluation.
//!
//! Here we implement a full normalization algorithm by first implementing
//! evaluation to `Value`s in weak-head-normal-form, and then reading it back
//! `Normal` terms.

use std::error::Error;
use std::fmt;
use std::rc::Rc;

use crate::syntax::core::{Item, RcTerm, Term};
use crate::syntax::domain::{
    AppClosure, Elim, Env, EnvSize, Head, LiteralClosure, RcType, RcValue, Spine, Value,
};
use crate::syntax::{AppMode, Label, LiteralIntro};

/// An error produced during normalization.
///
/// If a term has been successfully type checked prior to evaluation or
/// normalization, then this error should never be produced.
#[derive(Debug, Clone, PartialEq)]
pub struct NbeError {
    pub message: String,
}

impl NbeError {
    pub fn new(message: impl Into<String>) -> NbeError {
        NbeError {
            message: message.into(),
        }
    }
}

impl Error for NbeError {}

impl fmt::Display for NbeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to normalize: {}", self.message)
    }
}

/// An entry in the primitive environment.
#[derive(Clone)]
pub struct PrimEntry {
    /// The number of arguments that this primitive accepts before it reduces.
    // TODO: change to `Vec<Strictness>`?
    pub arity: u32,
    /// The interpretation to use during normalization.
    ///
    /// # Returns
    ///
    /// - `Some(Ok(_))`: if the primitive returned a value
    /// - `Some(Err(_))`: if the primitive resulted in an evaluation error
    /// - `None`: if the primitive is stuck on an argument
    pub interpretation: fn(Vec<RcValue>) -> Option<Result<RcValue, NbeError>>,
}

impl PrimEntry {
    /// Interpret a primitive if there are enough function eliminators provided
    /// in the spine. `None` is returned if evaluation is stuck.
    ///
    /// Also known as [δ-reduction (delta-reduction)][δ-reduction].
    ///
    /// [δ-reduction]: http://barrywatson.se/lsi/lsi_delta_reduction.html
    pub fn interpret<'spine>(
        &self,
        spine: &'spine [Elim],
    ) -> Option<Result<(RcValue, &'spine [Elim]), NbeError>> {
        // Prevent `split_at` from panicking if we don't have enough eliminators
        // in the spine.
        if spine.len() < self.arity as usize {
            return None;
        }

        let (arg_spine, rest_spine) = spine.split_at(self.arity as usize);
        let mut args = Vec::with_capacity(self.arity as usize);

        for arg_elim in arg_spine {
            match arg_elim {
                Elim::Fun(_, arg) => args.push(arg.clone()),
                Elim::Literal(_) | Elim::Record(_) => return None, // Return NbeError?
            }
        }

        let result = (self.interpretation)(args)?;
        Some(result.map(|value| (value, rest_spine)))
    }
}

impl fmt::Debug for PrimEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrimEntry")
            .field("arity", &self.arity)
            .field("interpretation", &"|args| { .. }")
            .finish()
    }
}

/// An environment of primitives to use during normalization.
#[derive(Debug, Clone)]
pub struct PrimEnv {
    entries: im::HashMap<String, PrimEntry>,
}

impl PrimEnv {
    /// Construct a new, empty environment.
    pub fn new() -> PrimEnv {
        PrimEnv {
            entries: im::HashMap::new(),
        }
    }

    /// Lookup an entry in the environment.
    pub fn lookup_entry(&self, name: &str) -> Option<&PrimEntry> {
        self.entries.get(name)
    }

    /// Add a new entry to the environment.
    pub fn add_entry(&mut self, name: String, entry: PrimEntry) {
        self.entries.insert(name, entry);
    }
}

trait TryFromValue {
    fn try_from_value(src: &Value) -> Option<&Self>;
}

macro_rules! impl_try_from_value_literal {
    ($T:ty, $Literal:ident) => {
        impl TryFromValue for $T {
            fn try_from_value(src: &Value) -> Option<&$T> {
                match src {
                    Value::LiteralIntro(LiteralIntro::$Literal(value)) => Some(value),
                    _ => None,
                }
            }
        }
    };
}

impl_try_from_value_literal!(Rc<str>, String);
impl_try_from_value_literal!(char, Char);
impl_try_from_value_literal!(bool, Bool);
impl_try_from_value_literal!(u8, U8);
impl_try_from_value_literal!(u16, U16);
impl_try_from_value_literal!(u32, U32);
impl_try_from_value_literal!(u64, U64);
impl_try_from_value_literal!(i8, S8);
impl_try_from_value_literal!(i16, S16);
impl_try_from_value_literal!(i32, S32);
impl_try_from_value_literal!(i64, S64);
impl_try_from_value_literal!(f32, F32);
impl_try_from_value_literal!(f64, F64);

impl Default for PrimEnv {
    fn default() -> PrimEnv {
        macro_rules! count {
            () => (0);
            ($x:tt $($xs:tt)*) => (1 + count!($($xs)*));
        }

        macro_rules! prim {
            (|$($param_name:ident : $PType:ty),*| $body:expr) => {
                PrimEntry {
                    arity: count!($($param_name)*),
                    interpretation: {
                        fn interpretation(params: Vec<RcValue>) -> Option<Result<RcValue, NbeError>> {
                            match params.as_slice() {
                                [$(ref $param_name),*] => {
                                    $(let $param_name = <$PType>::try_from_value($param_name)?;)*
                                    Some($body)
                                }
                                _ => None,
                            }
                        }
                        interpretation
                    }
                }
            };
        }

        PrimEnv {
            entries: im::hashmap! {
                "abort".to_owned() => prim!(|message: Rc<str>| Err(NbeError::new(message.to_string()))),

                "string-eq".to_owned() => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(RcValue::literal_intro(lhs == rhs))),
                "char-eq".to_owned() => prim!(|lhs: char, rhs: char| Ok(RcValue::literal_intro(lhs == rhs))),
                "u8-eq".to_owned() => prim!(|lhs: u8, rhs: u8| Ok(RcValue::literal_intro(lhs == rhs))),
                "u16-eq".to_owned() => prim!(|lhs: u16, rhs: u16| Ok(RcValue::literal_intro(lhs == rhs))),
                "u32-eq".to_owned() => prim!(|lhs: u32, rhs: u32| Ok(RcValue::literal_intro(lhs == rhs))),
                "u64-eq".to_owned() => prim!(|lhs: u64, rhs: u64| Ok(RcValue::literal_intro(lhs == rhs))),
                "s8-eq".to_owned() => prim!(|lhs: i8, rhs: i8| Ok(RcValue::literal_intro(lhs == rhs))),
                "s16-eq".to_owned() => prim!(|lhs: i16, rhs: i16| Ok(RcValue::literal_intro(lhs == rhs))),
                "s32-eq".to_owned() => prim!(|lhs: i32, rhs: i32| Ok(RcValue::literal_intro(lhs == rhs))),
                "s64-eq".to_owned() => prim!(|lhs: i64, rhs: i64| Ok(RcValue::literal_intro(lhs == rhs))),
                "f32-eq".to_owned() => prim!(|lhs: f32, rhs: f32| Ok(RcValue::literal_intro(lhs == rhs))),
                "f64-eq".to_owned() => prim!(|lhs: f64, rhs: f64| Ok(RcValue::literal_intro(lhs == rhs))),

                "string-ne".to_owned() => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(RcValue::literal_intro(lhs != rhs))),
                "char-ne".to_owned() => prim!(|lhs: char, rhs: char| Ok(RcValue::literal_intro(lhs != rhs))),
                "u8-ne".to_owned() => prim!(|lhs: u8, rhs: u8| Ok(RcValue::literal_intro(lhs != rhs))),
                "u16-ne".to_owned() => prim!(|lhs: u16, rhs: u16| Ok(RcValue::literal_intro(lhs != rhs))),
                "u32-ne".to_owned() => prim!(|lhs: u32, rhs: u32| Ok(RcValue::literal_intro(lhs != rhs))),
                "u64-ne".to_owned() => prim!(|lhs: u64, rhs: u64| Ok(RcValue::literal_intro(lhs != rhs))),
                "s8-ne".to_owned() => prim!(|lhs: i8, rhs: i8| Ok(RcValue::literal_intro(lhs != rhs))),
                "s16-ne".to_owned() => prim!(|lhs: i16, rhs: i16| Ok(RcValue::literal_intro(lhs != rhs))),
                "s32-ne".to_owned() => prim!(|lhs: i32, rhs: i32| Ok(RcValue::literal_intro(lhs != rhs))),
                "s64-ne".to_owned() => prim!(|lhs: i64, rhs: i64| Ok(RcValue::literal_intro(lhs != rhs))),
                "f32-ne".to_owned() => prim!(|lhs: f32, rhs: f32| Ok(RcValue::literal_intro(lhs != rhs))),
                "f64-ne".to_owned() => prim!(|lhs: f64, rhs: f64| Ok(RcValue::literal_intro(lhs != rhs))),

                "string-lt".to_owned() => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(RcValue::literal_intro(lhs < rhs))),
                "char-lt".to_owned() => prim!(|lhs: char, rhs: char| Ok(RcValue::literal_intro(lhs < rhs))),
                "u8-lt".to_owned() => prim!(|lhs: u8, rhs: u8| Ok(RcValue::literal_intro(lhs < rhs))),
                "u16-lt".to_owned() => prim!(|lhs: u16, rhs: u16| Ok(RcValue::literal_intro(lhs < rhs))),
                "u32-lt".to_owned() => prim!(|lhs: u32, rhs: u32| Ok(RcValue::literal_intro(lhs < rhs))),
                "u64-lt".to_owned() => prim!(|lhs: u64, rhs: u64| Ok(RcValue::literal_intro(lhs < rhs))),
                "s8-lt".to_owned() => prim!(|lhs: i8, rhs: i8| Ok(RcValue::literal_intro(lhs < rhs))),
                "s16-lt".to_owned() => prim!(|lhs: i16, rhs: i16| Ok(RcValue::literal_intro(lhs < rhs))),
                "s32-lt".to_owned() => prim!(|lhs: i32, rhs: i32| Ok(RcValue::literal_intro(lhs < rhs))),
                "s64-lt".to_owned() => prim!(|lhs: i64, rhs: i64| Ok(RcValue::literal_intro(lhs < rhs))),
                "f32-lt".to_owned() => prim!(|lhs: f32, rhs: f32| Ok(RcValue::literal_intro(lhs < rhs))),
                "f64-lt".to_owned() => prim!(|lhs: f64, rhs: f64| Ok(RcValue::literal_intro(lhs < rhs))),

                "string-le".to_owned() => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(RcValue::literal_intro(lhs <= rhs))),
                "char-le".to_owned() => prim!(|lhs: char, rhs: char| Ok(RcValue::literal_intro(lhs <= rhs))),
                "u8-le".to_owned() => prim!(|lhs: u8, rhs: u8| Ok(RcValue::literal_intro(lhs <= rhs))),
                "u16-le".to_owned() => prim!(|lhs: u16, rhs: u16| Ok(RcValue::literal_intro(lhs <= rhs))),
                "u32-le".to_owned() => prim!(|lhs: u32, rhs: u32| Ok(RcValue::literal_intro(lhs <= rhs))),
                "u64-le".to_owned() => prim!(|lhs: u64, rhs: u64| Ok(RcValue::literal_intro(lhs <= rhs))),
                "s8-le".to_owned() => prim!(|lhs: i8, rhs: i8| Ok(RcValue::literal_intro(lhs <= rhs))),
                "s16-le".to_owned() => prim!(|lhs: i16, rhs: i16| Ok(RcValue::literal_intro(lhs <= rhs))),
                "s32-le".to_owned() => prim!(|lhs: i32, rhs: i32| Ok(RcValue::literal_intro(lhs <= rhs))),
                "s64-le".to_owned() => prim!(|lhs: i64, rhs: i64| Ok(RcValue::literal_intro(lhs <= rhs))),
                "f32-le".to_owned() => prim!(|lhs: f32, rhs: f32| Ok(RcValue::literal_intro(lhs <= rhs))),
                "f64-le".to_owned() => prim!(|lhs: f64, rhs: f64| Ok(RcValue::literal_intro(lhs <= rhs))),

                "string-ge".to_owned() => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(RcValue::literal_intro(lhs >= rhs))),
                "char-ge".to_owned() => prim!(|lhs: char, rhs: char| Ok(RcValue::literal_intro(lhs >= rhs))),
                "u8-ge".to_owned() => prim!(|lhs: u8, rhs: u8| Ok(RcValue::literal_intro(lhs >= rhs))),
                "u16-ge".to_owned() => prim!(|lhs: u16, rhs: u16| Ok(RcValue::literal_intro(lhs >= rhs))),
                "u32-ge".to_owned() => prim!(|lhs: u32, rhs: u32| Ok(RcValue::literal_intro(lhs >= rhs))),
                "u64-ge".to_owned() => prim!(|lhs: u64, rhs: u64| Ok(RcValue::literal_intro(lhs >= rhs))),
                "s8-ge".to_owned() => prim!(|lhs: i8, rhs: i8| Ok(RcValue::literal_intro(lhs >= rhs))),
                "s16-ge".to_owned() => prim!(|lhs: i16, rhs: i16| Ok(RcValue::literal_intro(lhs >= rhs))),
                "s32-ge".to_owned() => prim!(|lhs: i32, rhs: i32| Ok(RcValue::literal_intro(lhs >= rhs))),
                "s64-ge".to_owned() => prim!(|lhs: i64, rhs: i64| Ok(RcValue::literal_intro(lhs >= rhs))),
                "f32-ge".to_owned() => prim!(|lhs: f32, rhs: f32| Ok(RcValue::literal_intro(lhs >= rhs))),
                "f64-ge".to_owned() => prim!(|lhs: f64, rhs: f64| Ok(RcValue::literal_intro(lhs >= rhs))),

                "string-gt".to_owned() => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(RcValue::literal_intro(lhs > rhs))),
                "char-gt".to_owned() => prim!(|lhs: char, rhs: char| Ok(RcValue::literal_intro(lhs > rhs))),
                "u8-gt".to_owned() => prim!(|lhs: u8, rhs: u8| Ok(RcValue::literal_intro(lhs > rhs))),
                "u16-gt".to_owned() => prim!(|lhs: u16, rhs: u16| Ok(RcValue::literal_intro(lhs > rhs))),
                "u32-gt".to_owned() => prim!(|lhs: u32, rhs: u32| Ok(RcValue::literal_intro(lhs > rhs))),
                "u64-gt".to_owned() => prim!(|lhs: u64, rhs: u64| Ok(RcValue::literal_intro(lhs > rhs))),
                "s8-gt".to_owned() => prim!(|lhs: i8, rhs: i8| Ok(RcValue::literal_intro(lhs > rhs))),
                "s16-gt".to_owned() => prim!(|lhs: i16, rhs: i16| Ok(RcValue::literal_intro(lhs > rhs))),
                "s32-gt".to_owned() => prim!(|lhs: i32, rhs: i32| Ok(RcValue::literal_intro(lhs > rhs))),
                "s64-gt".to_owned() => prim!(|lhs: i64, rhs: i64| Ok(RcValue::literal_intro(lhs > rhs))),
                "f32-gt".to_owned() => prim!(|lhs: f32, rhs: f32| Ok(RcValue::literal_intro(lhs > rhs))),
                "f64-gt".to_owned() => prim!(|lhs: f64, rhs: f64| Ok(RcValue::literal_intro(lhs > rhs))),

                "u8-add".to_owned() => prim!(|lhs: u8, rhs: u8| Ok(RcValue::literal_intro(lhs + rhs))),
                "u16-add".to_owned() => prim!(|lhs: u16, rhs: u16| Ok(RcValue::literal_intro(lhs + rhs))),
                "u32-add".to_owned() => prim!(|lhs: u32, rhs: u32| Ok(RcValue::literal_intro(lhs + rhs))),
                "u64-add".to_owned() => prim!(|lhs: u64, rhs: u64| Ok(RcValue::literal_intro(lhs + rhs))),
                "s8-add".to_owned() => prim!(|lhs: i8, rhs: i8| Ok(RcValue::literal_intro(lhs + rhs))),
                "s16-add".to_owned() => prim!(|lhs: i16, rhs: i16| Ok(RcValue::literal_intro(lhs + rhs))),
                "s32-add".to_owned() => prim!(|lhs: i32, rhs: i32| Ok(RcValue::literal_intro(lhs + rhs))),
                "s64-add".to_owned() => prim!(|lhs: i64, rhs: i64| Ok(RcValue::literal_intro(lhs + rhs))),
                "f32-add".to_owned() => prim!(|lhs: f32, rhs: f32| Ok(RcValue::literal_intro(lhs + rhs))),
                "f64-add".to_owned() => prim!(|lhs: f64, rhs: f64| Ok(RcValue::literal_intro(lhs + rhs))),

                "u8-sub".to_owned() => prim!(|lhs: u8, rhs: u8| Ok(RcValue::literal_intro(lhs - rhs))),
                "u16-sub".to_owned() => prim!(|lhs: u16, rhs: u16| Ok(RcValue::literal_intro(lhs - rhs))),
                "u32-sub".to_owned() => prim!(|lhs: u32, rhs: u32| Ok(RcValue::literal_intro(lhs - rhs))),
                "u64-sub".to_owned() => prim!(|lhs: u64, rhs: u64| Ok(RcValue::literal_intro(lhs - rhs))),
                "s8-sub".to_owned() => prim!(|lhs: i8, rhs: i8| Ok(RcValue::literal_intro(lhs - rhs))),
                "s16-sub".to_owned() => prim!(|lhs: i16, rhs: i16| Ok(RcValue::literal_intro(lhs - rhs))),
                "s32-sub".to_owned() => prim!(|lhs: i32, rhs: i32| Ok(RcValue::literal_intro(lhs - rhs))),
                "s64-sub".to_owned() => prim!(|lhs: i64, rhs: i64| Ok(RcValue::literal_intro(lhs - rhs))),
                "f32-sub".to_owned() => prim!(|lhs: f32, rhs: f32| Ok(RcValue::literal_intro(lhs - rhs))),
                "f64-sub".to_owned() => prim!(|lhs: f64, rhs: f64| Ok(RcValue::literal_intro(lhs - rhs))),

                "s8-neg".to_owned() => prim!(|rhs: i8| Ok(RcValue::literal_intro(-rhs))),
                "s16-neg".to_owned() => prim!(|rhs: i16| Ok(RcValue::literal_intro(-rhs))),
                "s32-neg".to_owned() => prim!(|rhs: i32| Ok(RcValue::literal_intro(-rhs))),
                "s64-neg".to_owned() => prim!(|rhs: i64| Ok(RcValue::literal_intro(-rhs))),
                "f32-neg".to_owned() => prim!(|rhs: f32| Ok(RcValue::literal_intro(-rhs))),
                "f64-neg".to_owned() => prim!(|rhs: f64| Ok(RcValue::literal_intro(-rhs))),

                "u8-mul".to_owned() => prim!(|lhs: u8, rhs: u8| Ok(RcValue::literal_intro(lhs * rhs))),
                "u16-mul".to_owned() => prim!(|lhs: u16, rhs: u16| Ok(RcValue::literal_intro(lhs * rhs))),
                "u32-mul".to_owned() => prim!(|lhs: u32, rhs: u32| Ok(RcValue::literal_intro(lhs * rhs))),
                "u64-mul".to_owned() => prim!(|lhs: u64, rhs: u64| Ok(RcValue::literal_intro(lhs * rhs))),
                "s8-mul".to_owned() => prim!(|lhs: i8, rhs: i8| Ok(RcValue::literal_intro(lhs * rhs))),
                "s16-mul".to_owned() => prim!(|lhs: i16, rhs: i16| Ok(RcValue::literal_intro(lhs * rhs))),
                "s32-mul".to_owned() => prim!(|lhs: i32, rhs: i32| Ok(RcValue::literal_intro(lhs * rhs))),
                "s64-mul".to_owned() => prim!(|lhs: i64, rhs: i64| Ok(RcValue::literal_intro(lhs * rhs))),
                "f32-mul".to_owned() => prim!(|lhs: f32, rhs: f32| Ok(RcValue::literal_intro(lhs * rhs))),
                "f64-mul".to_owned() => prim!(|lhs: f64, rhs: f64| Ok(RcValue::literal_intro(lhs * rhs))),

                "u8-div".to_owned() => prim!(|lhs: u8, rhs: u8| Ok(RcValue::literal_intro(lhs / rhs))),
                "u16-div".to_owned() => prim!(|lhs: u16, rhs: u16| Ok(RcValue::literal_intro(lhs / rhs))),
                "u32-div".to_owned() => prim!(|lhs: u32, rhs: u32| Ok(RcValue::literal_intro(lhs / rhs))),
                "u64-div".to_owned() => prim!(|lhs: u64, rhs: u64| Ok(RcValue::literal_intro(lhs / rhs))),
                "s8-div".to_owned() => prim!(|lhs: i8, rhs: i8| Ok(RcValue::literal_intro(lhs / rhs))),
                "s16-div".to_owned() => prim!(|lhs: i16, rhs: i16| Ok(RcValue::literal_intro(lhs / rhs))),
                "s32-div".to_owned() => prim!(|lhs: i32, rhs: i32| Ok(RcValue::literal_intro(lhs / rhs))),
                "s64-div".to_owned() => prim!(|lhs: i64, rhs: i64| Ok(RcValue::literal_intro(lhs / rhs))),
                "f32-div".to_owned() => prim!(|lhs: f32, rhs: f32| Ok(RcValue::literal_intro(lhs / rhs))),
                "f64-div".to_owned() => prim!(|lhs: f64, rhs: f64| Ok(RcValue::literal_intro(lhs / rhs))),

                "char-to-string".to_owned() => prim!(|value: char| Ok(RcValue::literal_intro(value.to_string()))),
                "u8-to-string".to_owned() => prim!(|value: u8| Ok(RcValue::literal_intro(value.to_string()))),
                "u16-to-string".to_owned() => prim!(|value: u16| Ok(RcValue::literal_intro(value.to_string()))),
                "u32-to-string".to_owned() => prim!(|value: u32| Ok(RcValue::literal_intro(value.to_string()))),
                "u64-to-string".to_owned() => prim!(|value: u64| Ok(RcValue::literal_intro(value.to_string()))),
                "s8-to-string".to_owned() => prim!(|value: i8| Ok(RcValue::literal_intro(value.to_string()))),
                "s16-to-string".to_owned() => prim!(|value: i16| Ok(RcValue::literal_intro(value.to_string()))),
                "s32-to-string".to_owned() => prim!(|value: i32| Ok(RcValue::literal_intro(value.to_string()))),
                "s64-to-string".to_owned() => prim!(|value: i64| Ok(RcValue::literal_intro(value.to_string()))),
                "f32-to-string".to_owned() => prim!(|value: f32| Ok(RcValue::literal_intro(value.to_string()))),
                "f64-to-string".to_owned() => prim!(|value: f64| Ok(RcValue::literal_intro(value.to_string()))),
            },
        }
    }
}

/// Case split on a literal.
fn do_literal_elim(
    prims: &PrimEnv,
    scrutinee: RcValue,
    closure: LiteralClosure,
) -> Result<RcValue, NbeError> {
    match scrutinee.as_ref() {
        Value::LiteralIntro(literal_intro) => {
            let index = closure.clauses.binary_search_by(|(l, _)| {
                l.partial_cmp(literal_intro).unwrap() // NaN?
            });

            match index {
                Ok(index) => eval_term(prims, &closure.env, &closure.clauses.get(index).unwrap().1),
                Err(_) => eval_term(prims, &closure.env, &closure.default),
            }
        },
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(Elim::Literal(closure));
            Ok(RcValue::from(Value::Neutral(head.clone(), spine)))
        },
        _ => Err(NbeError::new("do_literal_elim: not a literal")),
    }
}

/// Return the field in from a record.
fn do_record_elim(record: RcValue, label: &Label) -> Result<RcValue, NbeError> {
    match record.as_ref() {
        Value::RecordIntro(fields) => match fields.iter().find(|(l, _)| l == label) {
            Some((_, term)) => Ok(term.clone()),
            None => Err(NbeError::new(format!(
                "do_record_elim: field `{}` not found in record",
                label.0,
            ))),
        },
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(Elim::Record(label.clone()));
            // TODO: If head is `primitive`, and arity == number of initial spine apps in NF
            Ok(RcValue::from(Value::Neutral(head.clone(), spine)))
        },
        _ => Err(NbeError::new("do_record_elim: not a record")),
    }
}

/// Apply a function to an argument.
pub fn do_fun_elim(
    prims: &PrimEnv,
    fun: RcValue,
    app_mode: AppMode,
    arg: RcValue,
) -> Result<RcValue, NbeError> {
    match fun.as_ref() {
        Value::FunIntro(fun_app_mode, body) => {
            if *fun_app_mode == app_mode {
                app_closure(prims, body, arg)
            } else {
                Err(NbeError::new(format!(
                    "do_ap: unexpected application mode - {:?} != {:?}",
                    fun_app_mode, app_mode,
                )))
            }
        },
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(Elim::Fun(app_mode, arg));
            // TODO: If head is `primitive`, and arity == number of initial spine apps in NF
            Ok(RcValue::from(Value::Neutral(head.clone(), spine)))
        },
        _ => Err(NbeError::new("do_ap: not a function")),
    }
}

/// Apply a closure to an argument.
pub fn app_closure(
    prims: &PrimEnv,
    closure: &AppClosure,
    arg: RcValue,
) -> Result<RcValue, NbeError> {
    let mut env = closure.env.clone();
    env.add_defn(arg);
    eval_term(prims, &env, &closure.term)
}

/// Instantiate a closure at the given level.
pub fn inst_closure(
    prims: &PrimEnv,
    closure: &AppClosure,
    env_size: EnvSize,
) -> Result<RcValue, NbeError> {
    app_closure(prims, closure, RcValue::var(env_size.next_var_level()))
}

/// Evaluate a term in the environment that corresponds to the context in which
/// the term was typed.
pub fn eval_term(prims: &PrimEnv, env: &Env, term: &RcTerm) -> Result<RcValue, NbeError> {
    match term.as_ref() {
        Term::Var(index) => match env.lookup_value(*index) {
            Some(value) => Ok(value.clone()),
            None => Err(NbeError::new("eval: variable not found")),
        },
        Term::Prim(name) => {
            let prim = prims
                .lookup_entry(name)
                .ok_or_else(|| NbeError::new(format!("eval: primitive not found: {:?}", name)))?;

            match prim.interpret(&[]) {
                Some(result) => Ok(result?.0),
                None => Ok(RcValue::prim(name.clone())),
            }
        },

        Term::Ann(term, _) => eval_term(prims, env, term),
        Term::Let(items, body) => {
            let mut env = env.clone();
            for item in items {
                if let Item::Definition(_, _, term) = item {
                    env.add_defn(eval_term(prims, &env, term)?);
                }
            }
            eval_term(prims, &env, body)
        },

        // Literals
        Term::LiteralType(literal_ty) => Ok(RcValue::literal_ty(literal_ty.clone())),
        Term::LiteralIntro(literal_intro) => Ok(RcValue::literal_intro(literal_intro.clone())),
        Term::LiteralElim(scrutinee, clauses, default_body) => {
            let scrutinee = eval_term(prims, env, scrutinee)?;
            let closure = LiteralClosure::new(clauses.clone(), default_body.clone(), env.clone());

            do_literal_elim(prims, scrutinee, closure)
        },

        // Functions
        Term::FunType(app_mode, param_ty, body_ty) => {
            let app_mode = app_mode.clone();
            let param_ty = eval_term(prims, env, param_ty)?;
            let body_ty = AppClosure::new(body_ty.clone(), env.clone());

            Ok(RcValue::from(Value::FunType(app_mode, param_ty, body_ty)))
        },
        Term::FunIntro(app_mode, body) => {
            let app_mode = app_mode.clone();
            let body = AppClosure::new(body.clone(), env.clone());

            Ok(RcValue::from(Value::FunIntro(app_mode, body)))
        },
        Term::FunElim(fun, app_mode, arg) => {
            let fun = eval_term(prims, env, fun)?;
            let app_mode = app_mode.clone();
            let arg = eval_term(prims, env, arg)?;

            do_fun_elim(prims, fun, app_mode, arg)
        },

        // Records
        Term::RecordType(fields) => match fields.split_first() {
            None => Ok(RcValue::from(Value::RecordTypeEmpty)),
            Some(((doc, label, ty), rest)) => {
                let doc = doc.clone();
                let label = label.clone();
                let ty = eval_term(prims, env, ty)?;
                let rest_fields = rest.iter().cloned().collect(); // FIXME: Seems expensive?
                let rest =
                    AppClosure::new(RcTerm::from(Term::RecordType(rest_fields)), env.clone());

                Ok(RcValue::from(Value::RecordTypeExtend(doc, label, ty, rest)))
            },
        },
        Term::RecordIntro(fields) => {
            let fields = fields
                .iter()
                .map(|(label, term)| Ok((label.clone(), eval_term(prims, env, term)?)))
                .collect::<Result<_, _>>()?;

            Ok(RcValue::from(Value::RecordIntro(fields)))
        },
        Term::RecordElim(record, label) => do_record_elim(eval_term(prims, env, record)?, label),

        // Universes
        Term::Universe(level) => Ok(RcValue::universe(*level)),
    }
}

/// Read a value back into the core syntax, normalizing as required.
pub fn read_back_value(
    prims: &PrimEnv,
    env_size: EnvSize,
    term: &RcValue,
) -> Result<RcTerm, NbeError> {
    match term.as_ref() {
        Value::Neutral(head, spine) => read_back_neutral(prims, env_size, head, spine),

        // Literals
        Value::LiteralType(literal_ty) => Ok(RcTerm::literal_ty(literal_ty.clone())),
        Value::LiteralIntro(literal_intro) => Ok(RcTerm::literal_intro(literal_intro.clone())),

        // Functions
        Value::FunType(app_mode, param_ty, body_ty) => {
            let app_mode = app_mode.clone();
            let param_ty = read_back_value(prims, env_size, param_ty)?;
            let body_ty = inst_closure(prims, body_ty, env_size)?;
            let body_ty = read_back_value(prims, env_size + 1, &body_ty)?;

            Ok(RcTerm::from(Term::FunType(app_mode, param_ty, body_ty)))
        },
        Value::FunIntro(app_mode, body) => {
            let app_mode = app_mode.clone();
            let body = inst_closure(prims, body, env_size)?;
            let body = read_back_value(prims, env_size + 1, &body)?;

            Ok(RcTerm::from(Term::FunIntro(app_mode, body)))
        },

        // Records
        Value::RecordTypeExtend(doc, label, term_ty, rest_ty) => {
            let mut env_size = env_size;

            let term_ty = read_back_value(prims, env_size, term_ty)?;

            let mut rest_ty = inst_closure(prims, rest_ty, env_size)?;
            let mut field_tys = vec![(doc.clone(), label.clone(), term_ty)];

            while let Value::RecordTypeExtend(next_doc, next_label, next_term_ty, next_rest_ty) =
                rest_ty.as_ref()
            {
                env_size += 1;
                let next_term_ty = read_back_value(prims, env_size, next_term_ty)?;
                field_tys.push((next_doc.clone(), next_label.clone(), next_term_ty));
                rest_ty = inst_closure(prims, next_rest_ty, env_size)?;
            }

            Ok(RcTerm::from(Term::RecordType(field_tys)))
        },
        Value::RecordTypeEmpty => Ok(RcTerm::from(Term::RecordType(Vec::new()))),
        Value::RecordIntro(fields) => {
            let fields = fields
                .iter()
                .map(|(label, term)| Ok((label.clone(), read_back_value(prims, env_size, term)?)))
                .collect::<Result<_, _>>()?;

            Ok(RcTerm::from(Term::RecordIntro(fields)))
        },

        // Universes
        Value::Universe(level) => Ok(RcTerm::universe(*level)),
    }
}

/// Read a neutral value back into the core syntax, normalizing as required.
pub fn read_back_neutral(
    prims: &PrimEnv,
    env_size: EnvSize,
    head: &Head,
    spine: &Spine,
) -> Result<RcTerm, NbeError> {
    let (head, spine) = match head {
        Head::Var(var_level) => (
            RcTerm::var(env_size.var_index(*var_level)),
            spine.as_slice(),
        ),
        Head::Prim(name) => {
            let prim = prims
                .lookup_entry(name)
                .ok_or_else(|| NbeError::new(format!("eval: primitive not found: {:?}", name)))?;

            match prim.interpret(spine) {
                Some(result) => {
                    let (value, rest_spine) = result?;
                    (read_back_value(prims, env_size, &value)?, rest_spine)
                },
                None => (RcTerm::prim(name.clone()), spine.as_slice()),
            }
        },
    };

    spine.iter().fold(Ok(head), |acc, elim| match elim {
        Elim::Literal(closure) => {
            let clauses = Rc::from(
                closure
                    .clauses
                    .iter()
                    .map(|(literal_intro, body)| {
                        let body = eval_term(prims, &closure.env, body)?;
                        let body = read_back_value(prims, env_size, &body)?;
                        Ok((literal_intro.clone(), body))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );

            let default_body = eval_term(prims, &closure.env, &closure.default)?;
            let default_body = read_back_value(prims, env_size, &default_body)?;

            Ok(RcTerm::from(Term::LiteralElim(acc?, clauses, default_body)))
        },
        Elim::Fun(app_mode, arg) => {
            let arg = read_back_value(prims, env_size, &arg)?;

            Ok(RcTerm::from(Term::FunElim(acc?, app_mode.clone(), arg)))
        },
        Elim::Record(label) => Ok(RcTerm::from(Term::RecordElim(acc?, label.clone()))),
    })
}

/// Fully normalize a term by first evaluating it, then reading it back.
pub fn normalize_term(prims: &PrimEnv, env: &Env, term: &RcTerm) -> Result<RcTerm, NbeError> {
    let value = eval_term(prims, env, term)?;
    read_back_value(prims, env.size(), &value)
}

/// Check whether a semantic type is a subtype of another.
pub fn check_subtype(
    prims: &PrimEnv,
    env_size: EnvSize,
    ty1: &RcType,
    ty2: &RcType,
) -> Result<bool, NbeError> {
    match (ty1.as_ref(), ty2.as_ref()) {
        (Value::Neutral(head1, spine1), Value::Neutral(head2, spine2)) => {
            let term1 = read_back_neutral(prims, env_size, head1, spine1)?;
            let term2 = read_back_neutral(prims, env_size, head2, spine2)?;

            Ok(Term::alpha_eq(&term1, &term2))
        },
        (Value::LiteralType(literal_ty1), Value::LiteralType(literal_ty2)) => {
            Ok(literal_ty1 == literal_ty2)
        },
        (
            Value::FunType(app_mode1, param_ty1, body_ty1),
            Value::FunType(app_mode2, param_ty2, body_ty2),
        ) if app_mode1 == app_mode2 => Ok(check_subtype(prims, env_size, param_ty2, param_ty1)?
            && {
                let body_ty1 = inst_closure(prims, body_ty1, env_size)?;
                let body_ty2 = inst_closure(prims, body_ty2, env_size)?;
                check_subtype(prims, env_size + 1, &body_ty1, &body_ty2)?
            }),
        (
            Value::RecordTypeExtend(_, label1, term_ty1, rest_ty1),
            Value::RecordTypeExtend(_, label2, term_ty2, rest_ty2),
        ) if label1 == label2 => Ok(check_subtype(prims, env_size, term_ty1, term_ty2)? && {
            let rest_ty1 = inst_closure(prims, rest_ty1, env_size)?;
            let rest_ty2 = inst_closure(prims, rest_ty2, env_size)?;
            check_subtype(prims, env_size + 1, &rest_ty1, &rest_ty2)?
        }),
        (Value::RecordTypeEmpty, Value::RecordTypeEmpty) => Ok(true),
        (Value::Universe(level1), Value::Universe(level2)) => Ok(level1 <= level2),
        _ => Ok(false),
    }
}
