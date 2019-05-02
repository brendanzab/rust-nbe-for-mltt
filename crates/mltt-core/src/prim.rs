use std::fmt;
use std::rc::Rc;

use super::literal::LiteralIntro;
use crate::domain::{Elim, RcValue, Value};

/// An entry in the primitive environment.
#[derive(Clone)]
pub struct Entry {
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
    pub interpretation: fn(Vec<RcValue>) -> Option<Result<RcValue, String>>,
}

impl Entry {
    /// Interpret a primitive if there are enough function eliminators provided
    /// in the spine. `None` is returned if evaluation is stuck.
    ///
    /// Also known as [δ-reduction (delta-reduction)][δ-reduction].
    ///
    /// [δ-reduction]: http://barrywatson.se/lsi/lsi_delta_reduction.html
    pub fn interpret<'spine>(
        &self,
        spine: &'spine [Elim],
    ) -> Option<Result<(RcValue, &'spine [Elim]), String>> {
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
                Elim::Literal(_) | Elim::Record(_) => return None, // Return String?
            }
        }

        let result = (self.interpretation)(args)?;
        Some(result.map(|value| (value, rest_spine)))
    }
}

impl fmt::Debug for Entry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Entry")
            .field("arity", &self.arity)
            .field("interpretation", &"|args| { .. }")
            .finish()
    }
}

/// An environment of primitives to use during normalization.
#[derive(Debug, Clone)]
pub struct Env {
    entries: im::HashMap<String, Entry>,
}

impl Env {
    /// Construct a new, empty environment.
    pub fn new() -> Env {
        Env {
            entries: im::HashMap::new(),
        }
    }

    /// Lookup an entry in the environment.
    pub fn lookup_entry(&self, name: &str) -> Option<&Entry> {
        self.entries.get(name)
    }

    /// Add a new entry to the environment.
    pub fn add_entry(&mut self, name: String, entry: Entry) {
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

impl Default for Env {
    fn default() -> Env {
        macro_rules! count {
            () => (0);
            ($x:tt $($xs:tt)*) => (1 + count!($($xs)*));
        }

        macro_rules! prim {
            (|$($param_name:ident : $PType:ty),*| $body:expr) => {
                Entry {
                    arity: count!($($param_name)*),
                    interpretation: {
                        fn interpretation(params: Vec<RcValue>) -> Option<Result<RcValue, String>> {
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

        Env {
            entries: im::hashmap! {
                "abort".to_owned() => prim!(|message: Rc<str>| Err(message.to_string())),

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
