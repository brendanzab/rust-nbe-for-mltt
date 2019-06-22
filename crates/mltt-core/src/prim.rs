use std::fmt;
use std::rc::Rc;

use crate::domain::{Elim, Value};
use crate::literal::LiteralIntro;

/// The name of a primitive.
#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct Name(pub String);

impl<'a> From<&'a str> for Name {
    fn from(src: &'a str) -> Name {
        Name(src.to_owned())
    }
}

impl From<String> for Name {
    fn from(src: String) -> Name {
        Name(src)
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

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
    pub interpretation: fn(Vec<Rc<Value>>) -> Option<Result<Rc<Value>, String>>,
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
    ) -> Option<Result<(Rc<Value>, &'spine [Elim]), String>> {
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
    entries: im::HashMap<Name, Entry>,
}

impl Env {
    /// Construct a new, empty environment.
    pub fn new() -> Env {
        Env {
            entries: im::HashMap::new(),
        }
    }

    /// Lookup an entry in the environment.
    pub fn lookup_entry(&self, name: &Name) -> Option<&Entry> {
        self.entries.get(name)
    }

    /// Add a new entry to the environment.
    pub fn add_entry(&mut self, name: Name, entry: Entry) {
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
            (|| $body:expr) => {
                Entry {
                    arity: 0,
                    interpretation: {
                        fn interpretation(params: Vec<Rc<Value>>) -> Option<Result<Rc<Value>, String>> {
                            match params.as_slice() {
                                [] => Some($body),
                                _ => None,
                            }
                        }
                        interpretation
                    }
                }
            };
            (|$($param_name:ident : $PType:ty),*| $body:expr) => {
                Entry {
                    arity: count!($($param_name)*),
                    interpretation: {
                        fn interpretation(params: Vec<Rc<Value>>) -> Option<Result<Rc<Value>, String>> {
                            match params.as_slice() {
                                [$(ref $param_name),*] => {
                                    $(let $param_name = <$PType>::try_from_value($param_name)?;)*
                                    Some($body)
                                },
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
                Name::from("abort") => prim!(|message: Rc<str>| Err(message.to_string())),

                Name::from("string-eq") => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),
                Name::from("char-eq") => prim!(|lhs: char, rhs: char| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),
                Name::from("u8-eq") => prim!(|lhs: u8, rhs: u8| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),
                Name::from("u16-eq") => prim!(|lhs: u16, rhs: u16| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),
                Name::from("u32-eq") => prim!(|lhs: u32, rhs: u32| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),
                Name::from("u64-eq") => prim!(|lhs: u64, rhs: u64| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),
                Name::from("s8-eq") => prim!(|lhs: i8, rhs: i8| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),
                Name::from("s16-eq") => prim!(|lhs: i16, rhs: i16| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),
                Name::from("s32-eq") => prim!(|lhs: i32, rhs: i32| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),
                Name::from("s64-eq") => prim!(|lhs: i64, rhs: i64| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),
                Name::from("f32-eq") => prim!(|lhs: f32, rhs: f32| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),
                Name::from("f64-eq") => prim!(|lhs: f64, rhs: f64| Ok(Rc::from(Value::literal_intro(lhs == rhs)))),

                Name::from("string-ne") => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),
                Name::from("char-ne") => prim!(|lhs: char, rhs: char| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),
                Name::from("u8-ne") => prim!(|lhs: u8, rhs: u8| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),
                Name::from("u16-ne") => prim!(|lhs: u16, rhs: u16| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),
                Name::from("u32-ne") => prim!(|lhs: u32, rhs: u32| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),
                Name::from("u64-ne") => prim!(|lhs: u64, rhs: u64| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),
                Name::from("s8-ne") => prim!(|lhs: i8, rhs: i8| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),
                Name::from("s16-ne") => prim!(|lhs: i16, rhs: i16| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),
                Name::from("s32-ne") => prim!(|lhs: i32, rhs: i32| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),
                Name::from("s64-ne") => prim!(|lhs: i64, rhs: i64| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),
                Name::from("f32-ne") => prim!(|lhs: f32, rhs: f32| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),
                Name::from("f64-ne") => prim!(|lhs: f64, rhs: f64| Ok(Rc::from(Value::literal_intro(lhs != rhs)))),

                Name::from("string-lt") => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),
                Name::from("char-lt") => prim!(|lhs: char, rhs: char| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),
                Name::from("u8-lt") => prim!(|lhs: u8, rhs: u8| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),
                Name::from("u16-lt") => prim!(|lhs: u16, rhs: u16| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),
                Name::from("u32-lt") => prim!(|lhs: u32, rhs: u32| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),
                Name::from("u64-lt") => prim!(|lhs: u64, rhs: u64| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),
                Name::from("s8-lt") => prim!(|lhs: i8, rhs: i8| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),
                Name::from("s16-lt") => prim!(|lhs: i16, rhs: i16| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),
                Name::from("s32-lt") => prim!(|lhs: i32, rhs: i32| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),
                Name::from("s64-lt") => prim!(|lhs: i64, rhs: i64| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),
                Name::from("f32-lt") => prim!(|lhs: f32, rhs: f32| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),
                Name::from("f64-lt") => prim!(|lhs: f64, rhs: f64| Ok(Rc::from(Value::literal_intro(lhs < rhs)))),

                Name::from("string-le") => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),
                Name::from("char-le") => prim!(|lhs: char, rhs: char| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),
                Name::from("u8-le") => prim!(|lhs: u8, rhs: u8| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),
                Name::from("u16-le") => prim!(|lhs: u16, rhs: u16| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),
                Name::from("u32-le") => prim!(|lhs: u32, rhs: u32| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),
                Name::from("u64-le") => prim!(|lhs: u64, rhs: u64| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),
                Name::from("s8-le") => prim!(|lhs: i8, rhs: i8| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),
                Name::from("s16-le") => prim!(|lhs: i16, rhs: i16| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),
                Name::from("s32-le") => prim!(|lhs: i32, rhs: i32| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),
                Name::from("s64-le") => prim!(|lhs: i64, rhs: i64| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),
                Name::from("f32-le") => prim!(|lhs: f32, rhs: f32| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),
                Name::from("f64-le") => prim!(|lhs: f64, rhs: f64| Ok(Rc::from(Value::literal_intro(lhs <= rhs)))),

                Name::from("string-ge") => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),
                Name::from("char-ge") => prim!(|lhs: char, rhs: char| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),
                Name::from("u8-ge") => prim!(|lhs: u8, rhs: u8| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),
                Name::from("u16-ge") => prim!(|lhs: u16, rhs: u16| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),
                Name::from("u32-ge") => prim!(|lhs: u32, rhs: u32| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),
                Name::from("u64-ge") => prim!(|lhs: u64, rhs: u64| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),
                Name::from("s8-ge") => prim!(|lhs: i8, rhs: i8| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),
                Name::from("s16-ge") => prim!(|lhs: i16, rhs: i16| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),
                Name::from("s32-ge") => prim!(|lhs: i32, rhs: i32| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),
                Name::from("s64-ge") => prim!(|lhs: i64, rhs: i64| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),
                Name::from("f32-ge") => prim!(|lhs: f32, rhs: f32| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),
                Name::from("f64-ge") => prim!(|lhs: f64, rhs: f64| Ok(Rc::from(Value::literal_intro(lhs >= rhs)))),

                Name::from("string-gt") => prim!(|lhs: Rc<str>, rhs: Rc<str>| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),
                Name::from("char-gt") => prim!(|lhs: char, rhs: char| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),
                Name::from("u8-gt") => prim!(|lhs: u8, rhs: u8| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),
                Name::from("u16-gt") => prim!(|lhs: u16, rhs: u16| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),
                Name::from("u32-gt") => prim!(|lhs: u32, rhs: u32| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),
                Name::from("u64-gt") => prim!(|lhs: u64, rhs: u64| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),
                Name::from("s8-gt") => prim!(|lhs: i8, rhs: i8| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),
                Name::from("s16-gt") => prim!(|lhs: i16, rhs: i16| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),
                Name::from("s32-gt") => prim!(|lhs: i32, rhs: i32| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),
                Name::from("s64-gt") => prim!(|lhs: i64, rhs: i64| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),
                Name::from("f32-gt") => prim!(|lhs: f32, rhs: f32| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),
                Name::from("f64-gt") => prim!(|lhs: f64, rhs: f64| Ok(Rc::from(Value::literal_intro(lhs > rhs)))),

                Name::from("u8-add") => prim!(|lhs: u8, rhs: u8| Ok(Rc::from(Value::literal_intro(lhs + rhs)))),
                Name::from("u16-add") => prim!(|lhs: u16, rhs: u16| Ok(Rc::from(Value::literal_intro(lhs + rhs)))),
                Name::from("u32-add") => prim!(|lhs: u32, rhs: u32| Ok(Rc::from(Value::literal_intro(lhs + rhs)))),
                Name::from("u64-add") => prim!(|lhs: u64, rhs: u64| Ok(Rc::from(Value::literal_intro(lhs + rhs)))),
                Name::from("s8-add") => prim!(|lhs: i8, rhs: i8| Ok(Rc::from(Value::literal_intro(lhs + rhs)))),
                Name::from("s16-add") => prim!(|lhs: i16, rhs: i16| Ok(Rc::from(Value::literal_intro(lhs + rhs)))),
                Name::from("s32-add") => prim!(|lhs: i32, rhs: i32| Ok(Rc::from(Value::literal_intro(lhs + rhs)))),
                Name::from("s64-add") => prim!(|lhs: i64, rhs: i64| Ok(Rc::from(Value::literal_intro(lhs + rhs)))),
                Name::from("f32-add") => prim!(|lhs: f32, rhs: f32| Ok(Rc::from(Value::literal_intro(lhs + rhs)))),
                Name::from("f64-add") => prim!(|lhs: f64, rhs: f64| Ok(Rc::from(Value::literal_intro(lhs + rhs)))),

                Name::from("u8-sub") => prim!(|lhs: u8, rhs: u8| Ok(Rc::from(Value::literal_intro(lhs - rhs)))),
                Name::from("u16-sub") => prim!(|lhs: u16, rhs: u16| Ok(Rc::from(Value::literal_intro(lhs - rhs)))),
                Name::from("u32-sub") => prim!(|lhs: u32, rhs: u32| Ok(Rc::from(Value::literal_intro(lhs - rhs)))),
                Name::from("u64-sub") => prim!(|lhs: u64, rhs: u64| Ok(Rc::from(Value::literal_intro(lhs - rhs)))),
                Name::from("s8-sub") => prim!(|lhs: i8, rhs: i8| Ok(Rc::from(Value::literal_intro(lhs - rhs)))),
                Name::from("s16-sub") => prim!(|lhs: i16, rhs: i16| Ok(Rc::from(Value::literal_intro(lhs - rhs)))),
                Name::from("s32-sub") => prim!(|lhs: i32, rhs: i32| Ok(Rc::from(Value::literal_intro(lhs - rhs)))),
                Name::from("s64-sub") => prim!(|lhs: i64, rhs: i64| Ok(Rc::from(Value::literal_intro(lhs - rhs)))),
                Name::from("f32-sub") => prim!(|lhs: f32, rhs: f32| Ok(Rc::from(Value::literal_intro(lhs - rhs)))),
                Name::from("f64-sub") => prim!(|lhs: f64, rhs: f64| Ok(Rc::from(Value::literal_intro(lhs - rhs)))),

                Name::from("s8-neg") => prim!(|rhs: i8| Ok(Rc::from(Value::literal_intro(-rhs)))),
                Name::from("s16-neg") => prim!(|rhs: i16| Ok(Rc::from(Value::literal_intro(-rhs)))),
                Name::from("s32-neg") => prim!(|rhs: i32| Ok(Rc::from(Value::literal_intro(-rhs)))),
                Name::from("s64-neg") => prim!(|rhs: i64| Ok(Rc::from(Value::literal_intro(-rhs)))),
                Name::from("f32-neg") => prim!(|rhs: f32| Ok(Rc::from(Value::literal_intro(-rhs)))),
                Name::from("f64-neg") => prim!(|rhs: f64| Ok(Rc::from(Value::literal_intro(-rhs)))),

                Name::from("u8-mul") => prim!(|lhs: u8, rhs: u8| Ok(Rc::from(Value::literal_intro(lhs * rhs)))),
                Name::from("u16-mul") => prim!(|lhs: u16, rhs: u16| Ok(Rc::from(Value::literal_intro(lhs * rhs)))),
                Name::from("u32-mul") => prim!(|lhs: u32, rhs: u32| Ok(Rc::from(Value::literal_intro(lhs * rhs)))),
                Name::from("u64-mul") => prim!(|lhs: u64, rhs: u64| Ok(Rc::from(Value::literal_intro(lhs * rhs)))),
                Name::from("s8-mul") => prim!(|lhs: i8, rhs: i8| Ok(Rc::from(Value::literal_intro(lhs * rhs)))),
                Name::from("s16-mul") => prim!(|lhs: i16, rhs: i16| Ok(Rc::from(Value::literal_intro(lhs * rhs)))),
                Name::from("s32-mul") => prim!(|lhs: i32, rhs: i32| Ok(Rc::from(Value::literal_intro(lhs * rhs)))),
                Name::from("s64-mul") => prim!(|lhs: i64, rhs: i64| Ok(Rc::from(Value::literal_intro(lhs * rhs)))),
                Name::from("f32-mul") => prim!(|lhs: f32, rhs: f32| Ok(Rc::from(Value::literal_intro(lhs * rhs)))),
                Name::from("f64-mul") => prim!(|lhs: f64, rhs: f64| Ok(Rc::from(Value::literal_intro(lhs * rhs)))),

                Name::from("u8-div") => prim!(|lhs: u8, rhs: u8| Ok(Rc::from(Value::literal_intro(lhs / rhs)))),
                Name::from("u16-div") => prim!(|lhs: u16, rhs: u16| Ok(Rc::from(Value::literal_intro(lhs / rhs)))),
                Name::from("u32-div") => prim!(|lhs: u32, rhs: u32| Ok(Rc::from(Value::literal_intro(lhs / rhs)))),
                Name::from("u64-div") => prim!(|lhs: u64, rhs: u64| Ok(Rc::from(Value::literal_intro(lhs / rhs)))),
                Name::from("s8-div") => prim!(|lhs: i8, rhs: i8| Ok(Rc::from(Value::literal_intro(lhs / rhs)))),
                Name::from("s16-div") => prim!(|lhs: i16, rhs: i16| Ok(Rc::from(Value::literal_intro(lhs / rhs)))),
                Name::from("s32-div") => prim!(|lhs: i32, rhs: i32| Ok(Rc::from(Value::literal_intro(lhs / rhs)))),
                Name::from("s64-div") => prim!(|lhs: i64, rhs: i64| Ok(Rc::from(Value::literal_intro(lhs / rhs)))),
                Name::from("f32-div") => prim!(|lhs: f32, rhs: f32| Ok(Rc::from(Value::literal_intro(lhs / rhs)))),
                Name::from("f64-div") => prim!(|lhs: f64, rhs: f64| Ok(Rc::from(Value::literal_intro(lhs / rhs)))),

                Name::from("char-to-string") => prim!(|value: char| Ok(Rc::from(Value::literal_intro(value.to_string())))),
                Name::from("u8-to-string") => prim!(|value: u8| Ok(Rc::from(Value::literal_intro(value.to_string())))),
                Name::from("u16-to-string") => prim!(|value: u16| Ok(Rc::from(Value::literal_intro(value.to_string())))),
                Name::from("u32-to-string") => prim!(|value: u32| Ok(Rc::from(Value::literal_intro(value.to_string())))),
                Name::from("u64-to-string") => prim!(|value: u64| Ok(Rc::from(Value::literal_intro(value.to_string())))),
                Name::from("s8-to-string") => prim!(|value: i8| Ok(Rc::from(Value::literal_intro(value.to_string())))),
                Name::from("s16-to-string") => prim!(|value: i16| Ok(Rc::from(Value::literal_intro(value.to_string())))),
                Name::from("s32-to-string") => prim!(|value: i32| Ok(Rc::from(Value::literal_intro(value.to_string())))),
                Name::from("s64-to-string") => prim!(|value: i64| Ok(Rc::from(Value::literal_intro(value.to_string())))),
                Name::from("f32-to-string") => prim!(|value: f32| Ok(Rc::from(Value::literal_intro(value.to_string())))),
                Name::from("f64-to-string") => prim!(|value: f64| Ok(Rc::from(Value::literal_intro(value.to_string())))),

                Name::from("u8-min") => prim!(|| Ok(Rc::from(Value::literal_intro(std::u8::MIN)))),
                Name::from("u16-min") => prim!(|| Ok(Rc::from(Value::literal_intro(std::u16::MIN)))),
                Name::from("u32-min") => prim!(|| Ok(Rc::from(Value::literal_intro(std::u32::MIN)))),
                Name::from("u64-min") => prim!(|| Ok(Rc::from(Value::literal_intro(std::u64::MIN)))),
                Name::from("s8-min") => prim!(|| Ok(Rc::from(Value::literal_intro(std::i8::MIN)))),
                Name::from("s16-min") => prim!(|| Ok(Rc::from(Value::literal_intro(std::i16::MIN)))),
                Name::from("s32-min") => prim!(|| Ok(Rc::from(Value::literal_intro(std::i32::MIN)))),
                Name::from("s64-min") => prim!(|| Ok(Rc::from(Value::literal_intro(std::i64::MIN)))),

                Name::from("u8-max") => prim!(|| Ok(Rc::from(Value::literal_intro(std::u8::MAX)))),
                Name::from("u16-max") => prim!(|| Ok(Rc::from(Value::literal_intro(std::u16::MAX)))),
                Name::from("u32-max") => prim!(|| Ok(Rc::from(Value::literal_intro(std::u32::MAX)))),
                Name::from("u64-max") => prim!(|| Ok(Rc::from(Value::literal_intro(std::u64::MAX)))),
                Name::from("s8-max") => prim!(|| Ok(Rc::from(Value::literal_intro(std::i8::MAX)))),
                Name::from("s16-max") => prim!(|| Ok(Rc::from(Value::literal_intro(std::i16::MAX)))),
                Name::from("s32-max") => prim!(|| Ok(Rc::from(Value::literal_intro(std::i32::MAX)))),
                Name::from("s64-max") => prim!(|| Ok(Rc::from(Value::literal_intro(std::i64::MAX)))),

                Name::from("f32-nan") => prim!(|| Ok(Rc::from(Value::literal_intro(std::f32::NAN)))),
                Name::from("f64-nan") => prim!(|| Ok(Rc::from(Value::literal_intro(std::f64::NAN)))),

                Name::from("f32-infinity") => prim!(|| Ok(Rc::from(Value::literal_intro(std::f32::INFINITY)))),
                Name::from("f64-infinity") => prim!(|| Ok(Rc::from(Value::literal_intro(std::f64::INFINITY)))),

                Name::from("f32-neg-infinity") => prim!(|| Ok(Rc::from(Value::literal_intro(std::f32::NEG_INFINITY)))),
                Name::from("f64-neg-infinity") => prim!(|| Ok(Rc::from(Value::literal_intro(std::f64::NEG_INFINITY)))),
            },
        }
    }
}
