//! [`Value`] and friends: types representing valid configuration values.
//!
mod de;
mod escape;
mod parse;
mod ser;
mod tag;
mod value;

pub mod magic;

pub(crate) use {self::de::*, self::ser::*};

pub use tag::Tag;
pub use uncased::{Uncased, UncasedStr};
pub use value::{Dict, Empty, Map, Num, Value};
