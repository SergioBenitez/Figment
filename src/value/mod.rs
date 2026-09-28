//! [`Value`] and friends: types representing valid configuration values.
//!
#[allow(clippy::module_inception)]
mod value;
mod ser;
mod de;
mod tag;
mod parse;
mod escape;

pub mod dict;
pub mod magic;

pub(crate) use {self::ser::*, self::de::*};

pub use tag::Tag;
pub use dict::Dict;
pub use value::{Value, Map, Num, Empty};
pub use uncased::{Uncased, UncasedStr};
