//! [`Value`] and friends: types representing valid configuration values.
//!
mod value;
mod ser;
#[cfg(feature = "parse-value")]
mod parse;
mod de;
mod tag_id;

#[cfg(feature = "magic")]
#[cfg_attr(nightly, doc(cfg(feature = "magic")))]
pub mod magic;

pub(crate) use {self::ser::*, self::de::*};
pub use tag_id::{Tag, Id};
pub use value::{Value, Map, Num, Dict, Empty};
pub use uncased::{Uncased, UncasedStr};
