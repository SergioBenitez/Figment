//! Built-in [`Provider`](crate::Provider) implementations for common sources.
//!
//! The [top-level docs](crate#built-in-providers) contain a list and
//! description of each provider.

mod data;
mod env;
mod serialized;

pub use self::data::*;
pub use self::env::Env;
pub use self::serialized::Serialized;
