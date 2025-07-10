//! Built-in [`Provider`](crate::Provider) implementations for common sources.
//!
//! The [top-level docs](crate#built-in-providers) contain a list and
//! description of each provider.

mod serialized;
mod data;
mod env;
mod named;

pub use self::env::Env;
pub use self::serialized::Serialized;
pub use self::data::*;
pub use self::named::Named;
