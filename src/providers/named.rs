use std::borrow::Cow;

use crate::*;

/// Wrap a [`Provider`], giving it a new name.
/// 
/// ```
/// use clap::Parser;
/// use figment::*;
/// # use serde::*;
/// # fn tri() -> Result<()> {
/// 
/// #[derive(Parser, Serialize, Deserialize)]
/// struct Cli {
///     #[arg(long)]
///     num_yaks: Option<usize>,
/// }
/// 
/// let cli = Cli::parse();
/// 
/// # let _: serde::de::IgnoredAny = 
/// Figment::new()
///     // ...
///     .merge(providers::Named::new(
///         "cli arguments",
///         providers::Serialized::defaults(cli)
///     ))
///     .extract()?;
/// # Ok(()) }
/// ```
#[derive(Debug, Clone)]
pub struct Named<T> {
    name: Cow<'static, str>,
    provider: T,
}

impl<T> Named<T> {
    /// Wrap a [`Provider`], giving it a new name.
    pub fn new(name: impl Into<Cow<'static, str>>, provider: T) -> Self {
        Self { name: name.into(), provider }
    }
}

impl<T: Provider> Provider for Named<T> {
    fn metadata(&self) -> Metadata {
        let mut meta = self.provider.metadata();
        meta.name.clone_from(&self.name);
        meta
    }
    fn data(&self) -> Result<value::Map<Profile, value::Dict>> {
        self.provider.data()
    }
    fn profile(&self) -> Option<Profile> {
        self.provider.profile()
    }
    fn __metadata_map(&self) -> Option<value::Map<value::Tag, Metadata>> {
        self.provider.__metadata_map()
    }
}
