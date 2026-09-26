use std::borrow::Cow;

use crate::{Metadata, Profile, Provider};
use crate::value::{self, Dict, Map};
use crate::Result;

/// A provider that replaces the name in another provider's metadata.
///
/// ```rust
/// use figment::{Figment, providers::{Named, Serialized}};
///
/// let figment = Figment::from(Named::new(
///     "defaults",
///     Serialized::default("key", "value"),
/// ));
///
/// let value = figment.find_value("key").unwrap();
/// let metadata = figment.get_metadata(value.tag()).unwrap();
/// assert_eq!(metadata.name, "defaults");
/// ```
#[derive(Debug, Clone)]
pub struct Named<T> {
    name: Cow<'static, str>,
    provider: T,
}

impl<T> Named<T> {
    /// Wraps `provider`, replacing its metadata name with `name`.
    pub fn new(name: impl Into<Cow<'static, str>>, provider: T) -> Self {
        Self { name: name.into(), provider }
    }
}

impl<T: Provider> Provider for Named<T> {
    fn metadata(&self) -> Metadata {
        let mut metadata = self.provider.metadata();
        metadata.name.clone_from(&self.name);
        metadata
    }

    fn data(&self) -> Result<Map<Profile, Dict>> {
        self.provider.data()
    }

    fn profile(&self) -> Option<Profile> {
        self.provider.profile()
    }

    fn __metadata_map(&self) -> Option<Map<value::Tag, Metadata>> {
        self.provider.__metadata_map()
    }
}

#[cfg(test)]
mod tests {
    use crate::{Figment, Provider};
    use crate::providers::{Named, Serialized};

    #[test]
    fn replaces_metadata_name() {
        let provider = Serialized::default("key", "value");
        let original_name = provider.metadata().name;
        let figment = Figment::from(Named::new("custom", provider));
        let value = figment.find_value("key").unwrap();
        let metadata = figment.get_metadata(value.tag()).unwrap();

        assert_ne!(metadata.name, original_name);
        assert_eq!(metadata.name, "custom");
    }
}
