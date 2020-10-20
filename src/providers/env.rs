use std::fmt;

use crate::{Profile, Provider, Metadata};
use crate::value::{Map, Dict};
use crate::error::Error;

use uncased::{Uncased, UncasedStr};

crate::util::cloneable_fn_trait!(
    FilterMap: for<'a> Fn(&'a UncasedStr) -> Option<Uncased<'a>> + 'static
);

/// A [`Provider`] that sources its values from environment variables.
///
/// All key-lookups and comparisons are case insensitive, facilitated by the
/// [`UncasedStr`] and [`Uncased`] types. Environment variables names are
/// converted to lowercase before being emitted as keys in the provided data.
///
/// # Provider Details
///
///   * **Profile**
///
///     This provider does not set a profile.
///
///   * **Metadata**
///
///     This provider is named `environment variable(s)`. It does not specify a
///     [`Source`](crate::Source). Interpolation makes path parts uppercase and
///     delimited with a `.`.
///
///   * **Data**
///
///     The data emitted by this provider is single-level dictionary with the
///     keys and values returned by [`Env::iter()`], which reads from the
///     currently set environment variables and is customizable via the various
///     inherent methods. The dictionary is emitted to the profile
///     [`profile`](#structfield.profile), configurable via [`Env::profile()`].
#[derive(Clone)]
#[cfg_attr(nightly, doc(cfg(feature = "env")))]
pub struct Env {
    filter_map: Box<dyn FilterMap>,
    /// The profile config data will be emitted to. Defaults to
    /// [`Profile::Default`].
    pub profile: Profile,
    /// We use this to generate better metadata when available.
    prefix: Option<String>,
}

impl fmt::Debug for Env {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl Env {
    fn new<F: Clone + 'static>(f: F) -> Self
        where F: Fn(&UncasedStr) -> Option<Uncased>
    {
        Env { filter_map: Box::new(f), profile: Profile::Default, prefix: None }
    }

    /// Constructs and `Env` provider that does not filter or map any
    /// environment variables.
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::Env};
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     numbers: Vec<usize>,
    ///     app_bar: String,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.set_env("NUMBERS", "[1, 2, 3]");
    ///     jail.set_env("APP_BAR", "hi");
    ///
    ///     let config: Config = Figment::from(Env::raw()).extract()?;
    ///     assert_eq!(config, Config {
    ///         numbers: vec![1, 2, 3],
    ///         app_bar: "hi".into(),
    ///     });
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn raw() -> Self {
        Env::new(|key| Some(key.into()))
    }

    /// Return an `Env` provider that filters environment variables to those
    /// with the prefix `prefix` and maps to one without the prefix.
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::Env};
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     foo: usize,
    ///     bar: String,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.set_env("APP_FOO", 100);
    ///     jail.set_env("APP_BAR", "hi");
    ///
    ///     let config: Config = Figment::from(Env::prefixed("APP_")).extract()?;
    ///     assert_eq!(config, Config { foo: 100, bar: "hi".into() });
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn prefixed(prefix: &str) -> Self {
        let owned_prefix = prefix.to_string();
        let mut env = Env::new(move |key| match key.starts_with(&owned_prefix) {
            true => Some(key[owned_prefix.len()..].into()),
            false => None
        });

        env.prefix = Some(prefix.into());
        env
    }

    /// Applys an additional filter to the keys of environment variables being
    /// considered.
    ///
    /// ```rust
    /// use figment::{Jail, providers::Env};
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.set_env("FOO_FOO", 100);
    ///     jail.set_env("BAR_BAR", "hi");
    ///     jail.set_env("foobar", "hi");
    ///
    ///     let env = Env::raw().filter(|k| k.starts_with("foo"));
    ///     assert_eq!(env.iter().count(), 2);
    ///
    ///     // Filters chains, like iterator adapters.
    ///     let env = env.filter(|k| k.as_str().contains('_'));
    ///     assert_eq!(env.iter().count(), 1);
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn filter<F: Clone + 'static>(self, filter: F) -> Self
        where F: Fn(&UncasedStr) -> bool
    {
        let filter_map = self.filter_map;
        Env::new(move |key| match filter_map(key) {
            Some(key) if filter(&key) => Some(key),
            _ => None
        })
    }

    /// Applys an additional mapping to the keys of environment variables being
    /// considered.
    ///
    /// ```rust
    /// use figment::{Jail, providers::Env};
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.set_env("FOO_FOO", 100);
    ///     jail.set_env("BAR_FOO", "hi");
    ///     jail.set_env("foobar", "hi");
    ///
    ///     let env = Env::raw().map(|k| match k.starts_with("foo_") {
    ///         true => k["foo_".len()..].into(),
    ///         false => k.into()
    ///     });
    ///
    ///     assert_eq!(env.clone().filter(|k| k == "foo").iter().count(), 1);
    ///
    ///     // Mappings chains, like iterator adapters.
    ///     let env = env.map(|k| match k.starts_with("bar_") {
    ///         true => k["bar_".len()..].into(),
    ///         false => k.into()
    ///     });
    ///
    ///     assert_eq!(env.filter(|k| k == "foo").iter().count(), 2);
    ///     Ok(())
    /// });
    /// ```
    pub fn map<F: Clone + 'static>(self, mapper: F) -> Self
        where F: Fn(&UncasedStr) -> Uncased
    {
        let filter_map = self.filter_map;
        Env::new(move |key| filter_map(key).map(|key| mapper(&key).into_owned()))
    }

    /// Filters out all environment variable keys contained in `keys`.
    ///
    /// ```rust
    /// use figment::{Jail, providers::Env};
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.set_env("FOO_FOO", 1);
    ///     jail.set_env("FOO_BAR", 2);
    ///     jail.set_env("FOO_BAZ", 3);
    ///     jail.set_env("FOO_BAM", 4);
    ///
    ///     let env = Env::prefixed("FOO_").ignore(&["bar", "baz"]);
    ///     assert_eq!(env.clone().iter().count(), 2);
    ///
    ///     // Ignores chain.
    ///     let env = env.ignore(&["bam"]);
    ///     assert_eq!(env.iter().count(), 1);
    ///     Ok(())
    /// });
    /// ```
    pub fn ignore(self, keys: &[&str]) -> Self {
        let keys: Vec<String> = keys.iter().map(|s| s.to_string().into()).collect();
        self.filter(move |key| !keys.iter().any(|k| k.as_str() == key))
    }

    /// Filters out all environment variables keys _not_ contained in `keys`.
    ///
    /// ```rust
    /// use figment::{Jail, providers::Env};
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.set_env("FOO_FOO", 1);
    ///     jail.set_env("FOO_BAR", 2);
    ///     jail.set_env("FOO_BAZ", 3);
    ///     jail.set_env("FOO_BAM", 4);
    ///
    ///     let env = Env::prefixed("FOO_").only(&["bar", "baz", "zoo"]);
    ///     assert_eq!(env.iter().count(), 2);
    ///
    ///     jail.set_env("FOO_ZOO", 4);
    ///     assert_eq!(env.iter().count(), 3);
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn only(self, keys: &[&str]) -> Self {
        let keys: Vec<String> = keys.iter().map(|s| s.to_string().into()).collect();
        self.filter(move |key| keys.iter().any(|k| k.as_str() == key))
    }

    /// Returns an iterator over all of the environment variable `(key, value)`
    /// pairs that will be considered by `self`. The order is not specified.
    /// Keys are always lower-case.
    ///
    /// ```rust
    /// use figment::{Jail, providers::Env};
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.set_env("FOO_B", 2);
    ///     jail.set_env("FOO_A", 1);
    ///     jail.set_env("FOO_C", 3);
    ///
    ///     let env = Env::prefixed("FOO_");
    ///     let mut pairs: Vec<_> = env.iter().collect();
    ///     pairs.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
    ///
    ///     assert_eq!(pairs.len(), 3);
    ///     assert_eq!(pairs[0], ("a".into(), "1".into()));
    ///     assert_eq!(pairs[1], ("b".into(), "2".into()));
    ///     assert_eq!(pairs[2], ("c".into(), "3".into()));
    ///
    ///     jail.set_env("FOO_D", 4);
    ///     let mut pairs: Vec<_> = env.iter().collect();
    ///     pairs.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
    ///
    ///     assert_eq!(pairs.len(), 4);
    ///     assert_eq!(pairs[3], ("d".into(), "4".into()));
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn iter<'a>(&'a self) -> impl Iterator<Item=(Uncased, String)> + 'a {
        std::env::vars_os().filter_map(move |(k, v)| {
            let key = Uncased::from(k.to_string_lossy());
            let mapped_key = (self.filter_map)(&key)?;
            let lower = mapped_key.as_str().to_ascii_lowercase();
            Some((lower.into(), v.to_string_lossy().to_string()))
        })
    }

    /// Sets the profile config data will be emitted to.
    ///
    /// ```rust
    /// use figment::{Profile, providers::Env};
    ///
    /// let env = Env::raw();
    /// assert_eq!(env.profile, Profile::Default);
    ///
    /// let env = env.profile("debug");
    /// assert_eq!(env.profile, Profile::from("debug"));
    /// ```
    pub fn profile<P: Into<Profile>>(mut self, profile: P) -> Self {
        self.profile = profile.into();
        self
    }

    /// Sets the profile config data will be emitted to to `global`.
    ///
    /// ```rust
    /// use figment::{Profile, providers::Env};
    ///
    /// let env = Env::raw();
    /// assert_eq!(env.profile, Profile::Default);
    ///
    /// let env = env.global();
    /// assert_eq!(env.profile, Profile::Global);
    /// ```
    pub fn global(mut self) -> Self {
        self.profile = Profile::Global;
        self
    }

    /// A convenience method to retrieve the value for an environment variable
    /// with name `name`. Retrieval is case-insensitive.
    ///
    /// ```rust
    /// use figment::{Jail, providers::Env};
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.set_env("TESTING", 123);
    ///     assert_eq!(Env::var("testing"), Some("123".to_string()));
    ///     Ok(())
    /// });
    /// ```
    pub fn var(name: &str) -> Option<String> {
        for (env_key, val) in std::env::vars_os() {
            let env_key = env_key.to_string_lossy();
            if uncased::eq(env_key.trim(), name) {
                return Some(val.to_string_lossy().trim().into());
            }
        }

        None
    }

    /// A convenience method to retrieve the value for an environment variable
    /// with name `name` or a default `default` if one is not set. Retrieval
    /// is case-insensitive.
    ///
    /// ```rust
    /// use figment::{Jail, providers::Env};
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.set_env("TESTING", 123);
    ///     assert_eq!(Env::var_or("testing", "whoops"), "123");
    ///     assert_eq!(Env::var_or("hi", "whoops"), "whoops");
    ///     Ok(())
    /// });
    /// ```
    pub fn var_or<S: Into<String>>(name: &str, default: S) -> String {
        Self::var(name).unwrap_or_else(|| default.into())
    }
}

impl Provider for Env {
    fn metadata(&self) -> Metadata {
        let mut md = Metadata::named("environment variable(s)")
            .interpolater(move |_: &Profile, k: &[&str]| {
                let keys: Vec<_> = k.iter()
                    .map(|k| k.to_ascii_uppercase())
                    .collect();

                format!("{}", keys.join("."))
            });

        if let Some(prefix) = &self.prefix {
            md.name = format!("`{}` {}", prefix.to_ascii_uppercase(), md.name).into();
        }

        md
    }

    fn data(&self) -> Result<Map<Profile, Dict>, Error> {
        let dict: Dict = self.iter()
            .map(|(k, v)| (k.into_string(), v.parse().expect("infallible")))
            .collect();

        Ok(self.profile.collect(dict))
    }
}
