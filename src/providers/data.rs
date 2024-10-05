use std::marker::PhantomData;
use std::path::{Path, PathBuf};

use serde::de::{self, DeserializeOwned};

use crate::value::{Map, Dict};
use crate::{Error, Profile, Provider, Metadata};
use crate::error::Kind;

/// A `Provider` that sources values from a file or string in a given
/// [`Format`].
///
/// # Constructing
///
/// A `Data` provider is typically constructed indirectly via a type that
/// implements the [`Format`] trait via the [`Format::file()`] and
/// [`Format::string()`] methods which in-turn defer to [`Data::file()`] and
/// [`Data::string()`] by default:
///
/// ```rust
/// // The `Format` trait must be in-scope to use its methods.
/// use figment::providers::{Format, Data, Json};
///
/// // These two are equivalent, except the former requires the explicit type.
/// let json = Data::<Json>::file("foo.json");
/// let json = Json::file("foo.json");
/// ```
///
/// # Provider Details
///
///   * **Profile**
///
///     This provider does not set a profile.
///
///   * **Metadata**
///
///     This provider is named `${NAME} file` (when constructed via
///     [`Data::file()`]) or `${NAME} source string` (when constructed via
///     [`Data::string()`]), where `${NAME}` is [`Format::NAME`]. When
///     constructed from a file, the file's path is specified as file
///     [`Source`](crate::Source). Path interpolation is unchanged from the
///     default.
///
///   * **Data (Unnested, _default_)**
///
///     When nesting is _not_ specified, the source file or string is read and
///     parsed, and the parsed dictionary is emitted into the profile
///     configurable via [`Data::profile()`], which defaults to
///     [`Profile::Default`]. If the source is a file path and the file is not
///     present, an empty dictionary is emitted unless [`Data::required()`] is
///     set to `true` in which case the provider fails.
///
///   * **Data (Nested)**
///
///     When nesting is specified, the source value is expected to be a
///     dictionary. It's top-level keys are emitted as profiles, and the value
///     corresponding to each key as the profile data.
#[derive(Debug, Clone)]
pub struct Data<F: Format> {
    source: Source,
    /// The profile data will be emitted to if nesting is disabled. Defaults to
    /// [`Profile::Default`].
    pub profile: Option<Profile>,
    _format: PhantomData<F>,
}

#[derive(Debug, Clone)]
enum Source {
    File { path: PathBuf, required: bool, search: bool, },
    String(String),
}

impl<F: Format> Data<F> {
    fn new(profile: Option<Profile>, source: Source) -> Self {
        Data { source, profile, _format: PhantomData }
    }

    /// Returns a `Data` provider that sources its values by parsing the file at
    /// `path` as format `F`. If `path` is relative, the file is searched for in
    /// the current working directory and all parent directories until the root,
    /// and the first hit is used. If you don't want parent directories to be
    /// searched, use [`Data::file_exact()`] instead.
    ///
    /// Nesting is disabled by default. Use [`Data::nested()`] to enable it.
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}, value::Map};
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     numbers: Vec<usize>,
    ///     untyped: Map<String, usize>,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.create_file("Config.toml", r#"
    ///         numbers = [1, 2, 3]
    ///
    ///         [untyped]
    ///         key = 1
    ///         other = 4
    ///     "#)?;
    ///
    ///     let config: Config = Figment::from(Toml::file("Config.toml")).extract()?;
    ///     assert_eq!(config, Config {
    ///         numbers: vec![1, 2, 3],
    ///         untyped: figment::util::map!["key".into() => 1, "other".into() => 4],
    ///     });
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn file<P: AsRef<Path>>(path: P) -> Self {
        Data::new(Some(Profile::Default), Source::File {
            path: path.as_ref().to_path_buf(),
            required: false,
            search: true,
        })
    }

    /// Returns a `Data` provider that sources its values by parsing the string
    /// `string` as format `F`. Nesting is not enabled by default; use
    /// [`Data::nested()`] to enable nesting.
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}, value::Map};
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     numbers: Vec<usize>,
    ///     untyped: Map<String, usize>,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     let source = r#"
    ///         numbers = [1, 2, 3]
    ///         untyped = { key = 1, other = 4 }
    ///     "#;
    ///
    ///     let config: Config = Figment::from(Toml::string(source)).extract()?;
    ///     assert_eq!(config, Config {
    ///         numbers: vec![1, 2, 3],
    ///         untyped: figment::util::map!["key".into() => 1, "other".into() => 4],
    ///     });
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn string(string: &str) -> Self {
        Data::new(Some(Profile::Default), Source::String(string.into()))
    }

    /// Deprecated alias for `Data::file(path).search(false)`.
    ///
    /// Use [`file(path).search(false)`](Data::search) instead.
    #[doc(hidden)]
    #[deprecated(since = "0.10.20", note = "use `::file(path).search(false)` instead")]
    pub fn file_exact<P: AsRef<Path>>(path: P) -> Self {
        Data::file(path.as_ref()).search(false)
    }

    /// Enables nesting on `self`, which results in top-level keys of the
    /// sourced data being treated as profiles.
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}, value::Map};
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     numbers: Vec<usize>,
    ///     untyped: Map<String, usize>,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.create_file("Config.toml", r#"
    ///         [global.untyped]
    ///         global = 0
    ///         hi = 7
    ///
    ///         [staging]
    ///         numbers = [1, 2, 3]
    ///
    ///         [release]
    ///         numbers = [6, 7, 8]
    ///     "#)?;
    ///
    ///     // Enable nesting via `nested()`.
    ///     let figment = Figment::from(Toml::file("Config.toml").nested());
    ///
    ///     let figment = figment.select("staging");
    ///     let config: Config = figment.extract()?;
    ///     assert_eq!(config, Config {
    ///         numbers: vec![1, 2, 3],
    ///         untyped: figment::util::map!["global".into() => 0, "hi".into() => 7],
    ///     });
    ///
    ///     let config: Config = figment.select("release").extract()?;
    ///     assert_eq!(config, Config {
    ///         numbers: vec![6, 7, 8],
    ///         untyped: figment::util::map!["global".into() => 0, "hi".into() => 7],
    ///     });
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn nested(mut self) -> Self {
        self.profile = None;
        self
    }

    /// Sets whether the source file is required to be present. The default is
    /// `false`.
    ///
    /// When `false`, a non-existent file is treated as an empty source, that
    /// is, it deserializes to an empty dictionary. When `true`, a non-existent
    /// file causes an error. If the source is a string, this setting has no
    /// effect.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}};
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     #[serde(default)]
    ///     foo: usize,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     // Create 'config.toml'.
    ///     jail.create_file("config.toml", "foo = 123")?;
    ///
    ///     // By default, missing files are treated as empty. This implies
    ///     // `foo` is not set, so it defaults to `0` via `serde(default)`.
    ///     let config = Figment::from(Toml::file("missing.toml")).extract::<Config>()?;
    ///     assert_eq!(config.foo, 0);
    ///
    ///     // Set `required` to true to disallow missing files.
    ///     let source = Toml::file("missing.toml");
    ///     let config = Figment::from(source.required(true)).extract::<Config>();
    ///     assert!(config.is_err());
    ///
    ///     // Set `required` to false to explicitly allow missing files.
    ///     # let source = Toml::file("missing.toml").required(true);
    ///     let config = Figment::from(source.required(false)).extract::<Config>()?;
    ///     assert_eq!(config.foo, 0);
    ///
    ///     // The setting has no effect when the file is present.
    ///     let config = Figment::from(Toml::file("config.toml")).extract::<Config>()?;
    ///     assert_eq!(config.foo, 123);
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn required(mut self, yes: bool) -> Self {
        if let Source::File { required, .. } = &mut self.source {
            *required = yes;
        }

        self
    }

    /// Set whether to enable recursively searching in parent directories for
    /// the source file path. The default is `true`.
    ///
    /// When `true`, the search is enabled. When `false` or when the file path
    /// is absolute, no search is performed and only the exact file path is
    /// used. If the source is a string, this setting has no effect.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}};
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     foo: usize,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     // Create 'subdir/config.toml' and set `cwd = subdir`.
    ///     jail.create_file("config.toml", "foo = 123")?;
    ///     jail.change_dir(jail.create_dir("subdir")?)?;
    ///
    ///     // We are in `subdir`. `config.toml` is in `../`. Since `search` is
    ///     // enabled by default, the file is found in the parent directory.
    ///     let source = Toml::file("config.toml");
    ///     let config = Figment::from(source).extract::<Config>()?;
    ///     assert_eq!(config.foo, 123);
    ///
    ///     // Set `search` to false to disable searching.
    ///     let source = Toml::file("config.toml").search(false);
    ///     let config = Figment::from(source).extract::<Config>();
    ///     assert!(config.is_err());
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn search(mut self, enabled: bool) -> Self {
        if let Source::File { search, .. } = &mut self.source {
            *search = enabled;
        }

        self
    }

    /// Set the profile to emit data to when nesting is disabled.
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}, value::Map};
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config { value: u8 }
    ///
    /// Jail::expect_with(|jail| {
    ///     let provider = Toml::string("value = 123").profile("debug");
    ///     let config: Config = Figment::from(provider).select("debug").extract()?;
    ///     assert_eq!(config, Config { value: 123 });
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn profile<P: Into<Profile>>(mut self, profile: P) -> Self {
        self.profile = Some(profile.into());
        self
    }

    /// Resolves `path` to a valid file path or returns `None`. If `search` is
    /// `true` and `path` is not absolute, searches the current working
    /// directory and all parent directories until the root and return the first
    /// valid file path. Otherwise returns `path` if it points to a valid file.
    fn resolve(path: &Path, search: bool) -> Option<PathBuf> {
        if path.is_absolute() || !search {
            return path.is_file().then(|| path.to_path_buf());
        }

        let cwd = std::env::current_dir().ok()?;
        let mut cwd = cwd.as_path();
        loop {
            let file_path = cwd.join(path);
            if file_path.is_file() {
                return Some(file_path.into());
            }

            cwd = cwd.parent()?;
        }
    }
}

impl<F: Format> Provider for Data<F> {
    fn metadata(&self) -> Metadata {
        use Source::*;
        match &self.source {
            String(_) => Metadata::named(format!("{} source string", F::NAME)),
            File { path, search, required: _ } => {
                let path = Self::resolve(path, *search).unwrap_or_else(|| path.clone());
                Metadata::from(format!("{} file", F::NAME), path.as_path())
            }
        }
    }

    fn data(&self) -> Result<Map<Profile, Dict>, Error> {
        use Source as S;
        let map: Result<Map<Profile, Dict>, _> = match (&self.source, &self.profile) {
            (S::File { path, required, search }, profile) => {
                match Self::resolve(path, *search) {
                    Some(path) => match profile {
                        Some(prof) => F::from_path(&path).map(|v| prof.collect(v)),
                        None => F::from_path(&path),
                    },
                    None if !required => Ok(Map::new()),
                    None => {
                        let msg = format!("required file `{}` not found", path.display());
                        return Err(Kind::Message(msg).into());
                    }
                }
            },
            (S::String(s), None) => F::from_str(s),
            (S::String(s), Some(prof)) => F::from_str(s).map(|v| prof.collect(v)),
        };

        Ok(map.map_err(|e| e.to_string())?)
    }
}

/// Trait implementable by text-based [`Data`] format providers.
///
/// Instead of implementing [`Provider`] directly, types that refer to data
/// formats, such as [`Json`] and [`Toml`], implement this trait. By
/// implementing [`Format`], they become [`Provider`]s indirectly via the
/// [`Data`] type, which serves as a provider for all `T: Format`.
///
/// ```rust
/// use figment::providers::Format;
///
/// # use serde::de::DeserializeOwned;
/// # struct T;
/// # impl Format for T {
/// #     type Error = serde::de::value::Error;
/// #     const NAME: &'static str = "T";
/// #     fn from_str<'de, T: DeserializeOwned>(_: &'de str) -> Result<T, Self::Error> { todo!() }
/// # }
/// # fn is_provider<T: figment::Provider>(_: T) {}
/// // If `T` implements `Format`, `T` is a `Provider`.
/// // Initialize it with `T::file()` or `T::string()`.
/// let provider = T::file("foo.fmt");
/// # is_provider(provider);
/// let provider = T::string("some -- format");
/// # is_provider(provider);
/// ```
///
/// [`Data<T>`]: Data
///
/// # Implementing
///
/// There are two primary implementation items:
///
///   1. [`Format::NAME`]: This should be the name of the data format: `"JSON"`
///      or `"TOML"`. The string is used in the [metadata for `Data`].
///
///   2. [`Format::from_str()`]: This is the core string deserialization method.
///      A typical implementation will simply call an existing method like
///      [`toml_edit::de::from_str`]. For writing a custom data format, see
///      [serde's writing a data format guide].
///
/// The default implementations for [`Format::from_path()`], [`Format::file()`],
/// and [`Format::string()`] methods should likely not be overwritten.
///
/// [`NAME`]: Format::NAME
/// [serde's writing a data format guide]: https://serde.rs/data-format.html
pub trait Format: Sized {
    /// The data format's error type.
    type Error: de::Error;

    /// The name of the data format, for instance `"JSON"` or `"TOML"`.
    const NAME: &'static str;

    /// Returns a `Data` provider that sources its values by parsing the file at
    /// `path` as format `Self`. See [`Data::file()`] for more details. The
    /// default implementation calls `Data::file(path)`.
    fn file<P: AsRef<Path>>(path: P) -> Data<Self> {
        Data::file(path)
    }

    /// Returns a `Data` provider that sources its values by parsing `string` as
    /// format `Self`. See [`Data::string()`] for more details. The default
    /// implementation calls `Data::string(string)`.
    fn string(string: &str) -> Data<Self> {
        Data::string(string)
    }

    /// Deprecated alias for `file(path).search(false)`.
    ///
    /// Use [`file(path).search(false)`](Data::search) instead.
    #[doc(hidden)]
    #[deprecated(since = "0.10.20", note = "use `::file(path).search(false)` instead")]
    fn file_exact<P: AsRef<Path>>(path: P) -> Data<Self> {
        Data::file(path.as_ref()).search(false)
    }

    /// Parses `string` as the data format `Self` as a `T` or returns an error
    /// if the `string` is an invalid `T`. **_Note:_** This method is _not_
    /// intended to be called directly. Instead, it is intended to be
    /// _implemented_ and then used indirectly via the [`Data::file()`] or
    /// [`Data::string()`] methods.
    fn from_str<'de, T: DeserializeOwned>(string: &'de str) -> Result<T, Self::Error>;

    /// Parses the file at `path` as the data format `Self` as a `T` or returns
    /// an error if the `string` is an invalid `T`. The default implementation
    /// calls [`Format::from_str()`] with the contents of the file. **_Note:_**
    /// This method is _not_ intended to be called directly. Instead, it is
    /// intended to be _implemented on special occasions_ and then used
    /// indirectly via the [`Data::file()`] or [`Data::string()`] methods.
    fn from_path<T: DeserializeOwned>(path: &Path) -> Result<T, Self::Error> {
        let source = std::fs::read_to_string(path).map_err(de::Error::custom)?;
        Self::from_str(&source)
    }
}

#[allow(unused_macros)]
macro_rules! impl_format {
    ($name:ident $NAME:literal/$string:literal: $func:expr, $E:ty, $doc:expr) => (
        #[cfg(feature = $string)]
        #[cfg_attr(nightly, doc(cfg(feature = $string)))]
        #[doc = $doc]
        pub struct $name;

        #[cfg(feature = $string)]
        impl Format for $name {
            type Error = $E;

            const NAME: &'static str = $NAME;

            fn from_str<'de, T: DeserializeOwned>(s: &'de str) -> Result<T, $E> {
                $func(s)
            }
        }
    );

    ($name:ident $NAME:literal/$string:literal: $func:expr, $E:ty) => (
        impl_format!($name $NAME/$string: $func, $E, concat!(
            "A ", $NAME, " [`Format`] [`Data`] provider.",
            "\n\n",
            "Static constructor methods on `", stringify!($name), "` return a
            [`Data`] value with a generic marker of [`", stringify!($name), "`].
            Thus, further use occurs via methods on [`Data`].",
            "\n```\n",
            "use figment::providers::{Format, ", stringify!($name), "};",
            "\n\n// Source directly from a source string...",
            "\nlet provider = ", stringify!($name), r#"::string("source-string");"#,
            "\n\n// Or read from a file on disk.",
            "\nlet provider = ", stringify!($name), r#"::file("path-to-file");"#,
            "\n\n// Or configured as nested (via Data::nested()):",
            "\nlet provider = ", stringify!($name), r#"::file("path-to-file").nested();"#,
            "\n```",
            "\n\nSee also [`", stringify!($func), "`] for parsing details."
        ));
    )
}

#[cfg(feature = "yaml")]
#[cfg_attr(nightly, doc(cfg(feature = "yaml")))]
impl YamlExtended {
    /// This "YAML Extended" format parser implements the draft ["Merge Key
    /// Language-Independent Type for YAML™ Version
    /// 1.1"](https://yaml.org/type/merge.html) spec via
    /// [`serde_yml::Value::apply_merge()`]. This method is _not_ intended to
    /// be used directly but rather indirectly by making use of `YamlExtended`
    /// as a provider. The extension is not part of any officially supported
    /// YAML release and is deprecated entirely since YAML 1.2. Using
    /// `YamlExtended` instead of [`Yaml`] enables merge keys, allowing YAML
    /// like the following to parse with key merges applied:
    ///
    /// ```yaml
    /// tasks:
    ///   build: &webpack_shared
    ///     command: webpack
    ///     args: build
    ///     inputs:
    ///       - 'src/**/*'
    ///   start:
    ///     <<: *webpack_shared
    ///     args: start
    /// ```
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Yaml, YamlExtended}};
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Circle {
    ///     x: usize,
    ///     y: usize,
    ///     r: usize,
    /// }
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     circle1: Circle,
    ///     circle2: Circle,
    ///     circle3: Circle,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.create_file("Config.yaml", r#"
    ///         point: &POINT { x: 1, y: 2 }
    ///         radius: &RADIUS
    ///           r: 10
    ///
    ///         circle1:
    ///           <<: *POINT
    ///           r: 3
    ///
    ///         circle2:
    ///           <<: [ *POINT, *RADIUS ]
    ///
    ///         circle3:
    ///           <<: [ *POINT, *RADIUS ]
    ///           y: 14
    ///           r: 20
    ///     "#)?;
    ///
    ///     let config: Config = Figment::from(YamlExtended::file("Config.yaml")).extract()?;
    ///     assert_eq!(config, Config {
    ///         circle1: Circle { x: 1, y: 2, r: 3 },
    ///         circle2: Circle { x: 1, y: 2, r: 10 },
    ///         circle3: Circle { x: 1, y: 14, r: 20 },
    ///     });
    ///
    ///     // Note that just `Yaml` would fail, since it doesn't support merge.
    ///     let config = Figment::from(Yaml::file("Config.yaml"));
    ///     assert!(config.extract::<Config>().is_err());
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn from_str<'de, T: DeserializeOwned>(s: &'de str) -> serde_yml::Result<T> {
        let mut value: serde_yml::Value = serde_yml::from_str(s)?;
        value.apply_merge()?;
        T::deserialize(value)
    }
}

impl_format!(Toml "TOML"/"toml": toml_edit::de::from_str, toml_edit::de::Error);
impl_format!(Yaml "YAML"/"yaml": serde_yml::from_str, serde_yml::Error);
impl_format!(Json "JSON"/"json": serde_json::from_str, serde_json::error::Error);
impl_format!(YamlExtended "YAML Extended"/"yaml": YamlExtended::from_str, serde_yml::Error);
