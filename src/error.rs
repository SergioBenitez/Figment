//! Error values produces when extracting configurations.

use std::fmt::{self, Display};
use std::borrow::Cow;
use std::ops::{Deref, DerefMut};
use std::path::PathBuf;
use std::sync::Arc;

use serde::{ser, de};

use crate::{Figment, Profile, Metadata, key::KeyPath, value::{Tag, Value}};

/// An alias to [`std::result::Result`] with [`Error`] as the default error type.
pub type Result<T, E = Error> = std::result::Result<T, E>;

/// An origin of an [`Error`]: a provider's metadata and an optional profile.
///
/// # Overview
///
/// Every [`Error`] produced by a [`Figment`] records its _origins_, retrievable
/// via [`Error::origins()`]. An origin consists of:
///
///   * The [`Metadata`] of the [`Provider`] that supplied the value or data.
///   * The [`Profile`] of the value, if any.
///
/// An error for an individual value has one origin: that of the value. An error
/// for a dictionary or array has the origins of the values it contains. An
/// error that occurs while a provider produces data, that is, in
/// [`Provider::data()`], has an origin with no profile. Errors produced outside
/// of a `Figment`, such as by [`Value::deserialize()`], have no origins. See
/// [`Error::origins()`] for details.
///
/// ## Display
///
/// When an `Error` is displayed, each of its origins is listed on its own line
/// along with the metadata's name, its [`Source`], if it is known, and the
/// profile, if any. See [`Error`'s docs](Error#display) for examples.
///
/// # Example
///
/// ```rust
/// use figment::{Figment, Profile, providers::{Format, Toml}, value::Value};
///
/// figment::Jail::expect_with(|jail| {
///     jail.create_file("Config.toml", r#"port = "oops""#)?;
///
///     // The invalid `port` originated in the TOML file's default profile.
///     let figment = Figment::from(Toml::file("Config.toml"));
///     let error = figment.extract_inner::<u16>("port").unwrap_err();
///     assert_eq!(error.origins().len(), 1);
///     assert_eq!(error.origins()[0].metadata.name, "TOML file");
///     assert_eq!(error.origins()[0].profile, Some(Profile::Default));
///
///     // A file that fails to parse produces an error without a profile.
///     jail.create_file("Config.toml", "port = ")?;
///     let figment = Figment::from(Toml::file("Config.toml"));
///     let error = figment.extract::<Value>().unwrap_err();
///     assert_eq!(error.origins().len(), 1);
///     assert_eq!(error.origins()[0].metadata.name, "TOML file");
///     assert_eq!(error.origins()[0].profile, None);
///
///     Ok(())
/// });
/// ```
///
/// [`Provider`]: crate::Provider
/// [`Provider::data()`]: crate::Provider::data()
/// [`Source`]: crate::Source
#[derive(Clone, Debug, PartialEq)]
pub struct Origin {
    /// The profile of the value, or `None` if the error occurred while
    /// producing data.
    pub profile: Option<Profile>,
    /// The metadata for the value's provider, shared with the [`Figment`].
    pub metadata: Arc<Metadata>,
}

/// An error that occurred while producing data or extracting a configuration.
///
/// # Constructing Errors
///
/// An `Error` will generally be constructed indirectly via its implementations
/// of serde's [`de::Error`] and [`ser::Error`], that is, as a result of
/// serialization or deserialization errors. When implementing [`Provider`],
/// however, it may be necessary to construct an `Error` directly.
///
/// [`Provider`]: crate::Provider
///
/// Broadly, there are two ways to construct an `Error`:
///
///   * With an error message, as `Error` impls `From<String>` and `From<&str>`:
///
///     ```
///     use figment::Error;
///
///     Error::from(format!("{} is invalid", 1));
///
///     Error::from("whoops, something went wrong!");
///     ```
///
///   * With a [`Kind`], as `Error` impls `From<Kind>`:
///
///     ```
///     use figment::{error::{Error, Kind}, value::Value};
///
///     let value = Value::serialize(&100).unwrap();
///     if !value.as_str().is_some() {
///         let kind = Kind::InvalidType(value.to_actual(), "string".into());
///         let error = Error::from(kind);
///     }
///     ```
///
/// As always, `?` can be used to automatically convert into an `Error` using
/// the available `From` implementations:
///
/// ```
/// use std::fs::File;
///
/// fn try_read() -> Result<(), figment::Error> {
///     let x = File::open("/tmp/foo.boo").map_err(|e| e.to_string())?;
///     Ok(())
/// }
/// ```
///
/// # Display
///
/// `Error` uses all of the available information about the error, including its
/// kind, path, and [`origins()`](Error::origins()), to display a message. For
/// an individual value, such a message may look like:
///
/// ```text
/// invalid type: found string "hi", expected u16 for key "server" > "port"
///   from Config.toml TOML file (profile "staging", key "staging.server.port")
/// ```
///
/// Each component of the key path is quoted and separated by ` > `. The
/// provider's metadata is also used to interpolate the path to the key at its
/// source.
///
/// For a dictionary or array, the message lists the origins of its values:
///
/// ```text
/// min must not exceed max for key "limits"
///   from Config.toml TOML file (profile "default")
///   from `APP_` environment variable(s) (profile "global")
/// ```
///
/// # Iterator
///
/// An `Error` may contain more than one error. To process all errors, iterate
/// over an `Error`:
///
/// ```rust
/// fn with_error(error: figment::Error) {
///     for error in error {
///         println!("error: {}", error);
///     }
/// }
/// ```
#[derive(Clone, PartialEq)]
#[repr(transparent)]
pub struct Error {
    inner: Box<ErrorInner>,
}

const _: () = assert!(std::mem::size_of::<Error>() <= 128);

/// The contents of an [`Error`].
///
/// `Error` boxes this value so that returning an error is inexpensive and does
/// not trigger `clippy::result_large_err` in downstream crates.
#[derive(Clone, Debug, PartialEq)]
pub struct ErrorInner {
    /// The path to the configuration key that errored, if known.
    pub path: Vec<String>,
    /// The error kind.
    pub kind: Kind,
    context: Option<Context>,
    prev: Option<Error>,
}

/// The value or provider an error is about, which determines its origins.
///
/// A context is set in two steps. First, `Error::at()` records the `Tag` of the
/// value that errored or, if the value is a dictionary or array, the `Tags` of
/// the values it contains. An error passes through every parent value on its
/// way out of a deserializer, but only the first value, the one that errored,
/// is recorded. Then, `Error::resolved()` looks up each tag in the `Figment`
/// that produced the value, converting a `Tag` into an `Origin` and `Tags` into
/// `Origins`. Tags aren't resolved immediately because a value can be
/// deserialized without a `Figment`, as with `Value::deserialize()`.
///
/// A value that wasn't produced by a `Figment`, such as one created via
/// `Value::from()`, has a default tag and thus no origins. Its context is
/// recorded nonetheless so that the error isn't instead attributed to a parent
/// value. If a provider returns such an error, or an error without a context,
/// `Error::provided_by()` replaces the context with the provider's `Origin`.
#[derive(Clone, Debug, PartialEq)]
enum Context {
    /// An individual value with the given tag.
    Tag(Tag),
    /// A dictionary or array containing values with the given tags.
    Tags(Vec<Tag>),
    /// The origin of an individual value or of a provider's error, or `None` if
    /// the `Figment` has no metadata for the value's tag.
    Origin(Option<Origin>),
    /// The origins of the values in a dictionary or array. This is distinct
    /// from `Origin` even when there is only one origin since `Display` only
    /// interpolates the key path, e.g, `LIMITS.MIN`, for an individual value.
    Origins(Vec<Origin>),
}

impl Deref for Error {
    type Target = ErrorInner;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for Error {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Error")
            .field("context", &self.context)
            .field("path", &self.path)
            .field("kind", &self.kind)
            .field("prev", &self.prev)
            .finish()
    }
}

/// An error kind, encapsulating serde's [`serde::de::Error`].
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    /// A custom error message.
    Message(String),

    /// A required file could not be found: (requested path).
    FileNotFound(PathBuf),

    /// An invalid type: (actual, expected). See
    /// [`serde::de::Error::invalid_type()`].
    InvalidType(Actual, String),
    /// An invalid value: (actual, expected). See
    /// [`serde::de::Error::invalid_value()`].
    InvalidValue(Actual, String),
    /// Too many or too few items: (actual, expected). See
    /// [`serde::de::Error::invalid_length()`].
    InvalidLength(usize, String),

    /// A variant with an unrecognized name: (actual, expected). See
    /// [`serde::de::Error::unknown_variant()`].
    UnknownVariant(String, &'static [&'static str]),
    /// A field with an unrecognized name: (actual, expected). See
    /// [`serde::de::Error::unknown_field()`].
    UnknownField(String, &'static [&'static str]),
    /// A field was missing: (name). See [`serde::de::Error::missing_field()`].
    MissingField(Cow<'static, str>),
    /// A field appeared more than once: (name). See
    /// [`serde::de::Error::duplicate_field()`].
    DuplicateField(&'static str),

    /// The `isize` was not in range of any known sized signed integer.
    ISizeOutOfRange(isize),
    /// The `usize` was not in range of any known sized unsigned integer.
    USizeOutOfRange(usize),

    /// The serializer or deserializer does not support the `Actual` type.
    Unsupported(Actual),

    /// The type `.0` cannot be used for keys, need a `.1`.
    UnsupportedKey(Actual, Cow<'static, str>),
}

impl Error {
    fn contexts_mut(&mut self) -> impl Iterator<Item = &mut Option<Context>> {
        let mut next = Some(&mut *self.inner);
        std::iter::from_fn(move || {
            let error = next.take()?;
            next = error.prev.as_mut().map(|e| &mut *e.inner);
            Some(&mut error.context)
        })
    }

    pub(crate) fn missing_field<P: KeyPath + ?Sized>(path: &P) -> Self {
        let field = path.segments()
            .last()
            .map(|segment| segment.as_ref().to_owned())
            .unwrap_or_default();

        Kind::MissingField(field.into()).into()
    }

    pub(crate) fn prefixed(mut self, path: impl KeyPath) -> Self {
        let mut error = Some(&mut self);
        while let Some(e) = error {
            let suffix_len = e.path.len();
            e.path.extend(path.segments().map(|s| s.as_ref().to_owned()));
            e.path.rotate_left(suffix_len);
            error = e.prev.as_mut();
        }

        self
    }

    pub(crate) fn at(mut self, value: &Value) -> Self {
        let mut context: Option<&Context> = None;
        for slot in self.contexts_mut().filter(|c| c.is_none()) {
            context = Some(slot.insert(context.cloned().unwrap_or_else(|| match value {
                Value::Dict(..) | Value::Array(..) => Context::Tags(value.source_tags()),
                _ => Context::Tag(value.tag()),
            })));
        }

        self
    }

    pub(crate) fn provided_by(mut self, metadata: &Arc<Metadata>) -> Self {
        for context in self.contexts_mut() {
            let untagged = match context {
                None => true,
                Some(Context::Tag(tag)) => tag.is_default(),
                Some(Context::Tags(tags)) => tags.is_empty(),
                _ => false,
            };

            if untagged {
                *context = Some(Context::Origin(Some(Origin {
                    profile: None,
                    metadata: Arc::clone(metadata),
                })));
            }
        }

        self
    }

    pub(crate) fn resolved(mut self, config: &Figment) -> Self {
        let origin = |tag: Tag| config.metadata.get(&tag).map(|metadata| Origin {
            profile: Some(tag.profile().unwrap_or_else(|| config.profile().clone())),
            metadata: Arc::clone(metadata),
        });

        for context in self.contexts_mut().flatten() {
            *context = match context {
                Context::Tag(tag) => Context::Origin(origin(*tag)),
                Context::Tags(tags) => {
                    let mut origins = Vec::with_capacity(tags.len());
                    origins.extend(tags.iter().copied().filter_map(origin));
                    Context::Origins(origins)
                },
                _ => continue,
            };
        }

        self
    }
}

impl Error {
    /// Returns the known [origins](Origin) associated with this error.
    ///
    /// Each origin identifies a provider's [`Metadata`] and, for errors
    /// associated with a configuration value, the value's [`Profile`]. The
    /// origins depend on where the error occurred:
    ///
    ///   * **An individual value:** the origin of that value.
    ///   * **A dictionary or array:** the origins of the values it contains
    ///     after merging and joining. For an empty dictionary or array, the
    ///     origin is the provider that supplied the empty value, if known.
    ///   * **A missing key:** the origins of its first existing parent. For
    ///     example, if looking up `"server.tls.cert"` fails because `"server"`
    ///     has no `"tls"` key, the origins are those of `"server"`.
    ///   * **Producing data:** the provider's metadata, without a profile.
    ///
    /// Figment identifies the particular value that errored when possible.
    /// A custom deserializer or Serde buffering may instead associate the
    /// error with an entire dictionary or array. Thus, not every origin
    /// necessarily caused the error.
    ///
    /// Origins are returned in no particular order. Each error in a chain has
    /// its own origins, and their metadata remains available after the
    /// `Figment` is dropped. If no origins are known, returns an empty slice.
    /// This includes errors produced without a `Figment`, such as those from
    /// [`Value::deserialize()`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use figment::{Figment, providers::Named};
    ///
    /// let figment = Figment::from(Named::new("defaults", ("address", "127.0.0.1")))
    ///     .merge(Named::new("local", ("port", "oops")));
    ///
    /// // The invalid `port` was provided by `local`.
    /// let error = figment.extract_inner::<u16>("port").unwrap_err();
    /// assert_eq!(error.origins().len(), 1);
    /// assert_eq!(error.origins()[0].metadata.name, "local");
    ///
    /// // The missing `workers` key is an error for the containing dictionary.
    /// let error = figment.find_value("workers").unwrap_err();
    /// assert!(error.missing());
    /// let mut names: Vec<_> = error.origins().iter()
    ///     .map(|origin| origin.metadata.name.as_ref())
    ///     .collect();
    ///
    /// names.sort_unstable();
    /// assert_eq!(names, ["defaults", "local"]);
    /// ```
    pub fn origins(&self) -> &[Origin] {
        match &self.context {
            Some(Context::Origin(Some(origin))) => std::slice::from_ref(origin),
            Some(Context::Origins(origins)) => origins,
            _ => &[],
        }
    }

    /// Returns `true` if the error's kind is `MissingField`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use figment::error::{Error, Kind};
    ///
    /// let error = Error::from(Kind::MissingField("path".into()));
    /// assert!(error.missing());
    /// ```
    pub fn missing(&self) -> bool {
        matches!(self.kind, Kind::MissingField(..))
    }

    /// Appends `path` to the error's path.
    ///
    /// # Example
    ///
    /// ```rust
    /// use figment::Error;
    ///
    /// let error = Error::from("an error message").with_path("some_path");
    /// assert_eq!(error.path, vec!["some_path"]);
    ///
    /// let error = Error::from("an error message").with_path("some.path");
    /// assert_eq!(error.path, vec!["some", "path"]);
    ///
    /// let error = Error::from("an error message").with_path(["some.path"]);
    /// assert_eq!(error.path, vec!["some.path"]);
    /// ```
    pub fn with_path(mut self, path: impl KeyPath) -> Self {
        self.path.extend(path.segments().map(|v| v.as_ref().to_owned()));
        self
    }

    /// Prepends `self` to `error` and returns `error`.
    ///
    /// ```rust
    /// use figment::error::Error;
    ///
    /// let e1 = Error::from("1");
    /// let e2 = Error::from("2");
    /// let e3 = Error::from("3");
    ///
    /// let error = e1.chain(e2).chain(e3);
    /// assert_eq!(error.count(), 3);
    ///
    /// let unchained = error.into_iter()
    ///     .map(|e| e.to_string())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(unchained, vec!["3", "2", "1"]);
    ///
    /// let e1 = Error::from("1");
    /// let e2 = Error::from("2");
    /// let e3 = Error::from("3");
    /// let error = e3.chain(e2).chain(e1);
    /// assert_eq!(error.count(), 3);
    ///
    /// let unchained = error.into_iter()
    ///     .map(|e| e.to_string())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(unchained, vec!["1", "2", "3"]);
    /// ```
    pub fn chain(self, mut error: Error) -> Self {
        let mut tail = &mut error.inner.prev;
        while let Some(prev) = tail {
            tail = &mut prev.inner.prev;
        }

        *tail = Some(self);
        error
    }

    /// Returns the number of errors represented by `self`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use figment::{Figment, providers::{Format, Toml}};
    ///
    /// figment::Jail::expect_with(|jail| {
    ///     jail.create_file("Base.toml", r#"
    ///         # oh no, an unclosed array!
    ///         cat = [1
    ///     "#)?;
    ///
    ///     jail.create_file("Release.toml", r#"
    ///         # and now an unclosed string!?
    ///         cat = "
    ///     "#)?;
    ///
    ///     let figment = Figment::from(Toml::file("Base.toml"))
    ///         .merge(Toml::file("Release.toml"));
    ///
    ///     let error = figment.extract_inner::<String>("cat").unwrap_err();
    ///     assert_eq!(error.count(), 2);
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn count(&self) -> usize {
        1 + self.prev.as_ref().map_or(0, |e| e.count())
    }
}

/// An iterator over all errors in an [`Error`].
pub struct IntoIter(Option<Error>);

impl Iterator for IntoIter {
    type Item = Error;

    fn next(&mut self) -> Option<Self::Item> {
        let mut error = self.0.take()?;
        self.0 = error.prev.take();
        Some(error)
    }
}

impl IntoIterator for Error {
    type Item = Error;
    type IntoIter = IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(Some(self))
    }
}

/// A type that enumerates all of serde's types, used to indicate that a value
/// of the given type was received.
#[allow(missing_docs)]
#[derive(Clone, Debug, PartialEq)]
pub enum Actual {
    Bool(bool),
    Unsigned(u128),
    Signed(i128),
    Float(f64),
    Char(char),
    Str(String),
    Bytes(Vec<u8>),
    Unit,
    Option,
    NewtypeStruct,
    Seq,
    Map,
    Enum,
    UnitVariant,
    NewtypeVariant,
    TupleVariant,
    StructVariant,
    Other(String),
}

impl fmt::Display for Actual {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Actual::Bool(v) => write!(f, "bool {}", v),
            Actual::Unsigned(v) => write!(f, "unsigned int `{}`", v),
            Actual::Signed(v) => write!(f, "signed int `{}`", v),
            Actual::Float(v) => write!(f, "float `{}`", v),
            Actual::Char(v) => write!(f, "char {:?}", v),
            Actual::Str(v) => write!(f, "string {:?}", v),
            Actual::Bytes(v) => write!(f, "bytes {:?}", v),
            Actual::Unit => write!(f, "unit"),
            Actual::Option => write!(f, "option"),
            Actual::NewtypeStruct => write!(f, "new-type struct"),
            Actual::Seq => write!(f, "sequence"),
            Actual::Map => write!(f, "map"),
            Actual::Enum => write!(f, "enum"),
            Actual::UnitVariant => write!(f, "unit variant"),
            Actual::NewtypeVariant => write!(f, "new-type variant"),
            Actual::TupleVariant => write!(f, "tuple variant"),
            Actual::StructVariant => write!(f, "struct variant"),
            Actual::Other(v) => v.fmt(f),
        }
    }
}

impl From<de::Unexpected<'_>> for Actual {
    fn from(value: de::Unexpected<'_>) -> Actual {
        match value {
            de::Unexpected::Bool(v) => Actual::Bool(v),
            de::Unexpected::Unsigned(v) => Actual::Unsigned(v as u128),
            de::Unexpected::Signed(v) => Actual::Signed(v as i128),
            de::Unexpected::Float(v) => Actual::Float(v),
            de::Unexpected::Char(v) => Actual::Char(v),
            de::Unexpected::Str(v) => Actual::Str(v.into()),
            de::Unexpected::Bytes(v) => Actual::Bytes(v.into()),
            de::Unexpected::Unit => Actual::Unit,
            de::Unexpected::Option => Actual::Option,
            de::Unexpected::NewtypeStruct => Actual::NewtypeStruct,
            de::Unexpected::Seq => Actual::Seq,
            de::Unexpected::Map => Actual::Map,
            de::Unexpected::Enum => Actual::Enum,
            de::Unexpected::UnitVariant => Actual::UnitVariant,
            de::Unexpected::NewtypeVariant => Actual::NewtypeVariant,
            de::Unexpected::TupleVariant => Actual::TupleVariant,
            de::Unexpected::StructVariant => Actual::StructVariant,
            de::Unexpected::Other(v) => Actual::Other(v.into())
        }
    }
}

impl de::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Kind::Message(msg.to_string()).into()
    }

    fn invalid_type(unexp: de::Unexpected, exp: &dyn de::Expected) -> Self {
        Kind::InvalidType(unexp.into(), exp.to_string()).into()
    }

    fn invalid_value(unexp: de::Unexpected, exp: &dyn de::Expected) -> Self {
        Kind::InvalidValue(unexp.into(), exp.to_string()).into()
    }

    fn invalid_length(len: usize, exp: &dyn de::Expected) -> Self {
        Kind::InvalidLength(len, exp.to_string()).into()
    }

    fn unknown_variant(variant: &str, expected: &'static [&'static str]) -> Self {
        Kind::UnknownVariant(variant.into(), expected).into()
    }

    fn unknown_field(field: &str, expected: &'static [&'static str]) -> Self {
        Kind::UnknownField(field.into(), expected).into()
    }

    fn missing_field(field: &'static str) -> Self {
        Kind::MissingField(field.into()).into()
    }

    fn duplicate_field(field: &'static str) -> Self {
        Kind::DuplicateField(field).into()
    }
}

impl ser::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Kind::Message(msg.to_string()).into()
    }
}

impl From<Kind> for Error {
    fn from(kind: Kind) -> Error {
        Error {
            inner: Box::new(ErrorInner {
                path: vec![],
                context: None,
                prev: None,
                kind,
            }),
        }
    }
}

impl From<&str> for Error {
    fn from(string: &str) -> Error {
        Kind::Message(string.into()).into()
    }
}

impl From<String> for Error {
    fn from(string: String) -> Error {
        Kind::Message(string).into()
    }
}

impl Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Kind::Message(msg) => f.write_str(msg),
            Kind::FileNotFound(path) => {
                write!(f, "required file `{}` not found", path.display())
            }
            Kind::InvalidType(v, exp) => {
                write!(f, "invalid type: found {}, expected {}", v, exp)
            }
            Kind::InvalidValue(v, exp) => {
                write!(f, "invalid value {}, expected {}", v, exp)
            },
            Kind::InvalidLength(v, exp) => {
                write!(f, "invalid length {}, expected {}", v, exp)
            },
            Kind::UnknownVariant(v, exp) => {
                write!(f, "unknown variant: found `{}`, expected `{}`", v, OneOf(exp))
            }
            Kind::UnknownField(v, exp) => {
                write!(f, "unknown field: found `{}`, expected `{}`", v, OneOf(exp))
            }
            Kind::MissingField(v) => {
                write!(f, "missing field `{}`", v)
            }
            Kind::DuplicateField(v) => {
                write!(f, "duplicate field `{}`", v)
            }
            Kind::ISizeOutOfRange(v) => {
                write!(f, "signed integer `{}` is out of range", v)
            }
            Kind::USizeOutOfRange(v) => {
                write!(f, "unsigned integer `{}` is out of range", v)
            }
            Kind::Unsupported(v) => {
                write!(f, "unsupported type `{}`", v)
            }
            Kind::UnsupportedKey(a, e) => {
                write!(f, "unsupported type `{}` for key: must be `{}`", a, e)
            }
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.kind.fmt(f)?;

        for (i, key) in self.path.iter().enumerate() {
            f.write_str(if i == 0 { " for key " } else { " > " })?;
            write!(f, "{:?}", key)?;
        }

        let interpolate = !self.path.is_empty() && !self.missing()
            && matches!(self.context, Some(Context::Origin(_)));

        for origin in self.origins() {
            f.write_str("\n  from ")?;
            let md = &origin.metadata;
            if let Some(source) = &md.source {
                write!(f, "{} ", source)?;
            }

            md.name.fmt(f)?;
            if let Some(profile) = &origin.profile {
                write!(f, " (profile {:?}", profile.as_str().as_str())?;
                if interpolate {
                    write!(f, ", key {:?}", md.interpolate(profile, &self.path))?;
                }

                f.write_str(")")?;
            }
        }

        if let Some(prev) = &self.prev {
            write!(f, "\n{}", prev)?;
        }

        Ok(())
    }
}

impl std::error::Error for Error {}

/// A structure that implements [`de::Expected`] signaling that one of the types
/// in the slice was expected.
pub struct OneOf(pub &'static [&'static str]);

impl fmt::Display for OneOf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0.len() {
            0 => write!(f, "none"),
            1 => write!(f, "`{}`", self.0[0]),
            2 => write!(f, "`{}` or `{}`", self.0[0], self.0[1]),
            _ => {
                write!(f, "one of ")?;
                for (i, alt) in self.0.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "`{}`", alt)?;
                }

                Ok(())
            }
        }
    }
}

impl de::Expected for OneOf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_is_small() {
        assert!(std::mem::size_of::<Error>() <= 128);
    }

    #[test]
    fn error_fields_remain_accessible() {
        let mut error = Error::from("an error message").with_path("some.path");
        assert_eq!(error.path, ["some", "path"]);
        assert!(matches!(error.kind, Kind::Message(_)));
        assert!(error.origins().is_empty());

        error.path.push("more".into());
        assert_eq!(error.path, ["some", "path", "more"]);
        error.kind = Kind::MissingField("port".into());
        assert!(error.missing());
    }

    #[test]
    fn first_boundary_wins_even_without_metadata() {
        let figment = Figment::from(("known", 123));
        let parent = figment.find_value("").unwrap();
        for value in [123.into(), crate::value::Dict::new().into(), Value::Bool(Tag::next(), false)] {
            let error = Error::from("error").at(&value).at(&parent).resolved(&figment);
            assert!(error.origins().is_empty());
            let error = error.at(&parent).provided_by(figment.metadata.values().next().unwrap());
            assert!(error.resolved(&figment).origins().is_empty());
        }

        let known = parent.find_ref("known").unwrap();
        let error = Error::from("error").at(known);
        assert!(matches!(error.context, Some(Context::Tag(tag)) if tag == known.tag()));
    }

    #[test]
    fn chains_keep_independent_contexts_and_paths() {
        let figment = Figment::from(("a", 123)).merge(("b", 456));
        let parent = figment.find_value("").unwrap();
        let leaf = Error::from("leaf").at(parent.find_ref("a").unwrap());
        let error = leaf.chain("first".into()).chain("second".into())
            .at(&parent).prefixed(["child.key"]).prefixed("root.").resolved(&figment);

        for (error, origins) in error.into_iter().zip([2, 2, 1]) {
            assert_eq!(error.path, ["root", "", "child.key"]);
            assert_eq!(error.origins().len(), origins);
            let pointer = error.origins().as_ptr();
            assert_eq!(error.resolved(&figment).origins().as_ptr(), pointer);
        }
    }
}
