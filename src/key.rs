//! [`KeyPath`]: types representing configuration key paths.

/// A path to a configuration value.
///
/// A `KeyPath` is an ordered sequence of string components. Figment APIs that
/// locate configuration values, such as [`Value::find()`],
/// [`Figment::extract_inner()`], [`Serialized::key()`], and [`nest()`], accept
/// any type that implements `KeyPath`.
///
/// # Implementations
///
/// `KeyPath` is implemented for the following types:
///
///   * **Strings: `str`, `String`, and `Cow<'_, str>`**
///
///     In a string, the `.` character separates components. Thus:
///
///     * `"a.b"` maps to the components `"a"` and `"b"`.
///     * `"a.b.c"` maps to `"a"`, `"b"`, and `"c"`.
///     * `"a..b"` maps to `"a"`, `""`, and `"b"`.
///     * `".a."` maps to `""`, `"a"`, and `""`.
///     * `""` consists of zero components.
///     * `"a.b\.c"` maps to `"a"`, `"b\"`, and `"c"`; `\` does not escape `.`.
///
///   * **`[S]`, `[S; N]`, and `Vec<S>` where `S: AsRef<str>`**
///
///     Each item of the array is one component.
///
///     * `["a.b", "c"]` consists of the components `"a.b"` and `"c"`.
///     * `[""]` consists of one empty component.
///     * `[]` consists of zero components.
///
///   * **Any cloneable iterator whose items implement `AsRef<str>`**
///
///     Such an iterator can be converted into a `KeyPath` with
///     [`KeyPathExt::into_key_path()`]. Each item produced by the iterator is
///     one component.
///
///     * `"a/b".split('/').into_key_path()` consists of `"a"` and `"b"`.
///     * `"a/b".split('/')` is not itself a `KeyPath`; call
///       [`KeyPathExt::into_key_path()`] to convert it into one.
///
/// `KeyPath` is also implemented for references to any `KeyPath`.
///
/// # Example
///
/// ```rust
/// use figment::{key::KeyPathExt, util::map, value::Value};
///
/// let config = Value::from(map![
///     "hosts" => map!["example.com" => "127.0.0.1"],
/// ]);
///
/// // This is a path with three components: hosts > example > com.
/// assert!(config.find_ref("hosts.example.com").is_none());
///
/// // This is a path with two: hosts > example.com.
/// assert_eq!(
///     config.find_ref(["hosts", "example.com"]).unwrap().as_str(),
///     Some("127.0.0.1")
/// );
///
/// // Same as the above.
/// let path = "hosts/example.com".split('/').into_key_path();
/// assert_eq!(config.find_ref(path).unwrap().as_str(), Some("127.0.0.1"));
/// ```
///
/// # Implementing
///
/// Most code should use one of the existing implementations. A custom
/// implementation must return the path's components in order on every call to
/// [`KeyPath::segments()`]. Components should borrow from `self` when possible.
///
/// [`Value::find()`]: crate::value::Value::find()
/// [`Figment::extract_inner()`]: crate::Figment::extract_inner()
/// [`Serialized::key()`]: crate::providers::Serialized::key()
/// [`nest()`]: crate::util::nest()
pub trait KeyPath {
    /// The type of component yielded while `self` is borrowed for `'a`.
    type Segment<'a>: AsRef<str> where Self: 'a;

    /// The iterator over this path's components while borrowed for `'a`.
    type Segments<'a>: Iterator<Item = Self::Segment<'a>> where Self: 'a;

    /// Returns this path's components in order.
    fn segments(&self) -> Self::Segments<'_>;
}

/// A [`KeyPath`] backed by a cloneable iterator.
///
/// Values of this type are created with [`KeyPathExt::into_key_path()`].
#[derive(Debug, Clone, Copy)]
pub struct KeyPathSegments<I>(I);

/// Extension trait for converting a cloneable iterator into a [`KeyPath`].
pub trait KeyPathExt: Clone + Iterator + Sized
    where Self::Item: AsRef<str>,
{
    /// Converts this iterator into a key path, treating each item as one exact
    /// component.
    fn into_key_path(self) -> KeyPathSegments<Self> {
        KeyPathSegments(self)
    }
}

impl<I> KeyPathExt for I where I: Clone + Iterator, I::Item: AsRef<str> { }

impl<I> KeyPath for KeyPathSegments<I>
    where I: Clone + Iterator, I::Item: AsRef<str>
{
    type Segment<'a> = I::Item where Self: 'a;
    type Segments<'a> = I where Self: 'a;

    fn segments(&self) -> Self::Segments<'_> {
        self.0.clone()
    }
}

impl KeyPath for str {
    type Segment<'a> = &'a str where Self: 'a;
    type Segments<'a> = std::str::Split<'a, char> where Self: 'a;

    fn segments(&self) -> Self::Segments<'_> {
        let mut segments = self.split('.');
        if self.is_empty() {
            segments.next();
        }

        segments
    }
}

impl KeyPath for String {
    type Segment<'a> = &'a str where Self: 'a;
    type Segments<'a> = std::str::Split<'a, char> where Self: 'a;

    fn segments(&self) -> Self::Segments<'_> {
        str::segments(self)
    }
}

impl KeyPath for std::borrow::Cow<'_, str> {
    type Segment<'a> = &'a str where Self: 'a;
    type Segments<'a> = std::str::Split<'a, char> where Self: 'a;

    fn segments(&self) -> Self::Segments<'_> {
        str::segments(self)
    }
}

impl<S: AsRef<str>> KeyPath for [S] {
    type Segment<'a> = &'a S where Self: 'a;
    type Segments<'a> = std::slice::Iter<'a, S> where Self: 'a;

    fn segments(&self) -> Self::Segments<'_> {
        self.iter()
    }
}

impl<S: AsRef<str>, const N: usize> KeyPath for [S; N] {
    type Segment<'a> = &'a S where Self: 'a;
    type Segments<'a> = std::slice::Iter<'a, S> where Self: 'a;

    fn segments(&self) -> Self::Segments<'_> {
        self.iter()
    }
}

impl<S: AsRef<str>> KeyPath for Vec<S> {
    type Segment<'a> = &'a S where Self: 'a;
    type Segments<'a> = std::slice::Iter<'a, S> where Self: 'a;

    fn segments(&self) -> Self::Segments<'_> {
        self.iter()
    }
}

impl<P: KeyPath + ?Sized> KeyPath for &P {
    type Segment<'a> = P::Segment<'a> where Self: 'a;
    type Segments<'a> = P::Segments<'a> where Self: 'a;

    fn segments(&self) -> Self::Segments<'_> {
        P::segments(self)
    }
}
