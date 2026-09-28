//! A [`Dict`] mapping `String` keys to [`Value`]s.

use std::fmt;
use std::iter::{FromIterator, FusedIterator};
use std::ops::Index;

use serde::{Serialize, Serializer, Deserialize, Deserializer};

use super::{Map, Value};

#[cfg(not(feature = "preserve_order"))]
use std::collections::{BTreeMap as MapImpl, btree_map as backend};
#[cfg(feature = "preserve_order")]
use indexmap::{IndexMap as MapImpl, map as backend};

/// A dictionary mapping `String` keys to [`Value`]s.
///
/// By default, keys in a `Dict` are ordered lexicographically. With the
/// `preserve_order` feature enabled, keys are instead ordered by insertion.
/// In either case, replacing a value does not change the position of its key,
/// and removing a key preserves the relative order of the remaining keys.
///
/// Two dictionaries are equal if they contain the same keys with equal
/// corresponding values, irrespective of key order.
///
/// The `dict!` macro allows for easy `Dict` construction.
///
/// # Example
///
/// ```rust
/// use figment::{value::Dict, util::dict};
///
/// let mut dict = dict! {
///     "port" => 8000,
///     "address" => "127.0.0.1",
///     "workers" => 4,
/// };
///
/// assert_eq!(dict.insert("port", 9000), Some(8000.into()));
/// assert_eq!(dict["port"], 9000.into());
///
/// let keys: Vec<_> = dict.keys().map(String::as_str).collect();
/// if cfg!(feature = "preserve_order") {
///     // Replacing "port" preserves its position.
///     assert_eq!(keys, ["port", "address", "workers"]);
/// } else {
///     // Without `preserve_order`, keys are sorted lexicographically.
///     assert_eq!(keys, ["address", "port", "workers"]);
/// }
/// # let reversed = dict.iter().rev().map(|(k, v)| (k.clone(), v.clone())).collect::<Dict>();
/// # assert_eq!(dict, reversed);
/// # assert_eq!(dict.remove("port"), Some(9000.into()));
/// # assert_eq!(dict.keys().map(String::as_str).collect::<Vec<_>>(), ["address", "workers"]);
/// # dict.insert("port", 9000);
/// # #[cfg(feature = "preserve_order")]
/// # assert_eq!(dict.keys().last().map(String::as_str), Some("port"));
/// ```
#[derive(Clone, Default, PartialEq)]
pub struct Dict(MapImpl<String, Value>);

impl Dict {
    /// Creates an empty dictionary.
    #[inline]
    pub fn new() -> Self { Self(MapImpl::new()) }

    /// Returns the number of entries in the dictionary.
    #[inline]
    pub fn len(&self) -> usize { self.0.len() }

    /// Returns `true` if the dictionary contains no entries.
    #[inline]
    pub fn is_empty(&self) -> bool { self.0.is_empty() }

    /// Removes all entries from the dictionary.
    #[inline]
    pub fn clear(&mut self) { self.0.clear() }

    /// Returns an iterator over the keys and values.
    #[inline]
    pub fn iter(&self) -> Iter<'_> { Iter(self.0.iter()) }

    /// Returns an iterator over the keys and mutable values.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_> { IterMut(self.0.iter_mut()) }

    /// Returns an iterator over the keys.
    #[inline]
    pub fn keys(&self)
        -> impl DoubleEndedIterator<Item = &String> + ExactSizeIterator + FusedIterator + Clone
    {
        self.iter().map(|(key, _)| key)
    }

    /// Returns an iterator over the values.
    #[inline]
    pub fn values(&self)
        -> impl DoubleEndedIterator<Item = &Value> + ExactSizeIterator + FusedIterator + Clone
    {
        self.iter().map(|(_, value)| value)
    }

    /// Returns an iterator over the mutable values.
    #[inline]
    pub fn values_mut(&mut self)
        -> impl DoubleEndedIterator<Item = &mut Value> + ExactSizeIterator + FusedIterator
    {
        self.iter_mut().map(|(_, value)| value)
    }

    /// Returns `true` if the dictionary contains `key`.
    #[inline]
    pub fn contains_key(&self, key: &str) -> bool {
        self.0.contains_key(key)
    }

    /// Returns the value at `key`, if any.
    #[inline]
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.0.get(key)
    }

    /// Returns the mutable value at `key`, if any.
    #[inline]
    pub fn get_mut(&mut self, key: &str) -> Option<&mut Value> {
        self.0.get_mut(key)
    }

    /// Inserts `value` at `key`, returning the previous value, if any.
    /// Replacing a value does not change its key's position.
    #[inline]
    pub fn insert(&mut self, key: impl Into<String>, value: impl Into<Value>) -> Option<Value> {
        self.0.insert(key.into(), value.into())
    }

    /// Removes `key`, returning its value, if any. The relative order of
    /// remaining entries is unchanged.
    #[inline]
    pub fn remove(&mut self, key: &str) -> Option<Value> {
        #[cfg(not(feature = "preserve_order"))]
        { self.0.remove(key) }
        #[cfg(feature = "preserve_order")]
        { self.0.shift_remove(key) }
    }

    /// Returns a view into the entry at `key`, whether or not it exists.
    ///
    /// # Example
    ///
    /// ```rust
    /// use figment::util::dict;
    ///
    /// let mut dict = dict!["port" => 8000];
    /// dict.entry("port")
    ///     .and_modify(|value| *value = 9000.into())
    ///     .or_insert(7000);
    /// dict.entry("address").or_insert_with(|| "127.0.0.1");
    ///
    /// assert_eq!(dict["port"], 9000.into());
    /// assert_eq!(dict["address"], "127.0.0.1".into());
    /// # assert_eq!(dict.entry("port").key(), "port");
    /// # dict.entry("port").or_insert_with(|| -> i32 { panic!("entry exists") });
    /// # dict.entry("workers").and_modify(|_| panic!("entry is absent")).or_insert(4);
    /// # assert_eq!(dict["workers"], 4.into());
    /// # let keys: Vec<_> = dict.keys().map(String::as_str).collect();
    /// # if cfg!(feature = "preserve_order") {
    /// #     assert_eq!(keys, ["port", "address", "workers"]);
    /// # } else {
    /// #     assert_eq!(keys, ["address", "port", "workers"]);
    /// # }
    /// ```
    #[inline]
    pub fn entry(&mut self, key: impl Into<String>) -> Entry<'_> {
        Entry(self.0.entry(key.into()))
    }

    /// Retains only entries for which `f` returns `true`, allowing each value
    /// to be modified. The relative order of retained entries is unchanged.
    ///
    /// # Example
    ///
    /// ```rust
    /// use figment::util::dict;
    ///
    /// let mut dict = dict! {
    ///     "port" => 8000,
    ///     "_note" => "local settings",
    ///     "workers" => 4,
    ///     "address" => "127.0.0.1",
    /// };
    /// # let keys: Vec<_> = dict.keys().filter(|k| !k.starts_with('_')).cloned().collect();
    ///
    /// dict.retain(|key, value| {
    ///     if key == "port" {
    ///         *value = 9000.into();
    ///     }
    ///
    ///     !key.starts_with('_')
    /// });
    ///
    /// assert_eq!(dict["port"], 9000.into());
    /// assert!(!dict.contains_key("_note"));
    /// # assert_eq!(dict.keys().collect::<Vec<_>>(), keys.iter().collect::<Vec<_>>());
    /// ```
    #[inline]
    pub fn retain(&mut self, mut f: impl FnMut(&str, &mut Value) -> bool) {
        self.0.retain(|key, value| f(key, value));
    }
}

impl fmt::Debug for Dict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

impl Index<&str> for Dict {
    type Output = Value;

    #[inline]
    fn index(&self, key: &str) -> &Value {
        self.get(key).expect("no entry found for key")
    }
}

impl FromIterator<(String, Value)> for Dict {
    fn from_iter<I: IntoIterator<Item = (String, Value)>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl Extend<(String, Value)> for Dict {
    fn extend<I: IntoIterator<Item = (String, Value)>>(&mut self, iter: I) {
        self.0.extend(iter);
    }
}

impl<const N: usize> From<[(String, Value); N]> for Dict {
    fn from(entries: [(String, Value); N]) -> Self {
        IntoIterator::into_iter(entries).collect()
    }
}

impl From<Map<String, Value>> for Dict {
    fn from(map: Map<String, Value>) -> Self {
        #[cfg(not(feature = "preserve_order"))]
        { Self(map) }
        #[cfg(feature = "preserve_order")]
        { map.into_iter().collect() }
    }
}

impl Serialize for Dict {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Dict {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        MapImpl::deserialize(deserializer).map(Self)
    }
}

/// A view into a dictionary entry, returned by [`Dict::entry()`].
pub struct Entry<'a>(backend::Entry<'a, String, Value>);

impl<'a> Entry<'a> {
    /// Returns this entry's key.
    #[inline]
    pub fn key(&self) -> &str {
        self.0.key()
    }

    /// Returns a mutable reference to the value, inserting `value` if absent.
    #[inline]
    pub fn or_insert(self, value: impl Into<Value>) -> &'a mut Value {
        self.0.or_insert_with(|| value.into())
    }

    /// Returns a mutable reference to the value, calling `f` to insert it if
    /// absent.
    #[inline]
    pub fn or_insert_with<V: Into<Value>>(self, f: impl FnOnce() -> V) -> &'a mut Value {
        self.0.or_insert_with(|| f().into())
    }

    /// Calls `f` on an existing value, if any, then returns `self`.
    #[inline]
    pub fn and_modify(self, f: impl FnOnce(&mut Value)) -> Self {
        Self(self.0.and_modify(f))
    }
}

/// An iterator over a dictionary's keys and values.
#[derive(Clone)]
pub struct Iter<'a>(backend::Iter<'a, String, Value>);

/// An iterator over a dictionary's keys and mutable values.
pub struct IterMut<'a>(backend::IterMut<'a, String, Value>);

/// An iterator over an owned dictionary's keys and values.
pub struct IntoIter(backend::IntoIter<String, Value>);

macro_rules! impl_iterator {
    ($name:ident $(<$lt:lifetime>)?, $item:ty) => {
        impl$(<$lt>)? Iterator for $name$(<$lt>)? {
            type Item = $item;

            #[inline] fn next(&mut self) -> Option<Self::Item> { self.0.next() }
            #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
            #[inline] fn nth(&mut self, n: usize) -> Option<Self::Item> { self.0.nth(n) }
            #[inline] fn last(self) -> Option<Self::Item> { self.0.last() }
            #[inline] fn count(self) -> usize { self.0.count() }
        }

        impl$(<$lt>)? DoubleEndedIterator for $name$(<$lt>)? {
            #[inline] fn next_back(&mut self) -> Option<Self::Item> { self.0.next_back() }
            #[inline] fn nth_back(&mut self, n: usize) -> Option<Self::Item> { self.0.nth_back(n) }
        }

        impl$(<$lt>)? ExactSizeIterator for $name$(<$lt>)? { }
        impl$(<$lt>)? FusedIterator for $name$(<$lt>)? { }
    };
}

impl_iterator!(Iter<'a>, (&'a String, &'a Value));
impl_iterator!(IterMut<'a>, (&'a String, &'a mut Value));
impl_iterator!(IntoIter, (String, Value));

impl IntoIterator for Dict {
    type Item = (String, Value);
    type IntoIter = IntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter { IntoIter(self.0.into_iter()) }
}

impl<'a> IntoIterator for &'a Dict {
    type Item = (&'a String, &'a Value);
    type IntoIter = Iter<'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

impl<'a> IntoIterator for &'a mut Dict {
    type Item = (&'a String, &'a mut Value);
    type IntoIter = IterMut<'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter { self.iter_mut() }
}
