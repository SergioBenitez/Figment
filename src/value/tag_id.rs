use std::sync::atomic::{Ordering, AtomicU64};

/// An opaque, unique ID for a provider's [`Metadata`](crate::Metadata).
///
/// An `Id` is retrieved either via [`Tagged`], [`Value::metadata_id()`], or
/// [`Tag::id()`]. The corresponding metadata can be retrieved via
/// [`Figment::get_metadata()`].
///
/// [`Tagged`]: crate::value::magic::Tagged
/// [`Value::metadata_id()`]: crate::value::Value::metadata_id()
/// [`Figment::get_metadata()`]: crate::Figment::get_metadata()
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Id(pub(crate) u64);

static COUNTER: AtomicU64 = AtomicU64::new(0);

impl Id {
    pub(crate) fn next() -> Id {
        Id(COUNTER.fetch_add(1, Ordering::AcqRel))
    }
}

/// An opaque tag which may or may not contain an [`Id`].
#[derive(Copy, Clone, PartialEq)]
pub enum Tag {
    /// A defalt tag, with no [`Id`].
    Default,
    /// A tag _with_ an [`Id`].
    Id(Id),
}

impl Tag {
    /// Returns an [`Id`] if `self` is `Tag::Id`. For a value, this is identical
    /// to [`Value::metadata_id()`](crate::value::Value::metadata_id()).
    pub fn id(self) -> Option<Id> {
        match self {
            Tag::Id(id) => Some(id),
            Tag::Default => None
        }
    }
}

impl std::fmt::Debug for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.id()
            .map(|id| write!(f, "Tag({})", id.0))
            .unwrap_or_else(|| "Tag::Default".fmt(f))
    }
}
