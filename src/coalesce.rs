use crate::Profile;
use crate::value::{Value, Map};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Order {
    Merge,
    Join
}

pub trait Coalescible: Sized {
    fn coalesce(self, other: Self, order: Order) -> Self;
    fn merge(self, other: Self) -> Self { self.coalesce(other, Order::Merge) }
}

impl Coalescible for Profile {
    fn coalesce(self, other: Self, order: Order) -> Self {
        if order == Order::Join { self } else { other }
    }
}

impl Coalescible for Value {
    fn coalesce(self, other: Self, order: Order) -> Self {
        use {Value::Dict as D, Order::Join as L, Order::Merge as R};
        match (self, other, order) {
            (D(t, a), D(_, b), L) | (D(_, a), D(t, b), R) => D(t, a.coalesce(b, order)),
            (v, _, L) | (_, v, R) => v,
        }
    }
}

impl<K: Eq + std::hash::Hash + Ord, V: Coalescible> Coalescible for Map<K, V> {
    fn coalesce(self, mut other: Self, order: Order) -> Self {
        let mut joined = Map::new();
        for (a_key, a_val) in self {
            match other.remove(&a_key) {
                Some(b_val) => joined.insert(a_key, a_val.coalesce(b_val, order)),
                None => joined.insert(a_key, a_val),
            };
        }

        // `b` contains `b - a`, i.e, additions. keep them all.
        joined.extend(other);
        joined
    }
}
