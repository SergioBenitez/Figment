use crate::value::{Map, Value};
use crate::Profile;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Order {
    Merge,
    Join,
    Adjoin,
    Admerge,
    Zipjoin,
    Zipmerge,
}

pub trait Coalescible: Sized {
    fn coalesce(self, other: Self, order: Order) -> Self;
    fn merge(self, other: Self) -> Self { self.coalesce(other, Order::Merge) }
}

impl Coalescible for Profile {
    fn coalesce(self, other: Self, order: Order) -> Self {
        match order {
            Order::Join | Order::Adjoin | Order::Zipjoin => self,
            Order::Merge | Order::Admerge | Order::Zipmerge => other,
        }
    }
}

impl Coalescible for Value {
    fn coalesce(self, other: Self, o: Order) -> Self {
        use {Order::*, Value::Array as A, Value::Dict as D};
        match (self, other, o) {
            (D(t, a), D(_, b), Join | Adjoin | Zipjoin) => D(t, a.coalesce(b, o)),
            (D(_, a), D(t, b), Merge | Admerge | Zipmerge) => D(t, a.coalesce(b, o)),
            (A(t, a), A(_, b), _) => A(t, a.coalesce(b, o)),
            (v, _, Join | Adjoin | Zipjoin) | (_, v, Merge | Admerge | Zipmerge) => v,
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

impl Coalescible for Vec<Value> {
    fn coalesce(mut self, other: Self, order: Order) -> Self {
        match order {
            Order::Join => self,
            Order::Merge => other,
            Order::Adjoin | Order::Admerge => { self.extend(other); self }
            Order::Zipjoin | Order::Zipmerge => zip_vec(self, other, order),
        }
    }
}

fn zip_vec(this: Vec<Value>, other: Vec<Value>, order: Order) -> Vec<Value> {
    let mut zipped = Vec::new();
    let mut other = other.into_iter();

    // Coalesces self[0] with other[0], self[1] with other[1] and so on.
    for a_val in this.into_iter() {
        match other.next() {
            // Special cases: either a or b has an empty value, in which
            // case we always choose the non-empty one regardless of order.
            // If both are empty we just push either of the empties.
            Some(b_val) if a_val.is_none() => zipped.push(b_val),
            Some(b_val) if b_val.is_none() => zipped.push(a_val),

            Some(b_val) => zipped.push(a_val.coalesce(b_val, order)),
            None => zipped.push(a_val),
        };
    }

    // `b` contains more items than `a`; append them all.
    zipped.extend(other);
    zipped
}

#[cfg(test)]
mod tests {
    use crate::coalesce::{Coalescible, Order};
    use crate::value::Empty;
    use crate::{map, value::Value};

    #[test]
    pub fn coalesce_values() {
        fn a() -> Value { Value::from("a") }
        fn b() -> Value { Value::from("b") }

        assert_eq!(a().coalesce(b(), Order::Merge), b());
        assert_eq!(a().coalesce(b(), Order::Admerge), b());
        assert_eq!(a().coalesce(b(), Order::Zipmerge), b());
        assert_eq!(a().coalesce(b(), Order::Join), a());
        assert_eq!(a().coalesce(b(), Order::Adjoin), a());
        assert_eq!(a().coalesce(b(), Order::Zipjoin), a());
    }

    #[test]
    pub fn coalesce_dicts() {
        fn a() -> Value {
            Value::from(map!(
                "a" => map!("one" => 1, "two" => 2),
                "b" => map!("ten" => 10, "twenty" => 20),
            ))
        }

        fn b() -> Value {
            Value::from(map!(
                "a" => map!("one" => 2, "three" => 3),
                "b" => map!("ten" => 20, "thirty" => 30),
            ))
        }

        fn joined() -> Value {
            Value::from(map!(
                "a" => map!("one" => 1, "two" => 2, "three" => 3),
                "b" => map!("ten" => 10, "twenty" => 20, "thirty" => 30),
            ))
        }

        fn merged() -> Value {
            Value::from(map!(
                "a" => map!("one" => 2, "two" => 2, "three" => 3),
                "b" => map!("ten" => 20, "twenty" => 20, "thirty" => 30),
            ))
        }

        assert_eq!(a().coalesce(b(), Order::Merge), merged());
        assert_eq!(a().coalesce(b(), Order::Admerge), merged());
        assert_eq!(a().coalesce(b(), Order::Zipmerge), merged());
        assert_eq!(a().coalesce(b(), Order::Join), joined());
        assert_eq!(a().coalesce(b(), Order::Adjoin), joined());
        assert_eq!(a().coalesce(b(), Order::Zipjoin), joined());
    }

    #[test]
    pub fn coalesce_arrays() {
        fn a() -> Value { Value::from(vec![1, 2]) }
        fn b() -> Value { Value::from(vec![2, 3, 4]) }

        assert_eq!(
            a().coalesce(b(), Order::Merge),
            Value::from(vec![2, 3, 4])
        );

        assert_eq!(
            a().coalesce(b(), Order::Admerge),
            Value::from(vec![1, 2, 2, 3, 4])
        );

        assert_eq!(
            a().coalesce(b(), Order::Zipmerge),
            Value::from(vec![2, 3, 4])
        );

        assert_eq!(
            a().coalesce(b(), Order::Join),
            Value::from(vec![1, 2])
        );

        assert_eq!(
            a().coalesce(b(), Order::Adjoin),
            Value::from(vec![1, 2, 2, 3, 4])
        );

        assert_eq!(
            a().coalesce(b(), Order::Zipjoin),
            Value::from(vec![1, 2, 4])
        )
    }

    #[test]
    pub fn coalesce_arrays_empty() {
        fn e() -> Value { Value::from(Empty::None) }
        fn v(i: i32) -> Value { Value::from(i) }
        fn a() -> Value { Value::from(vec![v(50), e(), v(4)]) }
        fn b() -> Value { Value::from(vec![e(), v(2), v(6), e(), v(20)]) }

        assert_eq!(
            a().coalesce(b(), Order::Merge),
            Value::from(vec![e(), v(2), v(6), e(), v(20)])
        );

        assert_eq!(
            a().coalesce(b(), Order::Admerge),
            Value::from(vec![v(50), e(), v(4), e(), v(2), v(6), e(), v(20)]),
        );

        assert_eq!(
            a().coalesce(b(), Order::Zipmerge),
            Value::from(vec![v(50), v(2), v(6), e(), v(20)]),
        );

        assert_eq!(
            a().coalesce(b(), Order::Join),
            Value::from(vec![v(50), e(), v(4)]),
        );

        assert_eq!(
            a().coalesce(b(), Order::Adjoin),
            Value::from(vec![v(50), e(), v(4), e(), v(2), v(6), e(), v(20)]),
        );

        assert_eq!(
            a().coalesce(b(), Order::Zipjoin),
            Value::from(vec![v(50), v(2), v(4), e(), v(20)]),
        );
    }
}
