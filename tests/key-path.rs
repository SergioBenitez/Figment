use std::borrow::Cow;

use figment::providers::Serialized;
use figment::key::{KeyPath, KeyPathExt};
use figment::util::{dict, nest};
use figment::value::Value;
use figment::{Figment, error::Kind};

#[test]
fn exact_key_path_components() {
    let figment = Figment::from(Serialized::default(["root.key", "", "child.key"], "42"));
    assert!(!figment.contains("root.key..child.key"));

    let key_string = String::from("root.key;; child.key");
    let key = key_string.split(';').map(str::trim).into_key_path();
    let value = figment.find_value(&key).unwrap();
    assert_eq!(value.as_str(), Some("42"));

    let error = figment.extract_inner::<bool>(key).unwrap_err();
    assert_eq!(error.path, ["root.key", "", "child.key"]);

    let error = figment.find_value(["root.key", "", "missing.key"]).unwrap_err();
    assert!(matches!(error.kind, Kind::MissingField(ref key) if key == "missing.key"));
    assert_eq!(error.path, ["root.key", "", "missing.key"]);
}

#[test]
fn empty_dotted_components() {
    let leaf = Value::from(42);
    for (path, dict) in [
        (".", dict!["" => dict!["" => 42]]),
        (".a", dict!["" => dict!["a" => 42]]),
        ("a.", dict!["a" => dict!["" => 42]]),
        ("a..b", dict!["a" => dict!["" => dict!["b" => 42]]]),
    ] {
        let value = Value::from(dict);
        assert_eq!(nest(Cow::Borrowed(path), leaf.clone()), value);
        assert_eq!(value.find_ref(path), Some(&leaf));
        assert_eq!(value.find(path.to_owned()), Some(leaf.clone()));
    }
}

#[test]
fn empty_paths_and_keys() {
    assert!("".segments().next().is_none());
    assert!(String::new().segments().next().is_none());
    assert!(Cow::Borrowed("").segments().next().is_none());

    let leaf = Value::from(42);
    let value = Value::from(dict!["" => 42]);
    assert_eq!(nest([""], leaf.clone()), value);
    assert_eq!(value.find_ref([""]), Some(&leaf));
    assert_eq!(nest("", value.clone()), value);
    assert_eq!(value.find_ref(""), Some(&value));
    assert_eq!(value.clone().find(""), Some(value));

    let array = Value::from(vec![42]);
    assert!(array.find_ref([""]).is_none());
    assert!(array.find([""]).is_none());
}

#[test]
fn missing_empty_key() {
    let figment = Figment::from(("a", 42));
    let error = figment.extract_inner::<i32>("a.").unwrap_err();
    assert_eq!(error.path, ["a", ""]);
    assert_eq!(error.kind, Kind::MissingField("".into()));
    assert_eq!(figment.extract_inner::<Option<i32>>("a.").unwrap(), None);
}
