use figment::providers::Serialized;
use figment::key::KeyPathExt;
use figment::{Figment, error::Kind};

#[test]
fn exact_key_path_components() {
    let figment = Figment::from(Serialized::default(["root.key", "child.key"], "42"));
    assert!(!figment.contains("root.key.child.key"));

    let key_string = String::from("root.key; child.key");
    let key = key_string.split(';').map(str::trim).into_key_path();
    let value = figment.find_value(key).unwrap();
    assert_eq!(value.as_str(), Some("42"));

    let error = figment.find_value(["root.key", "missing.key"]).unwrap_err();
    assert!(matches!(error.kind, Kind::MissingField(ref key) if key == "missing.key"));
    assert_eq!(error.path, ["root.key", "missing.key"]);
}
