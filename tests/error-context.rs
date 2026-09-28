use std::convert::TryFrom;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use figment::{Error, Figment, Metadata, Profile, Provider, Result};
use figment::key::KeyPath;
use figment::providers::{Named, Serialized};
use figment::util::{dict, map};
use figment::value::{Dict, Map, Value};

/// A provider named `name` that supplies `data`. Its metadata has no source,
/// so error messages are predictable.
struct Mock {
    name: &'static str,
    data: Result<Map<Profile, Dict>>,
}

impl Provider for Mock {
    fn metadata(&self) -> Metadata { Metadata::named(self.name) }
    fn data(&self) -> Result<Map<Profile, Dict>> { self.data.clone() }
}

/// Deserializes from `{ min, max }`, failing as a whole when `min > max`.
#[derive(Debug, Deserialize)]
#[serde(try_from = "RawBounds")]
struct Bounds;

#[derive(Deserialize)]
struct RawBounds { min: u16, max: u16 }

impl TryFrom<RawBounds> for Bounds {
    type Error = &'static str;

    fn try_from(raw: RawBounds) -> Result<Self, Self::Error> {
        (raw.min <= raw.max).then_some(Bounds).ok_or("min must not exceed max")
    }
}

/// Deserializes from a `u16`, failing with a custom error when it is missing.
#[derive(Debug, Deserialize)]
#[serde(try_from = "Option<u16>")]
struct Required;

impl TryFrom<Option<u16>> for Required {
    type Error = &'static str;

    fn try_from(value: Option<u16>) -> Result<Self, Self::Error> {
        value.map(|_| Required).ok_or("a value is required")
    }
}

/// Asserts that `$result` is a single error at `$path` whose origins are the
/// providers named in `$origins`, in any order. Evaluates to the error.
macro_rules! assert_error {
    ($result:expr, at $path:expr, from $origins:expr) => ({
        let error: Error = $result.unwrap_err();
        let path: &[&str] = &$path;
        let mut expected: Vec<&str> = $origins.to_vec();
        let mut origins: Vec<&str> = error.origins().iter()
            .map(|origin| origin.metadata.name.as_ref())
            .collect();

        expected.sort_unstable();
        origins.sort_unstable();
        assert_eq!(error.count(), 1, "{}", stringify!($result));
        assert_eq!(error.path, path, "{}", stringify!($result));
        assert_eq!(origins, expected, "{}", stringify!($result));
        error
    })
}

/// A figment where providers `min` and `max` together supply an invalid
/// `Bounds` at `key`, and `other` supplies an unrelated value.
fn invalid_bounds(key: &str) -> Figment {
    Figment::from(source("min", key, map!["min" => 10]))
        .merge(source("max", key, map!["max" => 5]))
        .merge(source("other", "other", true))
}

/// A provider named `name` that supplies `value` at `key`.
fn source(name: &'static str, key: impl KeyPath, value: impl Serialize) -> Mock {
    Mock { name, data: Serialized::default(key, value).data() }
}

/// A provider named `name` that fails with `error`.
fn failing(name: &'static str, error: Error) -> Mock {
    Mock { name, data: Err(error) }
}

#[test]
fn nested_errors_use_only_their_own_origins() {
    let figment = invalid_bounds("limits");
    let error = assert_error!(figment.extract_inner::<Bounds>("limits"),
        at ["limits"], from ["min", "max"]);

    assert_eq!(figment.extract_inner_lossy::<Bounds>("limits").unwrap_err(), error);
    assert_eq!(figment.extract::<Map<String, Bounds>>().unwrap_err(), error);

    let figment = figment.merge(source("bad", "limits.min", "oops"));
    let error = assert_error!(figment.extract_inner::<Bounds>("limits"),
        at ["limits", "min"], from ["bad"]);

    assert_eq!(figment.extract_inner_lossy::<Bounds>("limits").unwrap_err(), error);
}

#[test]
fn root_errors_use_all_origins() {
    // Serde buffers the input to try each variant.
    #[derive(Debug, Deserialize)]
    #[serde(untagged)]
    #[allow(dead_code)]
    enum Buffered { Bounds(Bounds), Bool(bool) }

    // Discards the error it encounters.
    #[derive(Debug, Deserialize)]
    struct Fallback(#[serde(deserialize_with = "fallback")] u16);

    fn fallback<'de, D: serde::Deserializer<'de>>(de: D) -> Result<u16, D::Error> {
        Ok(u16::deserialize(de).unwrap_or(0))
    }

    let figment = invalid_bounds("");
    assert_error!(figment.extract::<Bounds>(), at [], from ["min", "max", "other"]);
    assert_error!(figment.extract::<Option<Bounds>>(), at [], from ["min", "max", "other"]);
    assert_error!(figment.extract::<Buffered>(), at [], from ["min", "max", "other"]);
    assert_eq!(figment.extract::<Fallback>().unwrap().0, 0);
}

#[test]
fn enums_newtypes_and_map_keys() {
    #[derive(Debug, Deserialize)]
    enum Limit { Bounds(Bounds) }

    #[derive(Debug, Deserialize)]
    #[allow(dead_code)]
    struct Wrapped(Option<Bounds>);

    let figment = invalid_bounds("Bounds");
    assert_error!(figment.extract::<Limit>(), at ["Bounds"], from ["min", "max"]);
    assert_error!(figment.extract_inner::<Wrapped>("Bounds"), at ["Bounds"], from ["min", "max"]);
    assert_error!(figment.extract::<Map<u16, Value>>(), at ["Bounds"], from ["min", "max"]);
}

#[test]
fn only_surviving_values_contribute() {
    let figment = Figment::from(source("old", "limits", map!["min" => 1]))
        .merge(source("new", "limits", map!["min" => 10, "max" => 5]))
        .join(source("ignored", "limits", map!["max" => 20]));

    assert_error!(figment.extract_inner::<Bounds>("limits"), at ["limits"], from ["new"]);

    let first = source("first", "items", [map!["min" => 1, "max" => 5]]);
    let second = source("second", "items", [map!["min" => 10, "max" => 5]]);

    let merged = Figment::from(&first).merge(&second);
    assert_error!(merged.extract_inner::<bool>("items"), at ["items"], from ["second"]);

    let admerged = Figment::from(&first).admerge(&second);
    assert_error!(admerged.extract_inner::<bool>("items"), at ["items"], from ["first", "second"]);
    assert_error!(admerged.extract_inner::<Vec<Bounds>>("items"),
        at ["items", "1"], from ["second"]);
}

#[test]
fn empty_containers_use_their_provider() {
    for empty in [Value::from(Dict::new()), Value::from(Vec::<Value>::new())] {
        let figment = Figment::from(source("first", "empty", &empty));
        let error = assert_error!(figment.extract_inner::<bool>("empty"),
            at ["empty"], from ["first"]);

        assert!(error.to_string().ends_with("\n  from first (profile \"default\")"));

        let merged = figment.clone().merge(source("second", "empty", &empty));
        assert_error!(merged.extract_inner::<bool>("empty"), at ["empty"], from ["second"]);

        let joined = figment.join(source("second", "empty", &empty));
        assert_error!(joined.extract_inner::<bool>("empty"), at ["empty"], from ["first"]);
    }
}

#[test]
fn missing_keys_use_their_first_existing_parent() {
    #[track_caller]
    fn assert_missing(figment: &Figment, key: &str, origins: &[&str]) {
        let path: Vec<_> = key.split('.').collect();
        let error = assert_error!(figment.find_value(key), at path, from origins);
        assert!(error.missing());
        assert_eq!(figment.extract_inner::<bool>(key).unwrap_err(), error);
        assert_eq!(figment.extract_inner::<Option<bool>>(key).unwrap(), None);
        assert_eq!(figment.extract_inner_lossy::<Option<bool>>(key).unwrap(), None);

        let error = assert_error!(figment.extract_inner::<Required>(key), at path, from origins);
        assert_eq!(error.kind.to_string(), "a value is required");
    }

    let figment = invalid_bounds("limits");
    assert_missing(&figment, "missing..child", &["min", "max", "other"]);
    assert_missing(&figment, "limits.missing", &["min", "max"]);
    assert_missing(&figment, "limits.", &["min", "max"]);
    assert_missing(&figment, "limits.min.missing", &["min"]);
    assert_missing(&figment, "limits.min.", &["min"]);

    let figment = Figment::from(source("a", "items", [1])).admerge(source("b", "items", [2]));
    assert_missing(&figment, "items.", &["a", "b"]);
    assert_missing(&figment, "items.2", &["a", "b"]);
    assert_missing(&figment, "items.bad", &["a", "b"]);
    assert_missing(&figment, "items.-1", &["a", "b"]);
    assert_missing(&figment, "items.99999999999999999999999999", &["a", "b"]);
}

#[test]
fn missing_fields_use_the_containing_dictionary() {
    let figment = Figment::from(source("min", "limits.min", 10))
        .merge(source("other", "limits.other", true));

    let error = assert_error!(figment.extract_inner::<Bounds>("limits"),
        at ["limits"], from ["min", "other"]);

    assert!(error.missing());

    let error = assert_error!(Figment::new().extract::<Bounds>(), at [], from []);
    assert_eq!(error.to_string(), "missing field `min`");
}

#[test]
fn provider_errors_use_their_provider() {
    let chain = || Error::from("first").chain("second".into());
    let figment = Figment::from(failing("a", chain()))
        .merge(failing("b", chain()))
        .merge(failing("c", chain()));

    for figment in [figment.clone(), figment.focus("missing"), Figment::from(&figment)] {
        let error = figment.data().unwrap_err();
        assert_eq!(figment.extract::<Value>().unwrap_err(), error);
        assert_eq!(error.count(), 6);
        assert_eq!(error.to_string(), concat!(
            "second\n  from a\nfirst\n  from a\n",
            "second\n  from b\nfirst\n  from b\n",
            "second\n  from c\nfirst\n  from c",
        ));
    }
}

#[test]
fn forwarded_errors_resolve_their_origins() {
    let figment = invalid_bounds("limits");
    let forward = |error| figment.clone().merge(failing("forward", error)).extract::<Value>();

    // Errors for the figment's own values resolve to those values' providers.
    let value = figment.find_value("").unwrap();
    let error = assert_error!(value.deserialize::<Map<String, Bounds>>(),
        at ["limits"], from []);

    let error = assert_error!(forward(error), at ["limits"], from ["min", "max"]);
    assert!(error.origins().iter().all(|o| o.profile == Some(Profile::Default)));

    let value = figment.find_value("limits.min").unwrap();
    let error = assert_error!(bool::deserialize(&value), at [], from []);
    assert_error!(forward(error), at [], from ["min"]);

    let value = figment.find_value("limits").unwrap();
    let error = assert_error!(bool::deserialize(&value), at [], from []);
    assert_error!(forward(error), at [], from ["min", "max"]);

    // Errors for any other value resolve to the forwarding provider.
    for value in [Value::from("oops"), Value::from(dict!["min" => 10, "max" => 5])] {
        let error = assert_error!(value.deserialize::<Bounds>(), at [], from []);
        let error = assert_error!(forward(error), at [], from ["forward"]);
        assert_eq!(error.origins()[0].profile, None);
    }
}

#[test]
fn origins_share_provider_metadata() {
    let data = map![
        Profile::Default => dict!["limits" => dict!["min" => 10]],
        Profile::from("debug") => dict!["limits" => dict!["max" => 5]],
    ];

    let figment = Figment::from(Mock { name: "profiles", data: Ok(data) }).select("debug");
    let error = assert_error!(figment.extract_inner::<Bounds>("limits"),
        at ["limits"], from ["profiles", "profiles"]);

    let origins = error.origins();
    assert!(origins.iter().any(|o| o.profile == Some(Profile::Default)));
    assert!(origins.iter().any(|o| o.profile == Some(Profile::from("debug"))));

    let metadata = &origins[0].metadata;
    assert!(Arc::ptr_eq(metadata, &origins[1].metadata));
    assert!(Arc::ptr_eq(metadata, &error.clone().origins()[0].metadata));
    assert!(std::ptr::eq(metadata.as_ref(), figment.metadata().next().unwrap()));

    let wrapped = Figment::from(Named::new("wrapper", &figment));
    for figment in [figment.clone(), wrapped] {
        let error = figment.focus("limits").extract::<Bounds>().unwrap_err();
        assert!(Arc::ptr_eq(metadata, &error.origins()[0].metadata));
    }

    drop(figment);
    assert_eq!(metadata.name, "profiles");
    assert!(metadata.provide_location.is_some());
}

#[test]
fn error_paths() {
    let figment = Figment::from(source("bad", ["server.name", "", "min"], "oops"));
    let error = assert_error!(figment.extract_inner::<Map<String, Bounds>>(["server.name"]),
        at ["server.name", "", "min"], from ["bad"]);

    assert_eq!(figment.extract_inner::<Bounds>(["server.name", ""]).unwrap_err(), error);
    assert_eq!(Error::from("error").with_path("a..b").path, ["a", "", "b"]);

    let display = |path: &[&str]| Error::from("error").with_path(path).to_string();
    assert_eq!(display(&[]), "error");
    assert_eq!(display(&[""]), r#"error for key """#);
    assert_eq!(display(&["a.b", "", ">"]), r#"error for key "a.b" > "" > ">""#);
    assert_eq!(display(&["a\"\\\n"]), r#"error for key "a\"\\\n""#);
}

#[test]
fn display_lists_every_origin() {
    let figment = invalid_bounds("limits");
    let error = figment.extract_inner::<Bounds>("limits").unwrap_err().to_string();

    // Origins are listed in no particular order.
    let mut lines: Vec<_> = error.lines().collect();
    lines[1..].sort_unstable();
    assert_eq!(lines, [
        "min must not exceed max for key \"limits\"",
        "  from max (profile \"default\")",
        "  from min (profile \"default\")",
    ]);
}

#[test]
#[cfg(feature = "test")]
fn display_interpolates_only_scalar_keys() {
    use figment::providers::Env;

    figment::Jail::expect_with(|jail| {
        jail.set_env("APP_LIMITS_MIN", 10);
        jail.set_env("APP_LIMITS_MAX", 5);

        let figment = Figment::from(Env::prefixed("APP_").split("_").global());
        let error = figment.extract_inner::<Bounds>("limits").unwrap_err();
        assert_eq!(error.to_string(), concat!(
            "min must not exceed max for key \"limits\"\n",
            "  from `APP_` environment variable(s) (profile \"global\")",
        ));

        let error = figment.extract_inner::<String>("limits.min").unwrap_err();
        assert_eq!(error.to_string(), concat!(
            "invalid type: found unsigned int `10`, expected a string for key \"limits\" > \"min\"\n",
            "  from `APP_` environment variable(s) (profile \"global\", key \"LIMITS.MIN\")",
        ));

        let error = figment.extract_inner::<String>("limits.min.missing").unwrap_err();
        assert_eq!(error.to_string(), concat!(
            "missing field `missing` for key \"limits\" > \"min\" > \"missing\"\n",
            "  from `APP_` environment variable(s) (profile \"global\")",
        ));

        Ok(())
    });
}
