#![cfg(all(feature = "test", feature = "json", feature = "yaml"))]

use figment::{Figment, Jail, providers::Env};

#[derive(serde::Deserialize)]
struct Config {
    foo: Vec<u32>,
    bar: Bar,
    int_value: u32,
}

#[derive(Debug, PartialEq, serde::Deserialize)]
struct Bar {
    x: u32,
}

#[test]
fn custom_env_parser() {
    Jail::expect_with(|jail| {
        jail.set_env("FOO", "[1, 2, 3]");
        jail.set_env("BAR", "{\"x\": 123}");
        jail.set_env("INT_VALUE", "0");

        let config = Figment::from(Env::raw().parser(|value| {
            serde_json::from_str(value)
                .unwrap_or_else(|_| figment::value::Value::from(value))
        })).extract::<Config>()?;

        assert_eq!(config.foo, vec![1, 2, 3]);
        assert_eq!(config.bar, Bar { x: 123 });
        assert_eq!(config.int_value, 0);

        jail.set_env("FOO", "[\n1 # One\n, 2 # Two\n, 3, # Three\n]");
        jail.set_env("BAR", "x: 321");
        jail.set_env("INT_VALUE", "987");

        let config = Figment::from(Env::raw().parser(|value| {
            serde_yaml::from_str(value)
                .unwrap_or_else(|_| figment::value::Value::from(value))
        })).extract::<Config>()?;

        assert_eq!(config.foo, vec![1, 2, 3]);
        assert_eq!(config.bar, Bar { x: 321 });
        assert_eq!(config.int_value, 987);

        Ok(())
    });
}
