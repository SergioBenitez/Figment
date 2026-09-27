#![cfg(all(feature = "test", feature = "json"))]

use figment::{Figment, Jail, providers::Env};

#[derive(Debug, PartialEq, serde::Deserialize)]
struct Config {
    foo: Vec<u32>,
    bar: Bar,
    int_value: u32,
    environment: String,
}

#[derive(Debug, PartialEq, serde::Deserialize)]
struct Bar {
    x: u32,
}

#[test]
fn infallible_parser() {
    Jail::expect_with(|jail| {
        jail.set_env("APP_VALUES", "one,two,three");
        jail.set_env("APP_SINGLE", "one");

        let figment = Figment::from(Env::prefixed("APP_").parser(|value| {
            value.split(',').collect::<Vec<_>>().into()
        }));

        let values = figment.extract_inner::<Vec<String>>("values")?;
        let single = figment.extract_inner::<Vec<String>>("single")?;
        assert_eq!(values, ["one", "two", "three"]);
        assert_eq!(single, ["one"]);
        Ok(())
    });
}

#[test]
fn fallible_parser() {
    Jail::expect_with(|jail| {
        jail.set_env("APP_FOO", "[1, 2, 3]");
        jail.set_env("APP_BAR", "{\"x\": 123}");
        jail.set_env("APP_INT_VALUE", "0");
        jail.set_env("APP_ENVIRONMENT", "development");

        let env = Env::prefixed("APP_")
            .try_parser(|value| serde_json::from_str(value));
        let config = Figment::from(env).extract::<Config>()?;

        assert_eq!(config, Config {
            foo: vec![1, 2, 3],
            bar: Bar { x: 123 },
            int_value: 0,
            environment: "development".into(),
        });

        Ok(())
    });
}
