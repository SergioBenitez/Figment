#![cfg(feature = "test")]

use figment::{Figment, providers::Env};

#[derive(serde::Deserialize)]
struct Config {
    foo: String
}

#[test]
fn empty_env_vars() {
    figment::Jail::expect_with(|jail| {
        jail.set_env("FOO", "bar");
        jail.set_env("BAZ", "put");

        let config = Figment::new()
            .merge(Env::raw().map(|_| "".into()))
            .extract::<Config>();

        assert!(config.is_err());

        let config = Figment::new()
            .merge(Env::raw().map(|_| "   ".into()))
            .extract::<Config>();

        assert!(config.is_err());

        let config = Figment::new()
            .merge(Env::raw().map(|k| {
                if k == "foo" { k.into() }
                else { "".into() }
            }))
            .extract::<Config>()?;

        assert_eq!(config.foo, "bar");

        let config = Figment::new()
            .merge(Env::raw().map(|k| {
                if k == "foo" { "   foo   ".into() }
                else { "".into() }
            }))
            .extract::<Config>()?;

        assert_eq!(config.foo, "bar");

        jail.set_env("___foo", "is here");
        let config = Figment::new()
            .merge(Env::raw().split("_"))
            .extract::<Config>()?;

        assert_eq!(config.foo, "bar");

        jail.set_env("foo__", "is here");
        let config = Figment::new()
            .merge(Env::raw().split("_"))
            .extract::<Config>()?;

        assert_eq!(config.foo, "bar");

        Ok(())
    });
}

#[test]
fn ignore_empty_values() {
    figment::Jail::expect_with(|jail| {
        jail.set_env("EMPTY", "");
        jail.set_env("WHITESPACE", " ");
        jail.set_env("VALUE", "value");

        let config = Figment::from(Env::raw().ignore_empty(true));
        assert!(config.find_value("empty").is_err());
        assert!(config.find_value("whitespace").is_ok());
        assert_eq!(config.find_value("value")?.as_str(), Some("value"));

        Ok(())
    });
}
