use figment::{Figment, providers::Env};

#[derive(serde::Deserialize)]
struct Config {
    foo: Vec<u32>,
    bar: BarStruct,
    int_value: u32,
}

#[derive(serde::Deserialize, PartialEq, Debug)]
struct BarStruct {
    x: u32,
}

#[test]
fn custom_env_parser() {
    figment::Jail::expect_with(|jail| {
        jail.set_env("FOO", "[1, 2, 3]");
        jail.set_env("BAR", "{\"x\": 123}");
        jail.set_env("INT_VALUE", "0");

        let config = Figment::new()
            .merge(Env::raw().parser(|v| {
                serde_json::from_str(v).unwrap_or_else(|_| figment::value::Value::from(v))
            }))
            .extract::<Config>()?;

        assert_eq!(config.foo, vec![1, 2, 3]);
        assert_eq!(config.bar, BarStruct { x: 123 });
        assert_eq!(config.int_value, 0);

        jail.set_env("FOO", "[\n1 # One\n, 2 # Two\n, 3, # Three\n]");
        jail.set_env("BAR", "x: 321");
        jail.set_env("INT_VALUE", "987");

        let config = Figment::new()
            .merge(Env::raw().parser(|v| {
                serde_yaml::from_str(v).unwrap_or_else(|_| figment::value::Value::from(v))
            }))
            .extract::<Config>()?;

        assert_eq!(config.foo, vec![1, 2, 3]);
        assert_eq!(config.bar, BarStruct { x: 321 });
        assert_eq!(config.int_value, 987);

        Ok(())
    });
}
