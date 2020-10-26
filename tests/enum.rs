use serde::{Deserialize, Serialize};
use figment::{Figment, providers::{Format, Toml, Serialized, Env}};

#[derive(Debug, Deserialize, Serialize)]
pub struct Test {
    service: Option<Foo>
}

impl Default for Test {
    fn default() -> Self {
        Test {
            service: None
        }
    }
}

#[derive(PartialEq, Debug, Deserialize, Serialize)]
pub enum Foo {
    Mega,
    Supa
}

#[test]
fn test_enum_de() {
    let figment = || Figment::new()
        .merge(Serialized::defaults(Test::default()))
        .merge(Toml::file("Test.toml"))
        .merge(Env::prefixed("TEST_"));

    figment::Jail::expect_with(|jail| {
        jail.create_file("Test.toml", "service = \"Mega\"")?;

        let test: Test = figment().extract()?;
        assert_eq!(test.service, Some(Foo::Mega));

        jail.set_env("TEST_SERVICE", "Supa");

        let test: Test = figment().extract()?;
        assert_eq!(test.service, Some(Foo::Supa));

        Ok(())
    })
}
