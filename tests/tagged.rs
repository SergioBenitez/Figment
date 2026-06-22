use figment::{Figment, Jail, Profile};
use figment::{value::{Value, magic::Tagged}, providers::Serialized};

#[test]
fn check_values_are_tagged_with_profile() {
    Jail::expect_with(|_| {
        let figment = Figment::new()
            .merge(Serialized::default("default", "default"))
            .merge(Serialized::global("global", "global"))
            .merge(Serialized::default("custom", "custom").profile("custom"));

        let tagged: Tagged<String> = figment.extract_inner("default")?;
        let value: Value = figment.find_value("default")?;
        assert_eq!(tagged.tag().profile(), Some(Profile::Default));
        assert_eq!(value.tag().profile(), Some(Profile::Default));

        let tagged: Tagged<String> = figment.extract_inner("global")?;
        let value: Value = figment.find_value("global")?;
        assert_eq!(tagged.tag().profile(), Some(Profile::Global));
        assert_eq!(value.tag().profile(), Some(Profile::Global));

        let figment = figment.select("custom");
        let tagged: Tagged<String> = figment.extract_inner("custom")?;
        let value: Value = figment.find_value("custom")?;
        assert_eq!(tagged.tag().profile(), None);
        assert_eq!(value.tag().profile(), None);

        Ok(())
    });
}

#[test]
fn check_errors_are_tagged_with_path() {
    Jail::expect_with(|_| {
        let figment = Figment::new()
            .merge(("foo", 123))
            .merge(("foo.bar", 789))
            .merge(("baz", 789));

        let err = figment.extract_inner::<String>("foo").unwrap_err();
        assert_eq!(err.path, vec!["foo"]);

        let err = figment.extract_inner::<String>("foo.bar").unwrap_err();
        assert_eq!(err.path, vec!["foo", "bar"]);

        let err = figment.extract_inner::<usize>("foo.bar.baz").unwrap_err();
        assert!(err.path.is_empty());
        Ok(())
    });
}

#[test]
fn find_all_values_recovers_every_layer_contribution() {
    Jail::expect_with(|jail| {
        use figment::providers::{Format, Toml};

        jail.create_file("Base.toml", r#"
            plugins = ["a", "b"]
            ring = "internal"
        "#)?;

        jail.create_file("Repo.toml", r#"
            plugins = ["c"]
            ring = "dogfood"
            only_repo = true
        "#)?;

        let figment = Figment::new()
            .merge(Toml::file("Base.toml"))
            .merge(Toml::file("Repo.toml"));

        // Coalesced view keeps only the highest-priority array / scalar.
        assert_eq!(figment.extract_inner::<Vec<String>>("plugins").unwrap(), vec!["c"]);
        assert_eq!(figment.extract_inner::<String>("ring").unwrap(), "dogfood");

        let source = |v: &Value| {
            figment.get_metadata(v.tag())
                .and_then(|m| m.source.as_ref())
                .map(|s| s.to_string())
                .unwrap_or_default()
        };

        // Array-replaced contributions are all recoverable, lowest → highest.
        let plugins = figment.find_all_values("plugins");
        assert_eq!(plugins.len(), 2);
        assert_eq!(plugins[0].clone().into_array().unwrap().len(), 2);
        assert!(source(&plugins[0]).contains("Base.toml"));
        assert_eq!(plugins[1].clone().into_array().unwrap().len(), 1);
        assert!(source(&plugins[1]).contains("Repo.toml"));

        // Overridden scalars are likewise all recoverable.
        let ring = figment.find_all_values("ring");
        assert_eq!(ring.len(), 2);
        assert_eq!(ring[0].clone().into_string().unwrap(), "internal");
        assert!(source(&ring[0]).contains("Base.toml"));
        assert_eq!(ring[1].clone().into_string().unwrap(), "dogfood");
        assert!(source(&ring[1]).contains("Repo.toml"));

        // A field set by only one layer yields exactly one contribution.
        let only = figment.find_all_values("only_repo");
        assert_eq!(only.len(), 1);
        assert!(source(&only[0]).contains("Repo.toml"));

        // A path no provider set yields nothing.
        assert!(figment.find_all_values("missing").is_empty());

        Ok(())
    });
}

#[test]
fn find_all_values_respects_profiles() {
    Jail::expect_with(|_| {
        let figment = Figment::new()
            .merge(Serialized::default("key", "default-1"))
            .merge(Serialized::default("key", "default-2"))
            .merge(Serialized::default("key", "custom").profile("custom"));

        // Default profile: both default contributions, in merge order; the
        // custom-profile contribution is not visible.
        let all = figment.find_all_values("key");
        assert_eq!(all.len(), 2);
        assert_eq!(all[0].clone().into_string().unwrap(), "default-1");
        assert_eq!(all[1].clone().into_string().unwrap(), "default-2");

        // Selecting the custom profile surfaces its contribution on top of the
        // defaults it merges with.
        let figment = figment.select("custom");
        let all = figment.find_all_values("key");
        assert_eq!(all.len(), 3);
        assert_eq!(all[2].clone().into_string().unwrap(), "custom");

        Ok(())
    });
}
