#![cfg(feature = "toml")]

use figment::{Figment, value::Dict};
use figment::providers::{Format, Toml, Serialized};

#[test]
fn dictionary_order() {
    let base = Figment::from(Toml::string("dict = { b = 1, a = 2 }"));
    let other = Toml::string("dict = { a = 3, d = 4, c = 5 }");
    let cases = [
        (base.clone().join(&other), 2),
        (base.clone().merge(&other), 3),
        (base.clone().adjoin(&other), 2),
        (base.admerge(&other), 3),
    ];

    for (config, expected_a) in cases {
        let dict: Dict = config.extract_inner("dict").unwrap();
        assert_eq!(dict["a"], expected_a.into());

        let keys: Vec<_> = dict.keys().collect();
        #[cfg(feature = "preserve_order")]
        assert_eq!(keys, ["b", "a", "d", "c"]);
        #[cfg(not(feature = "preserve_order"))]
        assert_eq!(keys, ["a", "b", "c", "d"]);

        let config = Figment::from(Serialized::defaults(&dict));
        let roundtrip: Dict = config.extract().unwrap();
        assert_eq!(roundtrip.keys().collect::<Vec<_>>(), keys);
        assert_eq!(roundtrip, dict);
    }
}
