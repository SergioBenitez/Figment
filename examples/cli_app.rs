/// An example application for reading cli and a configuration into a struct
///
/// First defaults can be optionally specified by using serde_inline_default
/// ```rust
/// #[serde_inline_default(Some(1))]
/// ```
/// 
/// Second any defaults are overridden via settings specified
/// within a configuration file `cli_app.toml``
/// 
/// Finally the cli arguments via clap override any settings
/// from the prior two steps.
/// 
/// Notes
///   * For this to work all fields need to be optional or typed as Option<>
///     This is to avoid clap reporting an error or missing option if an option is already set by figment or by serde’s defaults
///     If a field is "required" then this needs to be handled via custom validation after the reading in of values
///   * We also need to use a serde attribute `#[serde(skip_serializing_if = "::std::option::Option::is_none")]`
///     This is to avoid clap overriding values with None if no cli options are specified
///
/// Required Dependencies include
/// ```toml
/// clap = { version = "*", features = ["derive"] }
/// figment = { version = "*", features = ["toml"] }
/// serde = { version = "*", features = ["serde_derive"] }
/// serde_default_utils = { version = "*", features = ["inline"] }
/// ```


use clap::{error::ErrorKind, CommandFactory, Parser};
use figment::{
    providers::{Format, Serialized, Toml},
    Figment,
};
use serde::{Deserialize, Serialize};
use serde_default_utils::*;
use std::path::PathBuf;

/// A demo showing the use of figment with clap
#[serde_inline_default]
#[derive(Parser, Debug, Serialize, Deserialize)]
pub struct AppConfig {
    /// Name of the person to greet
    #[arg(short, long)]
    #[serde(skip_serializing_if = "::std::option::Option::is_none")]
    name: Option<String>,

    /// Number of times to greet - default value of 1
    #[arg(short, long)]
    #[serde_inline_default(Some(1))]
    #[serde(skip_serializing_if = "::std::option::Option::is_none")]
    count: Option<u8>,
}

fn main() {
    let cfgpath = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("cli_app.toml");

    let config: AppConfig = Figment::new()
        .merge(Toml::file(cfgpath))
        .merge(Serialized::defaults(AppConfig::parse()))
        .extract()
        .unwrap();

    // Custom Validation
    if config.name.is_none() {
        let mut cmd = AppConfig::command();
        cmd.error(ErrorKind::MissingRequiredArgument, "name option not found")
            .exit();
    }

    println!("Name: {}", config.name.unwrap());
    println!("Count: {}", config.count.unwrap());
}
