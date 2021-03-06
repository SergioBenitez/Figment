use std::fs::File;
use std::io::{Write, BufWriter};
use std::path::{Path, PathBuf};
use std::fmt::Display;

use tempfile::TempDir;
use parking_lot::Mutex;

use crate::error::Result;

// TODO: Clear environment variables before entering this? Will they mess with
// anything else?
/// A "sandboxed" environment with isolated env and file system namespace.
///
/// `Jail` creates a pseudo-sandboxed (not _actually_ sandboxed) environment for
/// testing configurations. Specifically, `Jail`:
///
///   * Synchronizes all calls to [`Jail::expect_with()`] and
///     [`Jail::try_with()`] to prevent environment variables races.
///   * Switches into a fresh temporary directory ([`Jail::directory()`]) where
///     files can be created with [`Jail::create_file()`].
///   * Keeps track of environment variables created with [`Jail::set_env()`]
///     and clears them when the `Jail` exits.
///   * Deletes the temporary directory and all of its contents when exiting.
///
/// Additionally, because `Jail` expects functions that return a [`Result`],
/// the `?` operator can be used liberally in a jail:
///
/// ```rust
/// use figment::{Figment, Jail, providers::{Format, Toml, Env}};
/// # #[derive(serde::Deserialize)]
/// # struct Config {
/// #     name: String,
/// #     authors: Vec<String>,
/// #     publish: bool
/// # }
///
/// figment::Jail::expect_with(|jail| {
///     jail.create_file("Cargo.toml", r#"
///       name = "test"
///       authors = ["bob"]
///       publish = false
///     "#)?;
///
///     jail.set_env("CARGO_NAME", "env-test");
///
///     let config: Config = Figment::new()
///         .merge(Toml::file("Cargo.toml"))
///         .merge(Env::prefixed("CARGO_"))
///         .extract()?;
///
///     Ok(())
/// });
/// ```
#[cfg_attr(nightly, doc(cfg(feature = "test")))]
pub struct Jail {
    _directory: TempDir,
    canonical_dir: PathBuf,
    env_vars: Vec<String>,
    old_cwd: PathBuf,
}

fn as_string<S: Display>(s: S) -> String { s.to_string() }

static LOCK: Mutex<()> = parking_lot::const_mutex(());

impl Jail {
    /// Creates a new jail that calls `f`, passing itself to `f`.
    ///
    /// # Panics
    ///
    /// Panics if `f` returns an `Err`; prints the error message.
    ///
    /// # Example
    ///
    /// ```rust
    /// figment::Jail::expect_with(|jail| {
    ///     /* in the jail */
    ///
    ///     Ok(())
    /// });
    /// ```
    #[track_caller]
    pub fn expect_with<F: FnOnce(&mut Jail) -> Result<()>>(f: F) {
        if let Err(e) = Jail::try_with(f) {
            panic!("jail failed: {}", e)
        }
    }

    /// Creates a new jail that calls `f`, passing itself to `f`. Does not panic;
    /// returns the result from `f`.
    ///
    /// # Example
    ///
    /// ```rust
    /// let result = figment::Jail::try_with(|jail| {
    ///     /* in the jail */
    ///
    ///     Ok(())
    /// });
    /// ```
    #[track_caller]
    pub fn try_with<F: FnOnce(&mut Jail) -> Result<()>>(f: F) -> Result<()> {
        let _lock = LOCK.lock();
        let directory = TempDir::new().map_err(as_string)?;
        let mut jail = Jail {
            canonical_dir: directory.path().canonicalize().map_err(as_string)?,
            _directory: directory,
            old_cwd: std::env::current_dir().map_err(as_string)?,
            env_vars: vec![],
        };

        std::env::set_current_dir(jail.directory()).map_err(as_string)?;
        f(&mut jail)
    }

    /// Returns the directory the jail has switched into. The contents of this
    /// directory will be cleared when `Jail` is dropped.
    ///
    /// # Example
    ///
    /// ```rust
    /// figment::Jail::expect_with(|jail| {
    ///     let tmp_directory = jail.directory();
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn directory(&self) -> &Path {
        &self.canonical_dir
    }

    /// Creates a file with contents `contents` in the jail's directory. The
    /// file will be deleted with the jail is dropped.
    ///
    /// # Example
    ///
    /// ```rust
    /// figment::Jail::expect_with(|jail| {
    ///     jail.create_file("MyConfig.json", "contents...");
    ///     Ok(())
    /// });
    /// ```
    pub fn create_file<P: AsRef<Path>>(&self, path: P, contents: &str) -> Result<File> {
        let path = path.as_ref();
        if !path.is_relative() {
            return Err("Jail::create_file(): file path is absolute".to_string().into());
        }

        let file = File::create(self.directory().join(path)).map_err(as_string)?;
        let mut writer = BufWriter::new(file);
        writer.write_all(contents.as_bytes()).map_err(as_string)?;
        Ok(writer.into_inner().map_err(as_string)?)
    }

    /// Set the environment variable `k` to value `v`. The variable will be
    /// removed when the jail is dropped.
    ///
    /// # Example
    ///
    /// ```rust
    /// const VAR_NAME: &str = "my-very-special-figment-var";
    ///
    /// assert!(std::env::var(VAR_NAME).is_err());
    ///
    /// figment::Jail::expect_with(|jail| {
    ///     jail.set_env(VAR_NAME, "value");
    ///     assert!(std::env::var(VAR_NAME).is_ok());
    ///     Ok(())
    /// });
    ///
    /// assert!(std::env::var(VAR_NAME).is_err());
    /// ```
    pub fn set_env<K: AsRef<str>, V: Display>(&mut self, k: K, v: V) {
        let key = k.as_ref();
        self.env_vars.push(key.to_string());
        std::env::set_var(key, v.to_string());
    }
}

impl Drop for Jail {
    fn drop(&mut self) {
        self.env_vars.iter().for_each(std::env::remove_var);
        let _ = std::env::set_current_dir(&self.old_cwd);
    }
}
