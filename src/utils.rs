use anyhow::{anyhow, Context};
use log::trace;

use crate::error::MyError;
/// Set up crate logging and environment variables.
pub(crate) fn setup() -> Result<(), MyError> {
  dotenvy::dotenv().ok();
  env_logger::init();
  std::env::var("DOTENV_OK").with_context(|| anyhow!("failed to load dotenv"))?;
  Ok(())
}
