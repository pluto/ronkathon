//! ronkathon error types
// https://docs.rs/thiserror/latest/thiserror/

use thiserror::Error;

#[derive(Debug, Error)]
pub enum MyError {
  // Derive Into<MyError> for io errors
  #[error("My Io error: {0}")]
  Io(#[from] std::io::Error),
  #[error("My dotenv error: {0}")]
  Dotenv(#[from] dotenvy::Error),
  // Derive Into<MyError> for anyhow errors
  #[error(transparent)]
  Anyhow(#[from] anyhow::Error),
  // Some other error type
  #[allow(dead_code)]
  #[error("an unhandled error")]
  Unhandled,
}
