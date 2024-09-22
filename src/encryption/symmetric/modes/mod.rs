//! Contains implementation of modes of operation for different ciphers. Modes of operation allows
//! ciphers to work on arbitrary length of data.
//! - [`cbc::CBC`]: Cipher Block Chaining
//! - [`ctr::CTR`]: Counter mode
//! - [`gcm::GCM`]: Galois Counter mode
#![doc = include_str!("./README.md")]
pub mod cbc;
pub mod ctr;
pub mod gcm;
