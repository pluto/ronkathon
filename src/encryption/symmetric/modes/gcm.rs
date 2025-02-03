//! Implementation of GCM cipher mode of operation based on NIST GCM specification.
//! [The Galois/Counter Mode of Operation (GCM)](http://www.csrc.nist.gov/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-revised-spec.pdf)
//!
//! GCM has two parts GCTR (used of encryption/decryption) and GHASH (used for authentication).
//!
//! GCTR is similar to CTR mode of operation. ASCII diagram of GCTR, courtesy of
//! @0xJepsen.
//!            -------------           inc           -------------
//!            |    ICB    | ----------------------> |    CB2    |
//!            -------------                         -------------
//!                  |                                      |
//!                  v                                      v
//!            ------------                           ------------
//!            |  CIPH_K  |                           |  CIPH_K  |
//!            ------------                           ------------
//!                  |                                      |
//!                  v                                      v
//!             ------------                           ------------
//!             |    X1    |                           |     X2   |
//!             ------------                           ------------
//!                   |                                      |
//!                   v                       ---------      v
//!                  XOR                   -->|  Y_1  |---> XOR
//!                   |                    |  ---------      |
//!                   v                    |                 v
//!               --------                 |              --------
//!               |  Y1  |------------------              |  Y2  |
//!               --------                                --------
//!                   |                                       |
//!                   v                                       v
//!
//! GCTR_K (ICB, X1 || X2 || ... || X_n*) = Y1 || Y2 || ... || Y_n*.

use super::ctr::CTR;
use crate::{
  encryption::{symmetric::counter::Counter, BlockOperations, Encryption},
  hashes::ghash::GHASH,
};

/// GCM (Galois/Counter Mode) struct holding a GHASH instance and a block cipher key.
///
/// This structure implements encryption and decryption operations using the GCM
/// authenticated encryption mode, combining the CTR (counter mode) for encryption
/// and GHASH for authentication.
///
/// # Generics
/// - `C`: A block cipher that implements the `BlockCipher` trait.
pub struct GCM<C: BlockOperations + Encryption> {
  ghash: GHASH,
  key:   C::Key,
}

impl<C: BlockOperations + Encryption> GCM<C>
where [(); C::BLOCK_SIZE - 4]:
{
  /// Constructs a new `GCM` instance with the given key.
  ///
  /// # Parameters
  /// - `key`: A key compatible with the block cipher `C`.
  ///
  /// # Returns
  /// A `GCM` instance ready for encryption or decryption.
  pub fn new(key: C::Key) -> Self {
    assert_eq!(C::BLOCK_SIZE, 16, "GCM only supports 128-bit block size.");
    // The GHASH algorithms requires the encryption of 128-bits of zeros.
    let zero_string = C::Block::from(vec![0u8; 16]);
    let cipher = match C::new(key.clone()) {
      Ok(cipher) => cipher,
      Err(_) => panic!("Error creating cipher"),
    };
    let hash_key = cipher.encrypt_block(zero_string).unwrap();
    let ghash = GHASH::new(hash_key.as_ref());
    GCM { ghash, key }
  }

  /// Encrypts the given plaintext using the specified nonce and additional authenticated data
  /// (AAD).
  ///
  /// # Parameters
  /// - `nonce`: A unique nonce for the encryption process (should be '12' bytes long).
  /// - `plaintext`: The data to be encrypted.
  /// - `aad`: Additional authenticated data (AAD) that will be included in the authentication tag
  ///   but not encrypted.
  ///
  /// # Returns
  /// A tuple `(ciphertext, tag)`:
  /// - `ciphertext`: The encrypted data.
  /// - `tag`: The authentication tag that verifies the integrity and authenticity of the ciphertext
  ///   and AAD.
  ///
  /// A `String` error if encryption fails.
  pub fn encrypt(
    &self,
    nonce: &[u8],
    plaintext: &[u8],
    aad: &[u8],
  ) -> Result<(Vec<u8>, Vec<u8>), String> {
    // The `initial_block` is the first block that is encrypted.
    // This is used in the tag generation step.
    // It consists of two parts, a 96-bit nonce value and 32-bit counter value, which is
    // incremented for each block to be encrypted.
    let mut initial_block;
    // `counter_start` is the start value for the 32-bit counter.
    let counter_start: [u8; 4];
    // `new_nonce` is the 96-bit nonce value.
    // That is C::BLOCK_SIZE(=16 bytes) - 4 bytes = 12 bytes = 96-bits!
    // Also NOTE: the compiler is not happy if I write 12 bytes instead of `C::BLOCK_SIZE - 4`. :(
    let new_nonce: [u8; C::BLOCK_SIZE - 4];

    // The GCM specification recommends a 96-bit(or 12-byte) nonce, but it may not be 96-bit.
    if nonce.len() != 12 {
      // If the nonce is not 96-bit, we GHASH the nonce, which outputs a 128-bit value.
      // The first 96-bit is used as new nonce(hence named `new_nonce`).
      // The rest of the 32-bits are used as the start of counter value!
      initial_block = self.ghash.digest(&[], nonce);
      new_nonce = initial_block[..12].try_into().unwrap();
      counter_start = initial_block[12..].try_into().unwrap();
    } else {
      new_nonce = nonce.try_into().unwrap();
      // The counter starts with `1`.
      counter_start = [0, 0, 0, 1];
      initial_block = [0u8; 16];
      initial_block[..12].copy_from_slice(&new_nonce);
      initial_block[12..].copy_from_slice(&counter_start);
    }

    // Step 1: Increment the counter
    let mut counter = Counter(counter_start);
    counter.increment()?;

    // Step 2: Encrypt the plaintext using the `CTR` object.
    let ctr = CTR::<C, 4>::new(new_nonce.into());
    let ciphertext = ctr.encrypt(&self.key, &counter, plaintext)?;

    // Step3: Generate Tag
    // The tag is the XOR of the `initial_block` and ghash of ciphertext.
    let y0_block = C::Block::from(initial_block.to_vec());
    let cipher = match C::new(self.key.clone()) {
      Ok(cipher) => cipher,
      Err(_) => panic!("Error creating cipher"),
    };
    let y0_enc = cipher.encrypt_block(y0_block).unwrap();
    let hash = self.ghash.digest(aad, ciphertext.as_ref());
    let mut tag = Vec::new();

    // XOR the ghash of ciphertext and `initial_block`
    for (x, y) in hash.iter().zip(y0_enc.as_ref()) {
      tag.push(x ^ y);
    }

    Ok((ciphertext.to_vec(), tag))
  }

  /// Decrypt the given ciphertext using the specified nonce and additional authenticated data
  /// (AAD).
  ///
  /// # Parameters
  /// - `nonce`: A unique nonce used during encryption (should be 12 bytes long).
  /// - `ciphertext`: The encrypted data to be decrypted.
  /// - `aad`: Additional authenticated data (AAD) used during encryption.
  ///
  /// # Returns
  /// A tuple `(plaintext, tag)`:
  /// - `plaintext`: The decrypted data.
  /// - `tag`: The authentication tag to verify the integrity and authenticity of the decrypted
  ///   data.
  ///
  /// A `String` error if decryption fails.
  pub fn decrypt(
    &self,
    nonce: &[u8],
    ciphertext: &[u8],
    aad: &[u8],
  ) -> Result<(Vec<u8>, Vec<u8>), String> {
    // The decryption algorithm is the same as the encryption algorithm but the tag is generated
    // first and then is move on to the encryption.

    let counter_start: [u8; 4];
    let new_nonce: [u8; C::BLOCK_SIZE - 4];
    let mut counter_block;

    if nonce.len() != 12 {
      counter_block = self.ghash.digest(&[], nonce);
      new_nonce = counter_block[..12].try_into().unwrap();
      counter_start = counter_block[12..].try_into().unwrap();
    } else {
      new_nonce = nonce.try_into().unwrap();
      counter_start = [0, 0, 0, 1];
      counter_block = [0u8; 16];
      counter_block[..12].copy_from_slice(&new_nonce);
      counter_block[12..].copy_from_slice(&counter_start);
    }

    // Step 1: Generate Tag (same as the encryption)
    let y0 = C::Block::from(counter_block.to_vec());
    let cipher = match C::new(self.key.clone()) {
      Ok(cipher) => cipher,
      Err(_) => panic!("Error creating cipher"),
    };
    let y0_enc = cipher.encrypt_block(y0).unwrap();
    let hash = self.ghash.digest(aad, ciphertext.as_ref());
    let mut tag = Vec::new();

    for (x, y) in hash.iter().zip(y0_enc.as_ref()) {
      tag.push(x ^ y);
    }

    // Step 2: Increment Counter
    let mut counter = Counter(counter_start);
    counter.increment()?;

    // Step 3: Decrypt ciphertext.
    let ctr = CTR::<C, 4>::new(new_nonce.into());
    let plaintext = ctr.decrypt(&self.key, &counter, ciphertext)?;

    Ok((plaintext.to_vec(), tag))
  }
}

#[cfg(test)]
mod tests {

  use std::{fmt::Write, num::ParseIntError};

  use rstest::rstest;

  use super::*;
  use crate::encryption::symmetric::aes::{Key, AES};

  /// Encode bytes to hex
  pub fn encode_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
      write!(&mut s, "{:02x}", b).unwrap();
    }
    s
  }

  pub fn decode_hex(s: &str) -> Result<Vec<u8>, ParseIntError> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16)).collect()
  }

  #[rstest]
  // NIST Test Case 1
  #[case(
    "00000000000000000000000000000000",
    "000000000000000000000000",
    "",
    "",
    "",
    "58e2fccefa7e3061367f1d57a4e7455a"
  )]
  // NIST Test Case 2
  #[case(
    "00000000000000000000000000000000",
    "000000000000000000000000",
    "00000000000000000000000000000000",
    "",
    "0388dace60b6a392f328c2b971b2fe78",
    "ab6e47d42cec13bdf53a67b21257bddf"
  )]
  // NIST Test Case 3
  #[case(
    "feffe9928665731c6d6a8f9467308308",
    "cafebabefacedbaddecaf888",
    "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255",
    "",
    "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985",
    "4d5c2af327cd64a62cf35abd2ba6fab4"
    )]
  // NIST Test Case 4
  #[case(
    "feffe9928665731c6d6a8f9467308308",
    "cafebabefacedbaddecaf888",
    "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
    "feedfacedeadbeeffeedfacedeadbeefabaddad2",
    "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091",
    "5bc94fbc3221a5db94fae95ae7121a47"
    )]
  // NIST Test Case 5
  #[case(
    "feffe9928665731c6d6a8f9467308308",
    "cafebabefacedbad",
    "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
    "feedfacedeadbeeffeedfacedeadbeefabaddad2",
    "61353b4c2806934a777ff51fa22a4755699b2a714fcdc6f83766e5f97b6c742373806900e49f24b22b097544d4896b424989b5e1ebac0f07c23f4598",
    "3612d2e79e3b0785561be14aaca2fccb"
    )]
  // NIST Test Case 6
  #[case(
    "feffe9928665731c6d6a8f9467308308",
    "9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b",
    "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
    "feedfacedeadbeeffeedfacedeadbeefabaddad2",
    "8ce24998625615b603a033aca13fb894be9112a5c3a211a8ba262a3cca7e2ca701e4a9a4fba43c90ccdcb281d48c7c6fd62875d2aca417034c34aee5",
    "619cc5aefffe0bfa462af43c1699d050"
    )]
  fn test_gcm_128(
    #[case] kx: &str,
    #[case] ivx: &str,
    #[case] ptx: &str,
    #[case] aadx: &str,
    #[case] expected_ctx: &str,
    #[case] expected_tagx: &str,
  ) {
    let k = decode_hex(kx).unwrap();
    let iv = decode_hex(ivx).unwrap();
    let pt = decode_hex(ptx).unwrap();
    let aad = decode_hex(aadx).unwrap();

    let key = Key::<128>::new(k.try_into().unwrap());
    let gcm = GCM::<AES<128>>::new(key);

    let (ct, tag) = gcm.encrypt(&iv, &pt, &aad).unwrap();

    let ctx = encode_hex(&ct);
    assert_eq!(ctx, expected_ctx);

    let tagx = encode_hex(&tag);
    assert_eq!(tagx, expected_tagx);

    let (_pt, _tag) = gcm.decrypt(&iv, &ct, &aad).unwrap();

    let _ptx = encode_hex(&_pt);
    assert_eq!(ptx, _ptx);

    let _tagx = encode_hex(&_tag);
    assert_eq!(_tagx, expected_tagx);
  }

  #[rstest]
  // NIST Test Case 7
  #[case(
    "000000000000000000000000000000000000000000000000",
    "000000000000000000000000",
    "",
    "",
    "",
    "cd33b28ac773f74ba00ed1f312572435"
  )]
  // NIST Test Case 8
  #[case(
    "000000000000000000000000000000000000000000000000",
    "000000000000000000000000",
    "00000000000000000000000000000000",
    "",
    "98e7247c07f0fe411c267e4384b0f600",
    "2ff58d80033927ab8ef4d4587514f0fb"
  )]
  // NIST Test Case 9
  #[case(
    "feffe9928665731c6d6a8f9467308308feffe9928665731c",
    "cafebabefacedbaddecaf888",
    "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255",
    "",
    "3980ca0b3c00e841eb06fac4872a2757859e1ceaa6efd984628593b40ca1e19c7d773d00c144c525ac619d18c84a3f4718e2448b2fe324d9ccda2710acade256",
    "9924a7c8587336bfb118024db8674a14")]
  // NIST Test Case 10
  #[case(
    "feffe9928665731c6d6a8f9467308308feffe9928665731c",
    "cafebabefacedbaddecaf888",
    "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
    "feedfacedeadbeeffeedfacedeadbeefabaddad2",
    "3980ca0b3c00e841eb06fac4872a2757859e1ceaa6efd984628593b40ca1e19c7d773d00c144c525ac619d18c84a3f4718e2448b2fe324d9ccda2710",
    "2519498e80f1478f37ba55bd6d27618c")]
  // NIST Test Case 11
  #[case(
    "feffe9928665731c6d6a8f9467308308feffe9928665731c",
    "cafebabefacedbad",
    "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
    "feedfacedeadbeeffeedfacedeadbeefabaddad2",
    "0f10f599ae14a154ed24b36e25324db8c566632ef2bbb34f8347280fc4507057fddc29df9a471f75c66541d4d4dad1c9e93a19a58e8b473fa0f062f7",
    "65dcc57fcf623a24094fcca40d3533f8")]
  // NIST Test Case 12
  #[case(
    "feffe9928665731c6d6a8f9467308308feffe9928665731c",
    "9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b",
    "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
    "feedfacedeadbeeffeedfacedeadbeefabaddad2",
    "d27e88681ce3243c4830165a8fdcf9ff1de9a1d8e6b447ef6ef7b79828666e4581e79012af34ddd9e2f037589b292db3e67c036745fa22e7e9b7373b",
    "dcf566ff291c25bbb8568fc3d376a6d9")]
  fn test_gcm_192(
    #[case] kx: &str,
    #[case] ivx: &str,
    #[case] ptx: &str,
    #[case] aadx: &str,
    #[case] expected_ctx: &str,
    #[case] expected_tagx: &str,
  ) {
    let k = decode_hex(kx).unwrap();
    let iv = decode_hex(ivx).unwrap();
    let pt = decode_hex(ptx).unwrap();
    let aad = decode_hex(aadx).unwrap();

    let key = Key::new(k.try_into().unwrap());
    let gcm = GCM::<AES<192>>::new(key);

    let (ct, tag) = gcm.encrypt(&iv, &pt, &aad).unwrap();

    let ctx = encode_hex(ct.as_ref());
    assert_eq!(ctx, expected_ctx);

    let tagx = encode_hex(&tag);
    assert_eq!(tagx, expected_tagx);

    let (_pt, _tag) = gcm.decrypt(&iv, &ct, &aad).unwrap();

    let _ptx = encode_hex(&_pt);
    assert_eq!(ptx, _ptx);

    let _tagx = encode_hex(&_tag);
    assert_eq!(_tagx, expected_tagx);
  }
}
