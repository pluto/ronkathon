use crate::hmac::hmac_sha256::hmac_sha256;
use crypto_bigint::U256;
use crypto_bigint::Encoding; 

/// Converts a nonnegative integer to an octet string of a specified length using crypto-bigint.
///
/// I2OSP (Integer-to-Octet-String Primitive) converts a nonnegative integer `x` (represented as a
/// 256-bit integer) into its big-endian representation, trimmed of any excess leading zeroes, and
/// left-padded with zeroes so that the result has exactly `length` bytes.
///
/// # Arguments
///
/// * `x` - A reference to a `U256` representing the nonnegative integer.
/// * `length` - The number of octets (bytes) the output string should have.
///
/// # Returns
///
/// * `Ok(Vec<u8>)` containing the octet string if the integer can be represented in the specified
///   length.
/// * `Err(String)` if the integer is too large to be encoded in the given number of octets.
///
/// # Example
///
/// ```
/// use crypto_bigint::U256;
/// use crate::dsa::utils::i2osp;
///
/// let x = U256::from(65535u64);
/// let os = i2osp(&x, 4).unwrap();
/// assert_eq!(os, vec![0, 0, 255, 255]);
/// ```
pub fn i2osp(x: &U256, length: usize) -> Result<Vec<u8>, String> {
    // U256 is internally represented as 32 bytes (big-endian).
    let full_bytes = x.to_be_bytes(); // This is a [u8; 32].
    
    // Convert to a minimal representation by skipping all leading zeros.
    let minimal: Vec<u8> = {
        let buf: Vec<u8> = full_bytes.iter().skip_while(|&&b| b == 0).cloned().collect();
        if buf.is_empty() { vec![0] } else { buf }
    };

    if minimal.len() > length {
        return Err(format!("Integer too large to encode in {} octets", length));
    }
    let mut result = vec![0u8; length - minimal.len()];
    result.extend_from_slice(&minimal);
    Ok(result)
}

/// Converts an octet string to a nonnegative integer as a U256 using crypto-bigint.
///
/// OS2IP (Octet-String-to-Integer Primitive) interprets an octet string as the big-endian
/// representation of a nonnegative integer. When the input slice is longer than 32 bytes, the
/// function verifies that the extra leading bytes are all zero (so that the value fits in 256 bits).
///
/// # Arguments
///
/// * `octets` - A slice of bytes representing the octet string.
///
/// # Returns
///
/// * `Ok(U256)` corresponding to the nonnegative integer value of `octets`.
/// * `Err(String)` if the octet string represents a number that does not fit in 256 bits.
///
/// # Example
///
/// ```
/// use crypto_bigint::U256;
/// use crate::dsa::utils::os2ip;
///
/// let bytes = vec![0, 0, 255, 255];
/// let x = os2ip(&bytes).unwrap();
/// assert_eq!(x, U256::from(65535u64));
/// ```
pub fn os2ip(octets: &[u8]) -> Result<U256, String> {
    let len = octets.len();
    if len > 32 {
        // For slices longer than 32 bytes, verify that the extra (leftmost) bytes are all zero.
        if octets[..len - 32].iter().any(|&b| b != 0) {
            return Err("Integer too large to represent in 256 bits".to_string());
        }
        let arr: [u8; 32] = octets[len - 32..]
            .try_into()
            .map_err(|_| "Invalid slice length")?;
        Ok(U256::from_be_bytes(arr))
    } else {
        // If fewer than 32 bytes, left-pad with zeros.
        let mut padded = [0u8; 32];
        padded[32 - len..].copy_from_slice(octets);
        Ok(U256::from_be_bytes(padded))
    }
}


// HKDF



/// HKDF-Extract according to RFC 5869. 
/// If no salt is provided (i.e., salt is empty), a zero-filled salt of 32-bytes (SHA-256 output length) is used.
pub fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> Vec<u8> {
    let salt = if salt.is_empty() {
        // For SHA-256, the hash length is 32 bytes.
        vec![0u8; 32]
    } else {
        salt.to_vec()
    };
    hmac_sha256(&salt, ikm).to_vec()
}

/// HKDF-Expand according to RFC 5869.
pub fn hkdf_expand(prk: &[u8], info: &[u8], l: usize) -> Vec<u8> {
    // Optionally: enforce l <= 255 * 32 if using SHA-256
    let n = (l + 31) / 32; // Ceiling division for hash length of 32 bytes
    let mut t = Vec::new(); // This will hold T(i-1), starting with empty T(0)
    let mut okm = Vec::new();
    for i in 1..=n {
        // Create message: T(i-1) || info || i
        let mut data = Vec::new();
        data.extend_from_slice(&t);
        data.extend_from_slice(info);
        data.push(i as u8);
        
        // Compute T(i)
        t = hmac_sha256(prk, &data).to_vec();
        
        // Append T(i) to the output
        okm.extend_from_slice(&t);
    }
    okm.truncate(l);
    okm
}
#[cfg(test)]
mod tests {
    use super::*;
    use crypto_bigint::U256;

    #[test]
    fn test_i2osp() {
        let x = U256::ZERO;
        let result = i2osp(&x, 4).unwrap();
        assert_eq!(result, vec![0, 0, 0, 0]);

        let y = U256::from(65535u64);
        let result = i2osp(&y, 4).unwrap();
        assert_eq!(result, vec![0, 0, 255, 255]);

        // A value that requires more than 4 bytes.
        let large_int = U256::ONE << 40; // This value cannot be encoded in just 4 bytes.
        assert!(i2osp(&large_int, 4).is_err());
    }

    #[test]
    fn test_os2ip() {
        let bytes = vec![0, 0, 255, 255];
        let x = os2ip(&bytes).unwrap();
        assert_eq!(x, U256::from(65535u64));

        let bytes = vec![0, 0, 0, 0];
        let x = os2ip(&bytes).unwrap();
        assert_eq!(x, U256::ZERO);

        // Test with an octet string longer than 32 bytes but valid (with leading zeros).
        let mut long_bytes = vec![0u8; 5];
        long_bytes.extend_from_slice(&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                                        10, 11, 12, 13, 14, 15, 16, 17,
                                        18, 19, 20, 21, 22, 23, 24, 25,
                                        26, 27, 28, 29, 30, 31, 32]); // total length: 5+32 = 37 bytes.
        // Only the last 32 bytes are used.
        let _ = os2ip(&long_bytes).unwrap();

        // Test error scenario: If any extra leading byte is nonzero, it is an overflow.
        let mut invalid_bytes = vec![1u8];
        invalid_bytes.extend(vec![0u8; 32]);
        assert!(os2ip(&invalid_bytes).is_err());
    }
} 