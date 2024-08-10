pub trait ToBytes {
    fn to_bytes(&self) -> Vec<u8>;
}