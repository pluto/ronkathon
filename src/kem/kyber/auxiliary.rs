use sha3::{
  digest::{ExtendableOutput, Update, XofReader},
  Digest, Shake128, Shake256,
};

pub fn prf<const eta: usize>(s: [u8; 32], b: u8) -> [u8; 64 * eta] {
  // concat s and b
  let mut hasher = Shake256::default();
  hasher.update(&s);
  hasher.update(&[b]);
  let mut res = [0u8; 64 * eta];
  XofReader::read(&mut hasher.finalize_xof(), &mut res);
  res
}

pub fn h(s: &[u8]) -> [u8; 32] { sha3::Sha3_256::digest(s).into() }

pub fn j(s: &[u8]) -> [u8; 32] {
  let mut hasher = Shake256::default();
  hasher.update(s);
  let mut reader = hasher.finalize_xof();
  let mut res = [0u8; 32];
  XofReader::read(&mut reader, &mut res);
  res
}

pub fn g(c: &[u8]) -> ([u8; 32], [u8; 32]) {
  let res = sha3::Sha3_512::digest(c);
  (res[..32].try_into().unwrap(), res[32..].try_into().unwrap())
}

pub struct Xof(Shake128);

impl Xof {
  pub fn init() -> Self { Self(Shake128::default()) }

  pub fn absorb(mut self, input: &[u8]) -> impl XofReader {
    self.0.update(input);
    self.0.finalize_xof()
  }

  pub fn squeeze(reader: &mut impl XofReader, output: &mut [u8]) {
    XofReader::read(reader, output);
  }
}
