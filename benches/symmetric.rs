//! Benchmarks for the symmetric ciphers in [`ronkathon::encryption::symmetric`].
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use ronkathon::encryption::{
  symmetric::{
    aes::{Block, Key, AES},
    chacha::{Counter, IETFChaCha20},
    modes::cbc::CBC,
  },
  BlockOperations, Encryption,
};

const MESSAGE_LEN: usize = 1024;

fn aes(c: &mut Criterion) {
  let key = Key::<128>::new([0x2b; 16]);
  let aes = AES::<128>::new(key).unwrap();

  let mut group = c.benchmark_group("aes128");
  group.throughput(Throughput::Bytes(16));
  group.bench_function("encrypt_block", |b| {
    b.iter(|| aes.encrypt_block(black_box(Block([0x32; 16]))))
  });
  group.bench_function("decrypt_block", |b| {
    b.iter(|| aes.decrypt_block(black_box(Block([0x32; 16]))))
  });

  let cbc = CBC::<AES<128>>::new(Block([0x01; 16]));
  let message = vec![0xab; MESSAGE_LEN];
  let ciphertext = cbc.encrypt(&key, &message);
  group.throughput(Throughput::Bytes(MESSAGE_LEN as u64));
  group.bench_function("cbc_encrypt_1KiB", |b| b.iter(|| cbc.encrypt(&key, black_box(&message))));
  group
    .bench_function("cbc_decrypt_1KiB", |b| b.iter(|| cbc.decrypt(&key, black_box(&ciphertext))));
  group.finish();
}

fn chacha(c: &mut Criterion) {
  let chacha = IETFChaCha20::new(&[0x0102_0304; 8], &[0x0506_0708; 3]);
  let counter = Counter::new([1]);
  let message = vec![0xab; MESSAGE_LEN];

  let mut group = c.benchmark_group("chacha20");
  group.throughput(Throughput::Bytes(MESSAGE_LEN as u64));
  group
    .bench_function("encrypt_1KiB", |b| b.iter(|| chacha.encrypt(&counter, black_box(&message))));
  group.finish();
}

criterion_group!(benches, aes, chacha);
criterion_main!(benches);
