//! Benchmarks for the hash functions in [`ronkathon::hashes`].
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use ronkathon::hashes::{
  sha::{Sha256, Sha512},
  sha3::Sha3_256,
};

const SIZES: [usize; 2] = [64, 1024];

fn sha2(c: &mut Criterion) {
  let mut group = c.benchmark_group("sha2");
  for size in SIZES {
    let input = vec![0xab; size];
    group.throughput(Throughput::Bytes(size as u64));
    group.bench_with_input(BenchmarkId::new("sha256", size), &input, |b, input| {
      let hasher = Sha256::new();
      b.iter(|| hasher.digest(black_box(input)))
    });
    group.bench_with_input(BenchmarkId::new("sha512", size), &input, |b, input| {
      let hasher = Sha512::new();
      b.iter(|| hasher.digest(black_box(input)))
    });
  }
  group.finish();
}

fn sha3(c: &mut Criterion) {
  let mut group = c.benchmark_group("sha3");
  for size in SIZES {
    let input = vec![0xab; size];
    group.throughput(Throughput::Bytes(size as u64));
    group.bench_with_input(BenchmarkId::new("sha3_256", size), &input, |b, input| {
      b.iter(|| {
        let mut hasher = Sha3_256::new();
        hasher.update(black_box(input));
        hasher.finalize()
      })
    });
  }
  group.finish();
}

criterion_group!(benches, sha2, sha3);
criterion_main!(benches);
