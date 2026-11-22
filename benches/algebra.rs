//! Benchmarks for field arithmetic, the Pluto curves, pairings and polynomials.
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ronkathon::{
  algebra::{
    field::{extension::PlutoBaseFieldExtension, prime::PlutoBaseField, Field},
    group::FiniteCyclicGroup,
  },
  curve::{
    pairing::pairing,
    pluto_curve::{PlutoBaseCurve, PlutoExtendedCurve},
    AffinePoint,
  },
  polynomial::{Monomial, Polynomial},
};

fn prime_field(c: &mut Criterion) {
  let (a, b) = (PlutoBaseField::new(42), PlutoBaseField::new(77));

  let mut group = c.benchmark_group("prime_field");
  group.bench_function("mul", |bench| bench.iter(|| black_box(a) * black_box(b)));
  group.bench_function("inverse", |bench| bench.iter(|| black_box(a).inverse()));
  group.bench_function("pow", |bench| bench.iter(|| black_box(a).pow(black_box(99))));
  group.finish();
}

fn extension_field(c: &mut Criterion) {
  let a = PlutoBaseFieldExtension::new([PlutoBaseField::new(9), PlutoBaseField::new(37)]);
  let b = PlutoBaseFieldExtension::new([PlutoBaseField::new(19), PlutoBaseField::new(93)]);

  let mut group = c.benchmark_group("extension_field");
  group.bench_function("mul", |bench| bench.iter(|| black_box(a) * black_box(b)));
  group.bench_function("inverse", |bench| bench.iter(|| black_box(a).inverse()));
  group.finish();
}

fn curve(c: &mut Criterion) {
  let generator = AffinePoint::<PlutoBaseCurve>::GENERATOR;

  let mut group = c.benchmark_group("pluto_curve");
  group.bench_function("add", |bench| bench.iter(|| black_box(generator) + black_box(generator)));
  group
    .bench_function("scalar_mul", |bench| bench.iter(|| black_box(13_u32) * black_box(generator)));

  // the torsion points from the `weil_tate_pairing_test` cases
  let p = AffinePoint::<PlutoExtendedCurve>::new(
    PlutoBaseFieldExtension::new([PlutoBaseField::new(9), PlutoBaseField::new(37)]),
    PlutoBaseFieldExtension::new([PlutoBaseField::new(19), PlutoBaseField::new(93)]),
  );
  let q = AffinePoint::<PlutoExtendedCurve>::new(
    PlutoBaseFieldExtension::new([PlutoBaseField::new(63), PlutoBaseField::new(0)]),
    PlutoBaseFieldExtension::new([PlutoBaseField::new(0), PlutoBaseField::new(35)]),
  );
  group.bench_function("tate_pairing", |bench| {
    bench.iter(|| pairing::<PlutoExtendedCurve, 17>(black_box(p), black_box(q)))
  });
  group.finish();
}

fn polynomial(c: &mut Criterion) {
  let poly = Polynomial::<Monomial, PlutoBaseField, 4>::new([
    PlutoBaseField::new(1),
    PlutoBaseField::new(2),
    PlutoBaseField::new(3),
    PlutoBaseField::new(4),
  ]);

  let mut group = c.benchmark_group("polynomial");
  group.bench_function("mul", |bench| bench.iter(|| black_box(poly) * black_box(poly)));
  group.bench_function("dft", |bench| bench.iter(|| black_box(&poly).dft()));
  group.bench_function("fft", |bench| bench.iter(|| black_box(&poly).fft()));
  group.bench_function("evaluate", |bench| {
    bench.iter(|| black_box(&poly).evaluate(black_box(PlutoBaseField::new(5))))
  });
  group.finish();
}

criterion_group!(benches, prime_field, extension_field, curve, polynomial);
criterion_main!(benches);
