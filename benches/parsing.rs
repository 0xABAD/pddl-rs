use criterion::{criterion_group, criterion_main, Criterion};
use pddl_rs::domain::{Domain};
use std::fs;

pub fn criterion_benchmark(c: &mut Criterion) {
    let s = fs::read_to_string("testdata/rover.pddl").unwrap();

    c.bench_function("parse parallel", |b| {
        b.iter(|| Domain::parse(&s));
    });

    c.bench_function("parse sequentially", |b| {
        b.iter(|| Domain::parse_seq(&s));
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
