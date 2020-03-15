use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pddl_rs::pddl;
use std::fs;

pub fn criterion_benchmark(c: &mut Criterion) {
    let s = fs::read_to_string("testdata/rover.pddl").unwrap();

    c.bench_function("parse parallel", |b| {
        b.iter(|| match pddl::Domain::parse(black_box(&s)) {
            Err(e) => panic!("Could not parse domain: {:?}", e),
            _ => (),
        });
    });

    c.bench_function("parse sequentially", |b| {
        b.iter(|| match pddl::Domain::parse_seq(black_box(&s)) {
            Err(e) => panic!("Could not parse domain: {:?}", e),
            _ => (),
        });
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
