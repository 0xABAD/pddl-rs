use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use pddl_rs::pddl::scanner;
use std::fs;

pub fn criterion_benchmark(c: &mut Criterion) {
    let src = fs::read_to_string("testdata/blocks.pddl").unwrap();

    c.bench_function("scanner", |b| {
        b.iter_batched(
            || scanner::Scanner::new(&src),
            |mut sc| while let Some(_) = sc.next() {},
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
