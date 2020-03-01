use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use pddl_rs::tokens::{TokenError, Tokenizer};
use std::fs;

pub fn criterion_benchmark(c: &mut Criterion) {
    let s = fs::read_to_string("testdata/blocks.pddl").unwrap();

    c.bench_function("tokenize", move |b| {
        b.iter_batched(
            || Tokenizer::new(&s),
            |mut tz| loop {
                match tz.next() {
                    Ok(_) => continue,
                    Err(TokenError::EndOfInput { line: _, col: _ }) => break,
                    Err(e) => panic!("Unexpected error during tokenization: {:#?}", e),
                }
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
