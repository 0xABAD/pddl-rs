use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use pddl_rs::{ tokens::{TokenError, Tokenizer}, pddl::scanner};
use std::fs;

pub fn criterion_benchmark(c: &mut Criterion) {
    let src = fs::read_to_string("testdata/blocks.pddl").unwrap();

    let s = src.clone();
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

    let s = src.clone();
    c.bench_function("scanner", |b| {
        b.iter(|| {
            scanner::scan(&s);
        });
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
