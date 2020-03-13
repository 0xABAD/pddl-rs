use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use pddl_rs::pddl::types::Types;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("types get", move |b| {
        b.iter_batched(
            || {
                let mut t = Types::default();

                t.insert("foo");
                t.insert("bar");
                t.insert("baz");
                t.insert("fub");
                t.insert("quux");
                t.insert("who");
                t.insert("are");
                t.insert("you");
                t.insert("said");
                t.insert("the");
                t.insert("catepillar");
                t.insert("object");

                t
            },
            |t| t.get("object"),
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
