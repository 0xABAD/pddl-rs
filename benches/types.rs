use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use pddl_rs::pddl::types::Types;
use std::fs;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("types get", move |b| {
        b.iter_batched(
            || {
                let mut t = Types::default();

                let foo = t.insert("foo");
                let bar = t.insert("bar");
                let baz = t.insert("baz");
                let fub = t.insert("fub");
                let quux = t.insert("quux");

                t.relate(foo, bar);
                t.relate(foo, baz);
                t.relate(baz, fub);
                t.relate(quux, foo);

                t
            },
            |t| t.get("Baz"),
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
