use criterion::{black_box, criterion_group, criterion_main, Criterion};
use in_mem_kv_store::key::Key;
use in_mem_kv_store::value::Value;
use in_mem_kv_store::KeyValueStore;

// These benchmarks measure the performance of the get, put, and delete, methods
// of the KeyValueStore implementation. They use the bench_function method from
// the criterion crate to run the methods with a fixed set of input values and
// measure the time taken to execute each method.

// To run these benchmarks, you can use the cargo bench command.
// This will run the benchmarks and output the results, including the
// average time taken to execute each method.
fn bench_in_memory_key_value_store(c: &mut Criterion) {
  let mut kvs = KeyValueStore::new();

  c.bench_function("put", |b| {
    b.iter(|| {
      kvs.put(
        black_box(&Key::from("key")),
        black_box(&Value::from("value")),
      );
    });
  });

  c.bench_function("get", |b| {
    b.iter(|| {
      kvs.get(black_box(&Key::from("key")));
    });
  });

  c.bench_function("delete", |b| {
    b.iter(|| {
      kvs.delete(black_box(&Key::from("key")));
    });
  });
}

criterion_group!(benches, bench_in_memory_key_value_store);
criterion_main!(benches);
