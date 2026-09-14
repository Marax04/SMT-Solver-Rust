use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use smt_mba::Gf2Matrix;

fn build_band_matrix(n: usize) -> Gf2Matrix {
    let cols = 2 * n;
    let mut mat = Gf2Matrix::new(n, cols);
    for i in 0..n {
        mat.set(i, i, true);
        if i + 1 < n {
            mat.set(i, i + 1, true);
        }
        if i + 3 < n {
            mat.set(i, i + 3, true);
        }
        mat.set(i, n + i, true);
    }
    mat
}

fn bench_gf2_rref(c: &mut Criterion) {
    let mut group = c.benchmark_group("GF2_Matrix_RREF");
    for &n in &[64, 128, 256, 512] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &size| {
            b.iter(|| {
                let mut mat = build_band_matrix(size);
                let pivots = mat.rref();
                black_box(pivots)
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_gf2_rref);
criterion_main!(benches);
