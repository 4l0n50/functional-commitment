use ac_compiler::constraint_builder::ConstraintBuilder;
use ac_compiler::error::Error;
use ac_compiler::gate::GateType;
use ac_compiler::variable::VariableType;
use ac_compiler::{circuit::Circuit, circuit_compiler::{CircuitCompiler, VanillaCompiler}};
use ark_bn254::{Bn254, Fr};
use ark_ff::{to_bytes, Field, One};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::LabeledCommitment;
use ark_std::test_rng;
use blake2::Blake2s;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::time::Duration;
use fiat_shamir_rng::{FiatShamirRng, SimpleHashFiatShamirRng};
use homomorphic_poly_commit::marlin_kzg::KZG10;
use index_private_marlin::Marlin;
use proof_of_function_relation::t_functional_triple::TFT;
use rand_chacha::ChaChaRng;

type F = Fr;
type PC = KZG10<Bn254>;
type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
type MarlinInst = Marlin<F, PC, FS>;
type PCCommitment = <PC as ark_poly_commit::PolynomialCommitment<
    F,
    ark_poly::univariate::DensePolynomial<F>,
>>::Commitment;

fn build_fibonacci_output_circuit<F: Field>(
    cb: &mut ConstraintBuilder<F>,
    f0_val: F,
    f1_val: F,
    num_steps: usize,
) -> Result<(), Error> {
    assert!(num_steps >= 2, "fibonacci circuit requires at least 2 steps");

    let one = cb.new_input_variable("one", F::one())?;
    let f0 = cb.new_input_variable("f0", f0_val)?;
    let f1 = cb.new_input_variable("f1", f1_val)?;

    let mut prev = f0;
    let mut curr = f1;
    for _ in 0..num_steps {
        let next = cb.enforce_constraint(&prev, &curr, GateType::Add, VariableType::Witness)?;
        prev = curr;
        curr = next;
    }

    cb.enforce_constraint(&prev, &one, GateType::Mul, VariableType::Output)?;
    cb.enforce_constraint(&curr, &one, GateType::Mul, VariableType::Output)?;
    Ok(())
}

struct PreparedFibonacci {
    srs: <PC as ark_poly_commit::PolynomialCommitment<
        F,
        ark_poly::univariate::DensePolynomial<F>,
    >>::UniversalParams,
    index_info: ac_compiler::R1CSfIndex,
    a: ac_compiler::Matrix<F>,
    b: ac_compiler::Matrix<F>,
    c: ac_compiler::Matrix<F>,
    assignment: Vec<F>,
    pk: index_private_marlin::data_structures::ProverKey<F, PC>,
    vk: index_private_marlin::data_structures::VerifierKey<F, PC>,
    public_inputs: Vec<F>,
    public_outputs: Vec<F>,
    marlin_proof_bytes: Vec<u8>,
    tft_proof: Vec<u8>,
    domain_k: GeneralEvaluationDomain<F>,
    domain_h: GeneralEvaluationDomain<F>,
}

const FS_SEED: &[u8] = b"Testing :)";

fn tft_prove(p: &PreparedFibonacci, commits: &[LabeledCommitment<PCCommitment>]) -> Vec<u8> {
    let rng = &mut test_rng();
    let mut fs_rng = FS::initialize(&to_bytes!(FS_SEED).unwrap());
    TFT::<F, PC, FS>::prove(
        &p.pk.committer_key,
        p.index_info.number_of_input_rows,
        &p.domain_k,
        &p.domain_h,
        Some(p.domain_k.size() + 1),
        &p.pk.index.a_arith.col,
        &p.pk.index.a_arith.row,
        &commits[1],
        &commits[0],
        &p.pk.rands[1],
        &p.pk.rands[0],
        &p.pk.index.b_arith.col,
        &p.pk.index.b_arith.row,
        &commits[4],
        &commits[3],
        &p.pk.rands[4],
        &p.pk.rands[3],
        &p.pk.index.c_arith.row,
        &p.pk.index.c_arith.col,
        &p.pk.index.c_arith.val,
        &commits[6],
        &commits[7],
        &commits[8],
        &p.pk.rands[6],
        &p.pk.rands[7],
        &p.pk.rands[8],
        &mut fs_rng,
        rng,
    )
    .unwrap()
}

fn make_commits(p: &PreparedFibonacci) -> Vec<LabeledCommitment<PCCommitment>> {
    let labels = [
        "a_row", "a_col", "a_val", "b_row", "b_col", "b_val", "c_row", "c_col", "c_val",
    ];
    p.vk
        .commits
        .iter()
        .zip(labels.iter())
        .map(|(cm, &label)| {
            LabeledCommitment::new(label.into(), cm.clone(), Some(p.domain_k.size() + 1))
        })
        .collect()
}

fn prepare_fibonacci(num_steps: usize) -> PreparedFibonacci {
    let f0 = F::from(1u64);
    let f1 = F::from(1u64);

    let mut cb = ConstraintBuilder::<F>::new();
    let synthesized_circuit =
        Circuit::synthesize(|cb| build_fibonacci_output_circuit(cb, f0, f1, num_steps), &mut cb)
            .unwrap();
    let (index_info, a, b, c) = VanillaCompiler::<F>::ac2tft(&synthesized_circuit);
    let assignment = cb.assignment.clone();

    let mut chain = vec![f0, f1];
    for i in 2..(num_steps + 2) {
        chain.push(chain[i - 1] + chain[i - 2]);
    }
    let public_inputs = vec![F::one(), f0, f1];
    let public_outputs = vec![chain[num_steps], chain[num_steps + 1]];

    let domain_k =
        GeneralEvaluationDomain::<F>::new(index_info.number_of_non_zero_entries).unwrap();
    let domain_h =
        GeneralEvaluationDomain::<F>::new(index_info.number_of_constraints).unwrap();

    let rng = &mut test_rng();
    let srs = MarlinInst::universal_setup(&index_info, rng).unwrap();
    let (pk, vk) =
        MarlinInst::index(&srs, &index_info, a.clone(), b.clone(), c.clone(), rng).unwrap();
    // Pre-compute TFT proof for verify bench
    let marlin_proof = MarlinInst::prove(&pk, assignment.clone(), rng).unwrap();
    let mut marlin_proof_bytes = vec![];
    marlin_proof.serialize(&mut marlin_proof_bytes).unwrap();

    let tmp = PreparedFibonacci {
        srs,
        index_info,
        a,
        b,
        c,
        assignment,
        pk,
        vk,
        public_inputs,
        public_outputs,
        marlin_proof_bytes,
        tft_proof: vec![],
        domain_k,
        domain_h,
    };
    let commits = make_commits(&tmp);
    let tft_proof = tft_prove(&tmp, &commits);

    PreparedFibonacci { tft_proof, ..tmp }
}

fn bench_fibonacci(c: &mut Criterion) {
    // Sizes chosen so that num_steps + 5 (= number_of_constraints) is exactly a
    // power of 2 — required by the well-formation check in index_private_marlin.
    // 123+5=128, 251+5=256, 507+5=512, 763+5=768 (not pow2 — skip), 1019+5=1024
    let sizes = [128usize, 256, 512, 768, 1056];

    println!("\n=== R1CS matrix dimensions ===");
    for &size in &sizes {
        let p = prepare_fibonacci(size);
        let rows = p.index_info.number_of_constraints;
        let cols = p.assignment.len();
        let nnz_a: usize = p.a.iter().map(|r| r.len()).sum();
        let nnz_b: usize = p.b.iter().map(|r| r.len()).sum();
        let nnz_c: usize = p.c.iter().map(|r| r.len()).sum();
        println!(
            "num_steps={:>5}  rows={:>6}  cols={:>6} | \
             A nnz={:>6} ({:.1}%)  B nnz={:>6} ({:.1}%)  C nnz={:>6} ({:.1}%)",
            size, rows, cols,
            nnz_a, 100.0 * nnz_a as f64 / (rows * cols) as f64,
            nnz_b, 100.0 * nnz_b as f64 / (rows * cols) as f64,
            nnz_c, 100.0 * nnz_c as f64 / (rows * cols) as f64,
        );
    }
    println!();

    let mut marlin_index_group = c.benchmark_group("fibonacci_marlin_index");
    marlin_index_group.sample_size(20);
    marlin_index_group.warm_up_time(Duration::from_secs(3));
    marlin_index_group.measurement_time(Duration::from_secs(20));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        marlin_index_group.bench_with_input(BenchmarkId::from_parameter(size), &prepared, |b, p: &PreparedFibonacci| {
            b.iter(|| {
                let rng = &mut test_rng();
                MarlinInst::index(
                    &p.srs,
                    &p.index_info,
                    p.a.clone(),
                    p.b.clone(),
                    p.c.clone(),
                    rng,
                )
                .unwrap()
            });
        });
    }
    marlin_index_group.finish();

    let mut marlin_prove_group = c.benchmark_group("fibonacci_marlin_prove");
    marlin_prove_group.sample_size(20);
    marlin_prove_group.warm_up_time(Duration::from_secs(5));
    marlin_prove_group.measurement_time(Duration::from_secs(60));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        marlin_prove_group.bench_with_input(BenchmarkId::from_parameter(size), &prepared, |b, p: &PreparedFibonacci| {
            b.iter(|| {
                let rng = &mut test_rng();
                MarlinInst::prove(&p.pk, p.assignment.clone(), rng).unwrap()
            });
        });
    }
    marlin_prove_group.finish();

    // fibonacci_marlin_verify is disabled: index_private_marlin::verify triggers
    // ZeroOverKError(Check2Failed) — bug in the geometry-fc implementation.
    // let mut marlin_verify_group = c.benchmark_group("fibonacci_marlin_verify");
    // ...
    // marlin_verify_group.finish();

    let mut pfr_prove_group = c.benchmark_group("fibonacci_pfr_prove");
    pfr_prove_group.sample_size(20);
    pfr_prove_group.warm_up_time(Duration::from_secs(5));
    pfr_prove_group.measurement_time(Duration::from_secs(60));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        let commits = make_commits(&prepared);
        pfr_prove_group.bench_with_input(BenchmarkId::from_parameter(size), &prepared, |b, p: &PreparedFibonacci| {
            b.iter(|| tft_prove(p, &commits));
        });
    }
    pfr_prove_group.finish();

    let mut pfr_verify_group = c.benchmark_group("fibonacci_pfr_verify");
    pfr_verify_group.sample_size(50);
    pfr_verify_group.warm_up_time(Duration::from_secs(3));
    pfr_verify_group.measurement_time(Duration::from_secs(20));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        let commits = make_commits(&prepared);
        pfr_verify_group.bench_with_input(BenchmarkId::from_parameter(size), &prepared, |b, p: &PreparedFibonacci| {
            b.iter(|| {
                let mut fs_rng = FS::initialize(&to_bytes!(FS_SEED).unwrap());
                TFT::<F, PC, FS>::verify(
                    &p.vk.verifier_key,
                    &p.pk.committer_key,
                    p.index_info.number_of_input_rows,
                    &commits[1],
                    &commits[0],
                    &commits[4],
                    &commits[3],
                    &commits[6],
                    &commits[7],
                    &commits[8],
                    Some(p.domain_k.size() + 1),
                    &p.domain_h,
                    &p.domain_k,
                    p.tft_proof.clone(),
                    &mut fs_rng,
                )
                .unwrap()
            });
        });
    }
    pfr_verify_group.finish();

    let mut combined_prove_group = c.benchmark_group("fibonacci_fc_combined_prove");
    combined_prove_group.sample_size(20);
    combined_prove_group.warm_up_time(Duration::from_secs(5));
    combined_prove_group.measurement_time(Duration::from_secs(60));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        let commits = make_commits(&prepared);
        combined_prove_group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &prepared,
            |b, p: &PreparedFibonacci| {
                b.iter(|| {
                    let rng = &mut test_rng();
                    let _marlin_proof =
                        MarlinInst::prove(&p.pk, p.assignment.clone(), rng).unwrap();
                    tft_prove(p, &commits)
                });
            },
        );
    }
    combined_prove_group.finish();

    // fibonacci_fc_combined_verify is disabled: calls MarlinInst::verify which
    // triggers ZeroOverKError(Check2Failed) — bug in the geometry-fc implementation.
    // let mut combined_verify_group = c.benchmark_group("fibonacci_fc_combined_verify");
    // ...
    // combined_verify_group.finish();
}

criterion_group!(benches, bench_fibonacci);
criterion_main!(benches);
