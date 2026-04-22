use ac_compiler::constraint_builder::ConstraintBuilder;
use ac_compiler::error::Error;
use ac_compiler::gate::GateType;
use ac_compiler::variable::VariableType;
use ac_compiler::{circuit::Circuit, circuit_compiler::{CircuitCompiler, VanillaCompiler}};
use ark_bn254::{Bn254, Fr};
use ark_ff::{Field, One};
use ark_marlin::{ahp::AHPForR1CS, Marlin as ModifiedMarlin, SimpleHashFiatShamirRng as ModifiedFS};
use ark_serialize::CanonicalSerialize;
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::{LabeledCommitment, PolynomialCommitment};
use ark_std::test_rng;
use blake2::Blake2s;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::time::Duration;
use functional_commitment::ac_bridge::AcCircuit;
use pfr::{PfrProof, PfrPublicInputs, PfrPublicKey, PfrStatement};
use rand_chacha::ChaChaRng;

type F = Fr;
type ModifiedPC = ark_poly_commit::marlin_pc::MarlinKZG10<Bn254, DensePolynomial<Fr>>;
type ModifiedMarlinInst = ModifiedMarlin<Fr, ModifiedPC, ModifiedFS<Blake2s, ChaChaRng>>;

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

fn marlin_statement_in_pfr_format(
    marlin_pk: &ark_marlin::IndexProverKey<F, ModifiedPC>,
    marlin_vk: &ark_marlin::IndexVerifierKey<F, ModifiedPC>,
) -> (Vec<usize>, Vec<usize>, PfrStatement<Bn254>) {
    let domain_h =
        GeneralEvaluationDomain::<F>::new(marlin_pk.index.index_info.num_constraints).unwrap();
    let (row_of_m, col_of_m) = marlin_pk.index.joint_arith.row_col_indices(domain_h);

    let pfr_rows = col_of_m;
    let pfr_cols = row_of_m;

    let stmt = PfrStatement::from_existing(
        marlin_pk.index.joint_arith.row.clone(),
        marlin_pk.index.joint_arith.col.clone(),
        marlin_pk.index.joint_arith.row_col.clone(),
        LabeledCommitment::new("row".into(), marlin_vk.index_comms[0].clone(), None),
        LabeledCommitment::new("col".into(), marlin_vk.index_comms[1].clone(), None),
        LabeledCommitment::new("row_col".into(), marlin_vk.index_comms[4].clone(), None),
        marlin_pk.index_comm_rands[0].clone(),
        marlin_pk.index_comm_rands[1].clone(),
        marlin_pk.index_comm_rands[4].clone(),
    );

    (pfr_rows, pfr_cols, stmt)
}

fn shared_srs_pfr_pk(
    srs: &<ModifiedPC as PolynomialCommitment<F, DensePolynomial<F>>>::UniversalParams,
    n: usize,
    m: usize,
    t: usize,
) -> PfrPublicKey<Bn254> {
    let pfr_max_degree = (n - 1).max(2 * m + 3);
    let (ck, vk) = ModifiedPC::trim(srs, pfr_max_degree, 1, None).unwrap();
    let mut rng = test_rng();
    PfrPublicKey::<Bn254>::with_keys(ck, vk, n, m, t, &mut rng)
}

struct PreparedFibonacci {
    srs: <ModifiedPC as PolynomialCommitment<F, DensePolynomial<F>>>::UniversalParams,
    marlin_pk: ark_marlin::IndexProverKey<F, ModifiedPC>,
    marlin_vk: ark_marlin::IndexVerifierKey<F, ModifiedPC>,
    circuit: AcCircuit<F>,
    public_inputs: Vec<F>,
    public_outputs: Vec<F>,
    pfr_pk: PfrPublicKey<Bn254>,
    pfr_rows: Vec<usize>,
    pfr_cols: Vec<usize>,
    pfr_stmt: PfrStatement<Bn254>,
    pfr_proof: PfrProof<Bn254>,
    pfr_public_inputs: PfrPublicInputs<Bn254>,
    marlin_proof_bytes: Vec<u8>,
    num_outputs: usize,
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

    let s = index_info.number_of_outputs;
    let t = index_info.number_of_input_rows;
    let n = GeneralEvaluationDomain::<F>::new(index_info.number_of_constraints)
        .unwrap()
        .size();
    let nc = index_info.number_of_constraints;
    let nz = index_info.number_of_non_zero_entries;
    // m is the K-domain size: next power of 2 above nz (same as what Marlin uses internally).
    let m_bound = GeneralEvaluationDomain::<F>::new(nz).unwrap().size();
    let marlin_bound = AHPForR1CS::<F>::max_degree(nc, assignment.len(), nz).unwrap();
    let pfr_bound = (n - 1).max(2 * m_bound + 3);
    let setup_bound = marlin_bound.max(pfr_bound);

    let mut chain = vec![f0, f1];
    for i in 2..(num_steps + 2) {
        chain.push(chain[i - 1] + chain[i - 2]);
    }
    let public_inputs = vec![F::one(), f0, f1];
    let public_outputs = vec![chain[num_steps], chain[num_steps + 1]];

    let mut rng = test_rng();
    let srs =
        ModifiedMarlinInst::universal_setup(setup_bound, setup_bound, setup_bound, &mut rng)
            .unwrap();
    let circuit = AcCircuit::new(a, b, c, assignment, index_info.clone());
    let (marlin_pk, marlin_vk) =
        ModifiedMarlinInst::index(&srs, circuit.clone(), s, &mut rng).unwrap();
    let m = marlin_pk.index.joint_arith.evals_on_K.row.evals.len();

    let pfr_pk = shared_srs_pfr_pk(&srs, n, m, t);
    let (pfr_rows, pfr_cols, pfr_stmt) = marlin_statement_in_pfr_format(&marlin_pk, &marlin_vk);
    let marlin_proof = ModifiedMarlinInst::prove(&marlin_pk, circuit.clone(), &mut rng).unwrap();
    let mut marlin_proof_bytes = Vec::new();
    marlin_proof.serialize(&mut marlin_proof_bytes).unwrap();
    let (pfr_proof, pfr_public_inputs) =
        pfr::prove(&pfr_pk, &pfr_rows, &pfr_cols, &pfr_stmt, &mut rng);

    PreparedFibonacci {
        srs,
        marlin_pk,
        marlin_vk,
        circuit,
        public_inputs,
        public_outputs,
        pfr_pk,
        pfr_rows,
        pfr_cols,
        pfr_stmt,
        pfr_proof,
        pfr_public_inputs,
        marlin_proof_bytes,
        num_outputs: s,
    }
}

fn bench_fibonacci(c: &mut Criterion) {
    let sizes = [128usize, 256, 512, 768, 1056];

    let mut marlin_index_group = c.benchmark_group("fibonacci_marlin_index");
    marlin_index_group.sample_size(20);
    marlin_index_group.warm_up_time(Duration::from_secs(3));
    marlin_index_group.measurement_time(Duration::from_secs(20));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        marlin_index_group.bench_with_input(BenchmarkId::from_parameter(size), &prepared, |b, p| {
            b.iter(|| {
                let mut rng = test_rng();
                let (_pk, _vk) =
                    ModifiedMarlinInst::index(&p.srs, p.circuit.clone(), p.num_outputs, &mut rng)
                        .unwrap();
            });
        });
    }
    marlin_index_group.finish();

    let mut marlin_group = c.benchmark_group("fibonacci_marlin_prove");
    marlin_group.sample_size(20);
    marlin_group.warm_up_time(Duration::from_secs(5));
    marlin_group.measurement_time(Duration::from_secs(60));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        marlin_group.bench_with_input(BenchmarkId::from_parameter(size), &prepared, |b, p| {
            b.iter(|| {
                let mut rng = test_rng();
                ModifiedMarlinInst::prove(&p.marlin_pk, p.circuit.clone(), &mut rng).unwrap()
            });
        });
    }
    marlin_group.finish();

    let mut marlin_verify_group = c.benchmark_group("fibonacci_marlin_verify");
    marlin_verify_group.sample_size(50);
    marlin_verify_group.warm_up_time(Duration::from_secs(3));
    marlin_verify_group.measurement_time(Duration::from_secs(20));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        marlin_verify_group.bench_with_input(BenchmarkId::from_parameter(size), &prepared, |b, p| {
            b.iter(|| {
                let mut rng = test_rng();
                let proof: ark_marlin::Proof<F, ModifiedPC> =
                    ark_serialize::CanonicalDeserialize::deserialize(
                        p.marlin_proof_bytes.as_slice(),
                    )
                    .unwrap();
                let ok = ModifiedMarlinInst::verify(
                    &p.marlin_vk,
                    &p.public_inputs,
                    &p.public_outputs,
                    &proof,
                    &mut rng,
                )
                .unwrap();
                assert!(ok);
            });
        });
    }
    marlin_verify_group.finish();

    let mut pfr_group = c.benchmark_group("fibonacci_pfr_prove");
    pfr_group.sample_size(20);
    pfr_group.warm_up_time(Duration::from_secs(5));
    pfr_group.measurement_time(Duration::from_secs(60));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        pfr_group.bench_with_input(BenchmarkId::from_parameter(size), &prepared, |b, p| {
            b.iter(|| {
                let mut rng = test_rng();
                pfr::prove(&p.pfr_pk, &p.pfr_rows, &p.pfr_cols, &p.pfr_stmt, &mut rng)
            });
        });
    }
    pfr_group.finish();

    let mut pfr_verify_group = c.benchmark_group("fibonacci_pfr_verify");
    pfr_verify_group.sample_size(50);
    pfr_verify_group.warm_up_time(Duration::from_secs(3));
    pfr_verify_group.measurement_time(Duration::from_secs(20));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        pfr_verify_group.bench_with_input(BenchmarkId::from_parameter(size), &prepared, |b, p| {
            b.iter(|| {
                let ok = pfr::verify(
                    &p.pfr_pk,
                    &p.pfr_proof,
                    &p.pfr_public_inputs.row_comm,
                    &p.pfr_public_inputs.col_comm,
                    &p.pfr_public_inputs.rowcol_comm,
                );
                assert!(ok);
            });
        });
    }
    pfr_verify_group.finish();

    let mut combined_group = c.benchmark_group("fibonacci_fc_combined_prove");
    combined_group.sample_size(20);
    combined_group.warm_up_time(Duration::from_secs(5));
    combined_group.measurement_time(Duration::from_secs(60));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        combined_group.bench_with_input(BenchmarkId::from_parameter(size), &prepared, |b, p| {
            b.iter(|| {
                let mut rng = test_rng();
                let _marlin_proof =
                    ModifiedMarlinInst::prove(&p.marlin_pk, p.circuit.clone(), &mut rng).unwrap();
                let (_pfr_proof, _public_inputs) =
                    pfr::prove(&p.pfr_pk, &p.pfr_rows, &p.pfr_cols, &p.pfr_stmt, &mut rng);
            });
        });
    }
    combined_group.finish();

    let mut combined_verify_group = c.benchmark_group("fibonacci_fc_combined_verify");
    combined_verify_group.sample_size(50);
    combined_verify_group.warm_up_time(Duration::from_secs(3));
    combined_verify_group.measurement_time(Duration::from_secs(20));
    for &size in &sizes {
        let prepared = prepare_fibonacci(size);
        combined_verify_group.bench_with_input(BenchmarkId::from_parameter(size), &prepared, |b, p| {
            b.iter(|| {
                let mut rng = test_rng();
                let proof: ark_marlin::Proof<F, ModifiedPC> =
                    ark_serialize::CanonicalDeserialize::deserialize(p.marlin_proof_bytes.as_slice()).unwrap();
                let ok = ModifiedMarlinInst::verify(&p.marlin_vk, &p.public_inputs, &p.public_outputs, &proof, &mut rng).unwrap();
                assert!(ok);
                let ok = pfr::verify(&p.pfr_pk, &p.pfr_proof, &p.pfr_public_inputs.row_comm, &p.pfr_public_inputs.col_comm, &p.pfr_public_inputs.rowcol_comm);
                assert!(ok);
            });
        });
    }
    combined_verify_group.finish();
}

criterion_group!(benches, bench_fibonacci);
criterion_main!(benches);
