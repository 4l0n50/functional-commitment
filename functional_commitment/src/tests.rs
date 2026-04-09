#[cfg(test)]
mod tests {
    use ac_compiler::constraint_builder::ConstraintBuilder;
    use ac_compiler::error::Error;
    use ac_compiler::gate::GateType;
    use ac_compiler::variable::VariableType;
    use ac_compiler::{circuit::Circuit, variable::Variable};
    use ark_bn254::{Bn254, Fr};
    use ark_ff::bytes::ToBytes;
    use ark_ff::PrimeField;
    use ark_ff::{Field, One, Zero};
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
    use ark_std::test_rng;
    use blake2::Blake2s;
    use rand_chacha::ChaChaRng;

    use ac_compiler::circuit_compiler::{CircuitCompiler, VanillaCompiler};

    use crate::ac_bridge::AcCircuit;
    use crate::{diag_test, slt_test};

    type F = Fr;
    type ModifiedPC = ark_poly_commit::marlin_pc::MarlinKZG10<Bn254, DensePolynomial<Fr>>;
    type ModifiedMarlinInst = ModifiedMarlin<Fr, ModifiedPC, ModifiedFS<Blake2s, ChaChaRng>>;

    // -----------------------------------------------------------------------
    // Modified Marlin integration
    // -----------------------------------------------------------------------
    use ark_marlin::{Marlin as ModifiedMarlin, SimpleHashFiatShamirRng as ModifiedFS};
    use ark_poly::univariate::DensePolynomial;
    use ark_poly_commit::PolynomialCommitment;
    use pfr::{commit_statement, verify as pfr_verify, PfrPublicKey, PfrStatement};

    pub fn build_mux1_circuit<F: Field>(
        cb: &mut ConstraintBuilder<F>,
        a_val: F,
        b_val: F,
        c_val: F,
    ) -> Result<(), Error> {
        let a = cb.new_input_variable("a", a_val)?;
        let b = cb.new_input_variable("b", b_val)?;
        let c = cb.new_input_variable("c", c_val)?;
        let minus_one = cb.new_input_variable("minus_one", F::zero() - F::one())?;

        // b * c
        let bc = cb.enforce_constraint(&b, &c, GateType::Mul, VariableType::Witness)?;

        // a * c
        let ac = cb.enforce_constraint(&a, &c, GateType::Mul, VariableType::Witness)?;

        // - (a * c)
        let neg_ac =
            cb.enforce_constraint(&ac, &minus_one, GateType::Mul, VariableType::Witness)?;

        // (b * c) - (a * c)
        let bcac = cb.enforce_constraint(&bc, &neg_ac, GateType::Add, VariableType::Witness)?;

        // (b * c) - (a * c) + a
        let _ = cb.enforce_constraint(&bcac, &a, GateType::Add, VariableType::Output)?;

        Ok(())
    }

    pub fn enforce_square<F: Field>(
        cb: &mut ConstraintBuilder<F>,
        x: &Variable<F>,
    ) -> Result<Variable<F>, Error> {
        cb.enforce_constraint(&x, &x, GateType::Mul, VariableType::Witness)
    }

    pub fn enforce_x_7<F: Field>(
        cb: &mut ConstraintBuilder<F>,
        t: &Variable<F>,
    ) -> Result<Variable<F>, Error> {
        let t2 = enforce_square(cb, &t)?;
        let t4 = enforce_square(cb, &t2)?;
        let t6 = cb.enforce_constraint(&t2, &t4, GateType::Mul, VariableType::Witness)?;
        let t7 = cb.enforce_constraint(&t, &t6, GateType::Mul, VariableType::Witness)?;
        Ok(t7)
    }

    // A circuit that composes enforce_square() such that the output = x^4
    pub fn build_x4_circuit<F: Field>(
        cb: &mut ConstraintBuilder<F>,
        x_val: F,
    ) -> Result<(), Error> {
        let one = cb.new_input_variable("one", F::one())?;
        let x = cb.new_input_variable("x", x_val)?;

        let x2 = enforce_square(cb, &x)?;
        let x4 = enforce_square(cb, &x2)?;

        let _ = cb.enforce_constraint(&x4, &one, GateType::Mul, VariableType::Output)?;

        Ok(())
    }

    pub fn build_fibonacci_output_circuit<F: PrimeField>(
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

    fn fibonacci_pair<F: Field>(f0: F, f1: F, num_steps: usize) -> (F, F) {
        let mut prev = f0;
        let mut curr = f1;
        for _ in 0..num_steps {
            let next = prev + curr;
            prev = curr;
            curr = next;
        }
        (prev, curr)
    }

    /// The mimc7 circuit where nRounds = 2 and k = 2
    pub fn build_mimc7_circuit<F: PrimeField>(
        cb: &mut ConstraintBuilder<F>,
        x_val: F,
        c: Vec<F>,
    ) -> Result<(), Error> {
        let n_rounds = 2;

        let x = cb.new_input_variable("x", x_val)?;
        let k = cb.new_input_variable("k", F::from(2u64))?;

        let mut c_inputs: Vec<Variable<F>> = vec![];
        for (i, val) in c.iter().enumerate() {
            let input = cb.new_input_variable(format!("c{}", i).as_str(), *val)?;
            c_inputs.push(input);
        }

        let mut r;
        let t = cb.enforce_constraint(&x, &k, GateType::Add, VariableType::Witness)?;
        r = enforce_x_7(cb, &t)?;
        for i in 1..n_rounds {
            let r_plus_k = cb.enforce_constraint(&r, &k, GateType::Add, VariableType::Witness)?;
            let t = cb.enforce_constraint(
                &r_plus_k,
                &c_inputs[i],
                GateType::Add,
                VariableType::Witness,
            )?;
            r = enforce_x_7(cb, &t)?;
        }

        let _ = cb.enforce_constraint(&r, &k, GateType::Add, VariableType::Output)?;

        Ok(())
    }

    fn circuit_test_template<Func>(constraints: Func, inputs: &Vec<F>, outputs: &Vec<F>)
    where
        Func: FnOnce(&mut ConstraintBuilder<F>) -> Result<(), Error>,
    {
        let rng = &mut test_rng();
        let mut cb = ConstraintBuilder::<F>::new();

        let synthesized_circuit = Circuit::synthesize(constraints, &mut cb).unwrap();
        let (index_info, a, b, c) = VanillaCompiler::<F>::ac2tft(&synthesized_circuit);

        assert_eq!(true, index_info.check_domains_sizes::<F>());

        slt_test!(a, index_info.number_of_input_rows);
        slt_test!(b, index_info.number_of_input_rows);
        diag_test!(c);

        let nc = index_info.number_of_constraints;
        let nv = nc;
        let nz = index_info.number_of_non_zero_entries;
        let s = index_info.number_of_outputs;
        let setup_bound = 4 * nc.max(nz).max(cb.assignment.len());

        let universal_srs =
            ModifiedMarlinInst::universal_setup(setup_bound, setup_bound, setup_bound, rng)
                .unwrap();

        let circuit = AcCircuit::new(a, b, c, cb.assignment.clone(), index_info);
        let (pk, vk) = ModifiedMarlinInst::index(&universal_srs, circuit.clone(), s, rng).unwrap();

        let proof = ModifiedMarlinInst::prove(&pk, circuit, rng).unwrap();

        assert!(ModifiedMarlinInst::verify(&vk, inputs, outputs, &proof, rng).unwrap());
    }

    #[test]
    fn test_simple_circuit() {
        // Tests a circuit which encodes the equation x^3 + 2x + 5

        let x_val = F::from(7u64);

        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            let two = cb.new_input_variable("two", F::from(2u64))?;
            let five = cb.new_input_variable("five", F::from(5u64))?;
            let x = cb.new_input_variable("x", x_val)?;

            let x_square = cb.enforce_constraint(&x, &x, GateType::Mul, VariableType::Witness)?;
            let x_cube =
                cb.enforce_constraint(&x_square, &x, GateType::Mul, VariableType::Witness)?;

            let two_x = cb.enforce_constraint(&two, &x, GateType::Mul, VariableType::Witness)?;
            let x_qubed_plus_2x =
                cb.enforce_constraint(&x_cube, &two_x, GateType::Add, VariableType::Witness)?;

            // output = dec: 362, hex: 16A
            let _ = cb.enforce_constraint(
                &x_qubed_plus_2x,
                &five,
                GateType::Add,
                VariableType::Output,
            )?;

            Ok(())
        };

        let inputs = vec![F::from(2u64), F::from(5u64), x_val];
        let outputs = vec![F::from(362u64)];
        circuit_test_template(constraints, &inputs, &outputs);
    }

    #[test]
    fn test_mux1() {
        // Inputs: a, b, and c
        // Output (b - a) * c + a
        // If c = 0, outputs a
        // If c = 1, outputs b

        let a_val = F::from(123);
        let b_val = F::from(456);
        let c_val = F::from(1);
        let expected_output = b_val;

        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            build_mux1_circuit::<Fr>(cb, a_val, b_val, c_val)?;
            Ok(())
        };

        let inputs = vec![a_val, b_val, c_val, F::from(-1)];
        let outputs = vec![expected_output];
        circuit_test_template(constraints, &inputs, &outputs);

        let c_val = F::from(0);
        let expected_output = a_val;
        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            build_mux1_circuit::<Fr>(cb, a_val, b_val, c_val)?;
            Ok(())
        };

        let inputs = vec![a_val, b_val, c_val, F::from(-1)];
        let outputs = vec![expected_output];
        circuit_test_template(constraints, &inputs, &outputs);
    }

    #[test]
    fn test_composed_circuit() {
        let x_val = F::from(2u64);
        let expected_output = F::from(16u64);
        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            build_x4_circuit::<Fr>(cb, x_val)?;
            Ok(())
        };
        let inputs = vec![F::one(), x_val];
        let outputs = vec![expected_output];
        circuit_test_template(constraints, &inputs, &outputs);
    }

    #[test]
    fn test_fibonacci_output_medium() {
        let f0 = F::from(1u64);
        let f1 = F::from(1u64);
        let num_steps = 10;
        let (out_n, out_n1) = fibonacci_pair(f0, f1, num_steps);

        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            build_fibonacci_output_circuit(cb, f0, f1, num_steps)
        };

        let inputs = vec![F::one(), f0, f1];
        let outputs = vec![out_n, out_n1];
        circuit_test_template(constraints, &inputs, &outputs);
    }

    #[test]
    fn test_fibonacci_output_longer() {
        let f0 = F::from(2u64);
        let f1 = F::from(3u64);
        let num_steps = 24;
        let (out_n, out_n1) = fibonacci_pair(f0, f1, num_steps);

        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            build_fibonacci_output_circuit(cb, f0, f1, num_steps)
        };

        let inputs = vec![F::one(), f0, f1];
        let outputs = vec![out_n, out_n1];
        circuit_test_template(constraints, &inputs, &outputs);
    }

    fn registers_to_f(registers: &[u64; 4]) -> F {
        let mut writer = vec![];
        let _ = registers.write(&mut writer);
        F::from_le_bytes_mod_order(&writer)
    }

    fn build_cts() -> Vec<F> {
        let cts_bigints = vec![
            [0, 0, 0, 0],
            [
                3366560258570492133,
                10070564347787222493,
                15604622621500992217,
                3327803545572961123,
            ],
            [
                2961805725237629769,
                17895266365305129804,
                3244298544786782209,
                2431874893373010386,
            ],
        ];
        let mut cts = vec![];
        for c in cts_bigints.iter() {
            cts.push(registers_to_f(c));
        }
        cts
    }

    fn pow7(x: F) -> F {
        x * x * x * x * x * x * x
    }

    #[test]
    fn test_mimc7() {
        // The mimc7 circuit where nRounds = 2 and k = 2
        let x_val = F::from(2u64);
        let k = F::from(2u64);
        let cts = build_cts();
        let mut inputs = vec![x_val, k];
        for c in cts.iter() {
            inputs.push(*c);
        }
        let n_rounds = 2;

        let t = x_val + k;

        let mut r;
        r = pow7(t);

        for i in 1..n_rounds {
            let t = r + k + cts[i];
            r = pow7(t);
        }

        let result = r + k;
        let outputs = vec![result];

        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            build_mimc7_circuit(cb, x_val, cts)?;
            Ok(())
        };
        circuit_test_template(constraints, &inputs, &outputs);
    }

    // -----------------------------------------------------------------------
    // Modified Marlin + PFR combined test
    // -----------------------------------------------------------------------

    /// Run the modified Marlin proof (satisfiability) and the PFR proof
    /// (index structure) over the same committed index polynomials.
    fn circuit_test_with_pfr<Func>(constraints: Func, inputs: &[F], outputs: &[F])
    where
        Func: FnOnce(&mut ConstraintBuilder<F>) -> Result<(), Error>,
    {
        let rng = &mut test_rng();

        // 1. Build circuit with ac_compiler.
        let mut cb = ConstraintBuilder::<F>::new();
        let synthesized_circuit = Circuit::synthesize(constraints, &mut cb).unwrap();
        let (index_info, a, b, c) = VanillaCompiler::<F>::ac2tft(&synthesized_circuit);
        let assignment = cb.assignment.clone();
        let _ = (&a, &b, &c); // used only to build AcCircuit below

        let s = index_info.number_of_outputs;
        let t = index_info.number_of_input_rows;

        // 2. Compute the domain sizes that Marlin and the PFR will use.
        let n = GeneralEvaluationDomain::<F>::new(index_info.number_of_constraints)
            .unwrap()
            .size(); // |H| — next power of 2 ≥ num_constraints
        // For the PFR, m must be the domain size |K| (next power of 2 ≥ num_non_zero),
        // because Marlin's committed row/col polynomials are interpolated over |K| points.
        let m = GeneralEvaluationDomain::<F>::new(index_info.number_of_non_zero_entries)
            .unwrap()
            .size(); // |K|

        // 3. Single SRS: use a conservative bound large enough for both Marlin and PFR.
        let nc = index_info.number_of_constraints;
        let nz = index_info.number_of_non_zero_entries;
        let setup_bound = 8 * nc.max(nz).max(cb.assignment.len()).max(2 * m + 3);
        let srs =
            ModifiedMarlinInst::universal_setup(setup_bound, setup_bound, setup_bound, rng)
                .unwrap();

        // 4. Marlin index: produces committed row, col, row_col polynomials.
        let circuit = AcCircuit::new(a.clone(), b.clone(), c.clone(), assignment, index_info.clone());
        let (marlin_pk, marlin_vk) =
            ModifiedMarlinInst::index(&srs, circuit.clone(), s, rng).unwrap();

        // 5. PFR public key: reuse Marlin's (ck, vk) so both proofs share the SRS.
        let pfr_pk = shared_srs_pfr_pk(&srs, n, m, t, rng);

        // 6. Marlin proof of satisfiability.
        let proof = ModifiedMarlinInst::prove(&marlin_pk, circuit, rng).unwrap();
        assert!(
            ModifiedMarlinInst::verify(&marlin_vk, inputs, outputs, &proof, rng).unwrap(),
            "Marlin verification failed"
        );

        // 7. Build the PFR relation from the compiler's original A-matrix order.
        // PFR uses the transposed TFT convention: row = original column, col = original row.
        let mut pfr_row_of_m = Vec::new();
        let mut pfr_col_of_m = Vec::new();
        for (row_index, row) in a.iter().enumerate() {
            for &(_, col_index) in row {
                pfr_row_of_m.push(col_index);
                pfr_col_of_m.push(row_index);
            }
        }
        let pad_row = *pfr_row_of_m.last().expect("A must contain at least one non-zero entry");
        let pad_col = *pfr_col_of_m.last().expect("A must contain at least one non-zero entry");
        while pfr_row_of_m.len() < m {
            pfr_row_of_m.push(pad_row);
            pfr_col_of_m.push(pad_col);
        }

        let pfr_stmt = pfr::commit_statement(&pfr_pk, &pfr_row_of_m, &pfr_col_of_m, rng);

        // 8. PFR proof of index structure.
        let (pfr_proof, pfr_pub_inputs) =
            pfr::prove(&pfr_pk, &pfr_row_of_m, &pfr_col_of_m, &pfr_stmt, rng);

        // 9. PFR verification.
        assert!(
            pfr_verify(
                &pfr_pk,
                &pfr_proof,
                &pfr_pub_inputs.row_comm,
                &pfr_pub_inputs.col_comm,
                &pfr_pub_inputs.rowcol_comm,
            ),
            "PFR verification failed"
        );
    }

    fn marlin_statement_in_pfr_format(
        marlin_pk: &ark_marlin::IndexProverKey<F, ModifiedPC>,
        marlin_vk: &ark_marlin::IndexVerifierKey<F, ModifiedPC>,
    ) -> (Vec<usize>, Vec<usize>, PfrStatement<Bn254>) {
        use ark_poly_commit::LabeledCommitment;

        let domain_h = GeneralEvaluationDomain::<F>::new(marlin_pk.index.index_info.num_constraints)
            .unwrap();
        let (row_of_m, col_of_m) = marlin_pk.index.joint_arith.row_col_indices(domain_h);

        // Appendix-B PFR convention:
        //   row(κ^i) = ω^{r_i}, col(κ^i) = ω^{c_i}, with c_i >= r_i + t.
        // Marlin stores the transpose, so PFR row = Marlin col and PFR col = Marlin row.
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
        rng: &mut impl ark_std::rand::RngCore,
    ) -> PfrPublicKey<Bn254> {
        let pfr_max_degree = (n - 1).max(2 * m + 3).max(2 * m);
        let (ck, vk) = ModifiedPC::trim(srs, pfr_max_degree, 1, None).unwrap();
        PfrPublicKey::<Bn254>::with_keys(ck, vk, n, m, t, rng)
    }

    fn rows_cols_match_pfr_format(
        rows: &[usize],
        cols: &[usize],
        n: usize,
        t: usize,
    ) -> bool {
        rows.iter().zip(cols.iter()).all(|(&r, &c)| r < c && c >= t && c < n)
    }

    fn format_failure_message(rows: &[usize], cols: &[usize], n: usize, t: usize) -> String {
        let direct_ok = rows_cols_match_pfr_format(rows, cols, n, t);
        let swapped_ok = rows_cols_match_pfr_format(cols, rows, n, t);
        let sample = rows
            .iter()
            .zip(cols.iter())
            .take(8)
            .map(|(&r, &c)| format!("({r}, {c})"))
            .collect::<Vec<_>>()
            .join(", ");

        if direct_ok {
            "rows/cols already match PFR format".to_string()
        } else if swapped_ok {
            format!(
                "Marlin row/col look transposed for PFR: got [{sample}] but swapping them satisfies r < c and c >= t"
            )
        } else {
            format!(
                "Marlin row/col are not in PFR format, even after swapping: got [{sample}] with n={n}, t={t}"
            )
        }
    }

    #[test]
    fn test_simple_circuit_marlin_row_col_shape_for_pfr() {
        let x_val = F::from(7u64);
        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            let two = cb.new_input_variable("two", F::from(2u64))?;
            let five = cb.new_input_variable("five", F::from(5u64))?;
            let x = cb.new_input_variable("x", x_val)?;
            let x_square = cb.enforce_constraint(&x, &x, GateType::Mul, VariableType::Witness)?;
            let x_cube = cb.enforce_constraint(&x_square, &x, GateType::Mul, VariableType::Witness)?;
            let two_x = cb.enforce_constraint(&two, &x, GateType::Mul, VariableType::Witness)?;
            let x_cubed_plus_2x =
                cb.enforce_constraint(&x_cube, &two_x, GateType::Add, VariableType::Witness)?;
            cb.enforce_constraint(&x_cubed_plus_2x, &five, GateType::Add, VariableType::Output)?;
            Ok(())
        };

        let rng = &mut test_rng();
        let mut cb = ConstraintBuilder::<F>::new();
        let synthesized_circuit = Circuit::synthesize(constraints, &mut cb).unwrap();
        let (index_info, a, b, c) = VanillaCompiler::<F>::ac2tft(&synthesized_circuit);
        let assignment = cb.assignment.clone();
        let s = index_info.number_of_outputs;
        let nc = index_info.number_of_constraints;
        let nz = index_info.number_of_non_zero_entries;
        let setup_bound = 8 * nc.max(nz).max(assignment.len());
        let srs =
            ModifiedMarlinInst::universal_setup(setup_bound, setup_bound, setup_bound, rng).unwrap();
        let circuit = AcCircuit::new(a, b, c, assignment, index_info.clone());
        let (marlin_pk, marlin_vk) = ModifiedMarlinInst::index(&srs, circuit, s, rng).unwrap();

        let (rows, cols, _) = marlin_statement_in_pfr_format(&marlin_pk, &marlin_vk);
        assert!(
            rows_cols_match_pfr_format(
                &rows,
                &cols,
                GeneralEvaluationDomain::<F>::new(index_info.number_of_constraints)
                    .unwrap()
                    .size(),
                index_info.number_of_input_rows,
            ),
            "{}",
            format_failure_message(
                &rows,
                &cols,
                GeneralEvaluationDomain::<F>::new(index_info.number_of_constraints)
                    .unwrap()
                    .size(),
                index_info.number_of_input_rows,
            )
        );
    }

    #[test]
    fn test_simple_circuit_marlin_row_col_exponents_for_pfr() {
        let x_val = F::from(7u64);
        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            let two = cb.new_input_variable("two", F::from(2u64))?;
            let five = cb.new_input_variable("five", F::from(5u64))?;
            let x = cb.new_input_variable("x", x_val)?;
            let x_square = cb.enforce_constraint(&x, &x, GateType::Mul, VariableType::Witness)?;
            let x_cube =
                cb.enforce_constraint(&x_square, &x, GateType::Mul, VariableType::Witness)?;
            let two_x = cb.enforce_constraint(&two, &x, GateType::Mul, VariableType::Witness)?;
            let x_cubed_plus_2x =
                cb.enforce_constraint(&x_cube, &two_x, GateType::Add, VariableType::Witness)?;
            cb.enforce_constraint(&x_cubed_plus_2x, &five, GateType::Add, VariableType::Output)?;
            Ok(())
        };

        let rng = &mut test_rng();
        let mut cb = ConstraintBuilder::<F>::new();
        let synthesized_circuit = Circuit::synthesize(constraints, &mut cb).unwrap();
        let (index_info, a, b, c) = VanillaCompiler::<F>::ac2tft(&synthesized_circuit);
        let assignment = cb.assignment.clone();
        let s = index_info.number_of_outputs;
        let t = index_info.number_of_input_rows;
        let n = GeneralEvaluationDomain::<F>::new(index_info.number_of_constraints)
            .unwrap()
            .size();
        let nc = index_info.number_of_constraints;
        let nz = index_info.number_of_non_zero_entries;
        let setup_bound = 8 * nc.max(nz).max(assignment.len());
        let srs =
            ModifiedMarlinInst::universal_setup(setup_bound, setup_bound, setup_bound, rng).unwrap();
        let circuit = AcCircuit::new(a, b, c, assignment, index_info.clone());
        let (marlin_pk, _) = ModifiedMarlinInst::index(&srs, circuit, s, rng).unwrap();

        let domain_h = GeneralEvaluationDomain::<F>::new(n).unwrap();
        let h_elems: std::collections::BTreeMap<_, _> = domain_h
            .elements()
            .enumerate()
            .map(|(i, e)| (e, i))
            .collect();

        for (k, (&marlin_row_eval, &marlin_col_eval)) in marlin_pk
            .index
            .joint_arith
            .evals_on_K
            .row
            .evals
            .iter()
            .zip(marlin_pk.index.joint_arith.evals_on_K.col.evals.iter())
            .enumerate()
        {
            // Marlin stores the transpose:
            //   row = ω^{col_of_M}, col = ω^{row_of_M}.
            // The standalone PFR uses the TFT convention:
            //   r_i = col_of_M, c_i = row_of_M.
            let r_i = *h_elems
                .get(&marlin_row_eval)
                .expect("Marlin row evaluation must be an H element");
            let c_i = *h_elems
                .get(&marlin_col_eval)
                .expect("Marlin col evaluation must be an H element");

            assert!(
                r_i < c_i,
                "entry {k}: expected r_i < c_i but got r_i={r_i}, c_i={c_i}"
            );
            assert!(
                c_i >= t,
                "entry {k}: expected c_i >= t but got c_i={c_i}, t={t}"
            );
            assert!(
                c_i < n,
                "entry {k}: expected c_i < n but got c_i={c_i}, n={n}"
            );
            assert_eq!(
                marlin_row_eval,
                domain_h.element(r_i),
                "entry {k}: decoded r_i does not match row evaluation"
            );
            assert_eq!(
                marlin_col_eval,
                domain_h.element(c_i),
                "entry {k}: decoded c_i does not match col evaluation"
            );
        }
    }

    #[test]
    fn test_simple_circuit_with_shared_marlin_pfr() {
        let x_val = F::from(7u64);
        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            let two = cb.new_input_variable("two", F::from(2u64))?;
            let five = cb.new_input_variable("five", F::from(5u64))?;
            let x = cb.new_input_variable("x", x_val)?;
            let x_square = cb.enforce_constraint(&x, &x, GateType::Mul, VariableType::Witness)?;
            let x_cube = cb.enforce_constraint(&x_square, &x, GateType::Mul, VariableType::Witness)?;
            let two_x = cb.enforce_constraint(&two, &x, GateType::Mul, VariableType::Witness)?;
            let x_cubed_plus_2x =
                cb.enforce_constraint(&x_cube, &two_x, GateType::Add, VariableType::Witness)?;
            cb.enforce_constraint(&x_cubed_plus_2x, &five, GateType::Add, VariableType::Output)?;
            Ok(())
        };

        let rng = &mut test_rng();
        let mut cb = ConstraintBuilder::<F>::new();
        let synthesized_circuit = Circuit::synthesize(constraints, &mut cb).unwrap();
        let (index_info, a, b, c) = VanillaCompiler::<F>::ac2tft(&synthesized_circuit);
        let assignment = cb.assignment.clone();
        let s = index_info.number_of_outputs;
        let t = index_info.number_of_input_rows;
        let n = GeneralEvaluationDomain::<F>::new(index_info.number_of_constraints)
            .unwrap()
            .size();
        let nc = index_info.number_of_constraints;
        let nz = index_info.number_of_non_zero_entries;
        let setup_bound = 4 * nc.max(nz).max(assignment.len());
        let srs =
            ModifiedMarlinInst::universal_setup(setup_bound, setup_bound, setup_bound, rng).unwrap();

        let circuit = AcCircuit::new(a, b, c, assignment, index_info.clone());
        let (marlin_pk, marlin_vk) = ModifiedMarlinInst::index(&srs, circuit.clone(), s, rng).unwrap();
        let m = marlin_pk.index.joint_arith.evals_on_K.row.evals.len();

        let proof = ModifiedMarlinInst::prove(&marlin_pk, circuit, rng).unwrap();
        assert!(
            ModifiedMarlinInst::verify(
                &marlin_vk,
                &[F::from(2u64), F::from(5u64), x_val],
                &[F::from(362u64)],
                &proof,
                rng,
            )
            .unwrap()
        );

        let pfr_pk = shared_srs_pfr_pk(&srs, n, m, t, rng);
        let (rows, cols, stmt) = marlin_statement_in_pfr_format(&marlin_pk, &marlin_vk);
        assert!(
            rows_cols_match_pfr_format(&rows, &cols, n, t),
            "Marlin row/col are not in PFR format"
        );
        let (pfr_proof, pfr_pub_inputs) = pfr::prove(&pfr_pk, &rows, &cols, &stmt, rng);
        assert!(pfr_verify(
            &pfr_pk,
            &pfr_proof,
            &pfr_pub_inputs.row_comm,
            &pfr_pub_inputs.col_comm,
            &pfr_pub_inputs.rowcol_comm,
        ));
    }

    #[test]
    fn test_simple_circuit_marlin_eq7_sumcheck() {
        let x_val = F::from(7u64);
        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            let two = cb.new_input_variable("two", F::from(2u64))?;
            let five = cb.new_input_variable("five", F::from(5u64))?;
            let x = cb.new_input_variable("x", x_val)?;
            let x_square = cb.enforce_constraint(&x, &x, GateType::Mul, VariableType::Witness)?;
            let x_cube =
                cb.enforce_constraint(&x_square, &x, GateType::Mul, VariableType::Witness)?;
            let two_x = cb.enforce_constraint(&two, &x, GateType::Mul, VariableType::Witness)?;
            let x_cubed_plus_2x =
                cb.enforce_constraint(&x_cube, &two_x, GateType::Add, VariableType::Witness)?;
            cb.enforce_constraint(&x_cubed_plus_2x, &five, GateType::Add, VariableType::Output)?;
            Ok(())
        };

        let rng = &mut test_rng();
        let mut cb = ConstraintBuilder::<F>::new();
        let synthesized_circuit = Circuit::synthesize(constraints, &mut cb).unwrap();
        let (index_info, a, b, c) = VanillaCompiler::<F>::ac2tft(&synthesized_circuit);
        let assignment = cb.assignment.clone();
        let s = index_info.number_of_outputs;
        let t = index_info.number_of_input_rows;
        let n = GeneralEvaluationDomain::<F>::new(index_info.number_of_constraints)
            .unwrap()
            .size();
        let nc = index_info.number_of_constraints;
        let nz = index_info.number_of_non_zero_entries;
        let setup_bound = 4 * nc.max(nz).max(assignment.len());
        let srs =
            ModifiedMarlinInst::universal_setup(setup_bound, setup_bound, setup_bound, rng).unwrap();
        let circuit = AcCircuit::new(a, b, c, assignment, index_info);
        let (marlin_pk, marlin_vk) = ModifiedMarlinInst::index(&srs, circuit, s, rng).unwrap();
        let m = marlin_pk.index.joint_arith.evals_on_K.row.evals.len();

        let pfr_pk = PfrPublicKey::<Bn254>::with_keys(
            marlin_pk.committer_key.clone(),
            marlin_vk.verifier_key.clone(),
            n,
            m,
            t,
            rng,
        );
        let (rows, cols, stmt) = marlin_statement_in_pfr_format(&marlin_pk, &marlin_vk);
        let r1 = pfr::round_one(&pfr_pk, &rows, &cols, &stmt, rng);
        let beta = F::from(42u64);
        let r2 = pfr::round_two(&pfr_pk, &r1, beta, rng);

        let sum: F = (0..rows.len())
            .map(|i| {
                let ki = pfr_pk.k_domain.element(i);
                r2.polynomials
                    .iter()
                    .map(|p| p.polynomial().evaluate(&ki))
                    .sum::<F>()
            })
            .sum();

        assert_eq!(sum, F::zero(), "Marlin-derived relation fails equation (7)");
    }

    #[test]
    fn test_simple_circuit_marlin_h_and_m_consistency() {
        let x_val = F::from(7u64);
        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            let two = cb.new_input_variable("two", F::from(2u64))?;
            let five = cb.new_input_variable("five", F::from(5u64))?;
            let x = cb.new_input_variable("x", x_val)?;
            let x_square = cb.enforce_constraint(&x, &x, GateType::Mul, VariableType::Witness)?;
            let x_cube =
                cb.enforce_constraint(&x_square, &x, GateType::Mul, VariableType::Witness)?;
            let two_x = cb.enforce_constraint(&two, &x, GateType::Mul, VariableType::Witness)?;
            let x_cubed_plus_2x =
                cb.enforce_constraint(&x_cube, &two_x, GateType::Add, VariableType::Witness)?;
            cb.enforce_constraint(&x_cubed_plus_2x, &five, GateType::Add, VariableType::Output)?;
            Ok(())
        };

        let rng = &mut test_rng();
        let mut cb = ConstraintBuilder::<F>::new();
        let synthesized_circuit = Circuit::synthesize(constraints, &mut cb).unwrap();
        let (index_info, a, b, c) = VanillaCompiler::<F>::ac2tft(&synthesized_circuit);
        let assignment = cb.assignment.clone();
        let s = index_info.number_of_outputs;
        let t = index_info.number_of_input_rows;
        let n = GeneralEvaluationDomain::<F>::new(index_info.number_of_constraints)
            .unwrap()
            .size();
        let nc = index_info.number_of_constraints;
        let nz = index_info.number_of_non_zero_entries;
        let setup_bound = 4 * nc.max(nz).max(assignment.len());
        let srs =
            ModifiedMarlinInst::universal_setup(setup_bound, setup_bound, setup_bound, rng).unwrap();
        let circuit = AcCircuit::new(a, b, c, assignment, index_info);
        let (marlin_pk, marlin_vk) = ModifiedMarlinInst::index(&srs, circuit, s, rng).unwrap();
        let m = marlin_pk.index.joint_arith.evals_on_K.row.evals.len();

        let pfr_pk = PfrPublicKey::<Bn254>::with_keys(
            marlin_pk.committer_key.clone(),
            marlin_vk.verifier_key.clone(),
            n,
            m,
            t,
            rng,
        );
        let (rows, cols, stmt) = marlin_statement_in_pfr_format(&marlin_pk, &marlin_vk);
        let r1 = pfr::round_one(&pfr_pk, &rows, &cols, &stmt, rng);
        let beta = F::from(42u64);
        let r2 = pfr::round_two(&pfr_pk, &r1, beta, rng);

        let mults = pfr_pk.compute_multiplicities(&rows, &cols);
        for j in 0..n {
            let got = r1.polynomials[2].polynomial().evaluate(&pfr_pk.h_domain.element(j));
            assert_eq!(
                got,
                F::from(mults[j]),
                "m(ω^{j}) mismatch: expected multiplicity {}",
                mults[j]
            );
            assert_eq!(
                pfr_pk.h_poly.evaluate(&pfr_pk.h_domain.element(j)),
                pfr_pk.d_domain.element(j),
                "h(ω^{j}) != Δ^{j}"
            );
        }

        let big_delta = pfr_pk.big_delta();
        let delta_t_inv = big_delta.pow([t as u64]).inverse().unwrap();
        let zkh = if n == m {
            DensePolynomial::from_coefficients_slice(&[F::one()])
        } else {
            let steps = m / n;
            let scale_factor = F::from(n as u64) * F::from(m as u64).inverse().unwrap();
            let mut coeffs = vec![F::zero(); (steps - 1) * n + 1];
            for k in 0..steps {
                coeffs[k * n] = scale_factor;
            }
            DensePolynomial::from_coefficients_vec(coeffs)
        };

        for i in 0..m {
            let ki = pfr_pk.k_domain.element(i);
            let h = pfr_pk.h_poly.evaluate(&ki);
            let m_eval = r1.polynomials[2].polynomial().evaluate(&ki);
            let f5 = r2.polynomials[4].polynomial().evaluate(&ki);
            let zkh_eval = zkh.evaluate(&ki);
            assert_eq!(
                f5 * (beta + h) + m_eval * zkh_eval,
                F::zero(),
                "η⁴ / F5 identity failed at κ^{i}"
            );
            let r = r1.polynomials[0].polynomial().evaluate(&ki);
            let c = r1.polynomials[1].polynomial().evaluate(&ki);
            let f1 = r2.polynomials[0].polynomial().evaluate(&ki);
            let f2 = r2.polynomials[1].polynomial().evaluate(&ki);
            let f3 = r2.polynomials[2].polynomial().evaluate(&ki);
            let f4 = r2.polynomials[3].polynomial().evaluate(&ki);
            assert_eq!(f1 * (beta + r), F::one(), "F1 identity failed at κ^{i}");
            assert_eq!(f2 * (beta + c), F::one(), "F2 identity failed at κ^{i}");
            assert_eq!(
                f3 * (beta + c * (big_delta * r).inverse().unwrap()),
                F::one(),
                "F3 identity failed at κ^{i}"
            );
            assert_eq!(
                f4 * (beta + c * delta_t_inv),
                F::one(),
                "F4 identity failed at κ^{i}"
            );
        }
    }

    #[test]
    fn test_simple_circuit_with_pfr() {
        let x_val = F::from(7u64);
        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            let two = cb.new_input_variable("two", F::from(2u64))?;
            let five = cb.new_input_variable("five", F::from(5u64))?;
            let x = cb.new_input_variable("x", x_val)?;
            let x_square = cb.enforce_constraint(&x, &x, GateType::Mul, VariableType::Witness)?;
            let x_cube = cb.enforce_constraint(&x_square, &x, GateType::Mul, VariableType::Witness)?;
            let two_x = cb.enforce_constraint(&two, &x, GateType::Mul, VariableType::Witness)?;
            let x_cubed_plus_2x =
                cb.enforce_constraint(&x_cube, &two_x, GateType::Add, VariableType::Witness)?;
            cb.enforce_constraint(&x_cubed_plus_2x, &five, GateType::Add, VariableType::Output)?;
            Ok(())
        };
        // Modified Marlin's verify calls format_public_input which prepends a 1,
        // so pass inputs without the leading constant.
        let inputs = vec![F::from(2u64), F::from(5u64), x_val];
        let outputs = vec![F::from(362u64)];
        circuit_test_with_pfr(constraints, &inputs, &outputs);
    }

    #[test]
    fn test_fibonacci_output_with_pfr() {
        let f0 = F::from(1u64);
        let f1 = F::from(1u64);
        let num_steps = 16;
        let (out_n, out_n1) = fibonacci_pair(f0, f1, num_steps);

        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            build_fibonacci_output_circuit(cb, f0, f1, num_steps)
        };

        let inputs = vec![F::one(), f0, f1];
        let outputs = vec![out_n, out_n1];
        circuit_test_with_pfr(constraints, &inputs, &outputs);
    }

    // Regression test: shared SRS must be large enough for both Marlin and PFR.
    // pfr_max_degree = (n-1).max(2*m+3) where m = |K| (next power of 2 above nz).
    // A heuristic like 8*nc or AHPForR1CS::max_degree(nc, nv, nz) may be smaller
    // than 2*m+3 for larger circuits, causing TrimmingDegreeTooLarge at PFR key setup.
    #[test]
    fn test_fibonacci_shared_srs_large_enough_for_pfr() {
        use ark_marlin::ahp::AHPForR1CS;
        use ac_compiler::circuit_compiler::{CircuitCompiler, VanillaCompiler};

        let f0 = F::from(1u64);
        let f1 = F::from(1u64);
        let num_steps = 128; // large enough to expose the SRS sizing bug

        let rng = &mut test_rng();
        let mut cb = ConstraintBuilder::<F>::new();
        let synthesized =
            Circuit::synthesize(|cb| build_fibonacci_output_circuit(cb, f0, f1, num_steps), &mut cb)
                .unwrap();
        let (index_info, a, b, c) = VanillaCompiler::<F>::ac2tft(&synthesized);
        let assignment = cb.assignment.clone();

        let s = index_info.number_of_outputs;
        let t = index_info.number_of_input_rows;
        let nc = index_info.number_of_constraints;
        let nz = index_info.number_of_non_zero_entries;
        let n = GeneralEvaluationDomain::<F>::new(nc).unwrap().size();
        let m_bound = GeneralEvaluationDomain::<F>::new(nz).unwrap().size();
        let marlin_bound = AHPForR1CS::<F>::max_degree(nc, assignment.len(), nz).unwrap();
        let pfr_bound = (n - 1).max(2 * m_bound + 3);
        let setup_bound = marlin_bound.max(pfr_bound);

        let srs = ModifiedMarlinInst::universal_setup(setup_bound, setup_bound, setup_bound, rng)
            .unwrap();
        let circuit = AcCircuit::new(a, b, c, assignment, index_info.clone());
        let (marlin_pk, _marlin_vk) =
            ModifiedMarlinInst::index(&srs, circuit, s, rng).unwrap();
        let m = marlin_pk.index.joint_arith.evals_on_K.row.evals.len();

        // This must not panic with TrimmingDegreeTooLarge:
        let _pfr_pk = shared_srs_pfr_pk(&srs, n, m, t, rng);
    }

    #[test]
    fn test_simple_circuit_marlin_vs_pfr_statement_commitments() {
        let x_val = F::from(7u64);
        let constraints = |cb: &mut ConstraintBuilder<F>| -> Result<(), Error> {
            let two = cb.new_input_variable("two", F::from(2u64))?;
            let five = cb.new_input_variable("five", F::from(5u64))?;
            let x = cb.new_input_variable("x", x_val)?;
            let x_square = cb.enforce_constraint(&x, &x, GateType::Mul, VariableType::Witness)?;
            let x_cube =
                cb.enforce_constraint(&x_square, &x, GateType::Mul, VariableType::Witness)?;
            let two_x = cb.enforce_constraint(&two, &x, GateType::Mul, VariableType::Witness)?;
            let x_cubed_plus_2x =
                cb.enforce_constraint(&x_cube, &two_x, GateType::Add, VariableType::Witness)?;
            cb.enforce_constraint(&x_cubed_plus_2x, &five, GateType::Add, VariableType::Output)?;
            Ok(())
        };

        let rng = &mut test_rng();
        let mut cb = ConstraintBuilder::<F>::new();
        let synthesized_circuit = Circuit::synthesize(constraints, &mut cb).unwrap();
        let (index_info, a, b, c) = VanillaCompiler::<F>::ac2tft(&synthesized_circuit);
        let assignment = cb.assignment.clone();
        let s = index_info.number_of_outputs;
        let t = index_info.number_of_input_rows;
        let n = GeneralEvaluationDomain::<F>::new(index_info.number_of_constraints)
            .unwrap()
            .size();
        let nc = index_info.number_of_constraints;
        let nz = index_info.number_of_non_zero_entries;
        let setup_bound = 4 * nc.max(nz).max(assignment.len());
        let srs =
            ModifiedMarlinInst::universal_setup(setup_bound, setup_bound, setup_bound, rng).unwrap();
        let circuit = AcCircuit::new(a, b, c, assignment, index_info);
        let (marlin_pk, marlin_vk) = ModifiedMarlinInst::index(&srs, circuit, s, rng).unwrap();
        let m = marlin_pk.index.joint_arith.evals_on_K.row.evals.len();

        let pfr_pk = PfrPublicKey::<Bn254>::with_keys(
            marlin_pk.committer_key.clone(),
            marlin_vk.verifier_key.clone(),
            n,
            m,
            t,
            rng,
        );
        let (rows, cols, marlin_stmt) = marlin_statement_in_pfr_format(&marlin_pk, &marlin_vk);
        let pfr_stmt = commit_statement(&pfr_pk, &rows, &cols, rng);

        let marlin_row_evals: Vec<_> = (0..m)
            .map(|i| marlin_stmt.row_poly.polynomial().evaluate(&pfr_pk.k_domain.element(i)))
            .collect();
        let marlin_col_evals: Vec<_> = (0..m)
            .map(|i| marlin_stmt.col_poly.polynomial().evaluate(&pfr_pk.k_domain.element(i)))
            .collect();
        let marlin_rowcol_evals: Vec<_> = (0..m)
            .map(|i| marlin_stmt.rowcol_poly.polynomial().evaluate(&pfr_pk.k_domain.element(i)))
            .collect();
        let pfr_row_evals: Vec<_> = (0..m)
            .map(|i| pfr_stmt.row_poly.polynomial().evaluate(&pfr_pk.k_domain.element(i)))
            .collect();
        let pfr_col_evals: Vec<_> = (0..m)
            .map(|i| pfr_stmt.col_poly.polynomial().evaluate(&pfr_pk.k_domain.element(i)))
            .collect();
        let pfr_rowcol_evals: Vec<_> = (0..m)
            .map(|i| pfr_stmt.rowcol_poly.polynomial().evaluate(&pfr_pk.k_domain.element(i)))
            .collect();

        assert_eq!(marlin_row_evals, pfr_row_evals, "row K-evaluations differ");
        assert_eq!(marlin_col_evals, pfr_col_evals, "col K-evaluations differ");
        assert_eq!(
            marlin_rowcol_evals, pfr_rowcol_evals,
            "rowcol K-evaluations differ"
        );

        assert_ne!(
            marlin_stmt.row_poly.polynomial().coeffs,
            pfr_stmt.row_poly.polynomial().coeffs,
            "expected Marlin row polynomial to differ from fresh PFR row polynomial"
        );
        assert_ne!(
            marlin_stmt.col_poly.polynomial().coeffs,
            pfr_stmt.col_poly.polynomial().coeffs,
            "expected Marlin col polynomial to differ from fresh PFR col polynomial"
        );
        assert_ne!(
            marlin_stmt.rowcol_poly.polynomial().coeffs,
            pfr_stmt.rowcol_poly.polynomial().coeffs,
            "expected Marlin rowcol polynomial to differ from fresh PFR rowcol polynomial"
        );

        let (marlin_nohide_comms, _) = ModifiedPC::commit(
            &pfr_pk.ck,
            [&marlin_stmt.row_poly, &marlin_stmt.col_poly, &marlin_stmt.rowcol_poly]
                .iter()
                .copied(),
            None,
        )
        .unwrap();
        let (pfr_nohide_comms, _) = ModifiedPC::commit(
            &pfr_pk.ck,
            [&pfr_stmt.row_poly, &pfr_stmt.col_poly, &pfr_stmt.rowcol_poly]
                .iter()
                .copied(),
            None,
        )
        .unwrap();

        assert_ne!(
            marlin_nohide_comms[0].commitment(),
            pfr_nohide_comms[0].commitment(),
            "row commitments should differ when committing the two different polynomials without hiding"
        );
        assert_ne!(
            marlin_nohide_comms[1].commitment(),
            pfr_nohide_comms[1].commitment(),
            "col commitments should differ when committing the two different polynomials without hiding"
        );
        assert_ne!(
            marlin_nohide_comms[2].commitment(),
            pfr_nohide_comms[2].commitment(),
            "rowcol commitments should differ when committing the two different polynomials without hiding"
        );
    }
}
