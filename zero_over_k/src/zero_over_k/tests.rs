#[cfg(test)]
mod test {
    use crate::{
        error::{to_pc_error, Error},
        virtual_oracle::generic_shifting_vo::{presets, GenericShiftingVO},
        zero_over_k::ZeroOverK,
    };
    use ark_bn254::{Bn254, Fr};
    use ark_ff::Field;
    use ark_ff::One;
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain,
        UVPolynomial,
    };
    use ark_poly_commit::{LabeledCommitment, LabeledPolynomial, PolynomialCommitment};
    use ark_std::{rand::thread_rng, test_rng};
    use blake2::Blake2s;
    use fiat_shamir_rng::SimpleHashFiatShamirRng;
    use homomorphic_poly_commit::marlin_kzg::KZG10;
    use rand_chacha::ChaChaRng;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;

    type F = Fr;
    type PC = KZG10<Bn254>;

    #[test]
    fn test_zero_over_k_inverse_check_oracle() {
        let m = 8;
        let rng = &mut test_rng();
        let domain_k = GeneralEvaluationDomain::<F>::new(m).unwrap();

        let max_degree = 20;
        let max_hiding = 1;

        let enforced_hiding_bound = Some(1);
        let enforced_degree_bound = 14;

        let pp = PC::setup(max_degree, None, rng).unwrap();
        let (ck, vk) = PC::trim(
            &pp,
            max_degree,
            max_hiding,
            Some(&[2, enforced_degree_bound]),
        )
        .unwrap();

        // Step 1: choose a random polynomial
        let f_unlabeled: DensePolynomial<F> = DensePolynomial::rand(7, rng);
        let f = LabeledPolynomial::new(
            String::from("f"),
            f_unlabeled,
            Some(enforced_degree_bound),
            enforced_hiding_bound,
        );

        // Step 2: evaluate it
        let f_evals = f.evaluate_over_domain_by_ref(domain_k);

        // Step 3: find the inverse at each of these points
        let desired_g_evals = f_evals
            .evals
            .iter()
            .map(|&x| x.inverse().unwrap())
            .collect::<Vec<_>>();
        let desired_g_evals = Evaluations::from_vec_and_domain(desired_g_evals, domain_k);

        // Step 4: interpolate a polynomial from the inverses
        let g = desired_g_evals.clone().interpolate();
        let g = LabeledPolynomial::new(
            String::from("g"),
            g.clone(),
            Some(enforced_degree_bound),
            enforced_hiding_bound,
        );

        // Step 5: commit to the concrete oracles
        let concrete_oracles = [f, g];
        let (commitments, rands) = PC::commit(&ck, &concrete_oracles, Some(rng))
            .map_err(to_pc_error::<F, PC>)
            .unwrap();

        // Step 6: Derive the desired virtual oracle
        let alphas = vec![F::one(), F::one()];
        let inverse_check_oracle =
            GenericShiftingVO::new(&vec![0, 1], &alphas, presets::inverse_check).unwrap();

        // Step 7: prove
        let zero_over_k_proof = ZeroOverK::<F, PC, FS>::prove(
            &concrete_oracles,
            &commitments,
            &rands,
            Some(enforced_degree_bound),
            &inverse_check_oracle,
            &domain_k,
            &ck,
            rng,
        );

        // Step 8: verify
        let is_valid = ZeroOverK::<F, PC, FS>::verify(
            zero_over_k_proof.unwrap(),
            &commitments,
            Some(enforced_degree_bound),
            &inverse_check_oracle,
            &domain_k,
            &vk,
        );

        assert!(is_valid.is_ok());
    }

    #[test]
    fn test_error_on_invalid_proof() {
        let m = 8;
        let rng = &mut thread_rng();
        let domain_k = GeneralEvaluationDomain::<F>::new(m).unwrap();

        let max_degree = 20;
        let max_hiding = 1;

        let enforced_hiding_bound = Some(1);
        let enforced_degree_bound = 14;

        let pp = PC::setup(max_degree, None, rng).unwrap();
        let (ck, vk) = PC::trim(&pp, max_degree, max_hiding, Some(&[2, 14])).unwrap();

        let f_evals: Vec<F> = vec![
            F::from(1u64),
            F::from(2u64),
            F::from(3u64),
            F::from(4u64),
            F::from(5u64),
            F::from(6u64),
            F::from(7u64),
            F::from(8u64),
        ];

        let f = DensePolynomial::<F>::from_coefficients_slice(&domain_k.ifft(&f_evals));
        let f = LabeledPolynomial::new(
            String::from("f"),
            f,
            Some(enforced_degree_bound),
            enforced_hiding_bound,
        );

        let g_evals: Vec<F> = vec![
            F::from(8u64),
            F::from(7u64),
            F::from(6u64),
            F::from(5u64),
            F::from(4u64),
            F::from(3u64),
            F::from(2u64),
            F::from(1u64),
        ];

        let g = DensePolynomial::<F>::from_coefficients_slice(&domain_k.ifft(&g_evals));
        let g = LabeledPolynomial::new(
            String::from("g"),
            g.clone(),
            Some(enforced_degree_bound),
            enforced_hiding_bound,
        );

        let concrete_oracles = [f, g];
        let alphas = vec![F::one(), F::one()];
        let (commitments, rands) = PC::commit(&ck, &concrete_oracles, Some(rng))
            .map_err(to_pc_error::<F, PC>)
            .unwrap();

        let zero_over_k_vo =
            GenericShiftingVO::new(&[0, 1], &alphas, presets::equality_check).unwrap();

        let zero_over_k_proof = ZeroOverK::<F, PC, FS>::prove(
            &concrete_oracles,
            &commitments,
            &rands,
            Some(enforced_degree_bound),
            &zero_over_k_vo,
            &domain_k,
            &ck,
            rng,
        )
        .unwrap();

        let res = ZeroOverK::<F, PC, FS>::verify(
            zero_over_k_proof,
            &commitments,
            Some(enforced_degree_bound),
            &zero_over_k_vo,
            &domain_k,
            &vk,
        );

        assert!(res.is_err());

        // Test for a specific error
        assert_eq!(res.unwrap_err(), Error::Check2Failed);
    }

    #[test]
    fn test_degree_bound_not_respected() {
        let m = 8;
        let rng = &mut test_rng();
        let domain_k = GeneralEvaluationDomain::<F>::new(m).unwrap();

        let max_degree = 20;
        let max_hiding = 1;

        let enforced_hiding_bound = Some(1);
        let prover_degree_bound = 15;
        let verifier_degree_bound = 14;

        let pp = PC::setup(max_degree, None, rng).unwrap();
        let (ck, vk) = PC::trim(
            &pp,
            max_degree,
            max_hiding,
            Some(&[2, verifier_degree_bound, prover_degree_bound]),
        )
        .unwrap();

        // Step 1: choose a random polynomial
        let f_unlabeled: DensePolynomial<F> = DensePolynomial::rand(7, rng);
        let f = LabeledPolynomial::new(
            String::from("f"),
            f_unlabeled,
            Some(prover_degree_bound),
            enforced_hiding_bound,
        );

        // Step 2: evaluate it
        let f_evals = f.evaluate_over_domain_by_ref(domain_k);

        // Step 3: find the inverse at each of these points
        let desired_g_evals = f_evals
            .evals
            .iter()
            .map(|&x| x.inverse().unwrap())
            .collect::<Vec<_>>();
        let desired_g_evals = Evaluations::from_vec_and_domain(desired_g_evals, domain_k);

        // Step 4: interpolate a polynomial from the inverses
        let g = desired_g_evals.clone().interpolate();
        let g = LabeledPolynomial::new(
            String::from("g"),
            g.clone(),
            Some(prover_degree_bound),
            enforced_hiding_bound,
        );

        // Step 5: commit to the concrete oracles
        let concrete_oracles = [f, g];
        let (commitments, rands) = PC::commit(&ck, &concrete_oracles, Some(rng))
            .map_err(to_pc_error::<F, PC>)
            .unwrap();

        // Step 6: Derive the desired virtual oracle
        let alphas = vec![F::one(), F::one()];
        let inverse_check_oracle =
            GenericShiftingVO::new(&vec![0, 1], &alphas, presets::inverse_check).unwrap();

        // Step 7: prove
        let zero_over_k_proof = ZeroOverK::<F, PC, FS>::prove(
            &concrete_oracles,
            &commitments,
            &rands,
            Some(prover_degree_bound),
            &inverse_check_oracle,
            &domain_k,
            &ck,
            rng,
        )
        .unwrap();

        // Step 8: verify
        let verifier_commitments: Vec<LabeledCommitment<_>> = commitments
            .iter()
            .map(|c| {
                let label = c.label().clone();
                let comm = c.commitment().clone();
                LabeledCommitment::new(label, comm, Some(verifier_degree_bound))
            })
            .collect();
        let res = ZeroOverK::<F, PC, FS>::verify(
            zero_over_k_proof,
            &verifier_commitments,
            Some(verifier_degree_bound),
            &inverse_check_oracle,
            &domain_k,
            &vk,
        );

        assert!(res.is_err());

        assert_eq!(res.unwrap_err(), Error::BatchCheckError);
    }

    #[test]
    fn test_well_formation_vo_quadratic_masking_check2_fails() {
        use crate::virtual_oracle::generic_shifting_vo::vo_term::VOTerm;
        use crate::vo_constant;
        use ark_ff::Zero;
        use ark_poly::Polynomial;

        let rng = &mut test_rng();

        // Use domain H of size 256, matching a fibonacci circuit with 128 steps
        let domain_h = GeneralEvaluationDomain::<F>::new(256).unwrap();
        let elems: Vec<F> = domain_h.elements().collect();

        let n_inputs = 3usize;  // one, f0, f1
        let n_outputs = 2usize; // two output values

        // Build the well-formation polynomials as index_private_marlin does,
        // using the actual construct_lagrange_basis / construct_vanishing from well_formation.rs.
        // We use fibonacci values to mirror the real failing case.
        let mut chain = vec![F::one(), F::one()];
        for i in 2..130usize { chain.push(chain[i-1] + chain[i-2]); }

        // public inputs: [1, fib(0)=1, fib(1)=1]
        let pi_vals = vec![F::one(), F::one(), F::one()];
        // outputs: [fib(128), fib(129)]
        let out_vals = vec![chain[128], chain[129]];

        let pi_roots    = &elems[..n_inputs];
        let out_roots   = &elems[elems.len() - n_outputs..];

        // Lagrange interpolation for x_poly and y_poly
        let lagrange_interp = |roots: &[F], vals: &[F]| -> DensePolynomial<F> {
            let mut poly = DensePolynomial::<F>::zero();
            for (i, &xi) in roots.iter().enumerate() {
                let mut li = DensePolynomial::from_coefficients_slice(&[F::one()]);
                for (j, &xj) in roots.iter().enumerate() {
                    if i != j {
                        let num = DensePolynomial::from_coefficients_slice(&[-xj, F::one()]);
                        li = &li * &(&num * (xi - xj).inverse().unwrap());
                    }
                }
                poly += &(&li * vals[i]);
            }
            while poly.coeffs.last().map_or(false, |c| c.is_zero()) { poly.coeffs.pop(); }
            poly
        };

        let x_poly = lagrange_interp(pi_roots, &pi_vals);
        let y_poly = lagrange_interp(out_roots, &out_vals);

        let trunc = |mut p: DensePolynomial<F>| -> DensePolynomial<F> {
            while p.coeffs.last().map_or(false, |c| c.is_zero()) { p.coeffs.pop(); }
            p
        };

        // vh_gt_x vanishes on elems[n_inputs..]
        let mut vh_gt_x = DensePolynomial::from_coefficients_slice(&[F::one()]);
        for &r in &elems[n_inputs..] {
            vh_gt_x = trunc(&vh_gt_x * &DensePolynomial::from_coefficients_slice(&[-r, F::one()]));
        }

        // vh_lt_y vanishes on elems[..256-n_outputs]
        let mut vh_lt_y = DensePolynomial::from_coefficients_slice(&[F::one()]);
        for &r in &elems[..elems.len() - n_outputs] {
            vh_lt_y = trunc(&vh_lt_y * &DensePolynomial::from_coefficients_slice(&[-r, F::one()]));
        }

        // z: interpolated over all of H with values matching x_poly on pi_roots
        // and y_poly on out_roots, and arbitrary elsewhere. Use random values in between.
        let z_evals = (0..256).map(|i| {
            if i < n_inputs { pi_vals[i] }
            else if i >= 256 - n_outputs { out_vals[i - (256 - n_outputs)] }
            else { F::from(i as u64) }
        }).collect::<Vec<_>>();
        let z = DensePolynomial::from_coefficients_slice(&domain_h.ifft(&z_evals));

        // Sanity: VO pointwise on H should be zero
        let sep = F::from(2u64);
        for &r in &elems {
            let zr = z.evaluate(&r);
            let xr = x_poly.evaluate(&r);
            let yr = y_poly.evaluate(&r);
            let vhx = vh_gt_x.evaluate(&r);
            let vhy = vh_lt_y.evaluate(&r);
            let vo_val = (zr - xr) * vhx + sep * (zr - yr) * vhy;
            assert_eq!(vo_val, F::zero(), "VO not zero at domain point");
        }

        // As polynomials, VO(z,x,vh_gt_x,y,vh_lt_y) should be divisible by zH
        let vo_poly = {
            let diff_x = &z - &x_poly;
            let diff_y = &z - &y_poly;
            &(&diff_x * &vh_gt_x) + &(&(&diff_y * &vh_lt_y) * sep)
        };
        let zh: DensePolynomial<F> = domain_h.vanishing_polynomial().into();
        let (_, remainder) = ark_poly::univariate::DenseOrSparsePolynomial::from(&vo_poly)
            .divide_with_q_and_r(&ark_poly::univariate::DenseOrSparsePolynomial::from(&zh))
            .unwrap();
        assert!(remainder.is_zero(), "VO poly not divisible by zH (unmasked)");

        // Setup PC
        let max_degree = 600;
        let pp = PC::setup(max_degree, None, rng).unwrap();
        let (ck, vk) = PC::trim(&pp, max_degree, 1, Some(&[2])).unwrap();

        // Concrete oracles: [z, x_poly, vh_gt_x, y_poly, vh_lt_y]
        // mapping [0,1,2,0,3,4] — z appears twice
        let oracles = vec![
            LabeledPolynomial::new("z".into(),       z,       None, Some(1)),
            LabeledPolynomial::new("x".into(),       x_poly,  None, Some(1)),
            LabeledPolynomial::new("vh_gt_x".into(), vh_gt_x, None, Some(1)),
            LabeledPolynomial::new("y".into(),       y_poly,  None, Some(1)),
            LabeledPolynomial::new("vh_lt_y".into(), vh_lt_y, None, Some(1)),
        ];

        let (commits, rands) = PC::commit(&ck, &oracles, Some(rng)).unwrap();

        // Well-formation VO: same as in index_private_marlin
        let vo = GenericShiftingVO::new(
            &vec![0, 1, 2, 0, 3, 4],
            &vec![F::one(); 6],
            |terms: &[VOTerm<F>]| {
                (terms[1].clone() - terms[2].clone()) * terms[3].clone()
                    + vo_constant!(sep) * (terms[4].clone() - terms[5].clone()) * terms[6].clone()
            },
        ).unwrap();

        let proof = ZeroOverK::<F, PC, FS>::prove(
            &oracles,
            &commits,
            &rands,
            None,
            &vo,
            &domain_h,
            &ck,
            rng,
        ).unwrap();

        let result = ZeroOverK::<F, PC, FS>::verify(
            proof,
            &commits,
            None,
            &vo,
            &domain_h,
            &vk,
        );

        assert!(result.is_ok());
    }
}
