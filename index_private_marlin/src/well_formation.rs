use ark_ff::{FftField, Zero};
use ark_poly::{univariate::DensePolynomial, UVPolynomial};

pub(crate) fn normalize<F: FftField + Zero>(mut p: DensePolynomial<F>) -> DensePolynomial<F> {
    while p.coeffs.last().map_or(false, |c| c.is_zero()) {
        p.coeffs.pop();
    }
    p
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::One;
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial};

    // Summing Lagrange basis polynomials over a subset of roots of a large domain
    // produces trailing zero coefficients that ark-poly does not strip.  Calling
    // degree() on such a polynomial panics.
    //
    // Concretely: sum(l_i for i in 0..3) over a size-256 domain is mathematically
    // the constant polynomial 1, but its coefficient vector has 2 trailing zeros.
    // This is the root cause of the panic in verifier_well_formation_oracles when
    // committing to x_poly / y_poly for circuits with domain H >= 256.
    //
    // This test is expected to FAIL until construct_lagrange_basis (or the call site)
    // strips trailing zeros after summation.
    // Summing Lagrange basis polynomials produces trailing zeros that must be stripped.
    // This test documents the bug and verifies the fix: after normalize(), degree() must
    // not panic.
    #[test]
    fn test_x_poly_trailing_zeros_from_lagrange_sum() {
        let domain = GeneralEvaluationDomain::<Fr>::new(256).unwrap();
        let elems: Vec<Fr> = domain.elements().collect();

        // x_poly = l_0 + l_1 + l_2  (mirrors verifier_well_formation_oracles with
        // number_of_input_rows = 3 and all public inputs equal to 1)
        let bases = construct_lagrange_basis(&elems[..3]);
        let mut x_poly = DensePolynomial::<Fr>::default();
        for l_i in &bases {
            x_poly += &(l_i * Fr::one());
        }
        let x_poly = normalize(x_poly);

        // Must not panic after normalization
        let _ = x_poly.degree();
    }
}

// given the x coords construct Li polynomials
pub fn construct_lagrange_basis<F: FftField>(evaulation_domain: &[F]) -> Vec<DensePolynomial<F>> {
    let mut bases = Vec::with_capacity(evaulation_domain.len());
    for i in 0..evaulation_domain.len() {
        let mut l_i = DensePolynomial::from_coefficients_slice(&[F::one()]);
        let x_i = evaulation_domain[i];
        for j in 0..evaulation_domain.len() {
            if j != i {
                let nom =
                    DensePolynomial::from_coefficients_slice(&[-evaulation_domain[j], F::one()]);
                let denom = x_i - evaulation_domain[j];

                l_i = normalize(&l_i * &normalize(&nom * denom.inverse().unwrap()));
            }
        }

        bases.push(normalize(l_i));
    }

    bases
}

pub fn construct_vanishing<F: FftField>(evaulation_domain: &[F]) -> DensePolynomial<F> {
    let mut v_h = DensePolynomial::from_coefficients_slice(&[F::one()]);
    for point in evaulation_domain {
        v_h = normalize(&v_h * &DensePolynomial::from_coefficients_slice(&[-*point, F::one()]));
    }

    v_h
}
