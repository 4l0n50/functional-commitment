/// Bridge between `ac_compiler`'s raw R1CS matrices and `ark-marlin`'s
/// `ConstraintSynthesizer<F>` interface.
///
/// # Variable layout
///
/// `ac_compiler` assigns column indices as:
/// - Column 0: constant "1" (`Variable::One` in ark-relations)
/// - Columns `1..t`: public inputs (`t = number_of_input_rows`)
/// - Columns `t..n-s`: internal witness variables
/// - Columns `n-s..n`: output witness variables (last `s = number_of_outputs`)
///
/// This ordering ensures the last `s` witness variables are the outputs,
/// matching the convention expected by the modified Marlin prover.
use ac_compiler::{Matrix, R1CSfIndex};
use ark_ff::Field;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};

#[derive(Clone)]
pub struct AcCircuit<F: Field> {
    pub a: Matrix<F>,
    pub b: Matrix<F>,
    pub c: Matrix<F>,
    /// Full assignment: index 0 = constant 1, indices 1..t = inputs, t.. = witnesses.
    pub assignment: Vec<F>,
    pub index_info: R1CSfIndex,
}

impl<F: Field> AcCircuit<F> {
    pub fn new(
        a: Matrix<F>,
        b: Matrix<F>,
        c: Matrix<F>,
        assignment: Vec<F>,
        index_info: R1CSfIndex,
    ) -> Self {
        Self { a, b, c, assignment, index_info }
    }
}

impl<F: Field> ConstraintSynthesizer<F> for AcCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let t = self.index_info.number_of_input_rows; // number of input rows (incl. constant)
        let s = self.index_info.number_of_outputs;
        let n = self.assignment.len(); // total variables incl. constant

        // Map from ac_compiler column index → ark-relations Variable.
        // Built as we allocate variables below.
        let mut col_to_var: Vec<Variable> = vec![Variable::Zero; n];

        // Column 0 → Variable::One
        col_to_var[0] = Variable::One;

        // Columns 1..t → instance variables
        for i in 1..t {
            let val = self.assignment[i];
            let v = cs.new_input_variable(|| Ok(val))?;
            col_to_var[i] = v;
        }

        // Columns t..n-s → internal witness variables
        for i in t..n - s {
            let val = self.assignment[i];
            let v = cs.new_witness_variable(|| Ok(val))?;
            col_to_var[i] = v;
        }

        // Columns n-s..n → output witness variables (last, as Marlin expects)
        for i in n - s..n {
            let val = self.assignment[i];
            let v = cs.new_witness_variable(|| Ok(val))?;
            col_to_var[i] = v;
        }

        // Enforce each constraint row: lc_A * lc_B = lc_C
        let num_constraints = self.a.len();
        for row in 0..num_constraints {
            let mut lc_a = lc!();
            let mut lc_b = lc!();
            let mut lc_c = lc!();
            for &(coeff, col) in &self.a[row] {
                lc_a = lc_a + (coeff, col_to_var[col]);
            }
            for &(coeff, col) in &self.b[row] {
                lc_b = lc_b + (coeff, col_to_var[col]);
            }
            for &(coeff, col) in &self.c[row] {
                lc_c = lc_c + (coeff, col_to_var[col]);
            }
            cs.enforce_constraint(lc_a, lc_b, lc_c)?;
        }

        Ok(())
    }
}
