use ac_compiler::constraint_builder::ConstraintBuilder;
use ac_compiler::error::Error;
use ac_compiler::gate::GateType;
use ac_compiler::variable::VariableType;
use ac_compiler::{circuit::Circuit, circuit_compiler::{CircuitCompiler, VanillaCompiler}};
use ark_bn254::Fr;
use ark_ff::{Field, One};

type F = Fr;

fn build_fibonacci_output_circuit<F: Field>(
    cb: &mut ConstraintBuilder<F>,
    f0_val: F,
    f1_val: F,
    num_steps: usize,
) -> Result<(), Error> {
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

fn main() {
    let sizes = [128usize, 256, 512, 768, 1056];

    println!("{:<12} {:>8} {:>8} | {:>10} {:>8} | {:>10} {:>8} | {:>10} {:>8}",
        "num_steps", "rows", "cols",
        "A nnz", "A sparsity",
        "B nnz", "B sparsity",
        "C nnz", "C sparsity",
    );
    println!("{}", "-".repeat(100));

    for &size in &sizes {
        let mut cb = ConstraintBuilder::<F>::new();
        let synthesized = Circuit::synthesize(
            |cb| build_fibonacci_output_circuit(cb, F::from(1u64), F::from(1u64), size),
            &mut cb,
        ).unwrap();
        let (index_info, a, b, c) = VanillaCompiler::<F>::ac2tft(&synthesized);
        let assignment = cb.assignment.clone();

        let rows = index_info.number_of_constraints;
        let cols = assignment.len();
        let nnz_a: usize = a.iter().map(|r| r.len()).sum();
        let nnz_b: usize = b.iter().map(|r| r.len()).sum();
        let nnz_c: usize = c.iter().map(|r| r.len()).sum();
        let total = (rows * cols) as f64;

        println!("{:<12} {:>8} {:>8} | {:>10} {:>8.2}% | {:>10} {:>8.2}% | {:>10} {:>8.2}%",
            size, rows, cols,
            nnz_a, 100.0 * nnz_a as f64 / total,
            nnz_b, 100.0 * nnz_b as f64 / total,
            nnz_c, 100.0 * nnz_c as f64 / total,
        );
    }
}
