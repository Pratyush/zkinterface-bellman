use r1cs_core::{
    ConstraintSystem,
    LinearCombination,
    SynthesisError,
    Variable,
    ConstraintVar,
};
use algebra::{FromBytes, PrimeField, BigInteger};
use r1cs_std::fields::{FieldGadget, fp::FpGadget};
use r1cs_std::prelude::*;
use std::collections::HashMap;
use zkinterface::{
    reading::{Constraint, Messages, Term},
    writing::{CircuitOwned, VariablesOwned},
};


/// Convert zkInterface little-endian bytes to bellman Fr.
pub fn le_to_fr<F: PrimeField>(bytes_le: &[u8]) -> F {
    if bytes_le.len() == 0 {
        return F::zero();
    }

    let mut bytes_le = Vec::from(bytes_le);
    let words = (F::size_in_bits() + 63) / 64;
    bytes_le.resize(8 * words as usize, 0);
    let repr = FromBytes::read(bytes_le.as_slice()).unwrap();
    F::from_repr(repr)
}

/// Convert zkInterface terms to bellman LinearCombination.
pub fn terms_to_lc<F: PrimeField>(vars: &HashMap<u64, Variable>, terms: &[Term]) -> LinearCombination<F> {
    let mut lc = LinearCombination::zero();
    for term in terms {
        let coeff = le_to_fr::<F>(term.value);
        let var = vars.get(&term.id).unwrap().clone();
        lc = lc + (coeff, var);
    }
    lc
}

/// Enforce a zkInterface constraint in bellman CS.
pub fn enforce<F: PrimeField, CS>(cs: &mut CS, vars: &HashMap<u64, Variable>, constraint: &Constraint)
    where 
          CS: ConstraintSystem<F>
{
    cs.enforce(|| "",
               |_| terms_to_lc(vars, &constraint.a),
               |_| terms_to_lc(vars, &constraint.b),
               |_| terms_to_lc(vars, &constraint.c),
    );
}

/// Call a foreign gadget through zkInterface.
pub fn call_gadget<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    inputs: &[FpGadget<F>],
    exec_fn: & dyn Fn(&[u8]) -> Result<Messages, String>,
) -> Result<(Vec<FpGadget<F>>), SynthesisError> {
    let witness_generation = inputs.len() > 0 && inputs[0].get_value().is_some();

    // Serialize input values.
    let values = if witness_generation {
        let mut values = Vec::<u8>::new();
        for i in inputs {
            i.get_value().unwrap().into_repr().write_le(&mut values)?;
        }
        Some(values)
    } else {
        None
    };

    // Describe the input connections.
    let first_input_id = 1;
    let free_variable_id = first_input_id + inputs.len() as u64;

    let call = CircuitOwned {
        connections: VariablesOwned {
            variable_ids: (first_input_id..free_variable_id).collect(),
            values,
        },
        free_variable_id,
        r1cs_generation: true,
        field_maximum: None,
    };

    // Prepare the call.
    let mut call_buf = vec![];
    call.write(&mut call_buf)?;

    // Call.
    let messages = exec_fn(&call_buf).or(Err(SynthesisError::Unsatisfiable))?;

    // Track variables by id. Used to convert constraints.
    let mut id_to_var = HashMap::<u64, ConstraintVar<F>>::new();

    id_to_var.insert(0, CS::one());

    for i in 0..inputs.len() {
        id_to_var.insert(call.connections.variable_ids[i], inputs[i].get_variable());
    }

    // Collect output variables and values to return.
    let mut outputs = Vec::new();

    // Allocate outputs, with optional values.
    if let Some(output_vars) = messages.connection_variables() {
        for var in output_vars {
            let num = FpGadget::alloc(
                cs.ns(|| format!("output_{}", var.id)), 
                || Ok(le_to_fr::<F>(var.value))
            )?;

            // Track output variable.
            id_to_var.insert(var.id, num.get_variable());
            outputs.push(num);
        }
    }

    // Allocate private variables, with optional values.
    let private_vars = messages.private_variables().unwrap();

    for var in private_vars {
        let alloc_var = cs.alloc(|| format!("local_{}", var.id), || Ok(le_to_fr::<F>(var.value)))?;
        // Track private variable.
        id_to_var.insert(var.id, alloc_var);
    };

    // Add gadget constraints.
    for (i, constraint) in messages.iter_constraints().enumerate() {
        enforce(&mut cs.ns(|| format!("constraint_{}", i)), &id_to_var, &constraint);
    }

    Ok(outputs)
}
