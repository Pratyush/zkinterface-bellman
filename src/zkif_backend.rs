use r1cs_core::{
    ConstraintSynthesizer,
    ConstraintSystem,
    SynthesisError,
    Variable,
};
use algebra::{Field, PairingEngine};
use rand::OsRng;
use r1cs_std::circuit::num::AllocatedNum;
use std::collections::HashMap;
use std::fs::File;
use std::path::Path;
use super::import::{enforce, le_to_fr};
pub use zkinterface::reading::Messages;


/// A circuit instance built from zkif messages.
#[derive(Clone, Debug)]
pub struct ZKIFCircuit<'a> {
    pub messages: &'a Messages,
}

impl<'a, F: Field> ConstraintSynthesizer<F> for ZKIFCircuit<'a> {
    fn generate_constraints<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        // Track variables by id. Used to convert constraints.
        let mut id_to_var = HashMap::<u64, Variable>::new();

        id_to_var.insert(0, CS::one());

        // Allocate public inputs, with optional values.
        let public_vars = self.messages.connection_variables().unwrap();

        for var in public_vars {
            let var = cs.alloc_input(|| format!("public_{}", var.id), || Ok(le_to_fr::<F>(var.value)))?;
            // Track input variable.
            id_to_var.insert(var.id, var);
        }

        // Allocate private variables, with optional values.
        let private_vars = self.messages.private_variables().unwrap();

        for var in private_vars {
            let var = cs.alloc(|| format!("public_{}", var.id), || Ok(le_to_fr::<F>(var.value)))?;
            // Track input variable.
            id_to_var.insert(var.id, var);
        };

        for (i, constraint) in self.messages.iter_constraints().enumerate() {
            enforce(&mut cs.namespace(|| format!("constraint_{}", i)), &id_to_var, &constraint);
        }

        Ok(())
    }
}


/// Process a circuit.
pub fn zkif_backend(
    messages: &Messages,
    out_dir: &Path,
) -> Result<(), SynthesisError>
{
    let key_path = out_dir.join("key");
    let proof_path = out_dir.join("proof");

    let circuit = ZKIFCircuit { messages };

    let circuit_msg = messages.last_circuit().ok_or(SynthesisError::AssignmentMissing)?;

    let mut rng = OsRng::new()?;

    if circuit_msg.r1cs_generation() {
        let params = generate_random_parameters::<Bls12, _, _>(
            circuit.clone(),
            &mut rng,
        )?;

        // Store params.
        let f = File::create(&key_path)?;
        params.write(f)?;
    }

    if circuit_msg.witness_generation() {
        // Load params.
        let mut fs = File::open(&key_path)?;
        let params = Parameters::<Bls12>::read(&mut fs, false)?;

        let proof = create_random_proof(
            circuit,
            &params,
            &mut rng,
        )?;

        // Store proof.
        let f = File::create(proof_path)?;
        proof.write(f)?;
    }
    Ok(())
}

#[test]
fn test_zkif_backend() {

    // Load test messages.
    let test_dir = Path::new("src/test/messages");
    let out_dir = Path::new("local");

    // Setup.
    {
        let mut messages = Messages::new(1);
        messages.read_file(test_dir.join("r1cs.zkif")).unwrap();
        messages.read_file(test_dir.join("circuit_r1cs.zkif")).unwrap();

        zkif_backend(&messages, out_dir).unwrap();
    }

    // Prove.
    {
        let mut messages = Messages::new(1);
        messages.read_file(test_dir.join("witness.zkif")).unwrap();
        messages.read_file(test_dir.join("circuit_witness.zkif")).unwrap();

        zkif_backend(&messages, out_dir).unwrap();
    }
}
