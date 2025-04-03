use fxhash::FxHashMap as HashMap;
use crate::ir::term::Value;
#[cfg(feature = "spartan")]
use rug::Integer;
use crate::eddsa::sigma::verifier_input_for_eddsa_sigma;
#[cfg(feature = "spartan")]
use crate::right_field_arithmetic::alloc::{map_field_double_vec};
#[cfg(feature = "spartan")]
use crate::right_field_arithmetic::field::{ARC_MOD_CURVE25519, ARC_MOD_T256, ARC_MOD_T25519};
#[cfg(feature = "spartan")]
use crate::ecdsa::verifier_input::{
    verifer_input_for_ecdsa_rightfield,
    verifer_input_for_ecdsa_rightfield_whole
};
#[cfg(feature = "spartan")]
use std::sync::Arc;

use super::create_input::{ComputeType, PfCurve};

use crate::ecdsa::verifier_input::{verifer_input_for_ecdsa_sigma};
use crate::ecdsa::verifier_input::{verifier_input_for_ecdsa};
use crate::hash::sha256::{verifier_input_for_sha256_ori, verifier_input_for_sha256_adv};
use crate::rsa::verifier_input::{verifier_input_for_verifyrsa};


#[cfg(feature = "spartan")]
fn matrix_multiply_and_conditionally_increment(
    a: &Vec<Vec<Integer>>,
    b: &Vec<Vec<Integer>>,
    c: &Vec<Vec<bool>>,
) -> Vec<Vec<Integer>> {
    let p = a.len(); // Assuming square matrices
    let mut ab = vec![vec![Integer::from(0); p]; p]; // Initialize the result matrix with zeros.

    for i in 0..p {
        for j in 0..p {
            for k in 0..p {
                let product = &a[i][k] * &b[k][j];
                ab[i][j] += product;
            }
            if c[i][j] {
                ab[i][j] += Integer::from(1);
            }
        }
    }
    ab
}

#[cfg(feature = "spartan")]
#[allow(unused)]
fn verifier_input_for_spartantest(modulus: &Arc<Integer>) -> HashMap<String, Value>{
    let p: usize = 19;
    let mut matrix = vec![vec![Integer::from(0); p]; p];
    let mut bool_matrix = vec![vec![false; p]; p];
    for i in 0..p {
        for j in 0..p {
            matrix[i][j] = Integer::from(i*j);
            if i*j % 2 == 1 {
                bool_matrix[i][j] = true;
            }
        }
    }
    let result = matrix_multiply_and_conditionally_increment(&matrix, &matrix, &bool_matrix);
    let mut input_map = HashMap::<String, Value>::default();
    map_field_double_vec(&matrix, modulus, "A", &mut input_map);
    // map_bool_double_vec(&bool_matrix, "C", &mut input_map);
    map_field_double_vec(&result, modulus, "return", &mut input_map);
    // input_map.insert("return".to_string(), bool_to_value(true)); // to do

    input_map
}


/// Create verifier input
pub fn create_verifier_input(compute: ComputeType, aux_input: String, pfcurve: &PfCurve) -> HashMap<String, Value> {

    let result = match compute {
        ComputeType::EddsaSigma => {
            verifier_input_for_eddsa_sigma(5, 55)
        }

        ComputeType::VerifyRsaAdvComplete => verifier_input_for_verifyrsa(false, 2048, ""),
        ComputeType::VerifyRsaAdvWhole => verifier_input_for_verifyrsa(true, 2048, ""), // to do: add aux input to specify the message length

        ComputeType::VerifyEcdsaAdvIncompl | ComputeType::VerifyEcdsaAdvIncomplWhole  => verifier_input_for_ecdsa(), // to fix
        ComputeType::VerifyEcdsaSigma| ComputeType::VerifyEcdsaSigmaWhole => verifer_input_for_ecdsa_sigma(), // to do: add aux input to specify the message length

        #[cfg(feature = "spartan")]
        ComputeType::VerifyEcdsaRight => verifer_input_for_ecdsa_rightfield(), // to modify
        #[cfg(feature = "spartan")]
        ComputeType::VerifyEcdsaRightWhole => verifer_input_for_ecdsa_rightfield_whole(),
        #[cfg(feature = "spartan")]
        ComputeType::SpartanTest => verifier_input_for_spartantest(&ARC_MOD_CURVE25519),
        #[cfg(feature = "spartan")]
        ComputeType::SpartanTestT256 => verifier_input_for_spartantest(&ARC_MOD_T256),
        ComputeType::Sha256Ori => verifier_input_for_sha256_ori(aux_input),
        ComputeType::Sha256Adv => verifier_input_for_sha256_adv(aux_input, None),
        #[cfg(feature = "spartan")]
        ComputeType::Sha256AdvSpartan => {
            match pfcurve {
                PfCurve::Curve25519 => verifier_input_for_sha256_adv(aux_input, Some(&ARC_MOD_CURVE25519)),
                PfCurve::T256 => verifier_input_for_sha256_adv(aux_input, Some(&ARC_MOD_T256)),
                PfCurve::T25519 => verifier_input_for_sha256_adv(aux_input, Some(&ARC_MOD_T25519)),
            }
        },
    };
    result
}
