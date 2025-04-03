//! This module creates the prover inputs

use fxhash::FxHashMap as HashMap;
use crate::ir::term::Value;
use rug::Integer;

use crate::bignat::bignat::{BigNat, BigNatModMult};
use crate::bignat::bignatwithlimbmax::{BigNatWithLimbMax, BigNatbWithLimbMax, BigNatModMultWithLimbMax}; //, BigNatExponWithLimbMax};
use crate::parse_cert::{X509Certificate, IssuerKey, Signature};
use crate::convert::{str_to_field, u64_to_value};
use crate::allocate::{map_bool_double_vec, map_u8_vec, map_u32_double_vec}; //,map_u32, map_bool_double_vec_to_single_vec};

use crate::hash::hash::DigestAlgorithm;
use crate::hash::sha256::{prover_input_for_sha256_ori, prover_input_for_sha256_adv};
use crate::conditional_print;
use crate::eddsa::sigma::prover_input_for_verifyeddsa_sigma;

#[cfg(feature = "spartan")]
use crate::right_field_arithmetic::field::{ARC_MOD_T256, ARC_MOD_CURVE25519, ARC_MOD_T25519};
#[cfg(feature = "spartan")]
use crate::ecdsa::prover_input::{prover_input_for_verifyecdsa_rightfield, prover_input_for_spartantest};
use crate::ecdsa::prover_input::{
    prover_input_for_verifyecdsa_sigma, 
    prover_input_for_verifyecdsa_sigma_whole, 
};
#[cfg(feature = "spartan")]
use crate::ecdsa::prover_input::prover_input_for_verifyecdsa_rightfield_whole;

use crate::ecdsa::prover_input::prover_input_for_verifyecdsa;

use crate::ecdsa::prover_input::prover_input_for_verifyecdsa_whole; 
use super::create_input::{ComputeType, PfCurve};
use crate::rsa::prover_input::{prover_input_for_verifyrsa_adv, prover_input_for_verifyrsa_adv_whole}; // prover_input_for_modexpon_for_rsa_v3, prover_input_for_modexpon_for_rsa_v4, prover_input_for_modexpon_for_rsa, 


#[allow(unused)]
fn prover_input_for_testfun3() -> HashMap<String, Value>{
    let mut input_map = HashMap::<String, Value>::default();
    input_map.insert("message".to_string(), u64_to_value(4));
    input_map
}

#[allow(unused)]
fn prover_input_for_testfun4() -> HashMap<String, Value>{
    let mut input_map = HashMap::<String, Value>::default();
    let a = "12";
    let b = "34";
    input_map.insert("a".to_string(), str_to_field(a));
    input_map.insert("b".to_string(), str_to_field(b));
    input_map
}


#[allow(unused)]
fn prover_input_for_testpadding() -> HashMap<String, Value>{
    let mut input_map = HashMap::<String, Value>::default();
    let input: Vec<u8> = vec![1, 2, 3, 4];
    map_u8_vec(&input, "input", &mut input_map);
    input_map
}

#[allow(unused)]
fn prover_input_for_testpadding2() -> HashMap<String, Value>{
    let mut input_map = HashMap::<String, Value>::default();
    let input: Vec<u8> = vec![1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56];
    let padded_input: Vec<u8> = DigestAlgorithm::padding(&input);
    conditional_print!("{:?}", padded_input);
    let padded_input_zokrates: Vec<Vec<u32>> = DigestAlgorithm::vecu8_to_doublevecu32(&padded_input);
    map_u8_vec(&input, "input", &mut input_map);
    conditional_print!("{:?}", padded_input_zokrates);
    map_u32_double_vec(&padded_input_zokrates, "padded_input", &mut input_map);
    input_map
}

#[allow(unused)]
fn prover_input_for_test_bug() -> HashMap<String, Value> {
    let limbwidth = 32;
    let n_limbs = 8;
    let remainder_int: Integer = Integer::from_str_radix("56515219790691171413109057904011688695424810155802929973526481321309856242040", 10).unwrap();
    let remainder: BigNat = BigNat::new(&remainder_int.clone(), limbwidth, n_limbs);
    let gx: BigNat = BigNat::new(&Integer::from_str_radix("48439561293906451759052585252797914202762949526041747995844080717082404635286", 10).unwrap(), limbwidth, n_limbs);
    let product: BigNat = remainder.create_product_nat(&gx);

    let mut input_map = HashMap::<String, Value>::default();
    BigNatbWithLimbMax::alloc_from_integer(&remainder_int, limbwidth, n_limbs, "remainderb", &mut input_map);
    product.alloc_from_nat("product", &mut input_map);
    input_map
}

#[allow(unused)]
fn prover_input_for_modmultiply(modulus_bits: usize) -> HashMap<String, Value>{
    let limbwidth = 121;
    let n_limbs = if modulus_bits == 2048 {17} else if modulus_bits == 4096 {34} else {panic!("Unspported modulus type")};
    let a: BigNat = BigNat::new(&Integer::from(10), limbwidth, n_limbs);
    let b: BigNat = BigNat::new(&Integer::from(17), limbwidth, n_limbs);
    let modul: BigNat = BigNat::new(&Integer::from(127), limbwidth, n_limbs);
    inner_prover_input_for_modmultiply(&a, &b, &modul)
}

fn inner_prover_input_for_modmultiply(a: &BigNat, b: &BigNat, modul: &BigNat) -> HashMap<String, Value>{
    let mm: BigNatModMult = BigNatModMult::new(&a, &b, &modul);
    let mut input_map = HashMap::<String, Value>::default();
    a.alloc_from_nat("a", &mut input_map);
    b.alloc_from_nat("b", &mut input_map);
    modul.alloc_from_nat("modul", &mut input_map); 
    mm.z.alloc_from_nat("z", &mut input_map);
    mm.v.alloc_from_nat("v", &mut input_map);
    mm.quotientb.alloc_from_natb("quotientb", &mut input_map);
    mm.remainderb.alloc_from_natb("remainderb", &mut input_map);
    map_bool_double_vec(&mm.carry, "carry", &mut input_map);
    input_map
}

#[allow(unused)]
fn prover_input_for_modmultiply_with_grouping3() -> HashMap<String, Value>{
    let limbwidth = 32;
    let n_limbs = 64;
    let limbs_per_gp = 6;
    let quotient_bits = 2049;
    let signed_certificate_path = "/home/anna/example_cert/_.google.com.cer";
    let issuer_certificate_path = "/home/anna/example_cert/_GTS_CA_1C3.cer";
    let cert: X509Certificate = X509Certificate::new(signed_certificate_path, issuer_certificate_path);
    cert.print_signature_algorithm();
    let a: BigNatWithLimbMax = if let Signature::StructRSA(rsa_signature) = cert.signature {
                            BigNatWithLimbMax::new(&rsa_signature.signature, limbwidth, n_limbs, false)} else {
                                panic!("Signature is not RSA");
                    }; 
    
    let modul: BigNatWithLimbMax = if let IssuerKey::StructRSA(rsa_key) = cert.issuer_key { 
                            BigNatWithLimbMax::new(&rsa_key.modulus, limbwidth, n_limbs, false)} else { // assume the modul is not constant
                                panic!("Issuer key is not RSA");
                        };
    inner_prover_input_for_modmultiply_with_grouping3(&a, &a, &modul, quotient_bits, limbs_per_gp)
}

fn inner_prover_input_for_modmultiply_with_grouping3(a: &BigNatWithLimbMax, b: &BigNatWithLimbMax, modul: &BigNatWithLimbMax, quotient_bits: usize, limbs_per_gp: usize) -> HashMap<String, Value>{
    let mm: BigNatModMultWithLimbMax = BigNatModMultWithLimbMax::new2(&a, &b, &modul, quotient_bits, limbs_per_gp, false);
    
    let mut input_map = HashMap::<String, Value>::default();
    mm.alloc_complete("", &mut input_map);

    input_map 
}


/// Create prover input
pub fn create_prover_input(compute: ComputeType, aux_input: String, pfcurve: &PfCurve) -> HashMap<String, Value> {

    let result = match compute {
        ComputeType::EddsaSigma => {
            let mut message = Vec::new();
            let mlen: usize = 64 * aux_input.parse::<usize>().expect("failed to parse message len");
            // println!("{}", mlen);
            for i in 0..mlen {
                message.push((i % 256) as u8);
            }
            prover_input_for_verifyeddsa_sigma(message, 5, 55, true)
        }
        ComputeType::VerifyRsaAdvComplete => prover_input_for_verifyrsa_adv(true, false, true, 2048),
        ComputeType::VerifyRsaAdvWhole => prover_input_for_verifyrsa_adv_whole(2048, "", aux_input),
        ComputeType::VerifyEcdsaAdvIncompl => prover_input_for_verifyecdsa(true, true, true, true), // advanced = true; incomplete = true
        ComputeType::VerifyEcdsaAdvIncomplWhole => prover_input_for_verifyecdsa_whole(aux_input), // same as before but include hashing
        ComputeType::VerifyEcdsaSigma => prover_input_for_verifyecdsa_sigma(),
        ComputeType::VerifyEcdsaSigmaWhole => prover_input_for_verifyecdsa_sigma_whole(aux_input), 
        #[cfg(feature = "spartan")]
        ComputeType::VerifyEcdsaRight => prover_input_for_verifyecdsa_rightfield(),// prover_input_for_verifyecdsa_right(),
        #[cfg(feature = "spartan")]
        ComputeType::SpartanTest => prover_input_for_spartantest(&ARC_MOD_CURVE25519),
        #[cfg(feature = "spartan")]
        ComputeType::SpartanTestT256 => prover_input_for_spartantest(&ARC_MOD_T256),
        ComputeType::Sha256Ori => prover_input_for_sha256_ori(aux_input),
        ComputeType::Sha256Adv => prover_input_for_sha256_adv(aux_input, None),
        #[cfg(feature = "spartan")]
        ComputeType::Sha256AdvSpartan => {
            match pfcurve {
                PfCurve::Curve25519 => prover_input_for_sha256_adv(aux_input, Some(&ARC_MOD_CURVE25519)),
                PfCurve::T256 => prover_input_for_sha256_adv(aux_input, Some(&ARC_MOD_T256)),
                PfCurve::T25519 => prover_input_for_sha256_adv(aux_input, Some(&ARC_MOD_T25519)),
            }
        },
        #[cfg(feature = "spartan")]
        ComputeType::VerifyEcdsaRightWhole => prover_input_for_verifyecdsa_rightfield_whole(aux_input), // to do
    };
    result
}
