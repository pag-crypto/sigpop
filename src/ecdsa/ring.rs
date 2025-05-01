use ark_secp256r1::{Projective as ark_Projective, Fq, Fr as Scalar};
use ark_secp256r1::{Projective, Config};
use super::pure_sigma::{
    ECDSASigmaPublicPrior, 
    ECDSASigmaPublic, 
    ECDSASigmaSetupParamsPrior, 
    create_proof
};
use crate::ecdsa::group::{ArkECPoint, ArkScalar, ECPoint};
use crate::target::r1cs::proof::{serialize_into_file, deserialize_from_file};

use ark_ec::CurveGroup;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::{BigInteger, PrimeField};
use merlin::Transcript;
use rand::rngs::OsRng;
use ark_std::{Zero, One, UniformRand};
use ark_ec::VariableBaseMSM;
use rand_core::RngCore;
use ark_ec::ScalarMul;
use crate::commitment::transcript::{GKMemberTranscript, CHALLENGE_SIZE};
use ark_serialize::CanonicalSerialize;
use ark_ff::Field;
use std::convert::TryInto;
use serde::{Serialize, Deserialize};

use std::time::Instant;
use crate::util::timer::print_time;
use crate::conditional_print;

use crate::commitment::pedersen::{G_ARK, PedersenComm};
use crate::commitment::elgamal::{ElGamalComm, ElGamalCommInner};
use crate::commitment::gk_mem::{MemberProofSerde, MemberProof};
use super::ecdsa::{EllipticCurveP256, ECDSASignatureVar, P256Point};
use p256::{ProjectivePoint};
use crate::parse_cert::{read_example_cert, parse_ecdsa_pk_sig, get_message_from_example_cert};
use std::path::Path;       
use rug::Integer;
use crate::hash::hash::DigestAlgorithm;
use std::str::FromStr;

pub const PRINT_MSG: bool = true;

#[derive(Serialize, Deserialize)]
pub struct Statement {
    /// Commitments to public key
    pub cm_pk: [ECPoint; 2],
    /// Partial Signature; The random elliptic curve point
    pub pt_r: ECPoint,
    /// List of public key
    pub pk_list: Vec<ArkECPoint>,
}

#[derive(Serialize, Deserialize)]
pub struct RingProof {
    /// Prove that the commited public key is in the ring
    pub member_proof: MemberProofSerde,
    /// Given committed pk, public R and public m, show that the prover knows a signature-message pair corresponding to the public key pk 
    pub ecdsa_proof: ECDSASigmaPublic,
}

fn len_of_list(N: usize) -> usize {
    1 << N
}

fn create_pk_list(pk: &ark_Projective, l: usize, N: usize) -> Vec<ark_Projective> {
    let mut rng = ark_std::test_rng();
    let LEN = len_of_list(N);
    let scalars = (0..LEN-1).map(|_| Scalar::rand(&mut rng))
                    .collect::<Vec<Scalar>>();
    let mut pk_list = scalars.iter().map(|s| *G_ARK * s)
                    .collect::<Vec<ark_Projective>>();
    pk_list.insert(l, *pk);
    pk_list
}

// hash the list of public keys in the setup phrase
fn hash_m_list(m_list: &Vec<ark_Projective>) -> [u8; CHALLENGE_SIZE] {
    let mut transcript = Transcript::new(b"Setup_GK_Membership_Proof");
    let mut compressed_bytes = Vec::new();
    for (i, m) in m_list.iter().enumerate() {
        m.serialize_compressed(&mut compressed_bytes).unwrap();
        transcript.append_point(b"m_list", &compressed_bytes[..]);
    }
    transcript.challenge_scalar(b"m_list")
}

fn write_statement_and_proof<P: AsRef<Path>>(
    pk_list: &Vec<ark_Projective>,
    member_proof: MemberProofSerde,
    ecdsa_proof: ECDSASigmaPublicPrior, 
    st_path: P,
    pf_path: P,
) {
    let (statement, proof) = convert_to_statement_and_proof(
        pk_list, 
        member_proof, 
        ecdsa_proof
    );
    let _ = serialize_into_file(&statement, st_path);
    let _ = serialize_into_file(&proof, pf_path);
}

fn convert_to_statement_and_proof(
    pk_list: &Vec<ark_Projective>,
    member_proof: MemberProofSerde,
    ecdsa_proof: ECDSASigmaPublicPrior, 
) -> (Statement, RingProof) {
    let statement = Statement { 
        cm_pk: ecdsa_proof.cm_pk.clone(), 
        pt_r: ecdsa_proof.pt_r.clone(), 
        pk_list: ArkECPoint::batch_from_projective(&pk_list),
    };
    let pure_ecdsa_proof = ECDSASigmaPublic { 
        responses: ecdsa_proof.responses.clone(),
        comm: ecdsa_proof.comm.clone(),
    };
    let ring_proof = RingProof { 
        member_proof, 
        ecdsa_proof: pure_ecdsa_proof
    };
    (statement, ring_proof)
}

fn from_statement_and_proof(
    statement: &Statement, 
    proof: &RingProof
) -> (
    ElGamalCommInner, 
    Vec<ark_Projective>, 
    MemberProof, 
    ECDSASigmaPublicPrior
) {
    let pk_list = ArkECPoint::batch_to_projective(&statement.pk_list);
    let comm: ElGamalCommInner = ElGamalCommInner::new(
        P256Point::projective_to_ark_projective(
            &statement.cm_pk[0].0
        ),
        P256Point::projective_to_ark_projective(
            &statement.cm_pk[1].0
        )
    );
    let member_proof = proof.member_proof.unwrap();
    let ecdsa_proof = ECDSASigmaPublicPrior {
        responses: proof.ecdsa_proof.responses,
        comm: proof.ecdsa_proof.comm,
        cm_pk: statement.cm_pk,
        pt_r: statement.pt_r,
    };
    (comm, pk_list, member_proof, ecdsa_proof)
}

fn print_proof_size(
    N: usize, // ring size
) {
    let scalar_bitlen = 256;
    let point_bitlen = 257; // ~33 bytes
    let ecdsa_proof_bitlen = 4 * scalar_bitlen + 4 * point_bitlen;
    let member_proof_bitlen = 2 * 4 * N * point_bitlen + (3 * N + 1) * scalar_bitlen;
    let proof_bitlen = ecdsa_proof_bitlen + member_proof_bitlen;
    println!("Proof size for ring depth {}: {} bit", N, proof_bitlen);
    let scalar_bytelen = scalar_bitlen / 8;
    let point_bytelen = 33;
    let ecdsa_proof_bytelen = 4 * scalar_bytelen + 4 * point_bytelen;
    // let member_proof_bytelen = 4 * N * point_bytelen + (3 * N + 1) * scalar_bytelen;
    let member_proof_bytelen = 2 * 4 * N * point_bytelen + (3 * N + 1) * scalar_bytelen;
    let proof_bytelen = ecdsa_proof_bytelen + member_proof_bytelen;
    println!("Proof size for ring depth {}: {} byte", N, proof_bytelen);
}

fn print_statement_size(N: usize) {
    let point_bytelen = 33;
    let LEN = len_of_list(N);
    let statement_bytelen = (2 + 1 + LEN) * point_bytelen;
    println!("Statement size for ring depth {}: {} byte", N, statement_bytelen);
}
/// Prover for ring signature for ECDSA
pub fn prover<P: AsRef<Path>>(
    st_path: P,
    pf_path: P,
    N: usize, // ring size
) {
    let cert = read_example_cert();
    let params = ECDSASigmaSetupParamsPrior::new();
    let (ecdsa_key, ecdsa_signature) = parse_ecdsa_pk_sig(&cert).unwrap();
    // Computations that are irrelated to the proving phase, including the following:
    // * Create a list of public keys
    // * Create a signature-message pair to a specific public key in the list
    let digest_result: Integer = DigestAlgorithm::sha256(&(cert.body));
    let issuer_key_p256pt: P256Point = ecdsa_key.to_p256point();
    let issuer_key_pt: ProjectivePoint = issuer_key_p256pt.to_projective_point(); // actually we only need projectivepoint
    let issuer_key_arkpt: ark_Projective = issuer_key_p256pt.to_ark_projective_point();
    let signature_var: ECDSASignatureVar = ECDSASignatureVar::from_ecdsasignature(
                                                &ecdsa_signature, 
                                                digest_result.clone(), 
                                                issuer_key_pt, 
                                                EllipticCurveP256::new().q.clone()
                                            );
    let l = 1;
    let l_scalar = Scalar::from(l as u32);
    let pk_list = create_pk_list(&issuer_key_arkpt, l, N);
    let hash_pk_list = hash_m_list(&pk_list);
    let start = Instant::now();
    let (ecdsa_proof, opening) = create_proof (
        issuer_key_pt,
        signature_var, 
        &cert.body,
        params,
    );
    let mut transcript = Transcript::new(b"GK_Membership_Proof");
    let mut rng = ark_std::test_rng();
    let opening_scalar = Scalar::from_str(&opening.to_string_radix(10)).unwrap();

    let cm = ElGamalComm {
        comm: ElGamalCommInner::new(
            P256Point::projective_to_ark_projective(&ecdsa_proof.cm_pk[0].0),
            P256Point::projective_to_ark_projective(&ecdsa_proof.cm_pk[1].0)
        ),
        r: opening_scalar,
    };
    
    let gk_proof = MemberProofSerde::create( // now
        &mut transcript,
        &mut rng,
        &cm,
        &pk_list,
        &hash_pk_list,
        &l_scalar,
        N
    );
    print_time("Time for Proving", start.elapsed(), PRINT_MSG);

    write_statement_and_proof(
        &pk_list,
        gk_proof,
        ecdsa_proof,
        st_path,
        pf_path,
    );
    conditional_print!("Proof has been written to file `pi_sigma`");
}

/// Verifier for ring signature for ECDSA
pub fn verifier<P: AsRef<Path>>(
    st_path: P,
    pf_path: P,
    N: usize, // ring size
) {
    let digest_result: Integer = {
        let message = get_message_from_example_cert();
        DigestAlgorithm::sha256(&message)
    };
    let statement: Statement = deserialize_from_file(st_path).unwrap();
    let proof: RingProof = deserialize_from_file(pf_path).unwrap();
    let params = ECDSASigmaSetupParamsPrior::new();

    let (cm_pk, pk_list, member_proof, ecdsa_proof) = 
        from_statement_and_proof(&statement, &proof);
    let hash_pk_list = hash_m_list(&pk_list);
    let start = Instant::now();
    ecdsa_proof.verify(&digest_result, params);
    let mut transcript = Transcript::new(b"GK_Membership_Proof");
    assert!(member_proof.verify(
        &mut transcript,
        &cm_pk,
        &pk_list,
        &hash_pk_list,
        N,
    ));
    print_time("Time for Verifying", start.elapsed(), PRINT_MSG);
}