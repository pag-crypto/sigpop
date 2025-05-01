//! 1-out-of-N Membership proof over Pedersen Commitment
//! From https://eprint.iacr.org/2014/764.pdf, Figure 2
//! Optimized for ring signatures; Might not work for other cases
use super::pedersen::PedersenComm;
use super::elgamal::{ElGamalComm, ElGamalCommInner, L_ARK};
use super::pedersen::{HASH_G_AFFINE, HASH_G_ARK, G_ARK};
use ark_ec::CurveGroup;
use super::compute_poly::{compute_pi_dp, compute_pi_eval_dp};

use ark_secp256r1::{Fq, Fr as Scalar};
use ark_secp256r1::{Projective, Config};
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::{BigInteger, PrimeField};
use merlin::Transcript;
use rand::rngs::OsRng;
use ark_std::{Zero, One, UniformRand};
use ark_ec::VariableBaseMSM;
use rand_core::RngCore;
use ark_ec::ScalarMul;
use super::transcript::GKMemberTranscript;
use ark_serialize::CanonicalSerialize;
use ark_ff::Field;
use std::convert::TryInto;
use serde::{Serialize, Deserialize};
use crate::ecdsa::group::{ArkECPoint, ArkScalar};
use std::env;

use std::time::Instant;
use crate::util::timer::print_time;


/// MemberProofTranscriptable. This trait provides a notion of `Transcriptable`, which implies
/// that the particular struct can, in some sense, be added to a transcript for the zero-one proof.
pub trait MemberProofTranscriptable {
    /// add_to_transcript. This function simply adds the commitments held by `self` to the `transcript`
    /// object.
    /// # Arguments
    /// * `self` - the proof object.
    /// * `transcript` - the transcript which is modified.
    /// * `cm` - a commitment to M_{l}.
    /// * `M_list` - [M_{0}, · · · , M_{N−1}].
    fn add_to_transcript(&self, transcript: &mut Transcript, cm: &ElGamalCommInner, hash_m_list: &[u8]);
}

/// MemberProof. This struct acts as a container for a membership proof
/// Length of comm_l/comm_a/comm_b/comm_d is n = log2(N)
/// New proof objects can be made via the `create` function, whereas existing
/// proofs may be verified via the `verify` function.
#[derive(Serialize, Deserialize)]
pub struct MemberProofSerde {
    /// The commitments to the bits of the index l
    pub comm_l: Vec<ElGamalCommInner>,
    /// The commitments to randomnesss
    pub comm_a: Vec<ElGamalCommInner>,
    /// The commitments to l_j * a_j
    pub comm_b: Vec<ElGamalCommInner>,
    /// The commitments for cancelling out the low order coefficients
    pub comm_d: Vec<ElGamalCommInner>,

    /// f_i
    pub f: Vec<ArkScalar>,
    /// Opening z_{a_j}
    pub z_a: Vec<ArkScalar>,
    /// Opening z_{b_j}
    pub z_b: Vec<ArkScalar>,
    /// Opening z_{d_j}
    pub z_d: ArkScalar,
}

pub struct MemberProof {
    /// The commitments to the bits of the index l
    pub comm_l: Vec<ElGamalCommInner>,
    /// The commitments to randomnesss
    pub comm_a: Vec<ElGamalCommInner>,
    /// The commitments to l_j * a_j
    pub comm_b: Vec<ElGamalCommInner>,
    /// The commitments for cancelling out the low order coefficients
    pub comm_d: Vec<ElGamalCommInner>,

    /// f_i
    pub f: Vec<Scalar>,
    /// Opening z_{a_j}
    pub z_a: Vec<Scalar>,
    /// Opening z_{b_j}
    pub z_b: Vec<Scalar>,
    /// Opening z_{d_j}
    pub z_d: Scalar,
}

/// MemberProofIntermediate. This struct provides a convenient wrapper for building
/// all of the the random values _before_ the challenge is generated. This struct
/// should only be used if the transcript needs to be modified in some way before
/// the proof is generated.
pub struct MemberProofIntermediate {
    /// Public messages
    pub pubmsg: MemberProofIntermediatePublic,
    /// Private messages
    pub wit: MemberProofIntermediatePrivate,
}

/// MemberProofIntermediatePrivate. This struct contains the private messages
pub struct MemberProofIntermediatePrivate {
    /// Randomness generated in the first round
    pub a: Vec<Scalar>,
    /// The randomness used to generate the commitments to the bits of l
    pub o_l: Vec<Scalar>,
    /// The randomness used to generate the commitments to the a_j
    pub o_a: Vec<Scalar>,
    /// The randomness used to generate the commitments to the b_j
    pub o_b: Vec<Scalar>,
    /// The randomness used to generate the commitments to the d_j
    pub o_d: Vec<Scalar>,
}

/// MemberProofIntermediatePublic.
pub struct MemberProofIntermediatePublic {
    /// comm_l: the commitment to the bits of l.
    pub comm_l: Vec<ElGamalCommInner>,

    /// ca: the commitment to the randomness.
    pub comm_a: Vec<ElGamalCommInner>,

    /// cb: the commitment to `la`.
    pub comm_b: Vec<ElGamalCommInner>,

    /// cd: the commitment to the low order coefficients.
    pub comm_d: Vec<ElGamalCommInner>,
}

impl MemberProofSerde {
    /// create. This function creates a new MemberProof, returning a proof for the relation as follows:
    /// (G, pp), (cm, L = (M_{0}, · · · , M_{N−1})), (l, o) so that:
    /// (1) l ∈ {0,...,N−1},
    /// (2) cm = Com_{pp}(M_{l},o).
    /// # Arguments
    /// * `transcript` - the transcript object. The intermediate commitments etc are added to this transcript.
    /// * `rng` - the random number generator to use. Must be cryptographically random.
    /// * `cm` - a commitment to M_{l} and its opening (ElGamal-like commitment to m_l without prover knowing m_l).
    /// * `M_list` - [M_{0}, · · · , M_{N−1}]
    /// Note: In our use case, M_{l} is the issuer's public key, 
    ///         and the prover does not know the secret key m_l of the issuer.
    pub fn create<T: RngCore>(
        transcript: &mut Transcript,
        rng: &mut T,
        cm: &ElGamalComm, // This struct includes the opening
        m_list: &Vec<Projective>,
        hash_m_list: &[u8], // Move the hash of the list of public keys to the setup phase
        l: &Scalar,
        N: usize,
    ) -> Self {
        assert_eq!(m_list.len(), 1<<N);
        let l_bits = l.into_bigint().to_bits_le(); 
        let l_bits = &l_bits[..N];
        let pf = MemberProof::create_proof_with_challenge(
            &cm.r,
            &MemberProof::phase_0(transcript, rng, &cm.comm, m_list, hash_m_list, l_bits, N),
            l_bits,
            &Scalar::from_be_bytes_mod_order(&transcript.challenge_scalar(b"x")[..]),
            N
        );
        pf
    }

    /// Convert MemberProofSerde to MemberProof
    pub fn unwrap(&self) -> MemberProof {
        MemberProof {
            comm_l: self.comm_l.clone(),
            comm_a: self.comm_a.clone(),
            comm_b: self.comm_b.clone(),
            comm_d: self.comm_d.clone(),
            f: ArkScalar::batch_to_scalar(&self.f),
            z_a: ArkScalar::batch_to_scalar(&self.z_a),
            z_b: ArkScalar::batch_to_scalar(&self.z_b),
            z_d: self.z_d.0,
        }
    }
}

impl MemberProof {
    /// make_transcript. This function just adds the affine commitments `cl`, `ca`, `cb`, `cd` to the
    /// `transcript` object.
    pub fn make_transcript(
        transcript: &mut Transcript,
        cm: &ElGamalCommInner,
        hash_m_list: &[u8],
        comm_l: &Vec<ElGamalCommInner>,
        comm_a: &Vec<ElGamalCommInner>,
        comm_b: &Vec<ElGamalCommInner>,
        comm_d: &Vec<ElGamalCommInner>,
    ) {
        transcript.domain_sep();

        // Serialize the primary commitment using your Serialize implementation.
        let compressed_cm = bincode::serialize(cm).expect("Serialization failed");
        transcript.append_point(b"cm", &compressed_cm);

        transcript.append_message(b"m_list", hash_m_list);

        // Serialize and append each commitment in the comm_l vector.
        for c in comm_l {
            let compressed = bincode::serialize(c).expect("Serialization failed");
            transcript.append_point(b"comm_l", &compressed);
        }

        for c in comm_a {
            let compressed = bincode::serialize(c).expect("Serialization failed");
            transcript.append_point(b"comm_a", &compressed);
        }

        for c in comm_b {
            let compressed = bincode::serialize(c).expect("Serialization failed");
            transcript.append_point(b"comm_b", &compressed);
        }

        for c in comm_d {
            let compressed = bincode::serialize(c).expect("Serialization failed");
            transcript.append_point(b"comm_d", &compressed);
        }
    }
    
    /// phase_0. This function creates a new set of intermediate values for the membership proof.
    /// This function should be called before a challenge is generated.
    /// # Arguments
    /// * `transcript` - the transcript object. The intermediate commitments are added to this transcript.
    /// * `rng` - the random number generator to use. Must be cryptographically random.
    /// * `cm` - a commitment to M_{l} (Pedersen commitment to m_l without prover knowing m_l).
    /// Outputs (First round message of the prover)
    /// * (c_{l_i})_{i \in [n]}
    /// * (c_{a_i})_{i \in [n]}
    /// * (c_{b_i})_{i \in [n]}
    /// * (c_{d_i})_{i \in [n]}
    /// Notes: 
    /// * We use Pedersen commitments for all these commitments
    /// * Internal outputs for the prover: openings for comm_l, comm_a, comm_b, comm_d and a_j
    pub fn phase_0<T: RngCore>(
        transcript: &mut Transcript,
        rng: &mut T,
        cm: &ElGamalCommInner,
        m_list: &Vec<Projective>,
        hash_m_list: &[u8],
        l_bits: &[bool],
        N: usize,
    ) -> MemberProofIntermediate {
        let (comm_l, o_l) = ElGamalComm::new_with_bool_list(&l_bits, rng);
        let a_list = (0..N)
            .map(|_| Scalar::rand(rng))
            .collect::<Vec<_>>();
        let (comm_a, o_a) = ElGamalComm::new_with_list(&a_list, rng);
        let a_l = a_list
            .iter()
            .zip(l_bits.iter())
            .map(|(a, l_b)| if *l_b {*a} else {Scalar::zero()})
            .collect::<Vec<_>>();
        let (comm_b, o_b) = ElGamalComm::new_with_list(&a_l, rng);
        let (comm_d, rho) = {
            let mut comm_d = Vec::with_capacity(N);
            let mut rho = Vec::with_capacity(N);

            // create second element of (c_0, c_1, ..., c_{N-1}, h)
            // Note: the first element in each element in c_0, c_1, ..., c_{N-1} is the same
            let bases_affine = {
                let mut bases = m_list.iter().map(|m| cm.1 - m).collect::<Vec<_>>();
                bases.push(*HASH_G_ARK);
                Projective::batch_convert_to_mul_base(&bases)
            };

            let mut poly_coeffs = compute_pi_dp(&a_list, &l_bits);
            // let start = Instant::now(); // debug
            for i in 0..N {
                let mut scalars = Vec::with_capacity(bases_affine.len());
                for poly in poly_coeffs.iter() {
                    scalars.push(poly.coeffs[i]);
                }
                let sum_scalars: Scalar = scalars.clone().into_iter().sum();
                let open = Scalar::rand(rng);
                rho.push(open);
                scalars.push(open);
                // c_0 * p_{0, k} + ... + c_{N-1} * p_{N-1, k} + Comm(0; r_k) where r_k = open
                comm_d.push(
                    ElGamalCommInner::new(
                        cm.0 * sum_scalars + *L_ARK * open, // cm.0 is a point whereas sum_scalars is a scalar
                        //(c_0, c_1, ..., c_{N-1}, h) * (p_{0, k}, p_{1, k}, ..., p_{N-1, k}, r_k)
                        Projective::msm(
                            &bases_affine, 
                            &scalars 
                        ).unwrap()
                    )
                );
            }
            // print_time("Time for Computing comm_d", start.elapsed(), true); // debug

            (comm_d, rho)
        };

        // Add them to the transcript and then just return the intermediate object.
        Self::make_transcript(
            transcript, 
            cm,
            hash_m_list,
            &comm_l, 
            &comm_a, 
            &comm_b, 
            &comm_d
        ); 
        MemberProofIntermediate { 
            pubmsg: MemberProofIntermediatePublic { 
                comm_l, comm_a, comm_b, comm_d 
            },
            wit: MemberProofIntermediatePrivate { 
                a: a_list, o_l, o_a, o_b, o_d: rho 
            }
        }
    }

    /// create_proof_with_challenge. This function returns a new MemberProof, returning the result. Note that this
    /// function uses the challenge in `chal_buf` to generate the proof.
    /// # Arguments
    /// * `r` - opening to cm.
    /// * `inter` - the intermediate values.
    /// * `l_bits` - binary representation of the index l.
    /// * `chal_buf` - a buffer of existing challenge bytes.
    pub fn create_proof_with_challenge(
        r: &Scalar,
        inter: &MemberProofIntermediate,
        l_bits: &[bool],
        chal: &Scalar,
        N: usize,
    ) -> MemberProofSerde {
        let f = l_bits.iter().zip(inter.wit.a.iter())
            .map(|(l, a)| if *l { *chal + *a } else { *a })
            .collect::<Vec<_>>();
        let z_a = inter.wit.o_l.iter().zip(&inter.wit.o_a)
            .map(|(r_j, s_j)| r_j*chal + s_j)
            .collect::<Vec<_>>();
        let z_b = inter.wit.o_l.iter().zip(&f).zip(&inter.wit.o_b)
            .map(|((r_j, f_j), t_j)| *r_j * (chal-f_j) + t_j)
            .collect::<Vec<_>>();
        let mut powers_of_x: Vec<Scalar> = Vec::with_capacity(N+1);
        let mut cur_power_of_x = Scalar::one();
        for _ in 0..=N {
            powers_of_x.push(cur_power_of_x);
            cur_power_of_x *= chal;
        }
        let scalars = inter.wit.o_d.clone();
        let z_d = {
            let slice_x  = &powers_of_x[..N];
            let slice_od = &inter.wit.o_d[..N];
            
            let sum = slice_x.iter()
                             .zip(slice_od)
                             .map(|(x, d)| *x * *d)
                             .fold(Scalar::zero(), |acc, v| acc + v);
            
            r * powers_of_x.last().unwrap() - sum
        };

        MemberProofSerde {
            comm_l: inter.pubmsg.comm_l.clone(),
            comm_a: inter.pubmsg.comm_a.clone(),
            comm_b: inter.pubmsg.comm_b.clone(),
            comm_d: inter.pubmsg.comm_d.clone(),
            f: ArkScalar::batch_from_scalar(&f),
            z_a: ArkScalar::batch_from_scalar(&z_a),
            z_b: ArkScalar::batch_from_scalar(&z_b),
            z_d: ArkScalar(z_d),
        }
    }   

    /// verify. This function verifies that the proof held by `self` is valid, returning true if so.
    /// # Arguments
    /// * `self` - the proof object.
    /// * `transcript` - the transcript object.
    /// * `cm` - a commitment to M_{l}
    /// * `M_list` - [M_{0}, · · · , M_{N−1}]
    pub fn verify(
        &self, 
        transcript: &mut Transcript, 
        cm: &ElGamalCommInner,
        m_list: &Vec<Projective>,
        hash_m_list: &[u8],
        N: usize,
    ) -> bool {
        self.add_to_transcript(transcript, cm, hash_m_list);
        self.verify_proof_with_challenge(
            cm, 
            m_list, 
            &Scalar::from_be_bytes_mod_order(&transcript.challenge_scalar(b"x")[..]),
            N
        )
    }

    /// verify_proof_with_challenge. This function verifies that the proof held by `self` is valid, returning true if so.
    /// This function uses the challenge bytes `chal_buf` to make the challenge.
    /// # Arguments
    /// * `self` - the proof object.
    /// * `cm` - a commitment to M_{l}
    /// * `M_list` - [M_{0}, · · · , M_{N−1}]
    pub fn verify_proof_with_challenge(
        &self, 
        cm: &ElGamalCommInner,
        m_list: &Vec<Projective>,
        chal: &Scalar,
        N: usize,
    ) -> bool {
        for ((c_l, c_a), (f_j, z_a_j)) in self.comm_l.iter()
            .zip(self.comm_a.iter())
            .zip(self.f.iter().zip(self.z_a.iter()))
        {
            // check c_{aj} = c_{lj}^{-chal} Com(f_j; z_{aj})
            // First element of rhs = c0_{lj}^{-chal} L^{z_{aj}} 
            // Second element of rhs = c1_{lj}^{-chal} G^{fj} K^{z_{aj}} where K = HASH_G_AFFINE
            let bases = vec![c_l.1.into_affine(), Config::GENERATOR, *HASH_G_AFFINE];  // Dereference `c_l` to use its value
            let scalars = vec![-(*chal), *f_j, *z_a_j];   // Dereference `chal`, `f_j`, and `z_a_j` to get values
        
            let expect_c_a = ElGamalCommInner::new(
                c_l.0 * -(*chal) + *L_ARK * (*z_a_j),
                Projective::msm(&bases, &scalars).unwrap()
            );
        
            if *c_a != expect_c_a {
                return false;
            }
        }
        for ((c_l, c_b), (f_j, z_b_j)) in self.comm_l.iter()
            .zip(self.comm_b.iter())
            .zip(self.f.iter().zip(self.z_b.iter()))
        {
            // Check c_{bj} = c_{lj}^{f_j-x} Com(0; z_{bj})
            // First element of rhs = c0_{lj}^{f_j-x} L^{z_{bj}}
            // Second element of rhs = c1_{lj}^{f_j-x} K^{z_{bj}} where K = HASH_G_AFFINE
            let bases = vec![c_l.1.into_affine(), *HASH_G_AFFINE];
            let scalars = vec![*f_j - *chal, *z_b_j];
        
            let expect_c_b = ElGamalCommInner::new(
                c_l.0 * (*f_j - *chal) + *L_ARK * (*z_b_j),
                Projective::msm(&bases, &scalars).unwrap()
            );
            
        
            if *c_b != expect_c_b {
                return false;
            }
        }
        // let start = Instant::now(); // debug
        let polys = compute_pi_eval_dp(&self.f, chal);
        let sum_poly = polys.clone().into_iter().sum();
        let powers_of_x_neg: Vec<Scalar> = {
            let mut cur_power_of_x = Scalar::one();
            let mut powers_of_x = Vec::with_capacity(N); 
            for _ in 1..=N {
                powers_of_x.push(-cur_power_of_x);
                cur_power_of_x *= chal;
            }
            powers_of_x
        };
        // print_time("Time for Computing Polynomial Evaluation", start.elapsed(), true); // debug
        let expected_zero_comm0 = {
            let bases_affine = {
                let mut bases: Vec<Projective> = Vec::with_capacity(1 + N);
                bases.push(cm.0);
                bases.extend(
                    self.comm_d.iter()
                    .map(|comm| comm.0.clone())
                );
                Projective::batch_convert_to_mul_base(&bases)
            };

            let mut scalars = Vec::with_capacity(1 + N);
            scalars.push(sum_poly);
            scalars.extend(powers_of_x_neg.iter().cloned());
            // (c0, c1_{d_0}, ..., c1_{d_{n-1}}) * (\sum_i p_i(x)}, -x^0, -x^1, ..., -x^{n-1})
            Projective::msm(&bases_affine, &scalars).unwrap()
        };
        let expected_zero_comm1 = {
            let scalars: Vec<Scalar> = {
                let mut scalars: Vec<Scalar> = vec![sum_poly];
                for poly in polys.iter() {
                    scalars.push(-*poly);
                }
                scalars.extend(powers_of_x_neg.iter().cloned());
                
                scalars
            };
    
            let bases_affine = { // to compute the second part of expected_zero_comm
                let mut bases: Vec<Projective> = vec![cm.1];
                bases.extend(m_list.clone());
                bases.extend(
                    self.comm_d.iter()
                    .map(|comm| comm.1.clone())
                );
                Projective::batch_convert_to_mul_base(&bases)
            };
            // (c_1, pk_0, ..., pk_{N-1}, c1_{d_0}, ..., c1_{d_{n-1}}) * (\sum_i p_i(x)}, -p_0(x), ..., -p_{N-1}(x), -x^0, -x^1, ..., -x^{n-1})
            Projective::msm(&bases_affine, &scalars).unwrap() // len (2^n) + n + 1
        };

        // let start = Instant::now(); // debug
        let actual_zero_comm = ElGamalCommInner::new(
            *L_ARK * self.z_d, // L^{z_d}
            *HASH_G_ARK * self.z_d, // K^{z_d}
        );
        let expected_zero_comm = ElGamalCommInner::new(
            expected_zero_comm0,
            expected_zero_comm1
        );

        // print_time("Time for Computing expected_zero_comm", start.elapsed(), true); // debug
        if actual_zero_comm != expected_zero_comm {
            return false;
        }
        true
    }


}

impl MemberProofTranscriptable for MemberProof {
    fn add_to_transcript(
        &self, 
        transcript: &mut Transcript, 
        cm: &ElGamalCommInner,
        hash_m_list: &[u8],
    ) {
        MemberProof::make_transcript(
            transcript, 
            cm,
            hash_m_list,
            &self.comm_l, 
            &self.comm_a, 
            &self.comm_b, 
            &self.comm_d
        );
    }
}