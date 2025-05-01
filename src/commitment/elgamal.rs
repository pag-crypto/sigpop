use crate::ecdsa::ecdsa::{HASH_G_PROJECT};
use rand_core::RngCore;
use elliptic_curve::Field; // used to generate random scalars

use lazy_static::lazy_static;

use ark_ec::models::short_weierstrass::SWCurveConfig;
use ark_ff::MontFp;
use ark_std::{One, UniformRand};
use ark_secp256r1::{Fq, Fr as Scalar};
use ark_secp256r1::{Projective, Affine, Config};
use core::ops::{Add, Mul};

use serde::{Serializer, Serialize}; // ser/de for sigma proof
use serde::{Deserialize, Deserializer}; // ser/de for sigma proof
pub use ark_std::io::{Read, Write};
use ark_serialize::SerializationError;
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use ark_ec::CurveGroup;

pub const HASH_G_X: Fq = MontFp!("22275546478013928845421778156819724388979498085958565250610071188208345353045");
pub const HASH_G_Y: Fq = MontFp!("87038901988042843095391562964749027457570902217912243630656660389794851490605");
lazy_static! {
    pub static ref HASH_G_AFFINE: Affine = Affine::new(HASH_G_X, HASH_G_Y);
    pub static ref HASH_G_ARK: Projective = Projective::new(HASH_G_X, HASH_G_Y, Fq::one());
    pub static ref G_ARK: Projective = Projective::from(Config::GENERATOR);
    pub static ref L_ARK: Projective = Projective::from(Config::GENERATOR);
    pub static ref L_AFFINE: Affine = Config::GENERATOR; // not sure
}


/// ElGamal-like commitment over P256
#[derive(PartialEq, Clone, Copy)]
pub struct ElGamalCommInner(pub Projective, pub Projective);


impl Serialize for ElGamalCommInner {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut bytes = Vec::new();
        // Serialize both points consecutively
        self.0.serialize_compressed(&mut bytes).unwrap();
        self.1.serialize_compressed(&mut bytes).unwrap();
        bytes.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for ElGamalCommInner {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes = Vec::<u8>::deserialize(deserializer)?;
        // Split the bytes into two parts and deserialize each point
        let point1 = Projective::deserialize_compressed(&bytes[..33])
            .map_err(|e| serde::de::Error::custom(format!("Deserialization error for first point: {:?}", e)))?;
        let point2 = Projective::deserialize_compressed(&bytes[33..])
            .map_err(|e| serde::de::Error::custom(format!("Deserialization error for second point: {:?}", e)))?;
        Ok(ElGamalCommInner(point1, point2))
    }
}


impl ElGamalCommInner {
    pub fn new(left: Projective, right: Projective) -> Self {
        Self(left, right)
    }
    
    /// Serializes both points in compressed form to the provided writer.
    pub fn serialize_compressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        self.0.serialize_compressed(&mut writer)?;
        self.1.serialize_compressed(&mut writer)
    }

    /// Converts both projective points to their affine representations.
    pub fn into_affine(&self) -> (Affine, Affine) {
        (self.0.into_affine(), self.1.into_affine())
    }
}

/// ElGamalComm. This struct acts as a convenient wrapper for ElGamal-like Commitments.
/// At a high-level, this struct is meant to be used whilst producing Pedersen Commitments
/// on the side of the Prover. Namely, this struct carries around the commitment (as two point, `comm`)
/// and the associated randomness. Any serialised proofs should solely use `comm` in their transcripts /
/// serialisations.
pub struct ElGamalComm { // To Do: Make a more generic struct for any prime curve later
    /// comm: the points which acts as the commitment.
    pub comm: ElGamalCommInner,
    /// r: the randomness used to generate `comm`. Should not be serialised.
    pub r: Scalar,
}

impl Add<ElGamalComm> for ElGamalComm { // might need similar things for pointers
    type Output = ElGamalComm;
  
    fn add(self, other: ElGamalComm) -> Self::Output {
        ElGamalComm {
            comm: ElGamalCommInner::new(
                self.comm.0 + other.comm.0, 
                self.comm.1 + other.comm.1
            ),
            r: self.r + other.r,
        }
    }
}

impl Mul<Scalar> for ElGamalComm {
    type Output = ElGamalComm;
  
    fn mul(self, other: Scalar) -> Self::Output {
        ElGamalComm {
            comm: ElGamalCommInner::new(
                self.comm.0 * other, 
                self.comm.1 * other
            ),
            r: self.r * other,
        }
    }
}

impl ElGamalComm {
    /// new. This function accepts a ScalarField element `x` and an rng, returning a Pedersen Commitment
    /// to `x`.
    /// # Arguments
    /// * `x` - the value that is committed to.
    /// * `rng` - the random number generator used to produce the randomness. Must be cryptographically
    /// secure.
    /// Returns a new Pedersen Commitment to `x`.
    pub fn new<T: RngCore>(x: &Scalar, rng: &mut T) -> Self {
        Self::new_with_generators(x, rng, &L_ARK, &G_ARK, &HASH_G_ARK)
    }

    /// the message is a boolean
    pub fn new_with_bool<T: RngCore>(x: bool, rng: &mut T) -> Self {
        let r = Scalar::rand(rng);
        if x {
            Self {
                comm: ElGamalCommInner::new(
                    (*L_ARK * r), 
                    *G_ARK + (*HASH_G_ARK * r)
                ),
                r,
            }
        } else {
            Self {
                comm: ElGamalCommInner::new(
                    *L_ARK * r, 
                    *HASH_G_ARK * r
                ),
                r,
            }
        }
    }

    /// commit to a list of boolean messages
    pub fn new_with_bool_list<T: RngCore>(x: &[bool], rng: &mut T) -> (Vec<ElGamalCommInner>, Vec<Scalar>) {
        let opens: Vec<Scalar> = x.iter().map(|_| Scalar::rand(rng)).collect();
        let comm: Vec<ElGamalCommInner> = x.iter().zip(opens.iter()).map(|(b, r)| {
            if *b {
                ElGamalCommInner::new(
                    *L_ARK * r, 
                    *G_ARK + (*HASH_G_ARK * r)
                )
            } else {
                ElGamalCommInner::new(
                    *L_ARK * r, 
                    *HASH_G_ARK * r
                )
            }
        }).collect();
        (comm, opens)
    }

    /// commit to a list of messages
    pub fn new_with_list<T: RngCore>(x: &[Scalar], rng: &mut T) -> (Vec<ElGamalCommInner>, Vec<Scalar>) {
        let opens: Vec<Scalar> = x.iter().map(|_| Scalar::rand(rng)).collect();
        let comm: Vec<ElGamalCommInner> = x.iter().zip(opens.iter()).map(|(b, r)| {
            ElGamalCommInner::new(
                *L_ARK * r, 
                *G_ARK * b + (*HASH_G_ARK * r)
            )
        }).collect();
        (comm, opens)
    }
    /// new_with_generator. This function accepts a ScalarField element `x`, an `rng`,
    /// and two generators (`g`, `q`) and returns a Pedersen Commitment C = xg + rq. Here `r` is
    /// the produced randomness.
    /// # Arguments
    /// * `x` - the value that is committed to.
    /// * `rng` - the random number generator used to produce the randomness. Must be cryptographically
    /// secure.
    /// * `l` - a generator of `P`'s scalar field.
    /// * `g` - a generator of `P`'s scalar field.
    /// * `q` - a distinct generator of `P`'s scalar field.
    /// Returns a new commitment to `x`.
    pub fn new_with_generators<T: RngCore>(
        x: &Scalar,
        rng: &mut T,
        l: &Projective,
        g: &Projective,
        q: &Projective,
    ) -> Self {
        // Returns a new pedersen commitment using fixed generators.
        // N.B First check that `g != q`.
        assert!(g != q);
        let r = Scalar::rand(rng);
        Self {
            comm: ElGamalCommInner::new(
                (*l * &r), 
                (*g * x) + (*q * &r)
            ),
            r,
        }
    }

    /// new_with_msg_n_opening. This function returns a new Pedersen Commitment to `x` with randomness
    /// `r` (i.e the commitment is C = xg + rq, where `g` and `q` are pre-defined generators.
    /// # Arguments
    /// * `x` - the value that is being committed to.
    /// * `r` - the randomness to use.
    /// Returns a new commitment to `x`.
    pub fn new_with_msg_n_opening(
        x: &Scalar,
        r: &Scalar,
    ) -> Self {
        // let hash_g_project: Projective = *HASH_G_ARK;
        Self {
            comm: ElGamalCommInner::new(
                Config::GENERATOR * r,
                (Config::GENERATOR * x) + (*HASH_G_ARK * r)
            ),
            r: *r,
        }
    }
}