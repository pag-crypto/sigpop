//! This module includes implementations related to Pedersen Commitment
//! Adapt from https://github.com/brave-experiments/CDLS/blob/main/pedersen/src/pedersen_config.rs

// use p256::{Scalar, ProjectivePoint};
// use crate::p256curve::HASH_G_PROJECT;
use crate::ecdsa::ecdsa::{HASH_G_PROJECT};
use rand_core::RngCore;
use elliptic_curve::Field; // used to generate random scalars

// use std::ops;

use lazy_static::lazy_static;

use ark_ec::models::short_weierstrass::SWCurveConfig;
use ark_ff::MontFp;
use ark_std::{One, UniformRand};
use ark_secp256r1::{Fq, Fr as Scalar};
use ark_secp256r1::{Projective, Affine, Config};
use core::ops::{Add, Mul};

pub const HASH_G_X: Fq = MontFp!("22275546478013928845421778156819724388979498085958565250610071188208345353045");
pub const HASH_G_Y: Fq = MontFp!("87038901988042843095391562964749027457570902217912243630656660389794851490605");
lazy_static! {
    pub static ref HASH_G_AFFINE: Affine = Affine::new(HASH_G_X, HASH_G_Y);
    pub static ref HASH_G_ARK: Projective = Projective::new(HASH_G_X, HASH_G_Y, Fq::one());
    pub static ref G_ARK: Projective = Projective::from(Config::GENERATOR);
}
/// PedersenComm. This struct acts as a convenient wrapper for Pedersen Commitments.
/// At a high-level, this struct is meant to be used whilst producing Pedersen Commitments
/// on the side of the Prover. Namely, this struct carries around the commitment (as a point, `comm`)
/// and the associated randomness. Any serialised proofs should solely use `comm` in their transcripts /
/// serialisations.
pub struct PedersenComm { // To Do: Make a more generic struct for any prime curve later
    /// comm: the point which acts as the commitment.
    pub comm: Projective,
    // pub comm: ProjectivePoint,
    /// r: the randomness used to generate `comm`. Should not be serialised.
    pub r: Scalar,
}

impl Add<PedersenComm> for PedersenComm { // might need similar things for pointers
    type Output = PedersenComm;
  
    fn add(self, other: PedersenComm) -> Self::Output {
        PedersenComm {
            comm: self.comm + other.comm,
            r: self.r + other.r,
        }
    }
}

impl Mul<Scalar> for PedersenComm {
    type Output = PedersenComm;
  
    fn mul(self, other: Scalar) -> Self::Output {
        PedersenComm {
            comm: self.comm * other,
            r: self.r * other,
        }
    }
}

impl PedersenComm {
    /// new. This function accepts a ScalarField element `x` and an rng, returning a Pedersen Commitment
    /// to `x`.
    /// # Arguments
    /// * `x` - the value that is committed to.
    /// * `rng` - the random number generator used to produce the randomness. Must be cryptographically
    /// secure.
    /// Returns a new Pedersen Commitment to `x`.
    pub fn new<T: RngCore>(x: &Scalar, rng: &mut T) -> Self {
        Self::new_with_generators(x, rng, &G_ARK, &HASH_G_ARK)
    }

    /// the message is a boolean
    pub fn new_with_bool<T: RngCore>(x: bool, rng: &mut T) -> Self {
        let r = Scalar::rand(rng);
        if x {
            Self {
                comm: *G_ARK + (*HASH_G_ARK * r),
                r,
            }
        } else {
            Self {
                comm: *HASH_G_ARK * r,
                r,
            }
        }
    }

    /// commit to a list of boolean messages
    pub fn new_with_bool_list<T: RngCore>(x: &[bool], rng: &mut T) -> (Vec<Projective>, Vec<Scalar>) {
        let opens: Vec<Scalar> = x.iter().map(|_| Scalar::rand(rng)).collect();
        let comm: Vec<Projective> = x.iter().zip(opens.iter()).map(|(b, r)| {
            if *b {
                *G_ARK + (*HASH_G_ARK * r)
            } else {
                *HASH_G_ARK * r
            }
        }).collect();
        (comm, opens)
    }

    /// commit to a list of messages
    pub fn new_with_list<T: RngCore>(x: &[Scalar], rng: &mut T) -> (Vec<Projective>, Vec<Scalar>) {
        let opens: Vec<Scalar> = x.iter().map(|_| Scalar::rand(rng)).collect();
        let comm: Vec<Projective> = x.iter().zip(opens.iter()).map(|(b, r)| {
            *G_ARK * b + (*HASH_G_ARK * r)
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
    /// * `g` - a generator of `P`'s scalar field.
    /// * `q` - a distinct generator of `P`'s scalar field.
    /// Returns a new commitment to `x`.
    pub fn new_with_generators<T: RngCore>(
        x: &Scalar,
        rng: &mut T,
        g: &Projective,
        q: &Projective,
    ) -> Self {
        // Returns a new pedersen commitment using fixed generators.
        // N.B First check that `g != q`.
        assert!(g != q);
        let r = Scalar::rand(rng);
        Self {
            comm: (*g * x) + (*q * &r),
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
        let hash_g_project: Projective = *HASH_G_ARK;
        Self {
            comm: (Config::GENERATOR * x) + (hash_g_project * r),
            r: *r,
        }
    }
}