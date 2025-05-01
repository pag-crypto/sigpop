//! This module includes implementations related to Elliptic curve points
use p256::{Scalar, ProjectivePoint};
use elliptic_curve::group::GroupEncoding; 
use core::ops::{Mul, Add};

use serde::{Serializer, Serialize}; // ser/de for sigma proof
use serde::{Deserialize, Deserializer}; // ser/de for sigma proof
use p256::elliptic_curve::generic_array::GenericArray;
use elliptic_curve::PrimeField;

use std::borrow::Borrow;

use ark_secp256r1::{Projective, Affine, Fr};
use ark_serialize::SerializationError;
pub use ark_std::io::{Read, Write};

use ark_ec::CurveGroup;
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};

/// Elliptic curve point over P256
#[derive(PartialEq, Clone, Copy)]
pub struct ArkECPoint(pub Projective);

/// Elliptic curve point over P256
#[derive(PartialEq, Clone, Copy)]
pub struct ECPoint(pub ProjectivePoint);

/// Elliptic curve scalar over P256
#[derive(Clone, Copy)]
pub struct ArkScalar(pub Fr);

/// Elliptic curve scalar over P256
#[derive(Clone, Copy)]
pub struct P256Scalar(pub Scalar);


impl ECPoint {
    /// Default
    pub fn default() -> ECPoint {
        ECPoint(ProjectivePoint::default())
    }
}
impl Mul<Scalar> for ECPoint {
    type Output = ECPoint;

    fn mul(self, scalar: Scalar) -> ECPoint { 
        ECPoint(self.0 * scalar)
    }
}

// implement Add for ECPoint
impl Add<ProjectivePoint> for ECPoint {
    type Output = ECPoint;
  
    fn add(self, other: ProjectivePoint) -> Self::Output {
        ECPoint(self.0 + other)
    }
}

impl Mul<P256Scalar> for ECPoint {
    type Output = ECPoint;

    fn mul(self, scalar: P256Scalar) -> ECPoint { 
        ECPoint(self.0 * scalar.0)
    }
}

// Implement Serialize for ECPoint
impl Serialize for ECPoint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let bytes = self.0.to_bytes(); 
        bytes.serialize(serializer)
    }
}

// Implement Deserialize for ECPoint
impl<'de> Deserialize<'de> for ECPoint { // Size: 33 bytes
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes = Vec::<u8>::deserialize(deserializer)?;
        let generic_bytes: &<ProjectivePoint as GroupEncoding>::Repr = GenericArray::from_slice(&bytes);

        let point = ProjectivePoint::from_bytes(generic_bytes);
        Ok(ECPoint(point.unwrap()))
    }
}

// Implement Serialize for ArkECPoint
impl Serialize for ArkECPoint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut bytes = Vec::new();
        self.0.serialize_compressed(&mut bytes).unwrap();
        bytes.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for ArkECPoint { // Size: 33 Bytes
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes = Vec::<u8>::deserialize(deserializer)?;
        let point = Projective::deserialize_compressed(&bytes[..])
            .map_err(|e| serde::de::Error::custom(format!("Deserialization error: {:?}", e)))?;
        Ok(ArkECPoint(point))
    }
}

impl ArkECPoint {
    pub fn serialize_compressed<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        self.0.serialize_compressed(writer)
    }

    pub fn into_affine(&self) -> Affine {
        self.0.into_affine()
    }

    pub fn batch_to_projective(points: &[Self]) -> Vec<Projective> {
        points.iter().map(|p| p.0).collect()
    }

    pub fn batch_from_projective(points: &[Projective]) -> Vec<ArkECPoint> {
        points.iter().map(|p| ArkECPoint(*p)).collect()
    }
}


impl Borrow<Scalar> for P256Scalar {
    fn borrow(&self) -> &Scalar {
        &self.0
    }
}

impl P256Scalar {
    /// Default
    pub fn default() -> P256Scalar {
        P256Scalar(Scalar::default())
    }
}
// Implement Serialize for P256Scalar
impl Serialize for P256Scalar {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let bytes = self.0.to_repr(); 
        bytes.serialize(serializer)
    }
}

// Implement Deserialize for P256Scalar
impl<'de> Deserialize<'de> for P256Scalar { // Size: 32 Bytes
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes = Vec::<u8>::deserialize(deserializer)?;
        let generic_bytes: &<Scalar as PrimeField>::Repr = GenericArray::from_slice(&bytes);
        let scalar = Scalar::from_repr(*generic_bytes).expect("Failed to create scalar");
        Ok(P256Scalar(scalar))
    }
}

// Implement Serialize for ArkScalar
impl Serialize for ArkScalar {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use ark_ff::PrimeField;  
        use ark_ff::BigInteger;    
        let bytes = self.0.into_bigint().to_bytes_le(); // testing
        bytes.serialize(serializer)
    }
}

// Implement Deserialize for ArkScalar
impl<'de> Deserialize<'de> for ArkScalar { // Size: 32 Bytes
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes = Vec::<u8>::deserialize(deserializer)?;
        let scalar = Fr::deserialize_compressed(&bytes[..]).unwrap();
        Ok(ArkScalar(scalar))
    }
}

impl ArkScalar {
    pub fn batch_to_scalar(scalars: &[Self]) -> Vec<Fr> {
        scalars.iter().map(|s| s.0).collect()
    }
    pub fn batch_from_scalar(scalars: &[Fr]) -> Vec<ArkScalar> {
        scalars.iter().map(|s| ArkScalar(*s)).collect()
    }
}