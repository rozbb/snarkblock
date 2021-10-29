use ark_bls12_381::Bls12_381;
use ark_ec::PairingEngine;
use ark_ec::{
    group::Group,
    models::{twisted_edwards_extended, TEModelParameters as Parameters},
    ProjectiveCurve,
};
use ark_ff::{
    fields::{Field, PrimeField},
    ToBytes, UniformRand, Zero,
};
use ark_r1cs_std::{
    alloc::AllocVar,
    bits::boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldOpsBounds, FieldVar},
    groups::curves::twisted_edwards,
    select::CondSelectGadget,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_serialize::{CanonicalSerialize, SerializationError};
use ark_std::rand::{prelude::StdRng, SeedableRng};
use arkworks_gadgets::poseidon::{constraints::PoseidonParametersVar, PoseidonParameters, Rounds};
use digest::Digest;

pub(crate) type BlsG1 = <Bls12_381 as PairingEngine>::G1Projective;
pub(crate) type BlsFr = ark_bls12_381::fr::Fr;
pub(crate) type BlsFq = <BlsG1 as ProjectiveCurve>::BaseField;
pub(crate) type BlsFrV = FpVar<BlsFr>;

// Some type aliases for the Poseidon construction
type CRH = arkworks_gadgets::setup::common::PoseidonCRH_x3_5<BlsFr>;
type CRHGadget = arkworks_gadgets::setup::common::PoseidonCRH_x3_5Gadget<BlsFr>;
type PoseidonRounds = arkworks_gadgets::setup::common::PoseidonRounds_x3_5;
const POSEIDON_CURVE: arkworks_gadgets::setup::common::Curve =
    arkworks_gadgets::setup::common::Curve::Bls381;

// A field element which is used to domain-separate the Poseidon-based commitment scheme from the
// Poseidon-based PRF scheme
const POSEIDON_COM_DOMAIN_SEP: u64 = 1337;

/// Provides all the Poseidon functionality we need natively
pub(crate) struct PoseidonCtx(PoseidonParameters<BlsFr>);

impl PoseidonCtx {
    pub(crate) fn new() -> PoseidonCtx {
        let params = arkworks_gadgets::setup::common::setup_params_x3_5::<BlsFr>(POSEIDON_CURVE);
        PoseidonCtx(params)
    }

    /// Computes the hash of the inputs
    pub(crate) fn digest(&self, input: &[BlsFr]) -> BlsFr {
        let params = &self.0;
        let state_width = PoseidonRounds::WIDTH;
        if input.len() > state_width {
            panic!("cannot digest more than {} field elements", state_width);
        }

        // Fill the buffer with the input
        let mut buffer = vec![BlsFr::zero(); state_width];
        buffer[..input.len()].clone_from_slice(input);

        // Run the permutation and return the first element of the resulting state
        let result = CRH::permute(params, buffer).expect("failed to permute Poseidon");
        result.get(0).cloned().unwrap()
    }

    /// Computes a commitment on the input
    pub(crate) fn com(&self, msg: BlsFr, nonce: BlsFr) -> BlsFr {
        let domain_sep = BlsFr::from(POSEIDON_COM_DOMAIN_SEP);
        self.digest(&[domain_sep, nonce, msg])
    }

    /// Computes a PRF on the input under the given key
    pub(crate) fn prf(&self, key: BlsFr, msg: BlsFr) -> BlsFr {
        self.digest(&[key, msg])
    }
}

/// Provides all the Poseidon functionality we need in circuits
pub(crate) struct PoseidonCtxVar(PoseidonParametersVar<BlsFr>);

impl PoseidonCtxVar {
    pub(crate) fn new(cs: impl Into<Namespace<BlsFr>>) -> Result<PoseidonCtxVar, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let params = arkworks_gadgets::setup::common::setup_params_x3_5::<BlsFr>(POSEIDON_CURVE);
        let params_var = PoseidonParametersVar::new_constant(cs, &params)?;
        Ok(PoseidonCtxVar(params_var))
    }

    /// Computes the hash of the inputs
    pub(crate) fn digest(&self, input: &[BlsFrV]) -> Result<BlsFrV, SynthesisError> {
        let params = &self.0;
        let state_width = PoseidonRounds::WIDTH;
        if input.len() > state_width {
            panic!("cannot digest more than {} field elements", state_width);
        }

        // Fill the buffer with input
        let mut buffer = vec![BlsFrV::zero(); state_width];
        buffer[..input.len()].clone_from_slice(input);

        // Run the permutation and return the first element of the resulting state
        let result = CRHGadget::permute(params, buffer);
        result.map(|x| x.get(0).cloned().ok_or(SynthesisError::AssignmentMissing))?
    }

    /// Computes a commitment on the input
    pub(crate) fn com(&self, msg: BlsFrV, nonce: BlsFrV) -> Result<BlsFrV, SynthesisError> {
        let domain_sep = BlsFrV::constant(BlsFr::from(POSEIDON_COM_DOMAIN_SEP));
        self.digest(&[domain_sep, nonce, msg])
    }

    /// Computes a PRF on the input under the given key
    pub(crate) fn prf(&self, key: BlsFrV, msg: BlsFrV) -> Result<BlsFrV, SynthesisError> {
        self.digest(&[key, msg])
    }
}

/// Converts an element of a curve's scalar field into an element of the base field
pub(crate) fn fr_to_fs<C, Fs>(x: <C as ProjectiveCurve>::ScalarField) -> Fs
where
    C: ProjectiveCurve<BaseField = Fs>,
    Fs: PrimeField,
{
    let mut x_bytes = Vec::new();
    x.write(&mut x_bytes).unwrap();
    Fs::read(&*x_bytes).unwrap()
}

pub(crate) fn hash_to_field<D, F>(input: &[u8]) -> F
where
    D: Digest,
    F: Field,
{
    let mut counter_nonce: usize = 0;
    loop {
        let mut hash_input = Vec::new();
        hash_input.extend_from_slice(&counter_nonce.to_be_bytes()[..]);
        hash_input.extend_from_slice(&input);
        if let Some(r) = F::from_random_bytes(&D::digest(&hash_input)) {
            return r;
        };
        counter_nonce += 1;
    }
}

/// Serializes the given value into a Vec<u8>
pub(crate) fn to_canonical_bytes(
    val: impl CanonicalSerialize,
) -> Result<Vec<u8>, SerializationError> {
    let mut buf = Vec::new();
    val.serialize(&mut buf)?;
    Ok(buf)
}

/// Enforces that the input bitstring has precisely 1 bit set
/// NOTE: Requires that one_hot_vec.len() < F.characteristic(). This is true for any reasonable
/// security parameter.
pub(crate) fn enforce_one_hot<F: PrimeField>(
    one_hot_vec: &[Boolean<F>],
) -> Result<(), SynthesisError> {
    let one = FpVar::one();
    let zero = FpVar::zero();

    // Convert the vector into field elements so we can sum them up
    let fp_one_hot_vec = one_hot_vec
        .iter()
        .map(|bit| FpVar::conditionally_select(bit, &one, &zero))
        .collect::<Result<Vec<FpVar<F>>, _>>()?;
    // Sum all the elements of the vector
    let num_ones = fp_one_hot_vec
        .into_iter()
        .fold(zero, |acc, elem| acc + elem);

    // Assert that the sum was 1, i.e., there was precisely 1 one in one_hot_vec
    num_ones.enforce_equal(&one)
}

/// Returns num_generators many deterministic pseudorandom group elements. This is used to
/// construct Pedersen commitments
pub fn get_pedersen_generators<G>(num_generators: usize) -> Vec<G>
where
    G: Group + UniformRand,
{
    // Pick a nothing-up-my-sleeve RNG seed
    let mut seed = [0u8; 32];
    seed[0..24].copy_from_slice(b"snarkblock-pedersen-seed");
    let mut rng = StdRng::from_seed(seed);

    // Generate and collect the requested number of group elements
    core::iter::repeat_with(|| G::rand(&mut rng))
        .take(num_generators)
        .collect()
}

/// This trait exposes the ability to retrieve affine coordinates from a curve point
pub trait GetAffineCoords {
    type OutputField;
    fn affine_coords(&self) -> Vec<Self::OutputField>;
}

impl<P> GetAffineCoords for twisted_edwards_extended::GroupProjective<P>
where
    P: Parameters,
{
    type OutputField = P::BaseField;

    // Convert to affine, then return coords
    fn affine_coords(&self) -> Vec<P::BaseField> {
        let a = twisted_edwards_extended::GroupAffine::<P>::from(*self);
        vec![a.x, a.y]
    }
}

impl<P, FV> GetAffineCoords for twisted_edwards::AffineVar<P, FV>
where
    P: Parameters,
    FV: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a FV: FieldOpsBounds<'a, P::BaseField, FV>,
{
    type OutputField = FV;

    fn affine_coords(&self) -> Vec<FV> {
        vec![self.x.clone(), self.y.clone()]
    }
}
