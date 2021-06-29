// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use std::{borrow::Borrow, marker::PhantomData};

use digest::Digest;
use itertools::Itertools;

use snarkvm_algorithms::signature::{SchnorrOutput, SchnorrParameters, SchnorrPublicKey, SchnorrSignature};
use snarkvm_curves::traits::Group;
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::serialize::{CanonicalDeserialize, CanonicalSerialize};

use crate::{
    bits::{Boolean, ToBytesGadget},
    integers::uint::UInt8,
    traits::{
        algorithms::SignaturePublicKeyRandomizationGadget,
        alloc::AllocGadget,
        curves::GroupGadget,
        eq::{ConditionalEqGadget, EqGadget},
        integers::Integer,
    },
    FieldGadget,
};

#[derive(Clone)]
pub struct SchnorrParametersGadget<G: Group, F: Field, D: Digest> {
    parameters: SchnorrParameters<G, D>,
    _group: PhantomData<*const G>,
    _engine: PhantomData<*const F>,
}

impl<G: Group, F: Field, D: Digest> AllocGadget<SchnorrParameters<G, D>, F> for SchnorrParametersGadget<G, F, D> {
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<SchnorrParameters<G, D>>, CS: ConstraintSystem<F>>(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let parameters = value.borrow().clone();
        Ok(Self {
            parameters,
            _engine: PhantomData,
            _group: PhantomData,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrParameters<G, D>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let parameters = value.borrow().clone();
        Ok(Self {
            parameters,
            _engine: PhantomData,
            _group: PhantomData,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchnorrPublicKeyGadget<G: Group, F: Field, GG: GroupGadget<G, F>> {
    public_key: GG,
    _group: PhantomData<G>,
    _engine: PhantomData<F>,
}

impl<G: Group + CanonicalSerialize + CanonicalDeserialize, F: Field, GG: GroupGadget<G, F>>
    AllocGadget<SchnorrPublicKey<G>, F> for SchnorrPublicKeyGadget<G, F, GG>
{
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<SchnorrPublicKey<G>>, CS: ConstraintSystem<F>>(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            public_key: GG::alloc_checked(cs, || f().map(|pk| pk.borrow().0))?,
            _engine: PhantomData,
            _group: PhantomData,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrPublicKey<G>>,
        CS: ConstraintSystem<F>,
    >(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            public_key: GG::alloc_input(cs, || f().map(|pk| pk.borrow().0))?,
            _engine: PhantomData,
            _group: PhantomData,
        })
    }
}

impl<G: Group, F: Field, GG: GroupGadget<G, F>> ConditionalEqGadget<F> for SchnorrPublicKeyGadget<G, F, GG> {
    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.public_key.conditional_enforce_equal(
            &mut cs.ns(|| "conditional_enforce_equal"),
            &other.public_key,
            condition,
        )?;
        Ok(())
    }

    fn cost() -> usize {
        <GG as ConditionalEqGadget<F>>::cost()
    }
}

impl<G: Group, F: Field, GG: GroupGadget<G, F>> EqGadget<F> for SchnorrPublicKeyGadget<G, F, GG> {}

impl<G: Group, F: Field, GG: GroupGadget<G, F>> ToBytesGadget<F> for SchnorrPublicKeyGadget<G, F, GG> {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.public_key.to_bytes(&mut cs.ns(|| "to_bytes"))
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.public_key.to_bytes_strict(&mut cs.ns(|| "to_bytes_strict"))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchnorrSignatureGadget<G: Group, F: Field, FG: FieldGadget<<G as Group>::ScalarField, F>> {
    prover_response: FG,
    verifier_challenge: FG,
    _field: PhantomData<*const F>,
    _group: PhantomData<*const G>,
}

impl<G: Group, F: Field, FG: FieldGadget<<G as Group>::ScalarField, F>> AllocGadget<SchnorrOutput<G>, F>
    for SchnorrSignatureGadget<G, F, FG>
{
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<SchnorrOutput<G>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let schnorr_output = value.borrow().clone();

        let prover_response = FG::alloc(
            cs.ns(|| "alloc_prover_response"),
            || Ok(&schnorr_output.prover_response),
        )?;
        let verifier_challenge = FG::alloc(cs.ns(|| "alloc_verifier_challenge"), || {
            Ok(&schnorr_output.verifier_challenge)
        })?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            _field: PhantomData,
            _group: PhantomData,
        })
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<SchnorrOutput<G>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let schnorr_output = value.borrow().clone();

        let prover_response = FG::alloc_input(cs.ns(|| "alloc_input_prover_response"), || {
            Ok(&schnorr_output.prover_response)
        })?;
        let verifier_challenge = FG::alloc_input(cs.ns(|| "alloc_input_verifier_challenge"), || {
            Ok(&schnorr_output.verifier_challenge)
        })?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            _field: PhantomData,
            _group: PhantomData,
        })
    }
}

impl<G: Group, F: Field, FG: FieldGadget<<G as Group>::ScalarField, F>> ConditionalEqGadget<F>
    for SchnorrSignatureGadget<G, F, FG>
{
    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.prover_response.conditional_enforce_equal(
            &mut cs.ns(|| "prover_response_conditional_enforce_equal"),
            &other.prover_response,
            condition,
        )?;
        self.verifier_challenge.conditional_enforce_equal(
            &mut cs.ns(|| "verifier_challenge_conditional_enforce_equal"),
            &other.verifier_challenge,
            condition,
        )?;
        Ok(())
    }

    fn cost() -> usize {
        <FG as ConditionalEqGadget<F>>::cost() * 2
    }
}

impl<G: Group, F: Field, FG: FieldGadget<<G as Group>::ScalarField, F>> EqGadget<F>
    for SchnorrSignatureGadget<G, F, FG>
{
}

impl<G: Group, F: Field, FG: FieldGadget<<G as Group>::ScalarField, F>> ToBytesGadget<F>
    for SchnorrSignatureGadget<G, F, FG>
{
    fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut result = Vec::new();

        result.extend(
            self.prover_response
                .to_bytes(&mut cs.ns(|| "prover_response_to_bytes"))?,
        );
        result.extend(
            self.verifier_challenge
                .to_bytes(&mut cs.ns(|| "verifier_challenge_to_bytes"))?,
        );

        Ok(result)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut result = Vec::new();

        result.extend(
            self.prover_response
                .to_bytes_strict(&mut cs.ns(|| "prover_response_to_bytes_strict"))?,
        );
        result.extend(
            self.verifier_challenge
                .to_bytes_strict(&mut cs.ns(|| "verifier_challenge_to_bytes_strict"))?,
        );

        Ok(result)
    }
}

pub struct SchnorrPublicKeyRandomizationGadget<
    G: Group,
    F: PrimeField,
    GG: GroupGadget<G, F>,
    FG: FieldGadget<<G as Group>::ScalarField, F>,
> {
    _group: PhantomData<*const G>,
    _group_gadget: PhantomData<*const GG>,
    _field_gadget: PhantomData<*const FG>,
    _engine: PhantomData<*const F>,
}

impl<
    G: Group + CanonicalSerialize + CanonicalDeserialize,
    GG: GroupGadget<G, F>,
    FG: FieldGadget<<G as Group>::ScalarField, F>,
    D: Digest + Send + Sync,
    F: PrimeField,
> SignaturePublicKeyRandomizationGadget<SchnorrSignature<G, D>, F>
    for SchnorrPublicKeyRandomizationGadget<G, F, GG, FG>
{
    type ParametersGadget = SchnorrParametersGadget<G, F, D>;
    type PublicKeyGadget = SchnorrPublicKeyGadget<G, F, GG>;
    type SignatureGadget = SchnorrSignatureGadget<G, F, FG>;

    fn check_randomization_gadget<CS: ConstraintSystem<F>>(
        mut cs: CS,
        parameters: &Self::ParametersGadget,
        public_key: &Self::PublicKeyGadget,
        randomness: &[UInt8],
    ) -> Result<Self::PublicKeyGadget, SynthesisError> {
        let randomness = randomness.iter().flat_map(|b| b.to_bits_le()).collect::<Vec<_>>();
        let mut rand_pk = public_key.public_key.clone();
        rand_pk.scalar_multiplication(
            cs.ns(|| "check_randomization_gadget"),
            randomness.iter().zip_eq(&parameters.parameters.generator_powers),
        )?;

        Ok(SchnorrPublicKeyGadget {
            public_key: rand_pk,
            _group: PhantomData,
            _engine: PhantomData,
        })
    }

    fn verify<CS: ConstraintSystem<F>>(
        cs: CS,
        parameters: &Self::ParametersGadget,
        public_key: &Self::PublicKeyGadget,
        message: &[UInt8],
        signature: &Self::SignatureGadget,
    ) -> Result<Self::PublicKeyGadget, SynthesisError> {
        unimplemented!()
    }
}
