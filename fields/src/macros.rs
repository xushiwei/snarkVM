// Copyright (C) 2019-2022 Aleo Systems Inc.
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

#[macro_export]
macro_rules! field {
    ($name:ident, $c0:expr) => {
        $name { 0: $c0, 1: std::marker::PhantomData }
    };
    ($name:ident, $c0:expr, $c1:expr $(,)?) => {
        $name { c0: $c0, c1: $c1 }
    };
    ($name:ident, $c0:expr, $c1:expr, $c2:expr $(,)?) => {
        $name { c0: $c0, c1: $c1, c2: $c2 }
    };
}

macro_rules! impl_field_into_biginteger {
    ($field: ident, $biginteger: ident, $parameters: ident) => {
        #[allow(clippy::from_over_into)]
        impl<P: $parameters> Into<$biginteger> for $field<P> {
            fn into(self) -> $biginteger {
                self.to_repr()
            }
        }
    };
}

macro_rules! impl_primefield_standard_sample {
    ($field: ident, $params: ident) => {
        impl<P: $params> rand::distributions::Distribution<$field<P>> for rand::distributions::Standard {
            #[inline]
            fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> $field<P> {
                loop {
                    let mut tmp = $field(rng.sample(rand::distributions::Standard), PhantomData);
                    // Mask away the unused bits at the beginning.
                    tmp.0.as_mut().last_mut().map(|val| *val &= std::u64::MAX >> P::REPR_SHAVE_BITS);

                    if tmp.is_valid() {
                        return tmp;
                    }
                }
            }
        }
    };
}

macro_rules! impl_primefield_from_int {
    ($field: ident, u128, $params: ident) => {
        impl<P: $params> From<u128> for $field<P> {
            /// Attempts to convert an integer into a field element.
            /// Panics if the provided integer is invalid (e.g. larger than the field modulus).
            fn from(other: u128) -> Self {
                let upper = (other >> 64) as u64;
                let lower = ((other << 64) >> 64) as u64;
                let mut default_int = P::BigInteger::default();
                default_int.0[0] = lower;
                default_int.0[1] = upper;
                Self::from_repr(default_int).unwrap()
            }
        }
    };
    ($field: ident, $int: ident, $params: ident) => {
        impl<P: $params> From<$int> for $field<P> {
            /// Attempts to convert an integer into a field element.
            /// Panics if the provided integer is invalid (e.g. larger than the field modulus).
            fn from(other: $int) -> Self {
                Self::from_repr(P::BigInteger::from(u64::from(other))).unwrap()
            }
        }
    };
}

macro_rules! sqrt_impl {
    ($Self:ident, $P:tt, $self:expr) => {{
        use crate::LegendreSymbol::*;
        // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)
        // Actually this is just normal Tonelli-Shanks; since `P::Generator`
        // is a quadratic non-residue, `P::ROOT_OF_UNITY = P::GENERATOR ^ t`
        // is also a quadratic non-residue (since `t` is odd).
        match $self.legendre() {
            Zero => Some(*$self),
            QuadraticNonResidue => None,
            QuadraticResidue => {
                let mut z = $Self::two_adic_root_of_unity();
                let mut w = $self.pow($P::T_MINUS_ONE_DIV_TWO);
                let mut x = w * $self;
                let mut b = x * w;

                let mut v = $P::TWO_ADICITY as usize;
                // t = self^t
                #[cfg(debug_assertions)]
                {
                    let mut check = b;
                    for _ in 0..(v - 1) {
                        check.square_in_place();
                    }
                    if !check.is_one() {
                        panic!("Input is not a square root, but it passed the QR test")
                    }
                }

                while !b.is_one() {
                    let mut k = 0usize;

                    let mut b2k = b;
                    while !b2k.is_one() {
                        // invariant: b2k = b^(2^k) after entering this loop
                        b2k.square_in_place();
                        k += 1;
                    }

                    let j = v - k - 1;
                    w = z;
                    for _ in 0..j {
                        w.square_in_place();
                    }

                    z = w.square();
                    b *= &z;
                    x *= &w;
                    v = k;
                }

                Some(x)
            }
        }
    }};
}

macro_rules! impl_primefield_serializer {
    ($field: ident, $params: ident, $byte_size: expr) => {
        impl<P: $params> CanonicalSerializeWithFlags for $field<P> {
            #[allow(unused_qualifications)]
            fn serialize_with_flags<W: snarkvm_utilities::io::Write, F: snarkvm_utilities::Flags>(
                &self,
                writer: &mut W,
                flags: F,
            ) -> Result<(), snarkvm_utilities::serialize::SerializationError> {
                const BYTE_SIZE: usize = $byte_size;

                let (output_bit_size, output_byte_size) =
                    snarkvm_utilities::serialize::number_of_bits_and_bytes($field::<P>::size_in_bits());
                if F::num_bits() > (output_bit_size - P::MODULUS_BITS as usize) {
                    return Err(snarkvm_utilities::serialize::SerializationError::NotEnoughSpace);
                }

                let mut bytes = [0u8; BYTE_SIZE];
                self.write_le(&mut bytes[..])?;

                bytes[output_byte_size - 1] |= flags.u8_bitmask();

                writer.write_all(&bytes[..output_byte_size])?;
                Ok(())
            }
        }

        impl<P: $params> ConstantSerializedSize for $field<P> {
            const SERIALIZED_SIZE: usize = snarkvm_utilities::serialize::number_of_bits_to_number_of_bytes(
                <$field<P> as crate::PrimeField>::Parameters::MODULUS_BITS as usize,
            );
            const UNCOMPRESSED_SIZE: usize = Self::SERIALIZED_SIZE;
        }

        impl<P: $params> CanonicalSerialize for $field<P> {
            #[allow(unused_qualifications)]
            #[inline]
            fn serialize<W: snarkvm_utilities::io::Write>(
                &self,
                writer: &mut W,
            ) -> Result<(), snarkvm_utilities::serialize::SerializationError> {
                self.serialize_with_flags(writer, snarkvm_utilities::serialize::EmptyFlags)
            }

            #[inline]
            fn serialized_size(&self) -> usize {
                Self::SERIALIZED_SIZE
            }
        }

        impl<P: $params> CanonicalDeserializeWithFlags for $field<P> {
            #[allow(unused_qualifications)]
            fn deserialize_with_flags<R: snarkvm_utilities::io::Read, F: snarkvm_utilities::Flags>(
                reader: &mut R,
            ) -> Result<(Self, F), snarkvm_utilities::serialize::SerializationError> {
                const BYTE_SIZE: usize = $byte_size;

                let (output_bit_size, output_byte_size) =
                    snarkvm_utilities::serialize::number_of_bits_and_bytes($field::<P>::size_in_bits());
                if F::num_bits() > (output_bit_size - P::MODULUS_BITS as usize) {
                    return Err(snarkvm_utilities::serialize::SerializationError::NotEnoughSpace);
                }

                let mut masked_bytes = [0; BYTE_SIZE];
                reader.read_exact(&mut masked_bytes[..output_byte_size])?;

                let flags = F::from_u8_remove_flags(&mut masked_bytes[output_byte_size - 1]);

                Ok((Self::read_le(&masked_bytes[..])?, flags))
            }
        }

        impl<P: $params> CanonicalDeserialize for $field<P> {
            #[allow(unused_qualifications)]
            fn deserialize<R: snarkvm_utilities::io::Read>(
                reader: &mut R,
            ) -> Result<Self, snarkvm_utilities::SerializationError> {
                const BYTE_SIZE: usize = $byte_size;

                let (_, output_byte_size) =
                    snarkvm_utilities::serialize::number_of_bits_and_bytes($field::<P>::size_in_bits());

                let mut masked_bytes = [0; BYTE_SIZE];
                reader.read_exact(&mut masked_bytes[..output_byte_size])?;
                Ok(Self::read_le(&masked_bytes[..])?)
            }
        }

        impl<P: $params> serde::Serialize for $field<P> {
            fn serialize<S: serde::ser::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                let mut bytes = Vec::with_capacity(Self::SERIALIZED_SIZE);
                CanonicalSerialize::serialize(self, &mut bytes).map_err(serde::ser::Error::custom)?;

                match serializer.is_human_readable() {
                    true => serializer.collect_str(self),
                    false => snarkvm_utilities::ToBytesSerializer::serialize(&bytes, serializer),
                }
            }
        }

        impl<'de, P: $params> serde::Deserialize<'de> for $field<P> {
            fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                match deserializer.is_human_readable() {
                    true => {
                        let s: String = serde::Deserialize::deserialize(deserializer)?;
                        core::str::FromStr::from_str(&s).map_err(serde::de::Error::custom)
                    }
                    false => {
                        struct SerVisitor<P>(std::marker::PhantomData<P>);

                        impl<'de, P: $params> serde::de::Visitor<'de> for SerVisitor<P> {
                            type Value = $field<P>;

                            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                                formatter.write_str("a valid field element")
                            }

                            fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
                            where
                                S: serde::de::SeqAccess<'de>,
                            {
                                let len = <Self::Value as ConstantSerializedSize>::SERIALIZED_SIZE;
                                let bytes: Vec<u8> = (0..len)
                                    .map(|_| {
                                        seq.next_element()?
                                            .ok_or_else(|| serde::de::Error::custom("could not read bytes"))
                                    })
                                    .collect::<Result<Vec<_>, _>>()?;

                                CanonicalDeserialize::deserialize(&mut &bytes[..]).map_err(serde::de::Error::custom)
                            }
                        }

                        let visitor = SerVisitor(std::marker::PhantomData);
                        deserializer.deserialize_tuple(Self::SERIALIZED_SIZE, visitor)
                    }
                }
            }
        }
    };
}

macro_rules! impl_field_from_random_bytes_with_flags {
    ($u64_limbs: expr) => {
        #[inline]
        fn from_random_bytes_with_flags<F: snarkvm_utilities::Flags>(bytes: &[u8]) -> Option<(Self, F)> {
            // Copy the input into a temporary buffer.
            let mut result_bytes = [0u8; $u64_limbs * 8 + 1];
            result_bytes.iter_mut().zip(bytes).for_each(|(result, input)| {
                *result = *input;
            });

            // The `last_limb_mask` retains everything in the final limb up to `P::MODULUS_BITS`.
            let last_limb_mask = u64::MAX >> P::REPR_SHAVE_BITS;

            let mut last_bytes_mask = [0u8; 9];
            last_bytes_mask[..8].copy_from_slice(&last_limb_mask.to_le_bytes());

            // Length of the buffer containing the field element and the flag.
            let output_byte_size =
                snarkvm_utilities::number_of_bits_to_number_of_bytes(P::MODULUS_BITS as usize + F::num_bits());

            // Flags are located in the final byte of the serialized field representation.
            let flag_location = output_byte_size - 1;

            // At which byte is the flag located in the last limb?
            let flag_location_in_last_limb = flag_location - (8 * ($u64_limbs - 1));

            // Take all but the last 9 bytes.
            let last_bytes = &mut result_bytes[8 * ($u64_limbs - 1)..];

            // The mask only has the last `F::num_bits()` bits set.
            let flags_mask = u8::MAX.checked_shl(8 - (F::num_bits() as u32)).unwrap_or(0);

            // Mask away the remaining bytes, and try to reconstruct the flag.
            let mut flags: u8 = 0;
            for (i, (b, m)) in last_bytes.iter_mut().zip(&last_bytes_mask).enumerate() {
                if i == flag_location_in_last_limb {
                    flags = *b & flags_mask
                }
                *b &= m;
            }

            <Self as CanonicalDeserialize>::deserialize(&mut &result_bytes[..($u64_limbs * 8)])
                .ok()
                .map(|f| (f, F::from_u8(flags)))
        }
    };
}

/// Implements Add, Sub, AddAssign, and SubAssign on Self by deferring to an implementation on &Self
#[macro_export]
macro_rules! impl_add_sub_from_field_ref {
    ($type: ident, $params: ident) => {
        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::Add<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn add(self, other: Self) -> Self {
                let mut result = self;
                result.add_assign(&other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::Sub<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn sub(self, other: Self) -> Self {
                let mut result = self;
                result.sub_assign(&other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::Add<&&Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn add(self, other: &&Self) -> Self {
                let mut result = self;
                result.add_assign(*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::Sub<&&Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn sub(self, other: &&Self) -> Self {
                let mut result = self;
                result.sub_assign(*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> core::ops::Add<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn add(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result.add_assign(&*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> core::ops::Sub<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn sub(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result.sub_assign(&*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::AddAssign<Self> for $type<P> {
            fn add_assign(&mut self, other: Self) {
                self.add_assign(&other)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::SubAssign<Self> for $type<P> {
            fn sub_assign(&mut self, other: Self) {
                self.sub_assign(&other)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::AddAssign<&&Self> for $type<P> {
            fn add_assign(&mut self, other: &&Self) {
                self.add_assign(*other)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::SubAssign<&&Self> for $type<P> {
            fn sub_assign(&mut self, other: &&Self) {
                self.sub_assign(*other)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> core::ops::AddAssign<&'a mut Self> for $type<P> {
            fn add_assign(&mut self, other: &'a mut Self) {
                self.add_assign(&*other)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> core::ops::SubAssign<&'a mut Self> for $type<P> {
            fn sub_assign(&mut self, other: &'a mut Self) {
                self.sub_assign(&*other)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::iter::Sum<Self> for $type<P> {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::zero(), core::ops::Add::add)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> core::iter::Sum<&'a Self> for $type<P> {
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Self::zero(), core::ops::Add::add)
            }
        }
    };
}

/// Implements Mul, Div, MulAssign, and DivAssign on Self by deferring to an implementation on &Self
#[macro_export]
macro_rules! impl_mul_div_from_field_ref {
    ($type: ident, $params: ident) => {
        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::Mul<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn mul(self, other: Self) -> Self {
                let mut result = self;
                result.mul_assign(&other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::Div<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn div(self, other: Self) -> Self {
                let mut result = self;
                result.div_assign(&other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::Mul<&&Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn mul(self, other: &&Self) -> Self {
                let mut result = self;
                result.mul_assign(*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::Div<&&Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn div(self, other: &&Self) -> Self {
                let mut result = self;
                result.div_assign(*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> core::ops::Mul<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn mul(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result.mul_assign(&*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> core::ops::Div<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn div(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result.div_assign(&*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::MulAssign<Self> for $type<P> {
            fn mul_assign(&mut self, other: Self) {
                self.mul_assign(&other)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::DivAssign<Self> for $type<P> {
            fn div_assign(&mut self, other: Self) {
                self.div_assign(&other)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::MulAssign<&&Self> for $type<P> {
            fn mul_assign(&mut self, other: &&Self) {
                self.mul_assign(*other)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::ops::DivAssign<&&Self> for $type<P> {
            fn div_assign(&mut self, other: &&Self) {
                self.div_assign(*other)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> core::ops::MulAssign<&'a mut Self> for $type<P> {
            fn mul_assign(&mut self, other: &'a mut Self) {
                self.mul_assign(&*other)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> core::ops::DivAssign<&'a mut Self> for $type<P> {
            fn div_assign(&mut self, other: &'a mut Self) {
                self.div_assign(&*other)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> core::iter::Product<Self> for $type<P> {
            fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::one(), core::ops::Mul::mul)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> core::iter::Product<&'a Self> for $type<P> {
            fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Self::one(), Mul::mul)
            }
        }
    };
}
