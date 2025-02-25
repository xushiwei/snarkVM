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

use super::*;

impl<E: Environment> ToUpperBits for Field<E> {
    type Boolean = Boolean<E>;

    ///
    /// Outputs the upper `k` bits of an `n`-bit field element in little-endian representation.
    /// Enforces that the lower `n - k` bits are zero.
    ///
    fn to_upper_bits_le(&self, k: usize) -> Vec<Self::Boolean> {
        let mut bits_le = self.to_upper_bits_be(k);
        bits_le.reverse();
        bits_le
    }

    ///
    /// Outputs the upper `k` bits of an `n`-bit field element in big-endian representation.
    /// Enforces that the lower `n - k` bits are zero.
    ///
    fn to_upper_bits_be(&self, k: usize) -> Vec<Self::Boolean> {
        // Ensure the size is within the allowed capacity.
        if k > E::BaseField::size_in_bits() {
            E::halt(format!(
                "Attempted to extract {k} bits from a {}-bit base field element",
                E::BaseField::size_in_bits()
            ))
        }

        // Construct a vector of `Boolean`s comprising the bits of the field value.
        let bits: Vec<Boolean<E>> = witness!(|self| self.to_bits_be().into_iter().take(k).collect());

        // Reconstruct the bits as a linear combination representing the original field value.
        let mut accumulator = Field::zero();
        let mut coefficient = Field::one();
        for _ in 0..(E::BaseField::size_in_bits() - k) {
            coefficient = coefficient.double();
        }
        for bit in bits.iter().rev() {
            accumulator += Field::from_boolean(bit) * &coefficient;
            coefficient = coefficient.double();
        }

        // Ensure value * 1 == (2^n * b_n + ... + 2^{n-k} * b_{n-k})
        // and ensures that b_{n-k-1}, ..., b_0 are all equal to zero.
        E::assert_eq(self, accumulator);

        bits
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{bytes_from_bits_le, test_rng, FromBytes, ToBytes, UniformRand};

    const ITERATIONS: usize = 100;

    #[rustfmt::skip]
    fn check_to_upper_k_bits_be<I: IntegerType + Unsigned + ToBytes>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let size_in_bits = <Circuit as Environment>::BaseField::size_in_bits();
        let size_in_bytes = (size_in_bits + 7) / 8;
        let num_leading_zero_bits = (size_in_bytes * 8) - size_in_bits;

        for i in 0..ITERATIONS {
            // Sample a random unsigned integer.
            let value: I = UniformRand::rand(&mut test_rng());
            let expected = value.to_bytes_le().unwrap().to_bits_le();

            // Construct the unsigned integer as a field element.
            let candidate = {
                //
                // Restructure the value as field element as follows.
                //
                // MSB | MSB-1 | MSB-2 | MSB-3 | MSB-4 | ... | MSB-k | MSB-k-1 | ... | LSB
                // ------------------------------------------------------------------------
                //  0  |   0   |   0   |   0   |  b_k  | ... |  b_0  |    0    | ... |  0
                //
                // For advanced readers: We extend the leading zeros one-past `MODULUS_BITS`
                // to ensure `CAPACITY` is always satisfied for testing.
                //
                let field_bytes = {
                    let mut field_bits_be_with_leading_zeros = vec![false; num_leading_zero_bits + 1];
                    for bit in &expected {
                        field_bits_be_with_leading_zeros.push(*bit);
                    }
                    field_bits_be_with_leading_zeros.resize(size_in_bytes * 8, false); // Pad up to field byte-aligned size.

                    let mut field_bits_le_with_leading_zeros = field_bits_be_with_leading_zeros;
                    field_bits_le_with_leading_zeros.reverse();

                    bytes_from_bits_le(&field_bits_le_with_leading_zeros)
                };
                Field::<Circuit>::new(mode, FromBytes::from_bytes_le(&field_bytes).unwrap())
            };

            Circuit::scope(&format!("{} {}", mode, i), || {
                let num_bits_with_capacity = I::BITS + 1;
                let candidate = candidate.to_upper_bits_be(num_bits_with_capacity);
                assert_eq!(num_bits_with_capacity, candidate.len());
                for (i, (expected_bit, candidate_bit)) in expected.iter().zip_eq(candidate.iter().skip(1)).enumerate() {
                    assert_eq!(*expected_bit, candidate_bit.eject_value(), "MSB-{}", i);
                }
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    // 8 bits

    #[test]
    fn test_to_8_bits_constant() {
        check_to_upper_k_bits_be::<u8>(Mode::Constant, 9, 0, 0, 0); // This actually tests 9 bits.
    }

    #[test]
    fn test_to_8_bits_public() {
        check_to_upper_k_bits_be::<u8>(Mode::Public, 0, 0, 9, 10); // This actually tests 9 bits.
    }

    #[test]
    fn test_to_8_bits_private() {
        check_to_upper_k_bits_be::<u8>(Mode::Private, 0, 0, 9, 10); // This actually tests 9 bits.
    }

    // 16 bits

    #[test]
    fn test_to_16_bits_constant() {
        check_to_upper_k_bits_be::<u16>(Mode::Constant, 17, 0, 0, 0); // This actually tests 17 bits.
    }

    #[test]
    fn test_to_16_bits_public() {
        check_to_upper_k_bits_be::<u16>(Mode::Public, 0, 0, 17, 18); // This actually tests 17 bits.
    }

    #[test]
    fn test_to_16_bits_private() {
        check_to_upper_k_bits_be::<u16>(Mode::Private, 0, 0, 17, 18); // This actually tests 17 bits.
    }

    // 32 bits

    #[test]
    fn test_to_32_bits_constant() {
        check_to_upper_k_bits_be::<u32>(Mode::Constant, 33, 0, 0, 0); // This actually tests 33 bits.
    }

    #[test]
    fn test_to_32_bits_public() {
        check_to_upper_k_bits_be::<u32>(Mode::Public, 0, 0, 33, 34); // This actually tests 33 bits.
    }

    #[test]
    fn test_to_32_bits_private() {
        check_to_upper_k_bits_be::<u32>(Mode::Private, 0, 0, 33, 34); // This actually tests 33 bits.
    }

    // 64 bits

    #[test]
    fn test_to_64_bits_constant() {
        check_to_upper_k_bits_be::<u64>(Mode::Constant, 65, 0, 0, 0); // This actually tests 65 bits.
    }

    #[test]
    fn test_to_64_bits_public() {
        check_to_upper_k_bits_be::<u64>(Mode::Public, 0, 0, 65, 66); // This actually tests 65 bits.
    }

    #[test]
    fn test_to_64_bits_private() {
        check_to_upper_k_bits_be::<u64>(Mode::Private, 0, 0, 65, 66); // This actually tests 65 bits.
    }

    // 128 bits

    #[test]
    fn test_to_128_bits_constant() {
        check_to_upper_k_bits_be::<u128>(Mode::Constant, 129, 0, 0, 0); // This actually tests 129 bits.
    }

    #[test]
    fn test_to_128_bits_public() {
        check_to_upper_k_bits_be::<u128>(Mode::Public, 0, 0, 129, 130); // This actually tests 129 bits.
    }

    #[test]
    fn test_to_128_bits_private() {
        check_to_upper_k_bits_be::<u128>(Mode::Private, 0, 0, 129, 130); // This actually tests 129 bits.
    }
}
