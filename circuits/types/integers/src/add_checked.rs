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

impl<E: Environment, I: IntegerType> Add<Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

impl<E: Environment, I: IntegerType> Add<Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn add(self, other: Integer<E, I>) -> Self::Output {
        self + &other
    }
}

impl<E: Environment, I: IntegerType> Add<&Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        &self + other
    }
}

impl<E: Environment, I: IntegerType> Add<&Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn add(self, other: &Integer<E, I>) -> Self::Output {
        let mut output = self.clone();
        output += other;
        output
    }
}

impl<E: Environment, I: IntegerType> AddAssign<Integer<E, I>> for Integer<E, I> {
    fn add_assign(&mut self, other: Integer<E, I>) {
        *self += &other;
    }
}

impl<E: Environment, I: IntegerType> AddAssign<&Integer<E, I>> for Integer<E, I> {
    fn add_assign(&mut self, other: &Integer<E, I>) {
        // Stores the sum of `self` and `other` in `self`.
        *self = self.add_checked(other);
    }
}

impl<E: Environment, I: IntegerType> AddChecked<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn add_checked(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the sum and return the new constant.
            match self.eject_value().checked_add(&other.eject_value()) {
                Some(value) => Integer::constant(value),
                None => E::halt("Integer overflow on addition of two constants"),
            }
        } else {
            // Instead of adding the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and summed, before converting back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let sum = self.to_field() + other.to_field();

            // Extract the integer bits from the field element, with a carry bit.
            let (sum, carry) = match sum.to_lower_bits_le(I::BITS + 1).split_last() {
                Some((carry, bits_le)) => (Integer::from_bits_le(bits_le), carry.clone()),
                None => E::halt("Malformed sum detected during integer addition"),
            };

            // Check for overflow.
            match I::is_signed() {
                // For signed addition, overflow and underflow conditions are:
                //   - a > 0 && b > 0 && a + b < 0 (Overflow)
                //   - a < 0 && b < 0 && a + b > 0 (Underflow)
                //   - Note: if sign(a) != sign(b) then over/underflow is impossible.
                //   - Note: the result of an overflow and underflow must be negative and positive, respectively.
                true => {
                    let is_same_sign = self.msb().is_equal(other.msb());
                    let is_overflow = is_same_sign & sum.msb().is_not_equal(self.msb());
                    E::assert_eq(is_overflow, E::zero());
                }
                // For unsigned addition, ensure the carry bit is zero.
                false => E::assert_eq(carry, E::zero()),
            }

            // Return the sum of `self` and `other`.
            sum
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use core::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_add<I: IntegerType + RefUnwindSafe>(
        name: &str,
        first: I,
        second: I,
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::new(mode_b, second);
        let case = format!("({} + {})", a.eject_value(), b.eject_value());

        match first.checked_add(&second) {
            Some(expected) => check_operation_passes(name, &case, expected, &a, &b, Integer::add_checked, num_constants, num_public, num_private, num_constraints),
            None => match mode_a.is_constant() && mode_b.is_constant() {
                true => check_operation_halts(&a, &b, Integer::add_checked),
                false => check_operation_fails(name, &case, &a, &b, Integer::add_checked, num_constants, num_public, num_private, num_constraints),
            },
        }
        Circuit::reset();
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("Add: {} + {} {}", mode_a, mode_b, i);
            check_add(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

            let name = format!("Add: {} + {} {} (commutative)", mode_a, mode_b, i);
            check_add(&name, second, first, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
        }

        // Overflow
        check_add("MAX + 1", I::MAX, I::one(), mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
        check_add("1 + MAX", I::one(), I::MAX, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

        // Underflow
        if I::is_signed() {
            check_add("MIN + (-1)", I::MIN, I::zero() - I::one(), mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            check_add("-1 + MIN", I::zero() - I::one(), I::MIN, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
        }
    }

    #[rustfmt::skip]
    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Add: ({} + {})", first, second);
                check_add(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            }
        }
    }

    #[test]
    fn test_u8_constant_plus_constant() {
        run_test::<u8>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_plus_public() {
        run_test::<u8>(Mode::Constant, Mode::Public, 0, 0, 9, 11);
    }

    #[test]
    fn test_u8_constant_plus_private() {
        run_test::<u8>(Mode::Constant, Mode::Private, 0, 0, 9, 11);
    }

    #[test]
    fn test_u8_public_plus_constant() {
        run_test::<u8>(Mode::Public, Mode::Constant, 0, 0, 9, 11);
    }

    #[test]
    fn test_u8_private_plus_constant() {
        run_test::<u8>(Mode::Private, Mode::Constant, 0, 0, 9, 11);
    }

    #[test]
    fn test_u8_public_plus_public() {
        run_test::<u8>(Mode::Public, Mode::Public, 0, 0, 9, 11);
    }

    #[test]
    fn test_u8_public_plus_private() {
        run_test::<u8>(Mode::Public, Mode::Private, 0, 0, 9, 11);
    }

    #[test]
    fn test_u8_private_plus_public() {
        run_test::<u8>(Mode::Private, Mode::Public, 0, 0, 9, 11);
    }

    #[test]
    fn test_u8_private_plus_private() {
        run_test::<u8>(Mode::Private, Mode::Private, 0, 0, 9, 11);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_plus_constant() {
        run_test::<i8>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_plus_public() {
        run_test::<i8>(Mode::Constant, Mode::Public, 0, 0, 10, 12);
    }

    #[test]
    fn test_i8_constant_plus_private() {
        run_test::<i8>(Mode::Constant, Mode::Private, 0, 0, 10, 12);
    }

    #[test]
    fn test_i8_public_plus_constant() {
        run_test::<i8>(Mode::Public, Mode::Constant, 0, 0, 11, 13);
    }

    #[test]
    fn test_i8_private_plus_constant() {
        run_test::<i8>(Mode::Private, Mode::Constant, 0, 0, 11, 13);
    }

    #[test]
    fn test_i8_public_plus_public() {
        run_test::<i8>(Mode::Public, Mode::Public, 0, 0, 12, 14);
    }

    #[test]
    fn test_i8_public_plus_private() {
        run_test::<i8>(Mode::Public, Mode::Private, 0, 0, 12, 14);
    }

    #[test]
    fn test_i8_private_plus_public() {
        run_test::<i8>(Mode::Private, Mode::Public, 0, 0, 12, 14);
    }

    #[test]
    fn test_i8_private_plus_private() {
        run_test::<i8>(Mode::Private, Mode::Private, 0, 0, 12, 14);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_plus_constant() {
        run_test::<u16>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_plus_public() {
        run_test::<u16>(Mode::Constant, Mode::Public, 0, 0, 17, 19);
    }

    #[test]
    fn test_u16_constant_plus_private() {
        run_test::<u16>(Mode::Constant, Mode::Private, 0, 0, 17, 19);
    }

    #[test]
    fn test_u16_public_plus_constant() {
        run_test::<u16>(Mode::Public, Mode::Constant, 0, 0, 17, 19);
    }

    #[test]
    fn test_u16_private_plus_constant() {
        run_test::<u16>(Mode::Private, Mode::Constant, 0, 0, 17, 19);
    }

    #[test]
    fn test_u16_public_plus_public() {
        run_test::<u16>(Mode::Public, Mode::Public, 0, 0, 17, 19);
    }

    #[test]
    fn test_u16_public_plus_private() {
        run_test::<u16>(Mode::Public, Mode::Private, 0, 0, 17, 19);
    }

    #[test]
    fn test_u16_private_plus_public() {
        run_test::<u16>(Mode::Private, Mode::Public, 0, 0, 17, 19);
    }

    #[test]
    fn test_u16_private_plus_private() {
        run_test::<u16>(Mode::Private, Mode::Private, 0, 0, 17, 19);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_plus_constant() {
        run_test::<i16>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_plus_public() {
        run_test::<i16>(Mode::Constant, Mode::Public, 0, 0, 18, 20);
    }

    #[test]
    fn test_i16_constant_plus_private() {
        run_test::<i16>(Mode::Constant, Mode::Private, 0, 0, 18, 20);
    }

    #[test]
    fn test_i16_public_plus_constant() {
        run_test::<i16>(Mode::Public, Mode::Constant, 0, 0, 19, 21);
    }

    #[test]
    fn test_i16_private_plus_constant() {
        run_test::<i16>(Mode::Private, Mode::Constant, 0, 0, 19, 21);
    }

    #[test]
    fn test_i16_public_plus_public() {
        run_test::<i16>(Mode::Public, Mode::Public, 0, 0, 20, 22);
    }

    #[test]
    fn test_i16_public_plus_private() {
        run_test::<i16>(Mode::Public, Mode::Private, 0, 0, 20, 22);
    }

    #[test]
    fn test_i16_private_plus_public() {
        run_test::<i16>(Mode::Private, Mode::Public, 0, 0, 20, 22);
    }

    #[test]
    fn test_i16_private_plus_private() {
        run_test::<i16>(Mode::Private, Mode::Private, 0, 0, 20, 22);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_plus_constant() {
        run_test::<u32>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_plus_public() {
        run_test::<u32>(Mode::Constant, Mode::Public, 0, 0, 33, 35);
    }

    #[test]
    fn test_u32_constant_plus_private() {
        run_test::<u32>(Mode::Constant, Mode::Private, 0, 0, 33, 35);
    }

    #[test]
    fn test_u32_public_plus_constant() {
        run_test::<u32>(Mode::Public, Mode::Constant, 0, 0, 33, 35);
    }

    #[test]
    fn test_u32_private_plus_constant() {
        run_test::<u32>(Mode::Private, Mode::Constant, 0, 0, 33, 35);
    }

    #[test]
    fn test_u32_public_plus_public() {
        run_test::<u32>(Mode::Public, Mode::Public, 0, 0, 33, 35);
    }

    #[test]
    fn test_u32_public_plus_private() {
        run_test::<u32>(Mode::Public, Mode::Private, 0, 0, 33, 35);
    }

    #[test]
    fn test_u32_private_plus_public() {
        run_test::<u32>(Mode::Private, Mode::Public, 0, 0, 33, 35);
    }

    #[test]
    fn test_u32_private_plus_private() {
        run_test::<u32>(Mode::Private, Mode::Private, 0, 0, 33, 35);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_plus_constant() {
        run_test::<i32>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_plus_public() {
        run_test::<i32>(Mode::Constant, Mode::Public, 0, 0, 34, 36);
    }

    #[test]
    fn test_i32_constant_plus_private() {
        run_test::<i32>(Mode::Constant, Mode::Private, 0, 0, 34, 36);
    }

    #[test]
    fn test_i32_public_plus_constant() {
        run_test::<i32>(Mode::Public, Mode::Constant, 0, 0, 35, 37);
    }

    #[test]
    fn test_i32_private_plus_constant() {
        run_test::<i32>(Mode::Private, Mode::Constant, 0, 0, 35, 37);
    }

    #[test]
    fn test_i32_public_plus_public() {
        run_test::<i32>(Mode::Public, Mode::Public, 0, 0, 36, 38);
    }

    #[test]
    fn test_i32_public_plus_private() {
        run_test::<i32>(Mode::Public, Mode::Private, 0, 0, 36, 38);
    }

    #[test]
    fn test_i32_private_plus_public() {
        run_test::<i32>(Mode::Private, Mode::Public, 0, 0, 36, 38);
    }

    #[test]
    fn test_i32_private_plus_private() {
        run_test::<i32>(Mode::Private, Mode::Private, 0, 0, 36, 38);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_plus_constant() {
        run_test::<u64>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_plus_public() {
        run_test::<u64>(Mode::Constant, Mode::Public, 0, 0, 65, 67);
    }

    #[test]
    fn test_u64_constant_plus_private() {
        run_test::<u64>(Mode::Constant, Mode::Private, 0, 0, 65, 67);
    }

    #[test]
    fn test_u64_public_plus_constant() {
        run_test::<u64>(Mode::Public, Mode::Constant, 0, 0, 65, 67);
    }

    #[test]
    fn test_u64_private_plus_constant() {
        run_test::<u64>(Mode::Private, Mode::Constant, 0, 0, 65, 67);
    }

    #[test]
    fn test_u64_public_plus_public() {
        run_test::<u64>(Mode::Public, Mode::Public, 0, 0, 65, 67);
    }

    #[test]
    fn test_u64_public_plus_private() {
        run_test::<u64>(Mode::Public, Mode::Private, 0, 0, 65, 67);
    }

    #[test]
    fn test_u64_private_plus_public() {
        run_test::<u64>(Mode::Private, Mode::Public, 0, 0, 65, 67);
    }

    #[test]
    fn test_u64_private_plus_private() {
        run_test::<u64>(Mode::Private, Mode::Private, 0, 0, 65, 67);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_plus_constant() {
        run_test::<i64>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_plus_public() {
        run_test::<i64>(Mode::Constant, Mode::Public, 0, 0, 66, 68);
    }

    #[test]
    fn test_i64_constant_plus_private() {
        run_test::<i64>(Mode::Constant, Mode::Private, 0, 0, 66, 68);
    }

    #[test]
    fn test_i64_public_plus_constant() {
        run_test::<i64>(Mode::Public, Mode::Constant, 0, 0, 67, 69);
    }

    #[test]
    fn test_i64_private_plus_constant() {
        run_test::<i64>(Mode::Private, Mode::Constant, 0, 0, 67, 69);
    }

    #[test]
    fn test_i64_public_plus_public() {
        run_test::<i64>(Mode::Public, Mode::Public, 0, 0, 68, 70);
    }

    #[test]
    fn test_i64_public_plus_private() {
        run_test::<i64>(Mode::Public, Mode::Private, 0, 0, 68, 70);
    }

    #[test]
    fn test_i64_private_plus_public() {
        run_test::<i64>(Mode::Private, Mode::Public, 0, 0, 68, 70);
    }

    #[test]
    fn test_i64_private_plus_private() {
        run_test::<i64>(Mode::Private, Mode::Private, 0, 0, 68, 70);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_plus_constant() {
        run_test::<u128>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_plus_public() {
        run_test::<u128>(Mode::Constant, Mode::Public, 0, 0, 129, 131);
    }

    #[test]
    fn test_u128_constant_plus_private() {
        run_test::<u128>(Mode::Constant, Mode::Private, 0, 0, 129, 131);
    }

    #[test]
    fn test_u128_public_plus_constant() {
        run_test::<u128>(Mode::Public, Mode::Constant, 0, 0, 129, 131);
    }

    #[test]
    fn test_u128_private_plus_constant() {
        run_test::<u128>(Mode::Private, Mode::Constant, 0, 0, 129, 131);
    }

    #[test]
    fn test_u128_public_plus_public() {
        run_test::<u128>(Mode::Public, Mode::Public, 0, 0, 129, 131);
    }

    #[test]
    fn test_u128_public_plus_private() {
        run_test::<u128>(Mode::Public, Mode::Private, 0, 0, 129, 131);
    }

    #[test]
    fn test_u128_private_plus_public() {
        run_test::<u128>(Mode::Private, Mode::Public, 0, 0, 129, 131);
    }

    #[test]
    fn test_u128_private_plus_private() {
        run_test::<u128>(Mode::Private, Mode::Private, 0, 0, 129, 131);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_plus_constant() {
        run_test::<i128>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_plus_public() {
        run_test::<i128>(Mode::Constant, Mode::Public, 0, 0, 130, 132);
    }

    #[test]
    fn test_i128_constant_plus_private() {
        run_test::<i128>(Mode::Constant, Mode::Private, 0, 0, 130, 132);
    }

    #[test]
    fn test_i128_public_plus_constant() {
        run_test::<i128>(Mode::Public, Mode::Constant, 0, 0, 131, 133);
    }

    #[test]
    fn test_i128_private_plus_constant() {
        run_test::<i128>(Mode::Private, Mode::Constant, 0, 0, 131, 133);
    }

    #[test]
    fn test_i128_public_plus_public() {
        run_test::<i128>(Mode::Public, Mode::Public, 0, 0, 132, 134);
    }

    #[test]
    fn test_i128_public_plus_private() {
        run_test::<i128>(Mode::Public, Mode::Private, 0, 0, 132, 134);
    }

    #[test]
    fn test_i128_private_plus_public() {
        run_test::<i128>(Mode::Private, Mode::Public, 0, 0, 132, 134);
    }

    #[test]
    fn test_i128_private_plus_private() {
        run_test::<i128>(Mode::Private, Mode::Private, 0, 0, 132, 134);
    }

    // Exhaustive tests for u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_plus_constant() {
        run_exhaustive_test::<u8>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_plus_public() {
        run_exhaustive_test::<u8>(Mode::Constant, Mode::Public, 0, 0, 9, 11);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_plus_private() {
        run_exhaustive_test::<u8>(Mode::Constant, Mode::Private, 0, 0, 9, 11);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_plus_constant() {
        run_exhaustive_test::<u8>(Mode::Public, Mode::Constant, 0, 0, 9, 11);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_plus_constant() {
        run_exhaustive_test::<u8>(Mode::Private, Mode::Constant, 0, 0, 9, 11);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_plus_public() {
        run_exhaustive_test::<u8>(Mode::Public, Mode::Public, 0, 0, 9, 11);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_plus_private() {
        run_exhaustive_test::<u8>(Mode::Public, Mode::Private, 0, 0, 9, 11);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_plus_public() {
        run_exhaustive_test::<u8>(Mode::Private, Mode::Public, 0, 0, 9, 11);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_plus_private() {
        run_exhaustive_test::<u8>(Mode::Private, Mode::Private, 0, 0, 9, 11);
    }

    // Exhaustive tests for i8.

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_plus_constant() {
        run_exhaustive_test::<i8>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_plus_public() {
        run_exhaustive_test::<i8>(Mode::Constant, Mode::Public, 0, 0, 10, 12);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_plus_private() {
        run_exhaustive_test::<i8>(Mode::Constant, Mode::Private, 0, 0, 10, 12);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_plus_constant() {
        run_exhaustive_test::<i8>(Mode::Public, Mode::Constant, 0, 0, 11, 13);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_plus_constant() {
        run_exhaustive_test::<i8>(Mode::Private, Mode::Constant, 0, 0, 11, 13);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_plus_public() {
        run_exhaustive_test::<i8>(Mode::Public, Mode::Public, 0, 0, 12, 14);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_plus_private() {
        run_exhaustive_test::<i8>(Mode::Public, Mode::Private, 0, 0, 12, 14);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_plus_public() {
        run_exhaustive_test::<i8>(Mode::Private, Mode::Public, 0, 0, 12, 14);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_plus_private() {
        run_exhaustive_test::<i8>(Mode::Private, Mode::Private, 0, 0, 12, 14);
    }
}
