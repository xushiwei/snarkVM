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

impl<E: Environment> Neg for Group<E> {
    type Output = Self;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        Group { x: -self.x, y: self.y }
    }
}

impl<E: Environment> Neg for &Group<E> {
    type Output = Group<E>;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        -(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 100;

    fn check_neg(
        name: &str,
        expected: <Circuit as Environment>::Affine,
        candidate_input: Group<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scope(name, || {
            let candidate_output = -candidate_input;
            assert_eq!(expected, candidate_output.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });
    }

    #[test]
    fn test_neg_constant() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let expected = -point;
            assert!(expected.is_on_curve());
            assert!(expected.is_in_correct_subgroup_assuming_on_curve());

            let candidate_input = Group::<Circuit>::new(Mode::Constant, point);
            check_neg(&format!("NEG Constant {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_neg_public() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let expected = -point;
            assert!(expected.is_on_curve());
            assert!(expected.is_in_correct_subgroup_assuming_on_curve());

            let candidate_input = Group::<Circuit>::new(Mode::Public, point);
            check_neg(&format!("NEG Public {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_neg_private() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let expected = -point;
            assert!(expected.is_on_curve());
            assert!(expected.is_in_correct_subgroup_assuming_on_curve());

            let candidate_input = Group::<Circuit>::new(Mode::Private, point);
            check_neg(&format!("NEG Private {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_zero() {
        let expected = <Circuit as Environment>::Affine::zero();

        let candidate_input = Group::<Circuit>::zero();
        check_neg("NEG Constant Zero", expected, candidate_input, 0, 0, 0, 0);

        let candidate_input = Group::<Circuit>::new(Mode::Public, expected);
        check_neg("NEG Public Zero", expected, candidate_input, 0, 0, 0, 0);

        let candidate_input = Group::<Circuit>::new(Mode::Private, expected);
        check_neg("NEG Private Zero", expected, candidate_input, 0, 0, 0, 0);
    }
}
