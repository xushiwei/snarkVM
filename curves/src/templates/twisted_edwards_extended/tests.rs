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

use super::{Affine, Projective};

use snarkvm_utilities::{
    io::Cursor,
    rand::{test_rng, UniformRand},
    serialize::{CanonicalDeserialize, CanonicalSerialize},
    to_bytes_le,
    ToBytes,
};

use crate::traits::{AffineCurve, MontgomeryParameters, ProjectiveCurve, TwistedEdwardsParameters};
use snarkvm_fields::{Field, One, PrimeField, Zero};

pub const ITERATIONS: usize = 10;

pub fn montgomery_conversion_test<P>()
where
    P: TwistedEdwardsParameters,
{
    // A = 2 * (a + d) / (a - d)
    let a = P::BaseField::one().double() * (P::COEFF_A + P::COEFF_D) * (P::COEFF_A - P::COEFF_D).inverse().unwrap();
    // B = 4 / (a - d)
    let b = P::BaseField::one().double().double() * (P::COEFF_A - P::COEFF_D).inverse().unwrap();

    assert_eq!(a, P::MontgomeryParameters::COEFF_A);
    assert_eq!(b, P::MontgomeryParameters::COEFF_B);
}

pub fn edwards_test<P: TwistedEdwardsParameters>()
where
    P::BaseField: PrimeField,
{
    edwards_curve_serialization_test::<P>();
    edwards_from_random_bytes::<P>();
    edwards_from_x_and_y_coordinates::<P>();
}

pub fn edwards_curve_serialization_test<P: TwistedEdwardsParameters>() {
    let buf_size = Affine::<P>::zero().serialized_size();

    let mut rng = test_rng();

    for _ in 0..10 {
        let a = Projective::<P>::rand(&mut rng);
        let a = a.to_affine();
        {
            let mut serialized = vec![0; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize(&mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let b = Affine::<P>::deserialize(&mut cursor).unwrap();
            assert_eq!(a, b);
        }

        {
            let a = Affine::<P>::zero();
            let mut serialized = vec![0; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize(&mut cursor).unwrap();
            let mut cursor = Cursor::new(&serialized[..]);
            let b = Affine::<P>::deserialize(&mut cursor).unwrap();
            assert_eq!(a, b);
        }

        {
            let a = Affine::<P>::zero();
            let mut serialized = vec![0; buf_size - 1];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize(&mut cursor).unwrap_err();
        }

        {
            let serialized = vec![0; buf_size - 1];
            let mut cursor = Cursor::new(&serialized[..]);
            Affine::<P>::deserialize(&mut cursor).unwrap_err();
        }

        {
            let mut serialized = vec![0; a.uncompressed_size()];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize_uncompressed(&mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let b = Affine::<P>::deserialize_uncompressed(&mut cursor).unwrap();
            assert_eq!(a, b);
        }

        {
            let a = Affine::<P>::zero();
            let mut serialized = vec![0; a.uncompressed_size()];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize_uncompressed(&mut cursor).unwrap();
            let mut cursor = Cursor::new(&serialized[..]);
            let b = Affine::<P>::deserialize_uncompressed(&mut cursor).unwrap();
            assert_eq!(a, b);
        }
    }
}

pub fn edwards_from_random_bytes<P: TwistedEdwardsParameters>()
where
    P::BaseField: PrimeField,
{
    let buf_size = Affine::<P>::zero().serialized_size();

    let mut rng = test_rng();

    for _ in 0..ITERATIONS {
        let a = Projective::<P>::rand(&mut rng);
        let a = a.to_affine();
        {
            let mut serialized = vec![0; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize(&mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let p1 = Affine::<P>::deserialize(&mut cursor).unwrap();
            let p2 = Affine::<P>::from_random_bytes(&serialized).unwrap();
            assert_eq!(p1, p2);
        }
    }

    for _ in 0..ITERATIONS {
        let biginteger = <<Affine<P> as AffineCurve>::BaseField as PrimeField>::BigInteger::rand(&mut rng);
        let mut bytes = to_bytes_le![biginteger].unwrap();
        let mut g = Affine::<P>::from_random_bytes(&bytes);
        while g.is_none() {
            bytes.iter_mut().for_each(|i| *i = i.wrapping_sub(1));
            g = Affine::<P>::from_random_bytes(&bytes);
        }
        let _g = g.unwrap();
    }
}

pub fn edwards_from_x_and_y_coordinates<P: TwistedEdwardsParameters>()
where
    P::BaseField: PrimeField,
{
    let mut rng = test_rng();

    for _ in 0..ITERATIONS {
        let a = Projective::<P>::rand(&mut rng);
        let a = a.to_affine();
        {
            let x = a.x;

            let a1 = Affine::<P>::from_x_coordinate(x, true).unwrap();
            let a2 = Affine::<P>::from_x_coordinate(x, false).unwrap();

            assert!(a == a1 || a == a2);
        }
        {
            let y = a.y;

            let a1 = Affine::<P>::from_y_coordinate(y, true).unwrap();
            let a2 = Affine::<P>::from_y_coordinate(y, false).unwrap();

            assert!(a == a1 || a == a2);
        }
    }
}
