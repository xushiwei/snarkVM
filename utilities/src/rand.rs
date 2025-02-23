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

use rand::{
    distributions::{Distribution, Standard},
    rngs::StdRng,
    Rng,
    SeedableRng,
};
use rand_xorshift::XorShiftRng;

pub trait UniformRand: Sized {
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self;
}

impl<T> UniformRand for T
where
    Standard: Distribution<T>,
{
    #[inline]
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        rng.sample(Standard)
    }
}

/// A fast Rng which should be used only in tests or benchmarks, but not for any real world purposes.
pub fn test_rng() -> XorShiftRng {
    // Obtain the initial seed using entropy provided by the OS.
    let seed = StdRng::from_entropy().gen();

    // Use the seed to initialize a fast, non-cryptographic Rng.
    XorShiftRng::seed_from_u64(seed)
}

/// An Rng which can be used in tests or benchmarks requiring a CryptoRng.
pub fn test_crypto_rng() -> StdRng {
    StdRng::from_entropy()
}
