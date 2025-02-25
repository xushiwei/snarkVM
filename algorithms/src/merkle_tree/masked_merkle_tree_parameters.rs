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

use crate::{MaskedMerkleParameters, MerkleParameters, CRH};

/// Defines a Merkle tree using the provided hash and depth.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MaskedMerkleTreeParameters<H: CRH, const DEPTH: usize>(H, H, String);

impl<H: CRH, const DEPTH: usize> MerkleParameters for MaskedMerkleTreeParameters<H, DEPTH> {
    type H = H;

    const DEPTH: usize = DEPTH;

    fn setup(message: &str) -> Self {
        Self(Self::H::setup(message), Self::H::setup(message), message.into())
    }

    // TODO (howardwu): TEMPORARY - This is a temporary fix to support ToBytes/FromBytes for
    //  LedgerProof and LocalProof. While it is "safe", it is not performant to deserialize
    //  in such a manual fashion. However, given the extent to which modifying the architecture
    //  of Merkle trees in snarkVM impacts many APIs downstream, this forward-compatible change
    //  is being introduced until a proper refactor can be discussed and implemented.
    //  If you are seeing this message, please be proactive in bringing it up :)
    /// Returns the saved `message` from calling the `MerkleParameters::setup()` function.
    fn setup_message(&self) -> &str {
        &self.2
    }

    fn crh(&self) -> &Self::H {
        &self.0
    }
}

impl<H: CRH, const DEPTH: usize> MaskedMerkleParameters for MaskedMerkleTreeParameters<H, DEPTH> {
    fn mask_crh(&self) -> &Self::H {
        &self.1
    }
}
