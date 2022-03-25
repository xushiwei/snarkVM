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

use crate::{instructions::Instruction, BinaryOperation, Memory, Operation};
use snarkvm_circuits::{Literal, MulWrapped as CircuitMulWrapped, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Multiplies `first` with `second`, wrapping on overflow, and stores the result in `destination`.
pub struct MulWrapped<M: Memory> {
    operation: BinaryOperation<M::Environment>,
}

impl<M: Memory> Operation for MulWrapped<M> {
    type Memory = M;

    /// Returns the mnemonic for the `MulWrapped` operation.
    #[inline]
    fn mnemonic() -> &'static str {
        "mul.w"
    }

    /// Parses a string into an `MulWrapped` operation.
    #[inline]
    fn parse(string: &str, memory: Self::Memory) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Initialize the destination register.
        memory.initialize(operation.operation.destination());
        // Return the operation.
        Ok((string, operation))
    }

    /// Evaluates the operation in-place.
    #[inline]
    fn evaluate(&self, memory: &Self::Memory) {
        // Load the values for the first and second operands.
        let first = self.operation.first().load(memory);
        let second = self.operation.second().load(memory);

        // Perform the operation.
        let result = match (first, second) {
            (Literal::I8(a), Literal::I8(b)) => Literal::I8(a.mul_wrapped(&b)),
            (Literal::I16(a), Literal::I16(b)) => Literal::I16(a.mul_wrapped(&b)),
            (Literal::I32(a), Literal::I32(b)) => Literal::I32(a.mul_wrapped(&b)),
            (Literal::I64(a), Literal::I64(b)) => Literal::I64(a.mul_wrapped(&b)),
            (Literal::I128(a), Literal::I128(b)) => Literal::I128(a.mul_wrapped(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a.mul_wrapped(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a.mul_wrapped(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a.mul_wrapped(&b)),
            (Literal::U64(a), Literal::U64(b)) => Literal::U64(a.mul_wrapped(&b)),
            (Literal::U128(a), Literal::U128(b)) => Literal::U128(a.mul_wrapped(&b)),
            _ => Self::Memory::halt(format!("Invalid '{}' instruction", Self::mnemonic())),
        };

        memory.store(self.operation.destination(), result);
    }
}

impl<M: Memory> fmt::Display for MulWrapped<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<M: Memory> FromBytes for MulWrapped<M> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<M: Memory> ToBytes for MulWrapped<M> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for MulWrapped<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::MulWrapped(self)
    }
}

#[cfg(test)]
mod tests {}
