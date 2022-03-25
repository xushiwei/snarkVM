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

use crate::{instructions::Instruction, Memory, Operation, UnaryOperation};
use snarkvm_circuits::{AbsChecked as CircuitAbsChecked, Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Computes the absolute value of `operand`, checks for overflow, and stores the result in `destination`.
pub struct AbsChecked<M: Memory> {
    operation: UnaryOperation<M::Environment>,
}

impl<M: Memory> Operation for AbsChecked<M> {
    type Memory = M;

    /// Returns the mnemonic for the `AbsChecked` operation.
    #[inline]
    fn mnemonic() -> &'static str {
        "abs.c"
    }

    /// Parses a string into an `AbsChecked` operation.
    #[inline]
    fn parse(string: &str, memory: Self::Memory) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(UnaryOperation::parse, |operation| Self { operation })(string)?;
        // Initialize the destination register.
        memory.initialize(operation.operation.destination());
        // Return the operation.
        Ok((string, operation))
    }

    /// Evaluates the operation in-place.
    #[inline]
    fn evaluate(&self, memory: &Self::Memory) {
        // Load the values for the first and second operands.
        let operand = self.operation.operand().load(memory);

        // Perform the operation.
        let result = match operand {
            Literal::I8(a) => Literal::I8(a.abs_checked()),
            Literal::I16(a) => Literal::I16(a.abs_checked()),
            Literal::I32(a) => Literal::I32(a.abs_checked()),
            Literal::I64(a) => Literal::I64(a.abs_checked()),
            Literal::I128(a) => Literal::I128(a.abs_checked()),
            Literal::U8(a) => Literal::U8(a.abs_checked()),
            Literal::U16(a) => Literal::U16(a.abs_checked()),
            Literal::U32(a) => Literal::U32(a.abs_checked()),
            Literal::U64(a) => Literal::U64(a.abs_checked()),
            Literal::U128(a) => Literal::U128(a.abs_checked()),
            _ => Self::Memory::halt(format!("Invalid '{}' instruction", Self::mnemonic())),
        };

        memory.store(self.operation.destination(), result);
    }
}

impl<M: Memory> fmt::Display for AbsChecked<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<M: Memory> FromBytes for AbsChecked<M> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)? })
    }
}

impl<M: Memory> ToBytes for AbsChecked<M> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for AbsChecked<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::AbsChecked(self)
    }
}

#[cfg(test)]
mod tests {}
