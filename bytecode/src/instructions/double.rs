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
use snarkvm_circuits::{Double as CircuitDouble, Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Doubles `operand`, storing the outcome in `destination`.
pub struct Double<M: Memory> {
    operation: UnaryOperation<M::Environment>,
}

impl<M: Memory> Operation for Double<M> {
    type Memory = M;

    /// Returns the opcode as a string.
    #[inline]
    fn mnemonic() -> &'static str {
        "double"
    }

    /// Parses a string into an 'double' operation.
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
        // Load the values for operand.
        let operand = self.operation.operand().load(memory);

        // Perform the operation.
        let result = match operand {
            Literal::Field(a) => Literal::Field(a.double()),
            Literal::Group(a) => Literal::Group(a.double()),
            _ => Self::Memory::halt(format!("Invalid '{}' instruction", Self::mnemonic())),
        };

        memory.store(self.operation.destination(), result);
    }
}

impl<M: Memory> fmt::Display for Double<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<M: Memory> FromBytes for Double<M> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)? })
    }
}

impl<M: Memory> ToBytes for Double<M> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for Double<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::Double(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Input, Register, Stack};
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_double_field() {
        let operand = Literal::<Circuit>::from_str("1field.private");
        let expected = Literal::<Circuit>::from_str("2field.private");

        let memory = Stack::<Circuit>::default();
        Input::from_str("input r0 field.private;", &memory).assign(operand).evaluate(&memory);

        Double::<Stack<Circuit>>::from_str("r1 r0", &memory).evaluate(&memory);
        assert_eq!(expected, memory.load(&Register::new(1)));
    }

    #[test]
    fn test_double_group() {
        let operand = Literal::<Circuit>::from_str("0group.private");
        let expected = Literal::<Circuit>::from_str("0group.private");

        let memory = Stack::<Circuit>::default();
        Input::from_str("input r0 group.private;", &memory).assign(operand).evaluate(&memory);

        Double::<Stack<Circuit>>::from_str("r1 r0", &memory).evaluate(&memory);
        assert_eq!(expected, memory.load(&Register::new(1)));
    }
}
