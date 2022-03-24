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
use snarkvm_circuits::{Compare, Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Checks that `first` is greater than `second`, storing the outcome in `destination`.
pub struct GreaterThan<M: Memory> {
    operation: BinaryOperation<M::Environment>,
}

impl<M: Memory> Operation for GreaterThan<M> {
    type Memory = M;

    /// Returns the opcode as a string.
    #[inline]
    fn mnemonic() -> &'static str {
        "gt"
    }

    /// Parses a string into an 'gt' operation.
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
            (Literal::Field(a), Literal::Field(b)) => Literal::Boolean(a.is_greater_than(&b)),
            (Literal::Scalar(a), Literal::Scalar(b)) => Literal::Boolean(a.is_greater_than(&b)),
            _ => Self::Memory::halt(format!("Invalid '{}' instruction", Self::mnemonic())),
        };

        memory.store(self.operation.destination(), result);
    }
}

impl<M: Memory> fmt::Display for GreaterThan<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<M: Memory> FromBytes for GreaterThan<M> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<M: Memory> ToBytes for GreaterThan<M> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for GreaterThan<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::GreaterThan(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Input, Register, Stack};
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_greater_than_field() {
        let first = Literal::<Circuit>::from_str("1field.public");
        let second = Literal::<Circuit>::from_str("2field.private");
        let expected = Literal::<Circuit>::from_str("false.private");

        let memory = Stack::<Circuit>::default();
        Input::from_str("input r0 field.public;", &memory).assign(first).evaluate(&memory);
        Input::from_str("input r1 field.private;", &memory).assign(second).evaluate(&memory);

        GreaterThan::<Stack<Circuit>>::from_str("r2 r0 r1", &memory).evaluate(&memory);
        assert_eq!(expected, memory.load(&Register::new(2)));
    }

    #[test]
    fn test_greater_than_scalar() {
        let first = Literal::<Circuit>::from_str("2scalar.public");
        let second = Literal::<Circuit>::from_str("1scalar.private");
        let expected = Literal::<Circuit>::from_str("true.private");

        let memory = Stack::<Circuit>::default();
        Input::from_str("input r0 scalar.public;", &memory).assign(first).evaluate(&memory);
        Input::from_str("input r1 scalar.private;", &memory).assign(second).evaluate(&memory);

        GreaterThan::<Stack<Circuit>>::from_str("r2 r0 r1", &memory).evaluate(&memory);
        assert_eq!(expected, memory.load(&Register::new(2)));
    }
}
