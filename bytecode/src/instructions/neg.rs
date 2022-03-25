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
use snarkvm_circuits::{Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::{
    io::{Read, Result as IoResult, Write},
    ops::Neg as OpNeg,
};

/// Negates `operand`, storing the outcome in `destination`.
pub struct Neg<M: Memory> {
    operation: UnaryOperation<M::Environment>,
}

impl<M: Memory> Operation for Neg<M> {
    type Memory = M;

    /// Returns the opcode as a string.
    #[inline]
    fn mnemonic() -> &'static str {
        "neg"
    }

    /// Parses a string into an 'add' operation.
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
            Literal::Field(a) => Literal::Field(a.neg()),
            Literal::Group(a) => Literal::Group(a.neg()),
            Literal::I8(a) => Literal::I8(a.neg()),
            Literal::I16(a) => Literal::I16(a.neg()),
            Literal::I32(a) => Literal::I32(a.neg()),
            Literal::I64(a) => Literal::I64(a.neg()),
            Literal::I128(a) => Literal::I128(a.neg()),
            Literal::U8(a) => Literal::U8(a.neg()),
            Literal::U16(a) => Literal::U16(a.neg()),
            Literal::U32(a) => Literal::U32(a.neg()),
            Literal::U64(a) => Literal::U64(a.neg()),
            Literal::U128(a) => Literal::U128(a.neg()),
            _ => Self::Memory::halt(format!("Invalid '{}' instruction", Self::mnemonic())),
        };

        memory.store(self.operation.destination(), result);
    }
}

impl<M: Memory> fmt::Display for Neg<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<M: Memory> FromBytes for Neg<M> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)? })
    }
}

impl<M: Memory> ToBytes for Neg<M> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for Neg<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::Neg(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Input, Register, Stack};
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_neg_field() {
        let operand = Literal::<Circuit>::from_str("1field.private");
        let expected = Literal::<Circuit>::from_str(
            "8444461749428370424248824938781546531375899335154063827935233455917409239040field.private",
        );

        let memory = Stack::<Circuit>::default();
        Input::from_str("input r0 field.private;", &memory).assign(operand).evaluate(&memory);

        Neg::<Stack<Circuit>>::from_str("r1 r0", &memory).evaluate(&memory);
        assert_eq!(expected, memory.load(&Register::new(1)));
    }

    #[test]
    fn test_neg_group() {
        let operand = Literal::<Circuit>::from_str("0group.private");
        let expected = Literal::<Circuit>::from_str("0group.private");

        let memory = Stack::<Circuit>::default();
        Input::from_str("input r0 group.private;", &memory).assign(operand).evaluate(&memory);

        Neg::<Stack<Circuit>>::from_str("r1 r0", &memory).evaluate(&memory);
        assert_eq!(expected, memory.load(&Register::new(1)));
    }
}
