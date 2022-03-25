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

use crate::{instructions::Instruction, Memory, Operand, Operation, Register};
use snarkvm_circuits::{
    Field,
    Group,
    Literal,
    Parser,
    ParserResult,
    Scalar,
    Ternary as CircuitTernary,
    I128,
    I16,
    I32,
    I64,
    I8,
    U128,
    U16,
    U32,
    U64,
    U8,
};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::bytes::complete::tag;
use std::io::{Read, Result as IoResult, Write};

/// Selects `first`, if `condition` is true, otherwise selects `second`, storing the result in `destination`.
pub struct Ternary<M: Memory> {
    destination: Register<M::Environment>,
    condition: Operand<M::Environment>,
    first: Operand<M::Environment>,
    second: Operand<M::Environment>,
}

impl<M: Memory> Operation for Ternary<M> {
    type Memory = M;

    /// Returns the opcode as a string.
    #[inline]
    fn mnemonic() -> &'static str {
        "ter"
    }

    // TODO (@pranav) Consider implementing a ternary parser.
    /// Parses a string into an 'add' operation.
    #[inline]
    fn parse(string: &str, memory: Self::Memory) -> ParserResult<Self> {
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the first operand from the string.
        let (string, condition) = Operand::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the second operand from the string.
        let (string, first) = Operand::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the third operand from the string.
        let (string, second) = Operand::parse(string)?;

        // Initialize the destination register.
        memory.initialize(&destination);

        Ok((string, Self { destination, condition, first, second }))
    }

    /// Evaluates the operation in-place.
    #[inline]
    fn evaluate(&self, memory: &Self::Memory) {
        // Load the values for the condition, first, and second operands.
        let condition = self.condition.load(memory);
        let first = self.first.load(memory);
        let second = self.second.load(memory);

        // Perform the operation.
        let result = match (condition, first, second) {
            (Literal::Boolean(condition), Literal::Field(a), Literal::Field(b)) => {
                Literal::Field(Field::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::Group(a), Literal::Group(b)) => {
                Literal::Group(Group::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::I8(a), Literal::I8(b)) => {
                Literal::I8(I8::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::I16(a), Literal::I16(b)) => {
                Literal::I16(I16::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::I32(a), Literal::I32(b)) => {
                Literal::I32(I32::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::I64(a), Literal::I64(b)) => {
                Literal::I64(I64::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::I128(a), Literal::I128(b)) => {
                Literal::I128(I128::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::Scalar(a), Literal::Scalar(b)) => {
                Literal::Scalar(Scalar::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::U8(a), Literal::U8(b)) => {
                Literal::U8(U8::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::U16(a), Literal::U16(b)) => {
                Literal::U16(U16::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::U32(a), Literal::U32(b)) => {
                Literal::U32(U32::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::U64(a), Literal::U64(b)) => {
                Literal::U64(U64::ternary(&condition, &a, &b))
            }
            (Literal::Boolean(condition), Literal::U128(a), Literal::U128(b)) => {
                Literal::U128(U128::ternary(&condition, &a, &b))
            }
            _ => Self::Memory::halt(format!("Invalid '{}' instruction", Self::mnemonic())),
        };

        memory.store(&self.destination, result);
    }
}

impl<M: Memory> fmt::Display for Ternary<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {} {} {}", self.destination, self.condition, self.first, self.second)
    }
}

impl<M: Memory> FromBytes for Ternary<M> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let destination = Register::read_le(&mut reader)?;
        let condition = Operand::read_le(&mut reader)?;
        let first = Operand::read_le(&mut reader)?;
        let second = Operand::read_le(&mut reader)?;
        Ok(Self { destination, condition, first, second })
    }
}

impl<M: Memory> ToBytes for Ternary<M> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.destination.write_le(&mut writer)?;
        self.condition.write_le(&mut writer)?;
        self.first.write_le(&mut writer)?;
        self.second.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<M: Memory> Into<Instruction<M>> for Ternary<M> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<M> {
        Instruction::Ternary(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Input, Register, Stack};
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_ternary_field() {
        let condition = Literal::<Circuit>::from_str("true.private");
        let first = Literal::<Circuit>::from_str("0field.private");
        let second = Literal::<Circuit>::from_str("1field.private");
        let expected = Literal::<Circuit>::from_str("0field.private");

        let memory = Stack::<Circuit>::default();
        Input::from_str("input r0 boolean.private;", &memory).assign(condition).evaluate(&memory);
        Input::from_str("input r1 field.private;", &memory).assign(first).evaluate(&memory);
        Input::from_str("input r2 field.private;", &memory).assign(second).evaluate(&memory);

        Ternary::<Stack<Circuit>>::from_str("r3 r0 r1 r2", &memory).evaluate(&memory);
        assert_eq!(expected, memory.load(&Register::new(3)));
    }

    #[test]
    fn test_ternary_group() {
        let condition = Literal::<Circuit>::from_str("false.private");
        let first = Literal::<Circuit>::from_str("0group.private");
        let second = Literal::<Circuit>::from_str("2group.private");
        let expected = Literal::<Circuit>::from_str("2group.private");

        let memory = Stack::<Circuit>::default();
        Input::from_str("input r0 boolean.private;", &memory).assign(condition).evaluate(&memory);
        Input::from_str("input r1 group.private;", &memory).assign(first).evaluate(&memory);
        Input::from_str("input r2 group.private;", &memory).assign(second).evaluate(&memory);

        Ternary::<Stack<Circuit>>::from_str("r3 r0 r1 r2", &memory).evaluate(&memory);
        assert_eq!(expected, memory.load(&Register::new(3)));
    }

    #[test]
    fn test_ternary_scalar() {
        let condition = Literal::<Circuit>::from_str("false.private");
        let first = Literal::<Circuit>::from_str("0scalar.private");
        let second = Literal::<Circuit>::from_str("1scalar.private");
        let expected = Literal::<Circuit>::from_str("1scalar.private");

        let memory = Stack::<Circuit>::default();
        Input::from_str("input r0 boolean.private;", &memory).assign(condition).evaluate(&memory);
        Input::from_str("input r1 scalar.private;", &memory).assign(first).evaluate(&memory);
        Input::from_str("input r2 scalar.private;", &memory).assign(second).evaluate(&memory);

        Ternary::<Stack<Circuit>>::from_str("r3 r0 r1 r2", &memory).evaluate(&memory);
        assert_eq!(expected, memory.load(&Register::new(3)));
    }
}
