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

use crate::{
    function::{parsers::*, Instruction, Opcode, Operation, Registers},
    helpers::Register,
    Program,
    Value,
};
use snarkvm_circuits::{Equal as EqualCircuit, Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Checks if `first` equals `second`, storing the outcome in `destination`.
pub struct Equal<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> Equal<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Equal<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "eq"
    }
}

impl<P: Program> Operation<P> for Equal<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the values for the first and second operands.
        let first = match registers.load(self.operation.first()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };
        let second = match registers.load(self.operation.second()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Perform the operation.
        let result = match (first, second) {
            (Literal::Address(a), Literal::Address(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::Boolean(a), Literal::Boolean(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::Field(a), Literal::Field(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::Group(a), Literal::Group(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::I8(a), Literal::I8(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::I16(a), Literal::I16(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::I32(a), Literal::I32(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::I64(a), Literal::I64(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::I128(a), Literal::I128(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::Scalar(a), Literal::Scalar(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::U64(a), Literal::U64(b)) => Literal::Boolean(a.is_equal(&b)),
            (Literal::U128(a), Literal::U128(b)) => Literal::Boolean(a.is_equal(&b)),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Equal<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'eq' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        let (string, operation) = map(BinaryOperation::parse, |operation| Self { operation })(string)?;
        // Return the operation.
        Ok((string, operation))
    }
}

impl<P: Program> fmt::Display for Equal<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Equal<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Equal<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Equal<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Equal(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process};

    const BOOLEAN_MODE_TESTS: [[&str; 3]; 9] = [
        ["public", "public", "private"],
        ["public", "constant", "public"],
        ["public", "private", "private"],
        ["private", "constant", "private"],
        ["private", "public", "private"],
        ["private", "private", "private"],
        ["constant", "private", "private"],
        ["constant", "public", "public"],
        ["constant", "constant", "constant"],
    ];

    test_modes!(
        address,
        Equal,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "true"
    );
    test_modes!(boolean, Equal, "true", "true", "true", BOOLEAN_MODE_TESTS);
    test_modes!(field, Equal, "1field", "1field", "true");
    test_modes!(group, Equal, "2group", "2group", "true");
    test_modes!(i8, Equal, "1i8", "1i8", "true");
    test_modes!(i16, Equal, "1i16", "1i16", "true");
    test_modes!(i32, Equal, "1i32", "1i32", "true");
    test_modes!(i64, Equal, "1i64", "1i64", "true");
    test_modes!(i128, Equal, "1i128", "1i128", "true");
    test_modes!(scalar, Equal, "1scalar", "1scalar", "true");
    test_modes!(u8, Equal, "1u8", "1u8", "true");
    test_modes!(u16, Equal, "1u16", "1u16", "true");
    test_modes!(u32, Equal, "1u32", "1u32", "true");
    test_modes!(u64, Equal, "1u64", "1u64", "true");
    test_modes!(u128, Equal, "1u128", "1u128", "true");

    test_instruction_halts!(string_halts, Equal, "Invalid 'eq' instruction", "\"hello\"", "\"hello\"");

    #[test]
    #[should_panic(expected = "message is not a literal")]
    fn test_composite_halts() {
        let first = Value::<Process>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("2group.public"),
            Literal::from_str("10field.private"),
        ]);
        let second = first.clone();

        let registers = Registers::<Process>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        Equal::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
