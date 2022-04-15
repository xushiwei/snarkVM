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
use snarkvm_circuits::{Double as DoubleCircuit, Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Doubles `first`, storing the outcome in `destination`.
pub struct Double<P: Program> {
    operation: UnaryOperation<P>,
}

impl<P: Program> Double<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for Double<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "double"
    }
}

impl<P: Program> Operation<P> for Double<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the values for the first operand.
        let first = match registers.load(self.operation.first()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Perform the operation.
        let result = match first {
            Literal::Field(a) => Literal::Field(a.double()),
            Literal::Group(a) => Literal::Group(a.double()),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

impl<P: Program> Parser for Double<P> {
    type Environment = P::Environment;

    /// Parses a string into an 'double' operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the operation from the string.
        map(UnaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for Double<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for Double<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for Double<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for Double<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::Double(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process};

    test_modes!(field, Double, "1field", "2field");
    test_modes!(
        group,
        Double,
        "2group",
        "6696402423798020098358712667671415812305707015226794708266486692814448135893group"
    );

    test_instruction_halts!(i8_double_halts, Double, "Invalid 'double' instruction", "1i8");
    test_instruction_halts!(i16_double_halts, Double, "Invalid 'double' instruction", "1i16");
    test_instruction_halts!(i32_double_halts, Double, "Invalid 'double' instruction", "1i32");
    test_instruction_halts!(i64_double_halts, Double, "Invalid 'double' instruction", "1i64");
    test_instruction_halts!(i128_double_halts, Double, "Invalid 'double' instruction", "1i128");
    test_instruction_halts!(u8_double_halts, Double, "Invalid 'double' instruction", "1u8");
    test_instruction_halts!(u16_double_halts, Double, "Invalid 'double' instruction", "1u16");
    test_instruction_halts!(u32_double_halts, Double, "Invalid 'double' instruction", "1u32");
    test_instruction_halts!(u64_double_halts, Double, "Invalid 'double' instruction", "1u64");
    test_instruction_halts!(u128_double_halts, Double, "Invalid 'double' instruction", "1u128");
    test_instruction_halts!(scalar_double_halts, Double, "Invalid 'double' instruction", "1scalar.constant");
    test_instruction_halts!(
        address_double_halts,
        Double,
        "Invalid 'double' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(boolean_double_halts, Double, "Invalid 'double' instruction", "true.constant");
    test_instruction_halts!(string_double_halts, Double, "Invalid 'double' instruction", "\"hello\".constant");

    #[test]
    #[should_panic(expected = "message is not a literal")]
    fn test_composite_halts() {
        let first = Value::<Process>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("2group.public"),
            Literal::from_str("10field.private"),
        ]);

        let registers = Registers::<Process>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        Double::from_str("r0 into r1").evaluate(&registers);
    }
}
