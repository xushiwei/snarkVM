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

pub mod abs_checked;
pub use abs_checked::*;

pub mod abs_wrapped;
pub use abs_wrapped::*;

pub mod add;
pub use add::*;

pub mod add_checked;
pub use add_checked::*;

pub mod add_wrapped;
pub use add_wrapped::*;

pub mod and;
pub use and::*;

pub mod div;
pub use div::*;

pub mod div_checked;
pub use div_checked::*;

pub mod div_wrapped;
pub use div_wrapped::*;

pub mod double;
pub use double::*;

pub mod equal;
pub use equal::*;

pub mod gt;
pub use gt::*;

pub mod gte;
pub use gte::*;

pub mod inv;
pub use inv::*;

pub mod lt;
pub use lt::*;

pub mod lte;
pub use lte::*;

pub mod mul;
pub use mul::*;

pub mod mul_checked;
pub use mul_checked::*;

pub mod mul_wrapped;
pub use mul_wrapped::*;

pub mod nand;
pub use nand::*;

pub mod neg;
pub use neg::*;

pub mod neq;
pub use neq::*;

pub mod nor;
pub use nor::*;

pub mod not;
pub use not::*;

pub mod or;
pub use or::*;

pub mod pow;
pub use pow::*;

pub mod pow_checked;
pub use pow_checked::*;

pub mod pow_wrapped;
pub use pow_wrapped::*;

pub mod shl_checked;
pub use shl_checked::*;

pub mod shl_wrapped;
pub use shl_wrapped::*;

pub mod shr_checked;
pub use shr_checked::*;

pub mod shr_wrapped;
pub use shr_wrapped::*;

pub mod square;
pub use square::*;

pub mod sub;
pub use sub::*;

pub mod sub_checked;
pub use sub_checked::*;

pub mod sub_wrapped;
pub use sub_wrapped::*;

pub mod ternary;
pub use ternary::*;

pub mod xor;
pub use xor::*;

use crate::{Memory, Operation, Sanitizer};
use snarkvm_circuits::ParserResult;
use snarkvm_utilities::{error, FromBytes, ToBytes};

use core::fmt;
use enum_index::EnumIndex;
use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::map,
    sequence::{pair, preceded},
};
use std::io::{Read, Result as IoResult, Write};

#[derive(EnumIndex)]
pub enum Instruction<M: Memory> {
    /// Computes the absolute value of `operand`, checks for overflow, and stores the result in `destination`.
    AbsChecked(AbsChecked<M>),
    /// Computes the absolute value of `operand`, wraps on overflow, and stores the result in `destination`.
    AbsWrapped(AbsWrapped<M>),
    /// Adds `first` with `second`, storing the result in `destination`.
    Add(Add<M>),
    /// Adds `first` with `second`, checks for overflow, and stores the result in `destination`.
    AddChecked(AddChecked<M>),
    /// Adds `first` with `second`, wrapping on overflow, and stores the result in `destination`.
    AddWrapped(AddWrapped<M>),
    /// Performs a bitwise AND operation on `first` and `second`, storing the result in `destination`.
    And(And<M>),
    /// Divides `first` with `second`, storing the result in `destination`.
    Div(Div<M>),
    /// Divides `first` with `second`, checks for overflow, and stores the result in `destination`.
    DivChecked(DivChecked<M>),
    /// Divides `first` with `second`, wrapping on overflow, and stores the result in `destination`.
    DivWrapped(DivWrapped<M>),
    /// Doubles `operand`, storing the result in `destination`.
    Double(Double<M>),
    /// Checks that `first` is equal to `second`, storing the result in `destination`.
    Equal(Equal<M>),
    /// Checks that `first` is greater than `second`, storing the result in `destination`.
    GreaterThan(GreaterThan<M>),
    /// Checks that `first` is greater than or equal to `second`, storing the result in `destination`.
    GreaterThanOrEqual(GreaterThanOrEqual<M>),
    /// Computes the multiplicative inverse of `operand`, storing the result in `destination`.
    Inv(Inv<M>),
    /// Checks that `first` is less than `second`, storing the result in `destination`.
    LessThan(LessThan<M>),
    /// Checks that `first` is less than or equal to `second`, storing the result in `destination`.
    LessThanOrEqual(LessThanOrEqual<M>),
    /// Multiplies `first` with `second`, storing the result in `destination`.
    Mul(Mul<M>),
    /// Multiplies `first` with `second`, checks for overflow, and stores the result in `destination`.
    MulChecked(MulChecked<M>),
    /// Multiplies `first` with `second`, wrapping on overflow, and stores the result in `destination`.
    MulWrapped(MulWrapped<M>),
    /// Performs a bitwise NAND operation on `first` and `second`, storing the result in `destination`.
    Nand(Nand<M>),
    /// Negates `operand`, storing the result in `destination`.
    Neg(Neg<M>),
    /// Performs a bitwise NOR operation on `first` and `second`, storing the result in `destination`.
    Nor(Nor<M>),
    /// Performs a bitwise NOT operation on `operand`, storing the result in `destination`.
    Not(Not<M>),
    /// Checks that `first` is not equal to `second`, storing the result in `destination`.
    NotEqual(NotEqual<M>),
    /// Performs a bitwise OR operation on `first` and `second`, storing the result in `destination`.
    Or(Or<M>),
    /// Exponentiates `first` by `second`, storing the result in `destination`.
    Pow(Pow<M>),
    /// Exponentiates `first` by `second`, checks for overflow, and stores the result in `destination`.
    PowChecked(PowChecked<M>),
    /// Exponentiates `first` by `second`, wrapping on overflow, and stores the result in `destination`.
    PowWrapped(PowWrapped<M>),
    /// Performs a bitwise left shift on `first` by `second`, checks that the value of `second` does
    /// not exceed the bit-width of `first`, and stores the result in `destination`.
    ShlChecked(ShlChecked<M>),
    /// Performs a bitwise left shift on `first` by `second`, truncating the value of `second` to the
    /// bit-width of `first`, and stores the result in `destination`.
    ShlWrapped(ShlWrapped<M>),
    /// Performs an arithmetic right shift on `first` by `second`, checks that the value of `second` does
    /// not exceed the bit-width of `first`, and stores the result in `destination`.
    ShrChecked(ShrChecked<M>),
    /// Performs an arithmetic right shift on `first` by `second`, truncating the value of `second` to the
    /// bit-width of `first`, and stores the result in `destination`.
    ShrWrapped(ShrWrapped<M>),
    /// Squares `operand`, storing the result in `destination`.
    Square(Square<M>),
    /// Subtracts `first` from `second`, storing the result in `destination`.
    Sub(Sub<M>),
    /// Subtracts `first` from `second`, checks for overflow, and stores the result in `destination`.
    SubChecked(SubChecked<M>),
    /// Subtracts `first` from `second`, wrapping on overflow, and stores the result in `destination`.
    SubWrapped(SubWrapped<M>),
    /// Selects `first`, if `condition` is true, otherwise selects `second`, storing the result in `destination`.
    Ternary(Ternary<M>),
    /// Performs a bitwise XOR operation on `first` and `second`, storing the result in `destination`.
    Xor(Xor<M>),
}

impl<M: Memory> Instruction<M> {
    /// Returns the opcode for the instruction
    #[inline]
    pub(crate) fn opcode(&self) -> u16 {
        self.enum_index() as u16
    }

    /// Returns the mnemonic for the instruction.
    #[inline]
    pub(crate) fn mnemonic(&self) -> &'static str {
        match self {
            Self::AbsChecked(..) => AbsChecked::<M>::mnemonic(),
            Self::AbsWrapped(..) => AbsWrapped::<M>::mnemonic(),
            Self::Add(..) => Add::<M>::mnemonic(),
            Self::AddChecked(..) => AddChecked::<M>::mnemonic(),
            Self::AddWrapped(..) => AddWrapped::<M>::mnemonic(),
            Self::And(..) => And::<M>::mnemonic(),
            Self::Div(..) => Div::<M>::mnemonic(),
            Self::DivChecked(..) => DivChecked::<M>::mnemonic(),
            Self::DivWrapped(..) => DivWrapped::<M>::mnemonic(),
            Self::Double(..) => Double::<M>::mnemonic(),
            Self::Equal(..) => Equal::<M>::mnemonic(),
            Self::GreaterThan(..) => GreaterThan::<M>::mnemonic(),
            Self::GreaterThanOrEqual(..) => GreaterThanOrEqual::<M>::mnemonic(),
            Self::Inv(..) => Inv::<M>::mnemonic(),
            Self::LessThan(..) => LessThan::<M>::mnemonic(),
            Self::LessThanOrEqual(..) => LessThanOrEqual::<M>::mnemonic(),
            Self::Mul(..) => Mul::<M>::mnemonic(),
            Self::MulChecked(..) => MulChecked::<M>::mnemonic(),
            Self::MulWrapped(..) => MulWrapped::<M>::mnemonic(),
            Self::Nand(..) => Nand::<M>::mnemonic(),
            Self::Neg(..) => Neg::<M>::mnemonic(),
            Self::Nor(..) => Nor::<M>::mnemonic(),
            Self::Not(..) => Not::<M>::mnemonic(),
            Self::NotEqual(..) => NotEqual::<M>::mnemonic(),
            Self::Or(..) => Or::<M>::mnemonic(),
            Self::Pow(..) => Pow::<M>::mnemonic(),
            Self::PowChecked(..) => PowChecked::<M>::mnemonic(),
            Self::PowWrapped(..) => PowWrapped::<M>::mnemonic(),
            Self::ShlChecked(..) => ShlChecked::<M>::mnemonic(),
            Self::ShlWrapped(..) => ShlWrapped::<M>::mnemonic(),
            Self::ShrChecked(..) => ShrChecked::<M>::mnemonic(),
            Self::ShrWrapped(..) => ShrWrapped::<M>::mnemonic(),
            Self::Square(..) => Square::<M>::mnemonic(),
            Self::Sub(..) => Sub::<M>::mnemonic(),
            Self::SubChecked(..) => SubChecked::<M>::mnemonic(),
            Self::SubWrapped(..) => SubWrapped::<M>::mnemonic(),
            Self::Ternary(..) => Ternary::<M>::mnemonic(),
            Self::Xor(..) => Xor::<M>::mnemonic(),
        }
    }

    /// Evaluates the instruction.
    #[inline]
    pub(crate) fn evaluate(&self, memory: &M) {
        match self {
            Self::AbsChecked(instruction) => instruction.evaluate(memory),
            Self::AbsWrapped(instruction) => instruction.evaluate(memory),
            Self::Add(instruction) => instruction.evaluate(memory),
            Self::AddChecked(instruction) => instruction.evaluate(memory),
            Self::AddWrapped(instruction) => instruction.evaluate(memory),
            Self::And(instruction) => instruction.evaluate(memory),
            Self::Div(instruction) => instruction.evaluate(memory),
            Self::DivChecked(instruction) => instruction.evaluate(memory),
            Self::DivWrapped(instruction) => instruction.evaluate(memory),
            Self::Double(instruction) => instruction.evaluate(memory),
            Self::Equal(instruction) => instruction.evaluate(memory),
            Self::GreaterThan(instruction) => instruction.evaluate(memory),
            Self::GreaterThanOrEqual(instruction) => instruction.evaluate(memory),
            Self::Inv(instruction) => instruction.evaluate(memory),
            Self::LessThan(instruction) => instruction.evaluate(memory),
            Self::LessThanOrEqual(instruction) => instruction.evaluate(memory),
            Self::Mul(instruction) => instruction.evaluate(memory),
            Self::MulChecked(instruction) => instruction.evaluate(memory),
            Self::MulWrapped(instruction) => instruction.evaluate(memory),
            Self::Nand(instruction) => instruction.evaluate(memory),
            Self::Neg(instruction) => instruction.evaluate(memory),
            Self::Nor(instruction) => instruction.evaluate(memory),
            Self::Not(instruction) => instruction.evaluate(memory),
            Self::NotEqual(instruction) => instruction.evaluate(memory),
            Self::Or(instruction) => instruction.evaluate(memory),
            Self::Pow(instruction) => instruction.evaluate(memory),
            Self::PowChecked(instruction) => instruction.evaluate(memory),
            Self::PowWrapped(instruction) => instruction.evaluate(memory),
            Self::ShlChecked(instruction) => instruction.evaluate(memory),
            Self::ShlWrapped(instruction) => instruction.evaluate(memory),
            Self::ShrChecked(instruction) => instruction.evaluate(memory),
            Self::ShrWrapped(instruction) => instruction.evaluate(memory),
            Self::Square(instruction) => instruction.evaluate(memory),
            Self::Sub(instruction) => instruction.evaluate(memory),
            Self::SubChecked(instruction) => instruction.evaluate(memory),
            Self::SubWrapped(instruction) => instruction.evaluate(memory),
            Self::Ternary(instruction) => instruction.evaluate(memory),
            Self::Xor(instruction) => instruction.evaluate(memory),
        }
    }

    /// Parses a string into an instruction.
    #[inline]
    pub(crate) fn parse(string: &str, memory: M) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the instruction from the string.
        let (string, instruction) = alt((
            // Note that order of the individual parsers matters.
            preceded(pair(tag(Add::<M>::mnemonic()), tag(" ")), map(|s| Add::parse(s, memory.clone()), Into::into)),
            preceded(pair(tag(Sub::<M>::mnemonic()), tag(" ")), map(|s| Sub::parse(s, memory.clone()), Into::into)),
        ))(string)?;

        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, instruction))
    }
}

impl<M: Memory> fmt::Display for Instruction<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::AbsChecked(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::AbsWrapped(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Add(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::AddChecked(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::AddWrapped(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::And(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Div(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::DivChecked(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::DivWrapped(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Double(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Equal(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::GreaterThan(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::GreaterThanOrEqual(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Inv(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::LessThan(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::LessThanOrEqual(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Mul(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::MulChecked(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::MulWrapped(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Nand(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Neg(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Nor(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Not(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::NotEqual(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Or(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Pow(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::PowChecked(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::PowWrapped(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::ShlChecked(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::ShlWrapped(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::ShrChecked(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::ShrWrapped(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Square(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Sub(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::SubChecked(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::SubWrapped(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Ternary(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
            Self::Xor(instruction) => write!(f, "{} {};", self.mnemonic(), instruction),
        }
    }
}

// TODO (@pranav) Hard coding constants is not maintainable.
impl<M: Memory> FromBytes for Instruction<M> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        match u16::read_le(&mut reader) {
            Ok(0) => Ok(Self::Add(Add::read_le(&mut reader)?)),
            Ok(1) => Ok(Self::Div(Div::read_le(&mut reader)?)),
            Ok(2) => Ok(Self::Double(Double::read_le(&mut reader)?)),
            Ok(3) => Ok(Self::Equal(Equal::read_le(&mut reader)?)),
            Ok(4) => Ok(Self::GreaterThan(GreaterThan::read_le(&mut reader)?)),
            Ok(5) => Ok(Self::GreaterThanOrEqual(GreaterThanOrEqual::read_le(&mut reader)?)),
            Ok(6) => Ok(Self::Inv(Inv::read_le(&mut reader)?)),
            Ok(7) => Ok(Self::LessThan(LessThan::read_le(&mut reader)?)),
            Ok(8) => Ok(Self::LessThanOrEqual(LessThanOrEqual::read_le(&mut reader)?)),
            Ok(9) => Ok(Self::Mul(Mul::read_le(&mut reader)?)),
            Ok(10) => Ok(Self::Neg(Neg::read_le(&mut reader)?)),
            Ok(11) => Ok(Self::NotEqual(NotEqual::read_le(&mut reader)?)),
            Ok(12) => Ok(Self::Pow(Pow::read_le(&mut reader)?)),
            Ok(13) => Ok(Self::Square(Square::read_le(&mut reader)?)),
            Ok(14) => Ok(Self::Sub(Sub::read_le(&mut reader)?)),
            Ok(15) => Ok(Self::Ternary(Ternary::read_le(&mut reader)?)),
            Ok(code) => Err(error(format!("FromBytes failed to parse an instruction of code {code}"))),
            Err(err) => Err(err),
        }
    }
}

impl<M: Memory> ToBytes for Instruction<M> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.opcode().write_le(&mut writer)?;
        match self {
            Self::AbsChecked(instruction) => instruction.write_le(&mut writer),
            Self::AbsWrapped(instruction) => instruction.write_le(&mut writer),
            Self::Add(instruction) => instruction.write_le(&mut writer),
            Self::AddChecked(instruction) => instruction.write_le(&mut writer),
            Self::AddWrapped(instruction) => instruction.write_le(&mut writer),
            Self::And(instruction) => instruction.write_le(&mut writer),
            Self::Div(instruction) => instruction.write_le(&mut writer),
            Self::DivChecked(instruction) => instruction.write_le(&mut writer),
            Self::DivWrapped(instruction) => instruction.write_le(&mut writer),
            Self::Double(instruction) => instruction.write_le(&mut writer),
            Self::Equal(instruction) => instruction.write_le(&mut writer),
            Self::GreaterThan(instruction) => instruction.write_le(&mut writer),
            Self::GreaterThanOrEqual(instruction) => instruction.write_le(&mut writer),
            Self::Inv(instruction) => instruction.write_le(&mut writer),
            Self::LessThan(instruction) => instruction.write_le(&mut writer),
            Self::LessThanOrEqual(instruction) => instruction.write_le(&mut writer),
            Self::Mul(instruction) => instruction.write_le(&mut writer),
            Self::MulChecked(instruction) => instruction.write_le(&mut writer),
            Self::MulWrapped(instruction) => instruction.write_le(&mut writer),
            Self::Nand(instruction) => instruction.write_le(&mut writer),
            Self::Neg(instruction) => instruction.write_le(&mut writer),
            Self::Nor(instruction) => instruction.write_le(&mut writer),
            Self::Not(instruction) => instruction.write_le(&mut writer),
            Self::NotEqual(instruction) => instruction.write_le(&mut writer),
            Self::Or(instruction) => instruction.write_le(&mut writer),
            Self::Pow(instruction) => instruction.write_le(&mut writer),
            Self::PowChecked(instruction) => instruction.write_le(&mut writer),
            Self::PowWrapped(instruction) => instruction.write_le(&mut writer),
            Self::ShlChecked(instruction) => instruction.write_le(&mut writer),
            Self::ShlWrapped(instruction) => instruction.write_le(&mut writer),
            Self::ShrChecked(instruction) => instruction.write_le(&mut writer),
            Self::ShrWrapped(instruction) => instruction.write_le(&mut writer),
            Self::Square(instruction) => instruction.write_le(&mut writer),
            Self::Sub(instruction) => instruction.write_le(&mut writer),
            Self::SubChecked(instruction) => instruction.write_le(&mut writer),
            Self::SubWrapped(instruction) => instruction.write_le(&mut writer),
            Self::Ternary(instruction) => instruction.write_le(&mut writer),
            Self::Xor(instruction) => instruction.write_le(&mut writer),
        }
    }
}
