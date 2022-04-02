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

// #[cfg(test)]
// use snarkvm_circuits_types::environment::assert_scope;

use crate::{
    program::{Literal, Value},
    Aleo,
};
use snarkvm_circuits_types::{environment::prelude::*, Address, I64};

// TODO (howardwu): Check mode is only public/private, not constant.
#[derive(Debug, Clone)]
pub struct Record<A: Aleo> {
    owner: Address<A>,
    value: I64<A>,
    data: Vec<Value<A>>,
    // program_id: Vec<Boolean<P>>>,
    // randomizer: BaseField<P>>,
    // record_view_key: BaseField<P>>,
}

impl<A: Aleo> Record<A> {
    /// Returns the members of the record.
    pub fn members(&self) -> Vec<Value<A>> {
        [Value::Literal(Literal::Address(self.owner.clone())), Value::Literal(Literal::I64(self.value.clone()))]
            .into_iter()
            .chain(self.data.iter().cloned())
            .collect::<Vec<_>>()
    }

    /// Returns the record owner.
    pub fn owner(&self) -> &Address<A> {
        &self.owner
    }

    /// Returns the record value.
    pub fn value(&self) -> &I64<A> {
        &self.value
    }

    /// Returns the record data.
    pub fn data(&self) -> &Vec<Value<A>> {
        &self.data
    }
}

impl<A: Aleo> TypeName for Record<A> {
    fn type_name() -> &'static str {
        "record"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Devnet as Circuit;
    use snarkvm_circuits_types::Group;

    #[test]
    fn test_record() {
        let first = Value::Literal(Literal::<Circuit>::from_str("10field.public"));
        let second = Value::Literal(Literal::from_str("true.private"));
        let third = Value::Literal(Literal::from_str("99i64.public"));

        let _candidate = Record::<Circuit> {
            owner: Address::from(Group::from_str("2group.private")),
            value: I64::from_str("1i64.private"),
            data: vec![first, second, third],
        };
    }
}
