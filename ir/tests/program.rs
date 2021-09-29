// Copyright (C) 2019-2021 Aleo Systems Inc.
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
use leo_compiler::compiler::{thread_leaked_context, Compiler};
use leo_package::inputs::*;
use leo_parser::parse_program_input;
use std::{env::current_dir, path::PathBuf};

#[test]
fn test_compile_program_to_ir() {
    let package_name = "hello-world".to_string();
    let mut path = current_dir().unwrap();
    path.push("tests");
    path.push("hello-world");

    let mut output_directory = package_path.clone();
    output_directory.push("outputs");

    let mut main_file_path = path.clone();
    main_file_path.push("src");
    main_file_path.push("main.leo");

    // Load the input file at `hello-world/inputs/hello-world.in`
    let (input_string, input_path) = InputFile::new(&package_name).read_from(&path).unwrap();

    // Load the state file at `hello-world/inputs/hello-world.state`
    let (state_string, state_path) = StateFile::new(&package_name).read_from(&path).unwrap();

    // parse the program inputs
    let input = parse_program_input(
        &input_string,
        &input_path.to_str().unwrap(),
        &state_string,
        &state_path.to_str().unwrap(),
    )
    .unwrap();

    // Load the program at `hello-world/src/main.leo`
    let program = Compiler::parse_program_without_input(
        package_name.clone(),
        main_file_path,
        output_directory,
        thread_leaked_context(),
        None,
        Default::default(),
        None,
    )
    .unwrap();

    // Compile the program to the ir
    let ir = program.compile_ir(&input).unwrap();

    println!("{}", ir);
}
