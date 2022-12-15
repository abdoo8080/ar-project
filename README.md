# LMT
This repository contains the source code for `CS 257: Automated Reasoning` course project.

## Build and Test Instructions
A Lean installation is required to build and test the code in this project. Follow these instruction to install the Lean toolchain in Unix:
1. Run `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh` to install elan, Lean's version manager.
2. Run `elan install leanprover/lean4:nightly-2022-11-16` to install the Lean toolchain used by this project.
3. Run `lake build LMT:shared generator translator` to build the project's libraries and executables.
4. Run `lake run test` to test the `arr` tactic on some benchmarks.

## Overview
This project is composed of the following components:

- `LMT`: the main component containing the decision procedure for EUF and Arrays. It contains 4 files:
  - `A.lean`: contains the specification for the theory of Arrays, theorems proving the calculus rules of the theory of Arrays, and a proof of the in-class example using the rules.
  - `Base.lean`: contains some useful utilities for `EUF.lean` and `Arr.lean`
  - `EUF.lean`: contains the `euf` tactic which runs the congruence closure decision procedure for EUF.
  - `Arr.lean`: contains the `arr` tactic which runs the decision procedure for the Theory of Arrays.
- `Example.lean`: contains an example use of the `arr` tactic to prove the unsatisfiability of the in-class example.
- `Sexp`: this component contains modules for parsing and printing S-exprs (copied from [`lean-smt`](https://github.com/ufmg-smite/lean-smt)). It contains 2 files:
  - `Data.lean`: contains the data-structure, printer, and parser for S-expr.
  - `Dsl.lean`: contains a Domain Specific Language (DSL) embedding of S-exprs in Lean for convenience.
- `arr-grammar.sy`: a SyGuS grammar used to synthesize `unsat` Array benchmarks. Refer to the file for instructions on how to use it.
- `Generator.lean`: the source code for the `generator` executable. It generates SMT-LIB benchmarks from a file containing solutions to `arr-grammar.sy` and saves them in `Test/SMT`. To run the generator, execute the command `lake exe generator <path to file containing solutions>`.
- `Translator.lean`: the source code for the `translator` executable. It takes an SMT-LIB ArraysEx query and translates it into a Lean example. To run the translator, execute the command `lake exe translator <path to SMT-LIB file>`. Run `lake run translate` to translate all the benchmarks in `Test/SMT` and save them in `Test/Lean`.
- `Test`: directory containing the Lean and SMT-LIB benchmarks. To test the performance of `arr` tactic on the Lean benchmarks, run `lake run test`.
