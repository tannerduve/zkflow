# zk-compiler: Lambda to Constraint Compiler in Lean

This project implements a compiler from a simple lambda calculus over a field `f` into a constraint DSL suitable for zero-knowledge proofs. It is written entirely in Lean 4.

## Overview

- **Source Language**: An untyped lambda calculus with literals, booleans, arithmetic, equality, conditionals, and hashing.
- **Intermediate Representation (IR)**: A closure-free, first-order expression language with arithmetic and conditional constructs.
- **Target Language**: A constraint DSL (`ZKExpr f`) representing R1CS-style arithmetic circuits.
- **Compilation Strategy**: Structured as a staged pipeline, producing constraints and witness assignments via a `ZKBuilder` monad.

## Code Structure

The project consists of both original components and vendored components from the [Zk-Lean](https://github.com/GaloisInc/zk-lean) project by Galois.

**Original code (this project):**
- `LCSyntax.lean`: Lambda calculus syntax
- `LCSemantics.lean`: Big-step semantics for source terms
- `IRExpr.lean`: Closure-free IR and normalization logic
- `Compile.lean`: End-to-end pipeline from lambda terms to constraints

**Vendored from [Zk-Lean](https://github.com/GaloisInc/zk-lean):**
- `AST.lean`: Defines the `ZKExpr` DSL for ZK constraint terms
- `Builder.lean`: A monadic API for witness allocation and constraint accumulation
- `Semantics.lean`: Interpreter for evaluating `ZKExpr` against a witness list

These files were copied directly from Zk-Lean and not modified substantially. Long-term, switching to Zk-Lean as a proper dependency is recommended.

## Compilation Pipeline


## Hashing Support

- Hashing is currently treated as a primitive.
- A dummy hash function (e.g., `x ↦ x^3 + 42`) is used for simulation and testing.
- In the future, this will be replaced with real cryptographic hash gadgets such as Poseidon, integrated via backend constraint systems.

## Formal Verification Goals

The goal is to formally verify the compiler in Lean by proving:

> If a `Term f` evaluates to a value `v`, then the compiled circuit will evaluate to `v` on a valid witness.

This involves proving semantic preservation through the normalization and compilation pipeline.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)

## Currently:
Writing proof of correctness (semantic preservation) of compilation

## Future Plans

- Backend integration (e.g., export constraints to R1CS or Halo2-compatible formats)
- Real cryptographic hash support
- Witness and constraint serialization for external proving systems
