# zkFlow

**zkFlow** is a small language for writing simple programs that automatically compile into zero-knowledge proof circuits.  
It enables users to express basic arithmetic, boolean logic, and control-flow computations over a finite field, and automatically generate the corresponding arithmetized circuits needed for proof systems such as zk-SNARKs or zk-STARKs.  
The target language is the zkLean DSL ([link](https://github.com/GaloisInc/zk-lean)) developed by Galois for specifying ZK statements.

The compiler is written and (partially — in progress) formally verified in Lean.

---

## Project Goals

- **Write small programs** using high-level constructs (arithmetic, booleans, if-then-else, etc.).
- **Compile automatically** into low-level constraint systems suitable for ZK proof backends.
- **Formally prove** that the compiler preserves semantics: the meaning of a program matches the meaning of the generated constraint system.

---

## Language Overview

The source language (called `Term`) includes:

- Field arithmetic: addition, multiplication, subtraction
- Boolean logic: and, or, not
- Equality checking
- Conditionals (`ifz` — if-then-else)
- Set membership tests (`inSet`)
- Let-bindings (`let x = t1 in t2`)
- Assertions (`assert t`)
- Sequencing of programs (`t1 ; t2`)

There are no functions or recursion — the language is deliberately small, static, and designed for easy compilation into circuit constraints.

---

## How Compilation Works

Each source program is compiled into:

- A **constraint system**: a list of polynomial equalities over the field.
- A **compiled expression** (`ZKExpr`) representing the program’s output.
- A **witness**: an assignment of field elements satisfying the constraints.

The compiler internally allocates **witness variables** as needed, enforces constraints through simple rewriting, and preserves the structure of computation.

The resulting constraint system can be passed directly into a ZK backend to generate proofs.

---

## File Overview

### Files Original to This Project:

- **`LCSyntax.lean`**  
  Defines the syntax of the source language (`Term`), the structure of environments, free variable computation, and the definition of values.

- **`LCSemantics.lean`**  
  Defines the big-step operational semantics (`Eval`) for executing programs in the source language.

- **`Compile.lean`**  
  Defines the main compiler (`compileExpr`) which translates `Term` programs into constraint systems (`ZKExpr` expressions and lists of constraints).

- **`Correctness.lean`**  
  Contains supporting lemmas and the main theorem (`compileExpr_correct`) showing that the compiler preserves the semantics of the source programs.

- **`Demo.lean`**  
  Provides a pretty-printer for `Term` and `ZKExpr`, and a demo runner that compiles a program and checks whether a provided witness satisfies the generated constraints.

---

### Files Imported from zkLean:

- **`AST.lean`**  
  Defines the `ZKExpr` datatype: a low-level language of field expressions used to represent circuits. Includes literals, arithmetic operations, equality checks, and lookup gadgets.

- **`Basic.lean`**  
  Provides basic operations over fields and field elements, including coercions, equality, and small helper structures.

- **`Builder.lean`**  
  Defines the `ZKBuilder` monad and state — a constraint generation monad that tracks allocated witnesses and emitted constraints during compilation.

- **`LookupTable.lean`**  
  Defines structures for composed lookup tables, subtables, and their evaluation semantics. Supports complex lookup operations needed for efficient circuit design.

- **`Semantics.lean`**  
  Defines the evaluation semantics (`semantics_zkexpr`) of `ZKExpr` expressions under a witness assignment, and the satisfaction semantics (`constraints_semantics`) for lists of constraints.

---

## Formal Verification

The key correctness theorem (`compileExpr_correct`) states:

> If a program `t` evaluates to value `v` under the source semantics,  
> then its compiled constraint system has a satisfying witness,  
> and the compiled expression evaluates to the same value `v` under that witness.

Along the way, several technical lemmas about constraint semantics, witness structure, and boolean handling have been proven.  
These include properties like:

- Distribution of constraint satisfaction over lists
- Soundness of boolean assertions
- Correctness of basic arithmetic and logical compilation
- Witness consistency during compilation steps
- (Kleisli) homomorphism theorem where languages are viewed as term algebras

**Progress**:  
The proof is complete for basic cases (variables, literals, booleans) and partial for arithmetic and logical operations.  
A few hundred lines of proof are complete. The remaining control-flow cases (`ifz`, `inSet`, sequencing) are straightforward extensions.

---

## Circuit Visualization Pipeline

zkFlow supports automatic visualization of compiled ZK circuits as directed graphs.

### How to Use

1. Write a `.zk` program, e.g.:

    ```zk
    let x = 2 + 3 in
    assert(x * 2 == 10)
    ```

2. Compile and generate constraints:

    ```bash
    python3 ZkLeanCompiler/Frontend/compile_to_circuit.py ZkLeanCompiler/Frontend/examples/test.zk
    ```

3. Visualize the circuit:

    ```bash
    python3 ZkLeanCompiler/Frontend/visualize_graph.py
    ```

4. The rendered circuit will be saved as `circuit_graph.png`.

### Output Description

- Witnesses are shown as light blue nodes (`w0`, `w1`, etc).
- Arithmetic and logical operations are yellow boxes (`add`, `mul`, `eq`, etc).
- Final output is a green octagon labeled `output`.
- Each constraint is visualized via orange diamonds representing equality.

### Pipeline Summary

`.zk` program → `Parsed.lean` → `out.json` → `circuit_graph.png`


## Future Work

- Add hashing as a language primitive for supporting more advanced cryptographic protocols.
- Add tuple types, map types, or Merkle tree operations for more expressive ZK computations.
- Extend to simple bounded loops for larger programs.
- Connect the output constraint system to real ZK proof backends (e.g., Halo2, Nova) for actual proof generation.
