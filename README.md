# zkFlow

**zkFlow** is a small language for writing simple programs that automatically compile into zero-knowledge proof circuits.  
It enables users to express basic arithmetic, boolean logic, and control-flow computations over a finite field, and automatically generate the corresponding arithmetized circuits needed for proof systems such as zk-SNARKs or zk-STARKs.  
The target language is the zkLean DSL ([link](https://github.com/GaloisInc/zk-lean)) developed by Galois for specifying ZK statements.

The compiler is written in Lean and several properties have been formally verified. The proof of the full correctness claim of the compiler is in progress.

---

## Project Goals

- **Write small programs** using high-level constructs (arithmetic, booleans, if-then-else, etc.).
- **Compile automatically** into low-level constraint systems suitable for ZK proof backends.
- **Formally prove** that the compiler preserves semantics: the meaning of a program matches the meaning of the generated constraint system.
- **Generate visualized circuits** produced by the compiler
---

## Language Overview

The source language (called `Term`) includes:

- Field arithmetic: addition, multiplication, subtraction
- Boolean logic: and, or, not
- Equality checking
- Conditionals (`ifz` — if-then-else)
- Set membership tests (`inSet`)
- Let-bindings (`let x = t1 in t2`)
- Assertions (`assert t1 then t1`)
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

### Core Project Files (Lean):

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

### Frontend and Visualization Tools (Python):

- **`zkparse.py`**  
  Parses `.zk` programs into fully desugared `Term` syntax and writes out a Lean file `Parsed.lean` that defines the program.

- **`compile_to_circuit.py`**  
  Runs the full pipeline: parses a `.zk` file, invokes Lean to compile it, and emits `out.json` representing the resulting ZK circuit.

- **`visualize_graph.py`**  
  Visualizes the compiled ZK circuit stored in `out.json` as a directed graph, saved as `circuit_graph.png`.

---

### Files Imported from zkLean:

- **`AST.lean`**  
  Defines the `ZKExpr` datatype: a low-level language of field expressions used to represent circuits.

- **`Basic.lean`**  
  Provides basic operations over fields and field elements, including coercions, equality, and small helper structures.

- **`Builder.lean`**  
  Defines the `ZKBuilder` monad and state — a constraint generation monad that tracks allocated witnesses and emitted constraints.

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
These include:

- Distribution of constraint satisfaction over list append
- Soundness of boolean assertions
- Correctness of arithmetic and logical compilation
- Witness consistency during compilation
- Kleisli homomorphism theorem viewing languages as term algebras
- Constraint semantics are invariant under permutation of constraints
- Suffix irrelevance of witness vectors: evaluating a compiled expression does not depend on entries beyond its referenced witness indices.

**Progress**:  
The proof is complete for base cases (variables, literals, booleans) and partially complete for arithmetic/logical ops.  
Control-flow cases like `ifz`, `inSet`, and sequencing are pending.

---

## Circuit Visualization Pipeline

zkFlow supports automatic visualization of compiled ZK circuits.

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

4. The rendered image is saved as `circuit_graph.png`.

### Output Description

- Light blue circles = witnesses (`w0`, `w1`, ...)
- Yellow rectangles = operations (`add`, `mul`, `eq`, ...)
- Green octagon = final output
- Orange diamonds = constraints (equalities)

### Pipeline Summary

`.zk` program → `Parsed.lean` → `out.json` → `circuit_graph.png`

---

## Future Work

- Add cryptographic primitives: hashing, commitments, etc.
- Extend language with tuples, maps, and Merkle tree access.
- Support simple loops and bounded iteration.
- Integrate with zk backends (e.g., Halo2, Nova) for full proof generation.
