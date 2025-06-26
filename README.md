# zkFlow

`zkFlow` is a proof-of-concept **Lean-verified compiler** that takes a tiny expression language and produces a complete zero-knowledge circuit that can be proven with the new [sTwo](https://github.com/starkware-libs/stwo) backend.

```
  Term program (.zk) ──► Lean compiler ──► JSON (constraints + witness slots)
                                            │
                                            └─► Rust driver ──► sTwo prover → proof
```

---
## 1.  What you can do

*   **Write programs** using arithmetic, booleans, `ifz`, `let`, `assert`, sequencing, and lookup-table access.
*   **Compile** them to an R1CS-like constraint system (`ZKExpr` + list of equalities).
*   **Formally reason** about the compiler in Lean (correctness statements are sketched in `CompileCorrect.lean`).
*   **Generate proofs** end-to-end with sTwo: Lean emits `out.json`, a small Rust tool turns that into a `Component`, then calls `stwo_prover::prove`.

---
## 2.  Directory map (high-level)

```
ZkLeanCompiler
 ├─ Lean/               — compiler, ASTs, semantics, proofs
 ├─ Frontend/           — Python scripts (.zk parser, viz, driver generator)
 ├─ rust/               — `zkprover` binary that feeds JSON to sTwo
 └─ Demo.lean           — interactive examples in Lean
```

---
## 3.  End-to-end workflow

### 3.1  From `.zk` to circuit JSON

```bash
python3 ZkLeanCompiler/Frontend/compile_to_circuit.py  path/to/file.zk
```
This script
1.  Parses the `.zk` file → `Parsed.lean`
2.  Generates a small Lean driver (`CompileZkProgram.lean`)
3.  Runs `lake build` which
    * invokes `compileExpr` → `runFold` (Lean)
    * writes `out.json` `{ expr, constraints, num_witness }`
4.  Adds stub `public_inputs` / `secret_inputs` arrays so that the Rust side can fill them.

### 3.2  Proof with sTwo

```bash
cargo run -p zkprover
```
The binary:
* deserialises `out.json`
* converts each JSON constraint to a `constraint_framework::Expr`
* builds a `Component`
* constructs
  ```rust
  let inputs = ProofInputs {
      component: &component,
      public_inputs: circuit.public_inputs.clone(),
      secret_inputs: circuit.secret_inputs.clone(), // <-- still dummy 0,1,2 …
  };
  ```
* calls `stwo_prover::prove` and prints the proof length.

(Real witness values will be injected later by a dedicated witness generator – see "Future work.")

## 4.  Building the project

```bash
# clone
git clone https://github.com/tannerduve/zkflow.git && cd zkflow

# Lean side
lake exe cache get   # pull mathlib & deps
lake build           # build everything

# Python helpers
pip install -r requirements.txt   # graphviz, etc.

# Rust prover (needs nightly or 1.71+)
cargo build -p zkprover
```
---
## 5.  Visualising a circuit

```bash
python3 ZkLeanCompiler/Frontend/visualize_graph.py
```
Produces `circuit_graph.png` with witnesses (blue), operations (yellow), constraints (orange), output (green).

