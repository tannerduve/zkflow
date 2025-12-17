# zkFlow

`zkFlow` is a proof-of-concept verified compiler that takes a tiny expression language and produces a complete zero-knowledge circuit

What you can do

*   **Write programs** using arithmetic, booleans, `ifz`, `let`, `assert`, sequencing, and lookup-table access.
*   **Compile** them to an R1CS-like constraint system (`ZKExpr` + list of equalities).
*   **Formally reason** about the compiler in Lean (correctness statements are sketched in `CompileCorrect.lean`).

. Demo (parse → compile → pretty-print)

```bash
lake build
lake exe zkflow_demo examples/01_nested_let.zk
```

.  Visualising a circuit

```bash
python3 ZkLeanCompiler/Frontend/visualize_graph.py
```
Produces `circuit_graph.png` with witnesses (blue), operations (yellow), constraints (orange), output (green).
