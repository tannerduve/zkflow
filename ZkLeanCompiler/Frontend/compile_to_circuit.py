#!/usr/bin/env python3
"""
compile_to_circuit.py   —   End‑to‑end demo

.zk source  ──►  Parsed.lean  ──►  CompileZkProgram.lean  ──►  lake build
                               ▼
                          out.json  (constraints as JSON)
"""
import subprocess, sys, json
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]   # project root

def run_parser(zk_file: str):
    if subprocess.call(
        ["python3", "ZkLeanCompiler/Frontend/zkparse.py", zk_file],
        cwd=REPO_ROOT
    ):
        print("Parsing failed"); sys.exit(1)

def write_driver(stem: str):
    dst = (
        Path(__file__).resolve()           # …/Frontend/compile_to_circuit.py
        .parent                           # …/Frontend
        / "CompileZkProgram.lean"
    )
    dst.parent.mkdir(parents=True, exist_ok=True)

    driver = f"""
import ZkLeanCompiler.Lean.Compile
import ZkLeanCompiler.Frontend.Parsed
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Defs
import Lean.Data.Json.Basic

open Term

def program : Term ℚ := parsedProg_{stem}

/-- convert compiled `ZKExpr` into a small Json tree -/
def toJson : ZKExpr ℚ → Lean.Json
  | .Literal n     => Lean.Json.mkObj [("type", .str "lit"),     ("val", .str (toString n))]
  | .WitnessVar w  => Lean.Json.mkObj [("type", .str "witness"), ("id",  .num w       )]
  | .Add a b       => Lean.Json.mkObj [("type", .str "add"),     ("a",   toJson a), ("b", toJson b)]
  | .Sub a b       => Lean.Json.mkObj [("type", .str "sub"),     ("a",   toJson a), ("b", toJson b)]
  | .Neg a         => Lean.Json.mkObj [("type", .str "neg"),     ("a",   toJson a)]
  | .Mul a b       => Lean.Json.mkObj [("type", .str "mul"),     ("a",   toJson a), ("b", toJson b)]
  | .Eq a b        => Lean.Json.mkObj [("type", .str "eq"),      ("a",   toJson a), ("b", toJson b)]
  | .Lookup _ _ _  => Lean.Json.mkObj [("type", .str "lookup")]

def main : IO Unit := do
  let env : Env ℚ := {{ lookup := fun _ => none }}
  let (expr, st) := runFold (compileExpr program env) initialZKBuilderState
  let constraints : Array Lean.Json := (st.constraints.map toJson).toArray
  let out := Lean.Json.mkObj
              [ ("expr",        toJson expr)
              , ("constraints", Lean.Json.arr constraints),
               ("num_witness", Lean.Json.num st.allocated_witness_count) ]
  IO.FS.writeFile "ZkLeanCompiler/Frontend/out.json" (Lean.Json.compress out)
  IO.println (Lean.Json.compress out)
  IO.println "ZK circuit JSON written to ZkLeanCompiler/Frontend/out.json"
"""
    dst.write_text(driver)

# --------------------------------------------------------------------
# 3.  Build the driver
# --------------------------------------------------------------------
def lake_build():
    if subprocess.call(
        ["lake", "build", "ZkLeanCompiler.Frontend.CompileZkProgram"],
        cwd=REPO_ROOT
    ):
        print("Lean build failed"); sys.exit(1)

def lake_run():
    if subprocess.call(
        ["lake", "exe", "ZkLeanCompiler.Frontend.CompileZkProgram"],
        cwd=REPO_ROOT
    ):
        print("Execution failed"); sys.exit(1)

def add_input_metadata(json_path: Path):
    with json_path.open("r") as f:
        circuit = json.loads(f.read())

    num = circuit.get("num_witness", 0)
    circuit["public_inputs"] = []
    circuit["secret_inputs"] = list(range(num))

    circuit.pop("num_witness", None)  # optional: clean up

    with json_path.open("w") as f:
        f.write(json.dumps(circuit, separators=(",", ":")))

# --------------------------------------------------------------------
# 4.  CLI wrapper
# --------------------------------------------------------------------
def main():
    if len(sys.argv) != 2:
        print("Usage: compile_to_circuit.py  path/to/file.zk")
        sys.exit(1)

    zk_file = Path(sys.argv[1]).resolve()
    if not zk_file.exists():
        print("No such .zk file"); sys.exit(1)

    stem = zk_file.stem  # foo.zk → “foo”

    run_parser(str(zk_file))
    write_driver(stem)
    lake_build()
    lake_run()  # <-- this runs the program, generating out.json

    out = REPO_ROOT / "ZkLeanCompiler/Frontend/out.json"
    if out.exists():
        add_input_metadata(out)
        print("\n✅  Circuit JSON\n"); print(out.read_text())
    else:
        print("❌  out.json not written")

if __name__ == "__main__":
    main()
