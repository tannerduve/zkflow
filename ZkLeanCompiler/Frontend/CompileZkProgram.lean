import ZkLeanCompiler.Lean.Compile
import ZkLeanCompiler.Frontend.Parsed
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Defs
import Lean.Data.Json.Basic

open Term

def program : Term ℚ := parsedProg_test

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
  let env : Env ℚ := { lookup := fun _ => none }
  let (expr, st) := runFold (compileExpr program env) initialZKBuilderState
  let constraints : Array Lean.Json := (st.constraints.map toJson).toArray
  let out := Lean.Json.mkObj
              [ ("expr",        toJson expr)
              , ("constraints", Lean.Json.arr constraints),
               ("num_witness", Lean.Json.num st.allocated_witness_count) ]
  IO.FS.writeFile "ZkLeanCompiler/Frontend/out.json" (Lean.Json.compress out)
  IO.println (Lean.Json.compress out)
  IO.println "ZK circuit JSON written to ZkLeanCompiler/Frontend/out.json"
