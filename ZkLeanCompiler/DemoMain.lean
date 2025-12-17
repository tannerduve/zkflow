import «ZkLeanCompiler».Lean.Compile
import «ZkLeanCompiler».Lean.Parse
import «ZkLeanCompiler».Lean.Pretty

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import ZKLean.Builder
import ZKLean.Semantics

open ZkLeanCompiler.Lean

namespace ZkLeanCompiler

instance : Fact (Nat.Prime 7) := by decide

instance : ZKField (ZMod 7) where
  hash x := (inferInstance : Hashable Nat).hash x.val
  field_to_bits {num_bits} x :=
    Vector.ofFn (fun i : Fin num_bits =>
      if Nat.testBit x.val i.val then (1 : ZMod 7) else 0)
  field_to_nat x := x.val

abbrev F := ZMod 7

def emptyEnv : Env F :=
  { lookup := fun _ => none }

def initialZKBuilderState (f : Type) : ZKBuilderState f :=
  { allocated_witness_count := 0, constraints := [], ram_sizes := #[], ram_ops := #[] }

structure CliOptions where
  file : String
  showAst : Bool := true
  showCircuit : Bool := true
deriving Inhabited

def usage : String :=
  "usage: lake exe zkflow_demo <file.zk> [--ast|--circuit]\n" ++
  "  --ast     print only the parsed AST\n" ++
  "  --circuit print only the compiled circuit\n"

def parseArgs (args : List String) : Except String CliOptions := do
  let some file := args[0]?
    | throw usage
  let flags := args.drop 1
  if flags.contains "--help" || flags.contains "-h" then
    throw usage
  let onlyAst := flags.contains "--ast"
  let onlyCircuit := flags.contains "--circuit"
  let showAst := if onlyCircuit && !onlyAst then false else true
  let showCircuit := if onlyAst && !onlyCircuit then false else true
  let unknown := flags.filter (fun f => f != "--ast" && f != "--circuit")
  if unknown != [] then
    throw s!"unknown flags: {String.intercalate " " unknown}\n{usage}"
  return { file, showAst, showCircuit }

def die (msg : String) : IO Unit :=
  throw (IO.userError msg)

def run (opts : CliOptions) : IO Unit := do
  let input ← IO.FS.readFile opts.file
  match Parse.ZkParser.parseString (f := F) input with
  | .error e =>
      die s!"parse error: {e}"
  | .ok t =>
      if opts.showAst then
        IO.println "AST:"
        IO.println (Pretty.Term.pretty t)
      if opts.showCircuit then
        let (out, st) := runFold (compileExpr (f := F) t emptyEnv) (initialZKBuilderState F)
        IO.println "\nCircuit:"
        IO.println (Pretty.Circuit.pretty out st)

end ZkLeanCompiler

open ZkLeanCompiler

def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .ok opts => run opts
  | .error e => die e
