import «ZkLeanCompiler».Lean.AST
import ZKLean.AST
import ZKLean.Builder

namespace ZkLeanCompiler.Lean.Pretty

open ZKBuilder

/-- Wrap `s` in parentheses iff `b` is true. -/
def parensIf (b : Bool) (s : String) : String :=
  if b then "(" ++ s ++ ")" else s

namespace Term

/--
Operator precedence used by `Term.pretty`.

Higher numbers bind tighter; parentheses are inserted when printing a subterm with lower precedence
than the surrounding context.
-/
def prec {f} : Term f → Nat
  | .seq _ _ => 10
  | .lett .. | .assert .. | .ifz .. | .inSet .. => 20
  | .boolB .or .. => 30
  | .boolB .and .. => 35
  | .eq .. => 40
  | .arith .add .. | .arith .sub .. => 50
  | .arith .mul .. => 60
  | .not _ => 70
  | .var _ | .lit _ | .bool _ => 100

/--
Pretty-print a source-language `Term`.

Notes:
- literals are printed via `ZKField.field_to_nat` (so the output is field-dependent),
- parentheses are inserted to preserve parsing precedence,
- this is intended for debugging/demo output rather than round-tripping.
-/
partial def pretty {f} [ZKField f] (t : Term f) : String :=
  pp 0 t
where
  pp (ctx : Nat) (t : Term f) : String :=
    let p := prec t
    let s :=
      match t with
      | .var x => x
      | .lit n => toString (ZKField.field_to_nat n)
      | .bool b => if b then "true" else "false"
      | .arith op a b =>
          let opStr := match op with | .add => "+" | .sub => "-" | .mul => "*"
          let opPrec := match op with | .mul => 60 | .add => 50 | .sub => 50
          pp opPrec a ++ " " ++ opStr ++ " " ++ pp (opPrec + 1) b
      | .boolB op a b =>
          let opStr := match op with | .and => "&&" | .or => "||"
          let opPrec := match op with | .or => 30 | .and => 35
          pp opPrec a ++ " " ++ opStr ++ " " ++ pp (opPrec + 1) b
      | .eq a b =>
          let opPrec := 40
          pp (opPrec + 1) a ++ " == " ++ pp (opPrec + 1) b
      | .not a =>
          let opPrec := 70
          "!" ++ pp opPrec a
      | .lett x rhs body =>
          let opPrec := 20
          "let " ++ x ++ " = " ++ pp opPrec rhs ++ " in " ++ pp opPrec body
      | .ifz c t₁ t₂ =>
          let opPrec := 20
          "ifz " ++ pp (opPrec + 1) c ++ " then " ++ pp (opPrec + 1) t₁ ++ " else " ++ pp (opPrec + 1) t₂
      | .inSet t ts =>
          let opPrec := 20
          let elems := ts.map (fun x => toString (ZKField.field_to_nat x))
          "inSet(" ++ pp (opPrec + 1) t ++ ", [" ++ String.intercalate ", " elems ++ "])"
      | .assert c body =>
          let opPrec := 20
          "assert (" ++ pp 0 c ++ ") then " ++ pp opPrec body
      | .seq a b =>
          let opPrec := 10
          pp opPrec a ++ " ; " ++ pp (opPrec + 1) b
    parensIf (p < ctx) s

end Term

namespace ZKExpr

/-- Operator precedence used by `ZKExpr.pretty`. -/
def prec {f} : ZKExpr f → Nat
  | .Add .. | .Sub .. => 50
  | .Mul .. => 60
  | .Neg _ => 70
  | _ => 100

/--
Pretty-print a `ZKExpr` produced by the compiler/builder.

This prints witness variables as `w<i>` and literals via `ZKField.field_to_nat`.
-/
partial def pretty {f} [ZKField f] (e : ZKExpr f) : String :=
  pp 0 e
where
  pp (ctx : Nat) (e : ZKExpr f) : String :=
    let p := prec e
    let s :=
      match e with
      | .Literal n => toString (ZKField.field_to_nat n)
      | .WitnessVar i => s!"w{i}"
      | .Add a b =>
          let opPrec := 50
          pp opPrec a ++ " + " ++ pp (opPrec + 1) b
      | .Sub a b =>
          let opPrec := 50
          pp opPrec a ++ " - " ++ pp (opPrec + 1) b
      | .Mul a b =>
          let opPrec := 60
          pp opPrec a ++ " * " ++ pp (opPrec + 1) b
      | .Neg a =>
          let opPrec := 70
          "-" ++ pp opPrec a
      | .ComposedLookupMLE _ c0 c1 c2 c3 =>
          "lookup4(" ++ pp 0 c0 ++ ", " ++ pp 0 c1 ++ ", " ++ pp 0 c2 ++ ", " ++ pp 0 c3 ++ ")"
      | .LookupMLE _ a b =>
          "lookup2(" ++ pp 0 a ++ ", " ++ pp 0 b ++ ")"
      | .LookupMaterialized _ a =>
          "tableLookup(" ++ pp 0 a ++ ")"
      | .RamOp i =>
          s!"ramOp[{i}]"
    parensIf (p < ctx) s

end ZKExpr

namespace Circuit

/-- Pretty-print a single equality constraint `lhs == rhs`. -/
def prettyConstraint {f} [ZKField f] (cd : ZKExpr f × ZKExpr f) : String :=
  ZKExpr.pretty cd.1 ++ " == " ++ ZKExpr.pretty cd.2

/--
Pretty-print a compiled circuit: witness count, output expression, and constraints.

This expects the builder state produced by `ZKBuilder.runFold`.
-/
def pretty {f} [ZKField f] (out : ZKExpr f) (st : ZKBuilderState f) : String :=
  let cs := st.constraints.reverse
  let header :=
    "witnesses: " ++ toString st.allocated_witness_count ++ "\n" ++
    "output: " ++ ZKExpr.pretty out ++ "\n" ++
    "constraints (" ++ toString cs.length ++ "):"
  let body :=
    match cs with
    | [] => "\n  <none>"
    | _ =>
        let rec lines : Nat → List (ZKExpr f × ZKExpr f) → List String
          | _, [] => []
          | i, cd :: rest => s!"  {i}: {prettyConstraint cd}" :: lines (i + 1) rest
        "\n" ++ String.intercalate "\n" (lines 0 cs)
  header ++ body

end Circuit

end ZkLeanCompiler.Lean.Pretty
