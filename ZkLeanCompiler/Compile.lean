import «ZkLeanCompiler».LCSemantics
import «ZkLeanCompiler».Semantics
import «ZkLeanCompiler».IRExpr
import Std.Data.HashMap


open IRExpr

def toStringIR (f : Type) [Field f] [BEq f] [ToString f] : IRExpr f → String
  | Const n     => s!"Const {n}"
  | IRExpr.Bool b      => s!"Bool {b}"
  | IRExpr.Add e1 e2   => s!"Add ({toStringIR f e1}) ({toStringIR f e2})"
  | IRExpr.Mul e1 e2   => s!"Mul ({toStringIR f e1}) ({toStringIR f e2})"
  | IRExpr.Eq e1 e2    => s!"Eq ({toStringIR f e1}) ({toStringIR f e2})"
  | IRExpr.Sub e1 e2   => s!"Sub ({toStringIR f e1}) ({toStringIR f e2})"
  | Hash e      => s!"Hash ({toStringIR f e})"
  | IfZero c t e => s!"IfZero ({toStringIR f c}) ({toStringIR f t}) ({toStringIR f e})"

instance [Field f] [BEq f] [ToString f] : ToString (IRExpr f) where
  toString := toStringIR f

/- Compile IR expressions into ZK -/
def compileIR [Field f] [BEq f] [ToString f] : IRExpr f → ZKBuilder f (ZKExpr f) :=
  λ expr =>
  match expr with
  | Const n     => pure (ZKExpr.Literal n)
  | IRExpr.Bool b      => pure (ZKExpr.Literal (if b then 1 else 0))
  | IRExpr.Add e1 e2   => do
    let a ← compileIR e1
    let b ← compileIR e2
    pure (ZKExpr.Add a b)
  | IRExpr.Mul e1 e2   => do
    let a ← compileIR e1
    let b ← compileIR e2
    pure (ZKExpr.Mul a b)
  | IRExpr.Eq e1 e2    => do
    let a ← compileIR e1
    let b ← compileIR e2
    pure (ZKExpr.Eq a b)
  | IRExpr.Sub e1 e2   => do
    let a ← compileIR e1
    let b ← compileIR e2
    pure (ZKExpr.Sub a b)
  | IRExpr.IfZero cond t1 t2 => do
    let c ← compileIR cond
    let thenV ← compileIR t1
    let elseV ← compileIR t2
  -- Witnesses
    let isNonZero ← Witnessable.witness
    let inv ← Witnessable.witness
    let out ← Witnessable.witness
  -- cond * inv = isNonZero
    constrainEq (ZKExpr.Mul c inv) isNonZero
  -- cond * (1 - isNonZero) = 0
    constrainEq (ZKExpr.Mul c (ZKExpr.Sub (ZKExpr.Literal 1) isNonZero)) (ZKExpr.Literal 0)
  -- out = isNonZero * thenV + (1 - isNonZero) * elseV
    constrainEq
      (ZKExpr.Add (ZKExpr.Mul isNonZero thenV)
                (ZKExpr.Mul (ZKExpr.Sub (ZKExpr.Literal 1) isNonZero) elseV))
      out
    pure out
  | Hash e      => do
    let a ← compileIR e
    let out ← Witnessable.witness
    constrainEq (ZKExpr.Hash a) out
    pure out

/-
Lets think about the types. Terms are our lambda terms, Env is our mapping from variables to values,
and Val is our value type. ZKBuilder f (ZKExpr f) is our monadic type for building ZK expressions.
It is a state monad and thus has the type (ZKBuilderState f) → (ZKExpr f, ZKBuilderState f).
A ZKBuilder State f consists of a list of constraints and a witness count.
The witness count is the number of witnesses we have allocated so far. The constraints are the ZK
expressions we have built so far.
-/
def compile [Field f] [BEq f] [ToString f] : Term f → Env f → ZKBuilder f (ZKExpr f) :=
  fun t env =>
    let t' := normalize t env
    let (ir, _) := (normalizeToIR t' IR.Env.empty).run 0
    compileIR ir

theorem compiler_correctness {f} [JoltField f] [BEq f] [ToString f]
  (t : Term f) (env : Env f) (v : Val f)
  (h : Eval f t env v) :
  ∃ (witness : List f),
    let t' := normalize t env
    let (ir, _) := (normalizeToIR t' IR.Env.empty).run 0
    let (compiled, state) := (compileIR ir).run ⟨0, []⟩
    semantics_zkexpr compiled witness = v.toValue := by sorry
