import ZkLeanCompiler.Lean.Compile
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Defs
open Term

instance hash : Hashable ℚ where
  hash q :=
    let n := q.num.natAbs
    let d := q.den
    (n + d).toUInt64

instance witness : Witnessable ℚ (ZKExpr ℚ) := inferInstance

instance : ZKField ℚ where
  toField := inferInstance
  toBEq := inferInstance
  toInhabited := inferInstance
  toHashable := hash

  eq_of_beq := by
    intros a b h
    simp only [BEq.beq, decide_eq_true_eq] at h
    exact h
  rfl := by
    intro a
    simp only [BEq.beq, decide_eq_true_eq]

def parsedProg_test : Term ℚ := (Term.let "x" (Term.arith ArithBinOp.add (Term.lit 2) (Term.lit 3)) (Term.assert (Term.eq (Term.arith ArithBinOp.mul (Term.var "x") (Term.lit 2)) (Term.lit 10)) (Term.arith ArithBinOp.add (Term.lit 3) (Term.lit 1))))
