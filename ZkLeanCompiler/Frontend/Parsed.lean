import ZkLeanCompiler.Lean.Compile
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Defs
open Term

instance hash : Hashable ℚ where
  hash q :=
    let n := q.num.natAbs
    let d := q.den
    (n + d).toUInt64

instance : JoltField ℚ where
  toField := inferInstance
  toBEq := inferInstance
  toToString := inferInstance
  toInhabited := inferInstance
  toWitnessable := inferInstance
  toHashable := hash
  eq_of_beq := by
    intros a b h
    simp only [BEq.beq, decide_eq_true_eq] at h
    exact h
  rfl := by
    intro a
    simp only [BEq.beq, decide_eq_true_eq]

def parsedProg_mul_self : Term ℚ := (Term.lett "x" (Term.lit 5) (Term.arith ArithBinOp.mul (Term.var "x") (Term.var "x")))
