import ZkLeanCompiler.Compile
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Defs
open Term

instance hash : Hashable ℚ where
  hash q :=
    let n := q.num.natAbs
    let d := q.den
    (n + d).toUInt64

instance witness : Witnessable ℚ (ZKExpr ℚ) where
  witness := do
    let st ← get
    let id := st.allocated_witness_count
    set { st with allocated_witness_count := id + 1 }
    pure (ZKExpr.WitnessVar id)

instance : JoltField ℚ where
  toField := inferInstance
  toBEq := inferInstance
  toToString := inferInstance
  toInhabited := inferInstance
  toWitnessable := witness
  toHashable := hash
  eq_of_beq := by
    intros a b h
    simp only [BEq.beq, decide_eq_true_eq] at h
    exact h
  rfl := by
    intro a
    simp only [BEq.beq, decide_eq_true_eq]

def parsedProg_complex : Term ℚ := (Term.assert (Term.eq (Term.arith ArithBinOp.add (Term.lit 1) (Term.lit 2)) (Term.lit 3)) (Term.seq (Term.bool true) (Term.assert (Term.boolB BoolBinOp.and (Term.not (Term.bool false)) (Term.bool true)) (Term.seq (Term.arith ArithBinOp.add (Term.lit 3) (Term.lit 1)) (Term.assert (Term.eq (Term.arith ArithBinOp.sub (Term.lit 7) (Term.lit 2)) (Term.lit 5)) (Term.bool true))))))
