
import ZkLeanCompiler.Compile
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

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


def parsedProg_test : Term ℚ := LET "x" := (2 .+. 3) in ASSERT (((Term.var "x" ⊗ 2) =-= 10))

def parsedProg_test : Term ℚ := LET "x" := (2 .+. 3) in ASSERT (((Term.var "x" ⊗ 2) =-= 10))

def parsedProg_test : Term ℚ := LET "x" := (2 .+. 3) in ASSERT (((Term.var "x" ⊗ 2) =-= 10))
