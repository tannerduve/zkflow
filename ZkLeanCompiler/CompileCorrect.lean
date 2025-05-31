import «ZkLeanCompiler».Compile
import «ZkLeanCompiler».Semantics
import Mathlib.Tactic.Cases
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.List.Basic

set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

variable {F} [JoltField F] [DecidableEq F]

open ZKBuilder
/--
This file contains the correctness proofs For the ZKLean compiler.
-/

theorem compile_preserves_semantics_rel
  {F} [inst1 : JoltField F] [inst2 : DecidableEq F]
  (t : Term F) (env : Env F) (v : Val F)
  (a : ZKBuilder F (ZKExpr F)) (e : ZKExpr F) (st : ZKBuilderState F) :
  Eval F t env v →
  Compiles env t a →
  run a initialZKBuilderState = (e, st) →
  ∃ w, ZKEval w e (Val.toValue v) := by
  intros eval compiles run_eq
  induction compiles
  case var_field env' x f hlookup =>
    simp [Val.toValue]
    cases v
    · case Field v' =>
      simp [pure, run] at *
      cases' run_eq with e' st'
      rw [← e']
      use [f]
      have : f = v' := by
        cases eval
        · case var h =>
          rw [hlookup] at h
          injection h with h_eq
          injection h_eq
      rw [← this]
      apply ZKEval.lit
    · case Bool b =>
      simp [pure, run] at *
      cases' run_eq with e' st'
      rw [← e']
      use [if b then 1 else 0]
      have : (if b then 1 else 0) = f := by
        cases eval
        · case var h =>
          rw [hlookup] at h
          injection h with h_eq
          injection h_eq
      rw [← this]
      apply ZKEval.lit
  case var_bool env' x b hlookup =>
    simp [Val.toValue]
    cases v
    · case Field v' =>
      simp [pure, run] at *
      cases' run_eq with e' st'
      rw [← e']
      use [if b then 1 else 0]
      have : (if b then 1 else 0) = v' := by
        cases eval
        · case var h =>
          rw [hlookup] at h
          injection h with h_eq
          injection h_eq
      rw [← this]
      apply ZKEval.lit
    · case Bool b' =>
      simp [pure, run] at *
      cases' run_eq with e' st'
      rw [← e']
      use [if b then 1 else 0]
      have h_eq : b = b' := by
        cases eval
        · case var h =>
          rw [hlookup] at h
          injection h with h_eq
          injection h_eq
      rw [h_eq]
      apply ZKEval.lit
  case lit env' f =>
    sorry
  all_goals sorry











theorem compile_constraints_satisfied
  {F} [JoltField F] [DecidableEq F]
  (t : Term F) (env : Env F) (v : Val F)
  (a : ZKBuilder F (ZKExpr F)) (e : ZKExpr F) (st : ZKBuilderState F) (w : List F) :
  Eval F t env v →
  Compiles env t a →
  run a initialZKBuilderState = (e, st) →
  ZKEval w e (Val.toValue v) →
  ConstraintsSatisfied st.constraints w := by sorry
