import «ZkLeanCompiler».Lean.Compile
import «ZkLeanCompiler».Lean.Semantics
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

-- theorem compile_preserves_semantics_rel
--   {F} [inst1 : JoltField F] [inst2 : DecidableEq F]
--   (t : Term F) (env : Env F) (v : Val F)
--   (a : ZKBuilder F (ZKExpr F)) (e : ZKExpr F) (st : ZKBuilderState F) :
--   Eval F t env v →
--   Compiles env t a →
--   run a initialZKBuilderState = (e, st) →
--   ∃ w, ZKEval w e (Val.toValue v) := by
--   intros eval compiles run_eq
--   induction compiles
--   case var_field env' x f hlookup =>
--     simp [Val.toValue]
--     cases v
--     · case Field v' =>
--       simp [pure, run] at *
--       cases' run_eq with e' st'
--       rw [← e']
--       use [f]
--       have : f = v' := by
--         cases eval
--         · case var h =>
--           rw [hlookup] at h
--           injection h with h_eq
--           injection h_eq
--       rw [← this]
--       apply ZKEval.lit
--     · case Bool b =>
--       simp [pure, run] at *
--       cases' run_eq with e' st'
--       rw [← e']
--       use [if b then 1 else 0]
--       have : (if b then 1 else 0) = f := by
--         cases eval
--         · case var h =>
--           rw [hlookup] at h
--           injection h with h_eq
--           injection h_eq
--       rw [← this]
--       apply ZKEval.lit
--   case var_bool env' x b hlookup =>
--     simp [Val.toValue]
--     cases v
--     · case Field v' =>
--       simp [pure, run] at *
--       cases' run_eq with e' st'
--       rw [← e']
--       use [if b then 1 else 0]
--       have : (if b then 1 else 0) = v' := by
--         cases eval
--         · case var h =>
--           rw [hlookup] at h
--           injection h with h_eq
--           injection h_eq
--       rw [← this]
--       apply ZKEval.lit
--     · case Bool b' =>
--       simp [pure, run] at *
--       cases' run_eq with e' st'
--       rw [← e']
--       use [if b then 1 else 0]
--       have h_eq : b = b' := by
--         cases eval
--         · case var h =>
--           rw [hlookup] at h
--           injection h with h_eq
--           injection h_eq
--       rw [h_eq]
--       apply ZKEval.lit
--   case lit env' f =>
--     sorry
--   all_goals sorry

-- **Semantic Preservation**: If a term evaluates to a value and compiles successfully,
-- then the compiled ZK expression evaluates to the same value under some witness.
theorem compile_preserves_semantics
  {F} [JoltField F] [DecidableEq F]
  (t : Term F) (env : Env F) (v : Val F)
  (a : ZKBuilder F (ZKExpr F)) (e : ZKExpr F) (st₀ st₁ : ZKBuilderState F) :
  Eval F t env v →
  Compiles env t a →
  runFold a st₀ = (e, st₁) →
  ∃ w, ZKEval w e (Val.toValue v) := by sorry

-- **Constraint Satisfiability**: If a term compiles successfully,
-- then the generated constraints have a satisfying witness.
theorem compile_constraints_satisfiable
  {F} [JoltField F] [DecidableEq F]
  (t : Term F) (env : Env F)
  (a : ZKBuilder F (ZKExpr F)) (e : ZKExpr F) (st₀ st₁ : ZKBuilderState F) :
  Compiles env t a →
  runFold a st₀ = (e, st₁) →
  ∃ w, ConstraintsSatisfied st₁.constraints w := by sorry

-- **Type Safety Lemma**: If an arithmetic operation compiles,
-- then both operands evaluate to field values.
lemma compiles_arith_well_typed
  {F} [JoltField F] [DecidableEq F]
  (env : Env F) (op : ArithBinOp) (t₁ t₂ : Term F) (a : ZKBuilder F (ZKExpr F)) :
  Compiles env (Term.arith op t₁ t₂) a →
  (∃ n₁, Eval F t₁ env (Val.Field n₁)) ∧ (∃ n₂, Eval F t₂ env (Val.Field n₂)) := by sorry

-- Similarly for boolean operations
lemma compiles_boolB_well_typed
  {F} [JoltField F] [DecidableEq F]
  (env : Env F) (op : BoolBinOp) (t₁ t₂ : Term F) (a : ZKBuilder F (ZKExpr F)) :
  Compiles env (Term.boolB op t₁ t₂) a →
  (∃ b₁, Eval F t₁ env (Val.Bool b₁)) ∧ (∃ b₂, Eval F t₂ env (Val.Bool b₂)) := by sorry

-- **Compiler Well-Formedness**: The compiler only accepts terms that evaluate to something.
theorem compiler_well_formed
  {F} [JoltField F] [DecidableEq F]
  (t : Term F) (env : Env F) (a : ZKBuilder F (ZKExpr F)) :
  Compiles env t a →
  ∃ v, Eval F t env v := by
  intro comp
  induction comp
  · case var_field env' x f hlookup =>
    use (Val.Field f)
    exact Eval.var env' x (Val.Field f) hlookup
  · case var_bool env' x b hlookup =>
    use (Val.Bool b)
    exact Eval.var env' x (Val.Bool b) hlookup
  · case lit env' f =>
    use (Val.Field f)
    exact Eval.lit env' f
  · case bool env' b =>
    use (Val.Bool b)
    exact Eval.bool env' b
  · case arith env' op t₁ t₂ a₁ a₂ comp₁ comp₂ ih₁ ih₂ =>
    cases' ih₁ with v₁ h₁
    cases' ih₂ with v₂ h₂
    cases v₁
    · case Field v₁' =>
      cases v₂
      · case Field v₂' =>
        use (Val.Field (match op with
          | .add => v₁' + v₂'
          | .sub => v₁' - v₂'
          | .mul => v₁' * v₂'))
        apply Eval.arith env' op t₁ t₂ v₁' v₂'
        exact h₁
        exact h₂
      · case Bool b => sorry -- Need type safety lemma: arith compilation requires field values
      · case None => sorry  -- Need type safety lemma: arith compilation requires field values
    · case Bool => sorry    -- Need type safety lemma: arith compilation requires field values
    · case None => sorry    -- Need type safety lemma: arith compilation requires field values
  all_goals sorry

-- **Soundness**: If we have a witness that satisfies the constraints,
-- then the compiled expression evaluates correctly under that witness.
theorem compile_sound {F : Type} [JoltField F] [DecidableEq F]
    (t : Term F) (env : Env F) (v : Val F) (comp : ZKBuilder F (ZKExpr F)) (witness : List F)
    (zkexpr : ZKExpr F) (st₀ st₁ : ZKBuilderState F) :
  Eval F t env v →
  Compiles env t comp →
  runFold comp st₀ = (zkexpr, st₁) →
  ConstraintsSatisfied st₁.constraints witness →
  ZKEval witness zkexpr (Val.toValue v) := by sorry
