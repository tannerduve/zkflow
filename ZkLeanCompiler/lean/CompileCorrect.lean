import «ZkLeanCompiler».Lean.Compile
import ZKLean.Semantics
import Mathlib.Tactic.Cases
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.List.Basic

set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

variable {F} [ZKField F] [DecidableEq F]

open ZKBuilder

/- Compatibility: older files used `JoltField`. -/
abbrev JoltField := ZKField

namespace Val

/- Encode a source-language value as a field element (Booleans as `0/1`). -/
def encode {F} [ZKField F] : Val F → Option F
  | .Field x => some x
  | .Bool b => some (if b then (1 : F) else 0)
  | .None => none

end Val

/- Evaluate a `ZKExpr` in the context of a builder state (to account for RAM operations). -/
def evalZKExprInState {F} [ZKField F] (witness : List F) (st : ZKBuilderState F) (e : ZKExpr F) :
    Option F :=
  match semantics_ram witness st.ram_sizes st.ram_ops with
  | some ramValues => semantics_zkexpr e witness ramValues
  | none => none

/- A witness satisfies a compiled circuit state. -/
def CircuitSatisfied {F} [ZKField F] (st : ZKBuilderState F) (witness : List F) : Prop :=
  semantics witness st = true

/- A circuit state is satisfiable if it has some satisfying witness. -/
def StateSatisfiable {F} [ZKField F] (st : ZKBuilderState F) : Prop :=
  ∃ w, CircuitSatisfied st w

/- A minimal source-level type system; needed because the compiler works over field encodings. -/
inductive Ty where
  | field
  | bool
deriving DecidableEq, Repr

inductive ValHasType {F} [ZKField F] : Val F → Ty → Prop
  | field (x : F) : ValHasType (.Field x) .field
  | bool (b : Bool) : ValHasType (.Bool b) .bool
  | none : ValHasType (.None) .field

inductive HasType {F} [ZKField F] : Env F → Term F → Ty → Prop
  | var_field {env x n} :
      env.lookup x = some (Val.Field n) →
      HasType env (.var x) .field
  | var_bool {env x b} :
      env.lookup x = some (Val.Bool b) →
      HasType env (.var x) .bool
  | lit {env n} :
      HasType env (.lit n) .field
  | bool {env b} :
      HasType env (.bool b) .bool
  | arith {env op t₁ t₂} :
      HasType env t₁ .field →
      HasType env t₂ .field →
      HasType env (.arith op t₁ t₂) .field
  | boolB {env op t₁ t₂} :
      HasType env t₁ .bool →
      HasType env t₂ .bool →
      HasType env (.boolB op t₁ t₂) .bool
  | eq {env t₁ t₂ τ} :
      HasType env t₁ τ →
      HasType env t₂ τ →
      HasType env (.eq t₁ t₂) .bool
  | not {env t} :
      HasType env t .bool →
      HasType env (.not t) .bool
  | ifz {env c t₁ t₂ τ} :
      HasType env c .bool →
      HasType env t₁ τ →
      HasType env t₂ τ →
      HasType env (.ifz c t₁ t₂) τ
  | inSet {env t ts} :
      HasType env t .field →
      HasType env (.inSet t ts) .bool

/--
This file contains the correctness proofs For the ZKLean compiler.
-/

-- **Semantic Preservation**: If a term evaluates to a value and compiles successfully,
-- then the compiled ZK expression evaluates to the same value under some witness.
theorem compile_preserves_semantics
  {F} [ZKField F] [DecidableEq F]
  (τ : Ty)
  (t : Term F) (env : Env F) (v : Val F)
  (a : ZKBuilder F (ZKExpr F)) (e : ZKExpr F) (st₀ st₁ : ZKBuilderState F) :
  HasType env t τ →
  ValHasType v τ →
  Eval F t env v →
  Compiles env t a →
  runFold a st₀ = (e, st₁) →
  ∀ w, CircuitSatisfied st₁ w → evalZKExprInState w st₁ e = Val.encode v := by
  sorry

-- **Preservation of Satisfiability**: For well-typed programs, compilation does not turn a satisfiable
-- pre-existing builder state into an unsatisfiable one.
theorem compile_preserves_satisfiable
  {F} [ZKField F] [DecidableEq F]
  (τ : Ty)
  (t : Term F) (env : Env F)
  (a : ZKBuilder F (ZKExpr F)) (e : ZKExpr F) (st₀ st₁ : ZKBuilderState F) :
  HasType env t τ →
  Compiles env t a →
  runFold a st₀ = (e, st₁) →
  StateSatisfiable st₀ →
  StateSatisfiable st₁ := by
  sorry

-- **Existence of a Correct Witness**: starting from a satisfiable state, compilation yields a satisfiable
-- state, and any satisfying witness makes the output compute the correct encoded value.
theorem compile_exists_correct_witness
  {F} [ZKField F] [DecidableEq F]
  (τ : Ty)
  (t : Term F) (env : Env F) (v : Val F)
  (a : ZKBuilder F (ZKExpr F)) (e : ZKExpr F) (st₀ st₁ : ZKBuilderState F) :
  HasType env t τ →
  ValHasType v τ →
  Eval F t env v →
  Compiles env t a →
  runFold a st₀ = (e, st₁) →
  StateSatisfiable st₀ →
  ∃ w, CircuitSatisfied st₁ w ∧ evalZKExprInState w st₁ e = Val.encode v := by
  sorry

-- **Type Safety (Evaluation)**: If an arithmetic term evaluates to a field value,
-- then both operands evaluate to field values.
lemma eval_arith_well_typed
  {F} [ZKField F] [DecidableEq F]
  (env : Env F) (op : ArithBinOp) (t₁ t₂ : Term F) (n : F) :
  Eval F (Term.arith op t₁ t₂) env (Val.Field n) →
  (∃ n₁, Eval F t₁ env (Val.Field n₁)) ∧ (∃ n₂, Eval F t₂ env (Val.Field n₂)) := by
  sorry

-- Similarly for boolean operations
lemma eval_boolB_well_typed
  {F} [ZKField F] [DecidableEq F]
  (env : Env F) (op : BoolBinOp) (t₁ t₂ : Term F) (b : Bool) :
  Eval F (Term.boolB op t₁ t₂) env (Val.Bool b) →
  (∃ b₁, Eval F t₁ env (Val.Bool b₁)) ∧ (∃ b₂, Eval F t₂ env (Val.Bool b₂)) := by
  sorry

-- **Source Progress**: A well-typed term evaluates to some value.
theorem well_typed_progress
  {F} [ZKField F] [DecidableEq F]
  (t : Term F) (env : Env F) (τ : Ty) :
  HasType env t τ →
  ∃ v, Eval F t env v ∧ ValHasType v τ := by
  sorry

-- **Soundness**: If we have a witness that satisfies the constraints,
-- then the compiled expression evaluates correctly under that witness.
theorem compile_sound {F : Type} [ZKField F] [DecidableEq F]
    (τ : Ty)
    (t : Term F) (env : Env F) (v : Val F) (comp : ZKBuilder F (ZKExpr F)) (witness : List F)
    (zkexpr : ZKExpr F) (st₀ st₁ : ZKBuilderState F) :
  HasType env t τ →
  ValHasType v τ →
  Eval F t env v →
  Compiles env t comp →
  runFold comp st₀ = (zkexpr, st₁) →
  CircuitSatisfied st₁ witness →
  evalZKExprInState witness st₁ zkexpr = Val.encode v := by
  sorry
