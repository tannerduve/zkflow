import «ZkLeanCompiler».Lean.Compile
import ZKLean.Semantics
import Mathlib.Tactic.Cases
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.List.Basic
import Init.Data.List.Lemmas

/-!
# Compiler Correctness and ZK circuit semantics lemmas

This module contains:

* **Small ZK-side lemmas** about `ZKLean.Semantics` (`semantics_zkexpr`, `semantics_constraints`) that
  are useful when proving compiler correctness.
* **Compiler correctness statement scaffolding** for `ZkLeanCompiler.Lean.Compile`.

Many of the main compiler theorems are currently left as `sorry`; the goal of this file is to keep
the statements correct for the current ZKLean API, and to accumulate reusable lemmas with real
proofs.
-/

set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

variable {F} [ZKField F] [DecidableEq F]

open ZKBuilder

/-- Compatibility alias: older code used `JoltField` for the ZK field class. -/
abbrev JoltField := ZKField

/-- A convenient empty builder state for small semantic lemmas. -/
def initialZKBuilderState (f : Type) : ZKBuilderState f :=
  { allocated_witness_count := 0, constraints := [], ram_sizes := #[], ram_ops := #[] }

namespace Val

/-- Encode a source-language value as a field element (Booleans as `0/1`). -/
def encode {F} [ZKField F] : Val F → Option F
  | .Field x => some x
  | .Bool b => some (if b then (1 : F) else 0)
  | .None => none

end Val

namespace ZKSemanticsLemmas

open ZKBuilder

/-- Boolean predicate: a single equality constraint holds under `semantics_zkexpr`. -/
def constraintOk {f} [ZKField f] (witness : List f) (ram_values : RamOpsEval f)
    (cd : ZKExpr f × ZKExpr f) : Bool :=
  match semantics_zkexpr cd.1 witness ram_values, semantics_zkexpr cd.2 witness ram_values with
  | some x, some y => x == y
  | _, _ => false

/--
`semantics_constraints` is equivalent to checking that *all* constraints satisfy `constraintOk`.

This rewrite is useful because it lets us reuse generic list lemmas such as permutation invariance
of `List.all`.
-/
lemma semantics_constraints_eq_all {f} [ZKField f]
    (cs : List (ZKExpr f × ZKExpr f)) (witness : List f) (ram_values : RamOpsEval f) :
    semantics_constraints cs witness ram_values = cs.all (constraintOk witness ram_values) := by
  induction cs with
  | nil =>
      simp [semantics_constraints]
  | cons hd tl ih =>
      rcases hd with ⟨c, d⟩
      cases hsc : semantics_zkexpr c witness ram_values <;>
      cases hsd : semantics_zkexpr d witness ram_values <;>
      simp [semantics_constraints, constraintOk, hsc, hsd, ih]

/-- `List.all` is invariant under `List.Perm`. -/
lemma perm_all_eq {α} (p : α → Bool) {l₁ l₂ : List α} (h : List.Perm l₁ l₂) :
    l₁.all p = l₂.all p := by
  induction h <;>
    simp [List.all, *, Bool.and_left_comm]

/-- `semantics_constraints` is invariant under permutation of the constraint list. -/
lemma semantics_constraints_perm {f} [ZKField f]
    {cs₁ cs₂ : List (ZKExpr f × ZKExpr f)} (h : List.Perm cs₁ cs₂)
    (witness : List f) (ram_values : RamOpsEval f) :
    semantics_constraints cs₁ witness ram_values = semantics_constraints cs₂ witness ram_values := by
  simpa [semantics_constraints_eq_all] using perm_all_eq (constraintOk witness ram_values) h

/-- `semantics_constraints` distributes over append as Boolean conjunction. -/
lemma semantics_constraints_append {f} [ZKField f]
    (cs₁ cs₂ : List (ZKExpr f × ZKExpr f)) (witness : List f) (ram_values : RamOpsEval f) :
    semantics_constraints (cs₁ ++ cs₂) witness ram_values =
      (semantics_constraints cs₁ witness ram_values && semantics_constraints cs₂ witness ram_values) := by
  simp [semantics_constraints_eq_all, List.all_append]

/-- Collect all witness indices referenced by a `ZKExpr`. -/
def witnessIndices {f} : ZKExpr f → Finset Nat
  | .Literal _ => ∅
  | .WitnessVar i => {i}
  | .Add e₁ e₂ => witnessIndices e₁ ∪ witnessIndices e₂
  | .Sub e₁ e₂ => witnessIndices e₁ ∪ witnessIndices e₂
  | .Neg e => witnessIndices e
  | .Mul e₁ e₂ => witnessIndices e₁ ∪ witnessIndices e₂
  | .ComposedLookupMLE _ c0 c1 c2 c3 =>
      witnessIndices c0 ∪ witnessIndices c1 ∪ witnessIndices c2 ∪ witnessIndices c3
  | .LookupMLE _ e1 e2 => witnessIndices e1 ∪ witnessIndices e2
  | .LookupMaterialized _ e => witnessIndices e
  | .RamOp _ => ∅

/--
Appending extra witness values does not change the evaluation of an expression, as long as all
`WitnessVar` indices used by the expression are in bounds of the original witness list.
-/
lemma semantics_zkexpr_suffix_irrelevant {f} [ZKField f]
    (e : ZKExpr f) (w w' : List f) (ram_values : RamOpsEval f)
    (h : ∀ i, i ∈ witnessIndices e → i < w.length) :
    semantics_zkexpr e w ram_values = semantics_zkexpr e (w ++ w') ram_values := by
  have hev :
      semantics_zkexpr.eval w ram_values e =
        semantics_zkexpr.eval (w ++ w') ram_values e := by
    induction e with
    | Literal lit =>
        simp [semantics_zkexpr.eval]
    | WitnessVar id =>
        have hid : id < w.length := h id (by simp [witnessIndices])
        simp [semantics_zkexpr.eval, List.getElem?_append_left hid]
    | Add e₁ e₂ ih₁ ih₂ =>
        have h₁ : ∀ i, i ∈ witnessIndices e₁ → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        have h₂ : ∀ i, i ∈ witnessIndices e₂ → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        simp [semantics_zkexpr.eval, ih₁ h₁, ih₂ h₂]
    | Sub e₁ e₂ ih₁ ih₂ =>
        have h₁ : ∀ i, i ∈ witnessIndices e₁ → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        have h₂ : ∀ i, i ∈ witnessIndices e₂ → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        simp [semantics_zkexpr.eval, ih₁ h₁, ih₂ h₂]
    | Neg e ih =>
        have h' : ∀ i, i ∈ witnessIndices e → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        simp [semantics_zkexpr.eval, ih h']
    | Mul e₁ e₂ ih₁ ih₂ =>
        have h₁ : ∀ i, i ∈ witnessIndices e₁ → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        have h₂ : ∀ i, i ∈ witnessIndices e₂ → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        simp [semantics_zkexpr.eval, ih₁ h₁, ih₂ h₂]
    | ComposedLookupMLE table c0 c1 c2 c3 ih0 ih1 ih2 ih3 =>
        have h0 : ∀ i, i ∈ witnessIndices c0 → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        have h1 : ∀ i, i ∈ witnessIndices c1 → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        have h2 : ∀ i, i ∈ witnessIndices c2 → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        have h3 : ∀ i, i ∈ witnessIndices c3 → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        simp [semantics_zkexpr.eval, ih0 h0, ih1 h1, ih2 h2, ih3 h3]
    | LookupMLE table e1 e2 ih1 ih2 =>
        have h₁ : ∀ i, i ∈ witnessIndices e1 → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        have h₂ : ∀ i, i ∈ witnessIndices e2 → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        simp [semantics_zkexpr.eval, ih1 h₁, ih2 h₂]
    | LookupMaterialized table e ih =>
        have h' : ∀ i, i ∈ witnessIndices e → i < w.length := by
          intro i hi; exact h i (by simp [witnessIndices, hi])
        simp [semantics_zkexpr.eval, ih h']
    | RamOp op_index =>
        simp [semantics_zkexpr.eval]
  simpa [semantics_zkexpr] using hev

/--
Soundness of a single R1CS constraint: if `a`, `b`, and `c` evaluate consistently as `x`, `y`, and
`x*y`, then the constraints produced by `constrainR1CS a b c` are satisfied.
-/
lemma constrainR1CS_sound {f} [ZKField f]
    (a b c : ZKExpr f) (witness : List f) (ram_values : RamOpsEval f) (x y : f)
    (ha : semantics_zkexpr a witness ram_values = some x)
    (hb : semantics_zkexpr b witness ram_values = some y)
    (hc : semantics_zkexpr c witness ram_values = some (x * y)) :
    semantics_constraints
        ((runFold (constrainR1CS a b c) (initialZKBuilderState f)).2.constraints)
        witness
        ram_values = true := by
  have haE : semantics_zkexpr.eval witness ram_values a = some x := by
    simpa [semantics_zkexpr] using ha
  have hbE : semantics_zkexpr.eval witness ram_values b = some y := by
    simpa [semantics_zkexpr] using hb
  have hcE : semantics_zkexpr.eval witness ram_values c = some (x * y) := by
    simpa [semantics_zkexpr] using hc
  have hmulE : semantics_zkexpr.eval witness ram_values (ZKExpr.Mul a b) = some (x * y) := by
    simp [semantics_zkexpr.eval, haE, hbE]
  have hmul : semantics_zkexpr (ZKExpr.Mul a b) witness ram_values = some (x * y) := by
    simpa [semantics_zkexpr] using hmulE
  have hc' : semantics_zkexpr c witness ram_values = some (x * y) := by
    simpa [semantics_zkexpr] using hcE
  simp [initialZKBuilderState, ZKBuilder.constrainR1CS, FreeM.lift, runFold, FreeM.foldM, ZKOpInterp,
    semantics_constraints, hmul, hc']

/--
Soundness of booleanity assertion: if `x` evaluates to `0` or `1`, then the constraints produced by
`assertIsBool x` are satisfied.
-/
lemma assertIsBool_sound {f} [ZKField f]
    (x : ZKExpr f) (witness : List f) (ram_values : RamOpsEval f) :
    (semantics_zkexpr x witness ram_values = some (0 : f) ∨
      semantics_zkexpr x witness ram_values = some (1 : f)) →
    semantics_constraints
        ((runFold (assertIsBool x) (initialZKBuilderState f)).2.constraints)
        witness
        ram_values = true := by
  intro hx
  rcases hx with hx0 | hx1
  · -- case `x = 0`
    have hx0E : semantics_zkexpr.eval witness ram_values x = some (0 : f) := by
      simpa [semantics_zkexpr] using hx0
    have hsubE :
        semantics_zkexpr.eval witness ram_values (ZKExpr.Sub (ZKExpr.Literal (1 : f)) x) =
          some (1 : f) := by
      simp [semantics_zkexpr.eval, hx0E]
    have hsub : semantics_zkexpr (ZKExpr.Sub (ZKExpr.Literal (1 : f)) x) witness ram_values = some (1 : f) := by
      simpa [semantics_zkexpr] using hsubE
    have hzeroE : semantics_zkexpr.eval witness ram_values (ZKExpr.Literal (0 : f)) = some (0 : f) := by
      simp [semantics_zkexpr.eval]
    have hzero : semantics_zkexpr (ZKExpr.Literal (0 : f)) witness ram_values = some (0 : f) := by
      simpa [semantics_zkexpr] using hzeroE
    -- `0 * (1-0) = 0`
    simpa [assertIsBool] using
      (constrainR1CS_sound (a := x) (b := ZKExpr.Sub (ZKExpr.Literal (1 : f)) x) (c := ZKExpr.Literal (0 : f))
        (witness := witness) (ram_values := ram_values) (x := (0 : f)) (y := (1 : f))
        hx0 hsub (by simpa using hzero))
  · -- case `x = 1`
    have hx1E : semantics_zkexpr.eval witness ram_values x = some (1 : f) := by
      simpa [semantics_zkexpr] using hx1
    have hsubE :
        semantics_zkexpr.eval witness ram_values (ZKExpr.Sub (ZKExpr.Literal (1 : f)) x) =
          some (0 : f) := by
      simp [semantics_zkexpr.eval, hx1E]
    have hsub : semantics_zkexpr (ZKExpr.Sub (ZKExpr.Literal (1 : f)) x) witness ram_values = some (0 : f) := by
      simpa [semantics_zkexpr] using hsubE
    have hzeroE : semantics_zkexpr.eval witness ram_values (ZKExpr.Literal (0 : f)) = some (0 : f) := by
      simp [semantics_zkexpr.eval]
    have hzero : semantics_zkexpr (ZKExpr.Literal (0 : f)) witness ram_values = some (0 : f) := by
      simpa [semantics_zkexpr] using hzeroE
    simpa [assertIsBool] using
      (constrainR1CS_sound (a := x) (b := ZKExpr.Sub (ZKExpr.Literal (1 : f)) x) (c := ZKExpr.Literal (0 : f))
        (witness := witness) (ram_values := ram_values) (x := (1 : f)) (y := (0 : f))
        hx1 hsub (by simpa using hzero))

end ZKSemanticsLemmas

/-- Evaluate a `ZKExpr` in the context of a builder state (to account for RAM operations). -/
def evalZKExprInState {F} [ZKField F] (witness : List F) (st : ZKBuilderState F) (e : ZKExpr F) :
    Option F :=
  match semantics_ram witness st.ram_sizes st.ram_ops with
  | some ramValues => semantics_zkexpr e witness ramValues
  | none => none

/-- A witness satisfies a compiled circuit state. -/
def CircuitSatisfied {F} [ZKField F] (st : ZKBuilderState F) (witness : List F) : Prop :=
  semantics witness st = true

/-- A circuit state is satisfiable if it has some satisfying witness. -/
def StateSatisfiable {F} [ZKField F] (st : ZKBuilderState F) : Prop :=
  ∃ w, CircuitSatisfied st w

/-- A minimal source-level type system; needed because the compiler works over field encodings. -/
inductive Ty where
  | field
  | bool
deriving DecidableEq, Repr

/-- A well-typed source value for the minimal type system. -/
inductive ValHasType {F} [ZKField F] : Val F → Ty → Prop
  | field (x : F) : ValHasType (.Field x) .field
  | bool (b : Bool) : ValHasType (.Bool b) .bool
  | none : ValHasType (.None) .field

/-- A well-typed source term for the minimal type system. -/
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
**Semantic preservation (statement)**: if a well-typed term evaluates to a value and compiles, then
for any satisfying witness of the produced circuit state, the compiled expression evaluates to the
encoded value.
-/
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

/--
**Preservation of satisfiability (statement)**: compiling a well-typed term does not turn an
initially satisfiable builder state into an unsatisfiable one.
-/
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

/--
**Existence of a correct witness (statement)**: starting from a satisfiable state, compilation
produces a satisfiable state and some satisfying witness makes the output compute the correct
encoded value.
-/
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

/--
**Type safety (evaluation)**: if an arithmetic term evaluates to a field value, then both operands
evaluate to field values.
-/
lemma eval_arith_well_typed
  {F} [ZKField F] [DecidableEq F]
  (env : Env F) (op : ArithBinOp) (t₁ t₂ : Term F) (n : F) :
  Eval F (Term.arith op t₁ t₂) env (Val.Field n) →
  (∃ n₁, Eval F t₁ env (Val.Field n₁)) ∧ (∃ n₂, Eval F t₂ env (Val.Field n₂)) := by
  sorry

/-- Type safety (evaluation) for boolean binary operations. -/
lemma eval_boolB_well_typed
  {F} [ZKField F] [DecidableEq F]
  (env : Env F) (op : BoolBinOp) (t₁ t₂ : Term F) (b : Bool) :
  Eval F (Term.boolB op t₁ t₂) env (Val.Bool b) →
  (∃ b₁, Eval F t₁ env (Val.Bool b₁)) ∧ (∃ b₂, Eval F t₂ env (Val.Bool b₂)) := by
  sorry

/-- **Source progress (statement)**: a well-typed term evaluates to some value of the same type. -/
theorem well_typed_progress
  {F} [ZKField F] [DecidableEq F]
  (t : Term F) (env : Env F) (τ : Ty) :
  HasType env t τ →
  ∃ v, Eval F t env v ∧ ValHasType v τ := by
  sorry

/--
**Soundness (statement)**: given a satisfying witness for the compiled circuit state, the compiled
expression evaluates to the encoded source value.
-/
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
