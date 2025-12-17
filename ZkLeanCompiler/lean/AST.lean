import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Basic
import ZKLean.FreeMonad
import ZKLean.Semantics
import Std.Data.HashMap
import ZKLean.Builder

open Nat
open Std

/-
The syntax of our expression language.
The language is a simple expression language with variables, literals, arithmetic and boolean operations,
and a few control flow constructs.
-/
inductive ArithBinOp where
| add | sub | mul
deriving Inhabited, BEq, Repr
inductive BoolBinOp where
| and | or
deriving Inhabited, BEq, Repr

inductive Term (f : Type u) where
| var : String → Term f
| lit : f → Term f
| bool : Bool → Term f
| arith : ArithBinOp → Term f → Term f → Term f
| boolB : BoolBinOp  → Term f → Term f → Term f
| eq  : Term f → Term f → Term f
| not : Term f → Term f
| lett : String → Term f → Term f → Term f
| ifz : Term f → Term f → Term f → Term f
| inSet : Term f → List f → Term f
| assert : Term f → Term f → Term f
| seq : Term f → Term f → Term f
deriving Inhabited, BEq, Repr

instance : ToString ArithBinOp where
  toString
    | .add => "+"
    | .sub => "-"
    | .mul => "*"

instance : ToString BoolBinOp where
  toString
    | .and => "&&"
    | .or => "||"

/-
Function to compute the free variables of a term.
-/
def freeVars {f} [Field f] : Term f → Finset String
  | .var x          => {x}
  | .lit _ | .bool _ => ∅
  | .arith _ t₁ t₂ => freeVars t₁ ∪ freeVars t₂
  | .boolB _ t₁ t₂ => freeVars t₁ ∪ freeVars t₂
  | .eq   t₁ t₂     => freeVars t₁ ∪ freeVars t₂
  | .not t          => freeVars t
  | .ifz c t₁ t₂    => freeVars c ∪ freeVars t₁ ∪ freeVars t₂
  | .lett x t₁ t₂   => freeVars t₁ ∪ (freeVars t₂ \ {x})
  | .inSet t _      => freeVars t
  | .assert t₁ t₂   => freeVars t₁ ∪ freeVars t₂
  | .seq t₁ t₂      => freeVars t₁ ∪ freeVars t₂

mutual
/--
The values of our expression language.
The values are either field elements, booleans, or unit.
Unit is used to represent the absence of a value, for example assert should execute without returning a value.
-/
inductive Val (f : Type) [ZKField f] where
| Field   : f → Val f
| Bool    : Bool → Val f
| None    : Val f
deriving Inhabited

structure Env (f : Type) [ZKField f] where
  lookup : String → Option (Val f)
end

def Env.insert {f : Type} [ZKField f] (x : String) (v : Val f) (ρ : Env f) : Env f :=
  { lookup := fun y => if x == y then some v else ρ.lookup y }

/-- A term `t` is well-scoped in an environment `env` iff all of its free variables
    are stored in `env` -/
def wellScoped {f} [ZKField f] (t : Term f) (env : Env f) : Prop :=
  ∀ x ∈ freeVars t, ∃ v, env.lookup x = some v

namespace WellScoped

/-- `¬t` is well scoped iff `t` is well scoped -/
theorem not_iff {f} [ZKField f] (t : Term f) (env : Env f) :
    wellScoped (Term.not t) env ↔ wellScoped t env := by
  simp [wellScoped, freeVars]

theorem inSet_iff {f} [ZKField f] (t : Term f) (ts : List f) (env : Env f) :
    wellScoped (Term.inSet t ts) env ↔ wellScoped t env := by
  simp [wellScoped, freeVars]

theorem assert_iff {f} [ZKField f] (t₁ t₂ : Term f) (env : Env f) :
    wellScoped (Term.assert t₁ t₂) env ↔ wellScoped t₁ env ∧ wellScoped t₂ env := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x (by
        simpa [freeVars] using (Finset.mem_union.mpr (Or.inl hx)))
    · intro x hx
      exact h x (by
        simpa [freeVars] using (Finset.mem_union.mpr (Or.inr hx)))
  · rintro ⟨h₁, h₂⟩ x hx
    have hx' : x ∈ freeVars t₁ ∪ freeVars t₂ := by
      simpa [freeVars] using hx
    rcases Finset.mem_union.mp hx' with hx' | hx'
    · exact h₁ x hx'
    · exact h₂ x hx'

theorem seq_iff {f} [ZKField f] (t₁ t₂ : Term f) (env : Env f) :
    wellScoped (Term.seq t₁ t₂) env ↔ wellScoped t₁ env ∧ wellScoped t₂ env := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x (by
        simpa [freeVars] using (Finset.mem_union.mpr (Or.inl hx)))
    · intro x hx
      exact h x (by
        simpa [freeVars] using (Finset.mem_union.mpr (Or.inr hx)))
  · rintro ⟨h₁, h₂⟩ x hx
    have hx' : x ∈ freeVars t₁ ∪ freeVars t₂ := by
      simpa [freeVars] using hx
    rcases Finset.mem_union.mp hx' with hx' | hx'
    · exact h₁ x hx'
    · exact h₂ x hx'

/-- For an arithmetic operation `op`, `t₁ op t₂` is well scoped iff `t₁` and `t₂` are well scoped -/
theorem arith_iff {f} [ZKField f] (op : ArithBinOp) (t₁ t₂ : Term f) (env : Env f) :
    wellScoped (Term.arith op t₁ t₂) env ↔ wellScoped t₁ env ∧ wellScoped t₂ env := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x (by
        simpa [freeVars] using (Finset.mem_union.mpr (Or.inl hx)))
    · intro x hx
      exact h x (by
        simpa [freeVars] using (Finset.mem_union.mpr (Or.inr hx)))
  · rintro ⟨h₁, h₂⟩ x hx
    have hx' : x ∈ freeVars t₁ ∪ freeVars t₂ := by
      simpa [freeVars] using hx
    rcases Finset.mem_union.mp hx' with hx' | hx'
    · exact h₁ x hx'
    · exact h₂ x hx'

theorem boolB_iff {f} [ZKField f] (op : BoolBinOp) (t₁ t₂ : Term f) (env : Env f) :
    wellScoped (Term.boolB op t₁ t₂) env ↔ wellScoped t₁ env ∧ wellScoped t₂ env := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x (by
        simpa [freeVars] using (Finset.mem_union.mpr (Or.inl hx)))
    · intro x hx
      exact h x (by
        simpa [freeVars] using (Finset.mem_union.mpr (Or.inr hx)))
  · rintro ⟨h₁, h₂⟩ x hx
    have hx' : x ∈ freeVars t₁ ∪ freeVars t₂ := by
      simpa [freeVars] using hx
    rcases Finset.mem_union.mp hx' with hx' | hx'
    · exact h₁ x hx'
    · exact h₂ x hx'

theorem eq_iff {f} [ZKField f] (t₁ t₂ : Term f) (env : Env f) :
    wellScoped (Term.eq t₁ t₂) env ↔ wellScoped t₁ env ∧ wellScoped t₂ env := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x (by
        simpa [freeVars] using (Finset.mem_union.mpr (Or.inl hx)))
    · intro x hx
      exact h x (by
        simpa [freeVars] using (Finset.mem_union.mpr (Or.inr hx)))
  · rintro ⟨h₁, h₂⟩ x hx
    have hx' : x ∈ freeVars t₁ ∪ freeVars t₂ := by
      simpa [freeVars] using hx
    rcases Finset.mem_union.mp hx' with hx' | hx'
    · exact h₁ x hx'
    · exact h₂ x hx'

theorem ifz_iff {f} [ZKField f] (c t₁ t₂ : Term f) (env : Env f) :
    wellScoped (Term.ifz c t₁ t₂) env ↔ wellScoped c env ∧ wellScoped t₁ env ∧ wellScoped t₂ env := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact h x (by simp [freeVars, hx])
    · intro x hx
      exact h x (by simp [freeVars, hx])
    · intro x hx
      exact h x (by simp [freeVars, hx])
  · rintro ⟨hc, ht₁, ht₂⟩ x hx
    simp [wellScoped] at hc ht₁ ht₂ ⊢
    have hx' : x ∈ freeVars c ∨ x ∈ freeVars t₁ ∨ x ∈ freeVars t₂ := by
      simpa [freeVars] using hx
    rcases hx' with hx' | hx'
    · exact hc x hx'
    · rcases hx' with hx' | hx'
      · exact ht₁ x hx'
      · exact ht₂ x hx'

end WellScoped

namespace Term
  variable {f} [Field f]
  abbrev add (a b : Term f) : Term f := .arith .add a b
  abbrev sub (a b : Term f) : Term f := .arith .sub a b
  abbrev mul (a b : Term f) : Term f := .arith .mul a b
  abbrev and (a b : Term f) : Term f := .boolB .and a b
  abbrev or  (a b : Term f) : Term f := .boolB .or  a b
end Term

notation " <{ " e:100 " }> " => e
infixl:65 " .+. " => Term.add
infixl:65 " ⊗ " => Term.mul
infixl:65 " .-. " => Term.sub
infix:50  " =-= " => Term.eq
infixr:40 " && " => Term.and
infixr:35 " || " => Term.or
infixl:70 " ; " => Term.seq
infix:60 " inn " => Term.inSet
notation "ifz` " t₁:100 " then` " t₂:100 " else`" t₃:100 => Term.ifz t₁ t₂ t₃
notation "ASSERT " t₁:100 " then " t₂:100 => Term.assert t₁ t₂
prefix:100 "~ " => Term.not
notation "LET " x " := " t " in " b => Term.lett x t b
