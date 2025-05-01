import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Basic
open Nat
open Std

/-
The syntax of our expression language.
The language is a simple expression language with variables, literals, arithmetic and boolean operations,
and a few control flow constructs.
-/
inductive Term (f : Type u) [Field f] where
| var : String → Term f
| lit : f → Term f
| bool : Bool → Term f
-- arithmetic
| add : Term f → Term f → Term f
| mul : Term f → Term f → Term f
| sub : Term f → Term f → Term f
-- logic
| eq  : Term f → Term f → Term f
| and : Term f → Term f → Term f
| or  : Term f → Term f → Term f
| not : Term f → Term f
| inSet : Term f → List f → Term f
-- control flow
| lett : String → Term f → Term f → Term f
| ifz : Term f → Term f → Term f → Term f
-- statements/commands
| assert : Term f → Term f
| seq : Term f → Term f → Term f
deriving Inhabited, BEq

/-
Function to compute the free variables of a term.
-/
def freeVars {f} [Field f] (t : Term f) : Finset String := match t with
  | Term.lit _        => ∅
  | Term.bool _       => ∅
  | Term.var x        => {x}
  | Term.add t₁ t₂    => freeVars t₁ ∪ freeVars t₂
  | Term.sub t₁ t₂    => freeVars t₁ ∪ freeVars t₂
  | Term.mul t₁ t₂    => freeVars t₁ ∪ freeVars t₂
  | Term.eq t₁ t₂     => freeVars t₁ ∪ freeVars t₂
  | Term.and t₁ t₂    => freeVars t₁ ∪ freeVars t₂
  | Term.or t₁ t₂     => freeVars t₁ ∪ freeVars t₂
  | Term.not t        => freeVars t
  | Term.ifz c t₁ t₂  => freeVars c ∪ freeVars t₁ ∪ freeVars t₂
  | Term.lett x t₁ t₂ => freeVars t₁ ∪ (freeVars t₂ \ {x})
  | Term.assert t      => freeVars t
  | Term.inSet t _    => freeVars t
  | Term.seq t₁ t₂     => freeVars t₁ ∪ freeVars t₂

mutual
inductive Val (f : Type) [Field f] where
| Field   : f → Val f
| Bool    : Bool → Val f
| Unit   : Val f

structure Env (f : Type) [Field f] where
  lookup : String → Option (Val f)
end

def Env.insert {f : Type} [Field f] (x : String) (v : Val f) (ρ : Env f) : Env f :=
  { lookup := fun y => if x == y then some v else ρ.lookup y }

def wellScoped {f} [Field f] (t : Term f) (env : Env f) : Prop :=
  ∀ x ∈ freeVars t, ∃ v, env.lookup x = some v ∧ v ≠ Val.Unit

notation "<{" e:100 "}>" => e
infixl:99 " + " => Term.add
infixl:99 " * " => Term.mul
infixl:99 " - " => Term.sub
infixl:99 " == " => Term.eq
infixl:99 " && " => Term.and
infixl:99 " || " => Term.or
prefix:100 "!" => Term.not
notation "if" t₁ " then " t₂ " else " t₃ => Term.ifz t₁ t₂ t₃
infixl:99 " ; " => Term.seq
infixl:99 " inn " => Term.inSet
prefix:100 "assert " => Term.assert
notation "let " x " := " t " in " b => Term.lett x t b
