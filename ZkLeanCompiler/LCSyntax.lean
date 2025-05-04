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
inductive ArithBinOp where
| add | sub | mul
deriving Inhabited, BEq, Repr
inductive BoolBinOp where
| and | or
deriving Inhabited, BEq, Repr

inductive Term (f : Type u) [Field f] where
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
deriving Inhabited, BEq

/-
Function to compute the free variables of a term.
-/
def freeVars {f} [Field f] : Term f → Finset String
  | .var x          => {x}
  | .lit _ | .bool _ => ∅
  | .arith _ t₁ t₂ => freeVars t₁ ∪ freeVars t₂
  | .boolB _ t₁ t₂ => freeVars t₁ ∪ freeVars t₂
  | .seq  t₁ t₂     => freeVars t₁ ∪ freeVars t₂
  | .eq   t₁ t₂     => freeVars t₁ ∪ freeVars t₂
  | .not t          => freeVars t
  | .ifz c t₁ t₂    => freeVars c ∪ freeVars t₁ ∪ freeVars t₂
  | .lett x t₁ t₂   => freeVars t₁ ∪ (freeVars t₂ \ {x})
  | .assert t₁ t₂      => freeVars t₁ ∪ freeVars t₂
  | .inSet t _      => freeVars t

mutual
/--
The values of our expression language.
The values are either field elements, booleans, or unit.
Unit is used to represent the absence of a value, for example assert should execute without returning a value.
-/
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
