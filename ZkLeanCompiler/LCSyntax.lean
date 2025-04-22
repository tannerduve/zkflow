import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Field.Defs
open Nat
open Std



inductive Term (f : Type u) [Field f] where
| var : String → Term f
| lit : f → Term f
| bool : Bool → Term f
| lam : String → Term f → Term f
| app : Term f → Term f → Term f
| add : Term f → Term f → Term f
| mul : Term f → Term f → Term f
| sub : Term f → Term f → Term f
| hash : Term f → Term f
| eq  : Term f → Term f → Term f
| ifz : Term f → Term f → Term f → Term f
deriving Inhabited, BEq, Hashable

mutual
inductive Val (f : Type) [Field f] where
| Field     : f → Val f
| Bool    : Bool → Val f
| Closure : Term f → Env f → Val f

structure Env (f : Type) [Field f] where
  lookup : String → Option (Val f)
end

def Env.insert {f : Type} [Field f] (x : String) (v : Val f) (ρ : Env f) : Env f :=
  { lookup := fun y => if x == y then some v else ρ.lookup y }

notation "<{" e:99 "}>" => e
notation "λ" x ", " y => Term.lam x y
infixl:99 " ∘ " => Term.app
infixl:99 " ⊕ " => Term.add
infixl:99 " ⊗ " => Term.mul
infixl:99 " ∼ " => Term.sub
infixl:99 " =-= " => Term.eq
notation "ifz" t₁ " then " t₂ " else " t₃ => Term.ifz t₁ t₂ t₃
notation "⟨" t ", " ρ "⟩" => Val.Closure t ρ
prefix:100 "#" => Term.hash
