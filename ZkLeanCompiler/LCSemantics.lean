import «ZkLeanCompiler».LCSyntax
import Mathlib.Data.Nat.Basic
open Nat

-- Helper for deciding equality in the big step semantics
def eqVal {f : Type} [Field f] [BEq f] : Val f → Val f → Bool
  | Val.Field n1, Val.Field n2 => n1 == n2
  | Val.Bool b1, Val.Bool b2 => b1 == b2
  | _, _ => false

/-
Big step semantics of our expression language.
The semantics is defined as a relation `Eval` that takes a term, an environment, and a value.
The relation holds if the term evaluates to the value in the given environment.
-/
inductive Eval (f : Type) [Field f] [BEq f] : Term f → Env f → Val f → Prop
| var : ∀ (env : Env f) (x : String) (v : Val f),
    env.lookup x = some v →
    Eval f (Term.var x) env v
| lit : ∀ (env : Env f) (n : f),
    Eval f (Term.lit n) env (Val.Field n)
| bool : ∀ (env : Env f) (b : Bool),
    Eval f (Term.bool b) env (Val.Bool b)
| add : ∀ (env : Env f) (t1 t2 : Term f) (n1 n2 : f),
    Eval f t1 env (Val.Field n1) →
    Eval f t2 env (Val.Field n2) →
    Eval f (t1 ⊕ t2) env (Val.Field (n1 + n2))
| sub : ∀ (env : Env f) (t1 t2 : Term f) (n1 n2 : f),
    Eval f t1 env (Val.Field n1) →
    Eval f t2 env (Val.Field n2) →
    Eval f (t1 - t2) env (Val.Field (n1 - n2))
| mul : ∀ (env : Env f) (t1 t2 : Term f) (n1 n2 : f),
    Eval f t1 env (Val.Field n1) →
    Eval f t2 env (Val.Field n2) →
    Eval f (t1 ⊗ t2) env (Val.Field (n1 * n2))
| eq : ∀ (env : Env f) (t1 t2 : Term f) (v1 v2 : Val f),
    Eval f t1 env v1 →
    Eval f t2 env v2 →
    Eval f (t1 =-= t2) env (Val.Bool (eqVal v1 v2))
| and : ∀ (env : Env f) (t1 t2 : Term f) (b1 b2 : Bool),
    Eval f t1 env (Val.Bool b1) →
    Eval f t2 env (Val.Bool b2) →
    Eval f (t1 && t2) env (Val.Bool (b1 && b2))
| or : ∀ (env : Env f) (t1 t2 : Term f) (b1 b2 : Bool),
    Eval f t1 env (Val.Bool b1) →
    Eval f t2 env (Val.Bool b2) →
    Eval f (t1 || t2) env (Val.Bool (b1 || b2))
| not : ∀ (env : Env f) (t : Term f) (b : Bool),
    Eval f t env (Val.Bool b) →
    Eval f (∼t) env (Val.Bool (!b))
| lett : ∀ (env env' : Env f) (x : String) (t₁ t₂ : Term f) (v : Val f) (v' : Val f),
    Eval f t₁ env v →
    env' = Env.insert x v env →
    Eval f t₂ env' v' →
    Eval f (Term.lett x t₁ t₂) env v'
| ifz_true : ∀ (env : Env f) (t₁ t₂ t₃ : Term f) (v : Val f),
    Eval f t₁ env (Val.Bool true) →
    Eval f t₂ env v →
    Eval f (ifz t₁ then t₂ else t₃) env v
| ifz_false : ∀ (env : Env f) (t₁ t₂ t₃ : Term f) (v : Val f),
    Eval f t₁ env (Val.Bool false) →
    Eval f t₃ env v →
    Eval f (ifz t₁ then t₂ else t₃) env v
| assert : ∀ (env : Env f) (t : Term f),
    Eval f t env (Val.Bool true) →
    Eval f (Term.assert t) env (Val.Unit)
-- | hash1 : ∀ (env : Env f) (t : Term f) (v : f),
--     Eval f t env (Val.Field v) →
--     Eval f (#t) env (Val.Field (unaryhashFn v))
-- | hash2 : ∀ (env : Env f) (t1 t2 : Term f) (v1 v2 : f),
--     Eval f t1 env (Val.Field v1) →
--     Eval f t2 env (Val.Field v2) →
--     Eval f (t1 ## t2) env (Val.Field (binaryhashFn v1 v2))
| inSet_true : ∀ (env : Env f) (t : Term f) (ts : List f) (x : f),
    Eval f t env (Val.Field x) →
    x ∈ ts →
    Eval f (t inn ts) env (Val.Bool true)
| inSet_false : ∀ (env : Env f) (t : Term f) (ts : List f) (x : f),
    Eval f t env (Val.Field x) →
    x ∉ ts →
    Eval f (t inn ts) env (Val.Bool false)
| seq : ∀ (env : Env f) (t1 t2 : Term f) (v : Val f),
    Eval f t1 env (Val.Unit) →
    Eval f t2 env v →
    Eval f (t1 ; t2) env v
