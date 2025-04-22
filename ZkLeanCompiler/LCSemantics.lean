import «ZkLeanCompiler».LCSyntax
import Mathlib.Data.Nat.Basic
open Nat


-- Dummy hash function
def hashFn [Field f] (x : f) : f :=
  x ^ 3 + 42  -- dummy field hash function

-- Helper for deciding equality in the big step semantics
def eqVal {f : Type} [Field f] [BEq f] : Val f → Val f → Bool
  | Val.Field n1, Val.Field n2 => n1 == n2
  | Val.Bool b1, Val.Bool b2 => b1 == b2
  | _, _ => false

/-
Big step semantics of our lambda calculus
-/
inductive Eval (f : Type) [Field f] [BEq f] : Term f → Env f → Val f → Prop
| var : ∀ (env : Env f) (x : String) (v : Val f),
    env.lookup x = some v →
    Eval f (Term.var x) env v
| nat : ∀ (env : Env f) (n : ℕ),
    Eval f (Term.lit n) env (Val.Field n)
| bool : ∀ (env : Env f) (b : Bool),
    Eval f (Term.bool b) env (Val.Bool b)
| lam : ∀ (env : Env f) (x : String) (t : Term f),
    Eval f (<{λ x, y}>) env (Val.Closure t env)
| app {t1} : ∀ (env env' : Env f) (x : String) (t_body t2 : Term f) (v : Val f),
    Eval f t1 env (Val.Closure (Term.lam x t_body) env') →
    Eval f t2 env v →
    Eval f t_body (Env.insert x v env') v →
    Eval f (t1 ∘ t2) env v
| add : ∀ (env : Env f) (t1 t2 : Term f) (n1 n2 : ℕ),
    Eval f t1 env (Val.Field n1) →
    Eval f t2 env (Val.Field n2) →
    Eval f (t1 ⊕ t2) env (Val.Field (n1 + n2))
| sub : ∀ (env : Env f) (t1 t2 : Term f) (n1 n2 : ℕ),
    Eval f t1 env (Val.Field n1) →
    Eval f t2 env (Val.Field n2) →
    Eval f (t1 ∼ t2) env (Val.Field (n1 - n2))
| mul : ∀ (env : Env f) (t1 t2 : Term f) (n1 n2 : ℕ),
    Eval f t1 env (Val.Field n1) →
    Eval f t2 env (Val.Field n2) →
    Eval f (t1 ⊗ t2) env (Val.Field (n1 * n2))
| hash : ∀ (env : Env f) (t : Term f) (n : ℕ),
    Eval f t env (Val.Field n) →
    Eval f (#t1) env (Val.Field (hashFn n))
| eq : ∀ (env : Env f) (t1 t2 : Term f) (v1 v2 : Val f),
    Eval f t1 env v1 →
    Eval f t2 env v2 →
    Eval f (t1 =-= t2) env (Val.Bool (eqVal v1 v2))
| ifz_true : ∀ (env : Env f) (t₁ t₂ t₃ : Term f) (v : Val f),
    Eval f t₁ env (Val.Bool true) →
    Eval f t₂ env v →
    Eval f (<{ifz t₁ then t₂ else t₃}>) env v
| ifz_false : ∀ (env : Env f) (t₁ t₂ t₃ : Term f) (v : Val f),
    Eval f t₁ env (Val.Bool false) →
    Eval f t₃ env v →
    Eval f (<{ifz t₁ then t₂ else t₃}>) env v
