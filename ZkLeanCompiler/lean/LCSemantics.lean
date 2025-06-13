import «ZkLeanCompiler».Lean.LCSyntax
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
| arith : ∀ (env : Env f) (op : ArithBinOp) (t₁ t₂ : Term f) (n₁ n₂ : f),
    Eval f t₁ env (Val.Field n₁) →
    Eval f t₂ env (Val.Field n₂) →
    Eval f (Term.arith op t₁ t₂) env (Val.Field (
      match op with
      | .add => n₁ + n₂
      | .sub => n₁ - n₂
      | .mul => n₁ * n₂))
| boolB : ∀ (env : Env f) (op : BoolBinOp) (t₁ t₂ : Term f) (b₁ b₂ : Bool),
    Eval f t₁ env (Val.Bool b₁) →
    Eval f t₂ env (Val.Bool b₂) →
    Eval f (Term.boolB op t₁ t₂) env (Val.Bool (
      match op with
      | .and => b₁ && b₂
      | .or  => b₁ || b₂))
| eq : ∀ (env : Env f) (t₁ t₂ : Term f) (v₁ v₂ : Val f),
    Eval f t₁ env v₁ →
    Eval f t₂ env v₂ →
    Eval f (t₁ =-= t₂) env (Val.Bool (eqVal v₁ v₂))
| not : ∀ (env : Env f) (t : Term f) (b : Bool),
    Eval f t env (Val.Bool b) →
    Eval f (~t) env (Val.Bool (!b))
| lett : ∀ (env env' : Env f) (x : String) (t₁ t₂ : Term f) (v : Val f) (v' : Val f),
    Eval f t₁ env v →
    env' = Env.insert x v env →
    Eval f t₂ env' v' →
    Eval f (Term.lett x t₁ t₂) env v'
| ifz_true : ∀ (env : Env f) (t₁ t₂ t₃ : Term f) (v : Val f),
    Eval f t₁ env (Val.Bool true) →
    Eval f t₂ env v →
    Eval f (ifz` t₁ then` t₂ else` t₃) env v
| ifz_false : ∀ (env : Env f) (t₁ t₂ t₃ : Term f) (v : Val f),
    Eval f t₁ env (Val.Bool false) →
    Eval f t₃ env v →
    Eval f (ifz` t₁ then` t₂ else` t₃) env v
| assert : ∀ (env : Env f) (t₁ t₂ : Term f) (v : Val f),
    Eval f t₁ env (Val.Bool true) →
    Eval f t₂ env v →
    Eval f (Term.assert t₁ t₂) env v
| inSet_true : ∀ (env : Env f) (t : Term f) (ts : List f) (x : f),
    Eval f t env (Val.Field x) →
    x ∈ ts →
    Eval f (t inn ts) env (Val.Bool true)
| inSet_false : ∀ (env : Env f) (t : Term f) (ts : List f) (x : f),
    Eval f t env (Val.Field x) →
    x ∉ ts →
    Eval f (t inn ts) env (Val.Bool false)
| seq : ∀ (env : Env f) (t₁ t₂ : Term f) (v v' : Val f),
    Eval f t₁ env v' →
    Eval f t₂ env v →
    Eval f (t₁ ; t₂) env v

/-
A functional version of our operational semantics
-/
def eval {f} [Field f] [BEq f] [DecidableEq f] : Term f → Env f → Option (Val f)
| Term.var x, env =>
  match env.lookup x with
  | some (Val.Bool b)  => some (Val.Bool b)
  | other              => other
| Term.lit n, _ =>
  some (Val.Field n)
| Term.bool b, _ =>
  some (Val.Bool b)
| Term.arith op t₁ t₂, env =>
  match op with
  | ArithBinOp.add =>
    match eval t₁ env, eval t₂ env with
    | some (Val.Field n₁), some (Val.Field n₂) => some (Val.Field (n₁ + n₂))
    | _, _ => none
  | ArithBinOp.sub =>
    match eval t₁ env, eval t₂ env with
    | some (Val.Field n₁), some (Val.Field n₂) => some (Val.Field (n₁ - n₂))
    | _, _ => none
  | ArithBinOp.mul =>
    match eval t₁ env, eval t₂ env with
    | some (Val.Field n₁), some (Val.Field n₂) => some (Val.Field (n₁ * n₂))
    | _, _ => none
| Term.boolB op t₁ t₂, env =>
  match op with
  | BoolBinOp.and =>
    match eval t₁ env, eval t₂ env with
    | some (Val.Bool b₁), some (Val.Bool b₂) => some (Val.Bool (b₁ && b₂))
    | _, _ => none
  | BoolBinOp.or  =>
    match eval t₁ env, eval t₂ env with
    | some (Val.Bool b₁), some (Val.Bool b₂) => some (Val.Bool (b₁ || b₂))
    | _, _ => none
| Term.eq t₁ t₂, env =>
  match eval t₁ env, eval t₂ env with
  | some v₁, some v₂ => some (Val.Bool (eqVal v₁ v₂))
  | _, _ => none
| Term.not t, env =>
  match eval t env with
  | some (Val.Bool b) => some (Val.Bool (!b))
  | _ => none
| Term.ifz c t₁ t₂, env =>
  match eval c env with
  | some (Val.Field n) =>
      if n ≠ 0 then eval t₁ env else eval t₂ env
  | _ => none
| Term.lett x t₁ t₂, env =>
  match eval t₁ env with
  | some v =>
    let env' := env.insert x v
    eval t₂ env'
  | _ => none
| Term.assert t₁ t₂, env =>
  match eval t₁ env with
  | some (Val.Bool true) => eval t₂ env
  | some (Val.Bool false) => none
  | _ => none
| Term.inSet t ts, env =>
  match eval t env with
  | some (Val.Field x) => some (Val.Bool (x ∈ ts.toFinset))
  | _ => none
| Term.seq t₁ t₂, env =>
  match eval t₁ env, eval t₂ env with
  | some _, some v₂ => some v₂
  | _, _ => none
