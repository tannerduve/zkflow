import Std.Data.HashMap.Basic
import «ZkLeanCompiler».AST
import Mathlib.Tactic.Cases

structure ZKBuilderState (f : Type) where
  allocated_witness_count: Nat
  constraints: List (ZKExpr f)
  env : Std.HashMap String (ZKExpr f)
deriving instance Inhabited for ZKBuilderState

def initialZKBuilderState : ZKBuilderState f :=
  { allocated_witness_count := 0,
    constraints := [],
    env := ∅ }

-- ZKRepr ??
-- ZKRepr Jolt u32 = F128p

inductive Free (f : Type -> Type) (a : Type) where
| pure : a -> Free f a
| bind : ∀ x, f x -> (x -> Free f a) -> Free f a

def Free.map {α β : Type} (F : Type → Type) (f : α → β) : Free F α → Free F β :=
λ FFa =>
match FFa with
| pure a => Free.pure (f a)
| bind X Fx k => Free.bind X Fx (λ z => map F f (k z))

instance : Functor (Free F) where
map := Free.map F

def bindFree {a b : Type} (F : Type → Type) (x : Free F a) (f : a → Free F b) : Free F b :=
match x with
| .pure a => f a
| .bind X Fx k => .bind X Fx (λ z => bindFree F (k z) f)

instance FreeMonad (F : Type → Type) : Monad (Free F) where
  pure := Free.pure
  bind := bindFree F

/-- Primitive instructions for the circuit DSL - the effect 'functor'. -/
inductive ZKOp (f : Type) : Type → Type
| AllocWitness                         : ZKOp f (ZKExpr f)
| ConstrainEq    (x y    : ZKExpr f)   : ZKOp f PUnit
| ConstrainR1CS  (a b c  : ZKExpr f)   : ZKOp f PUnit
| Lookup         (tbl    : ComposedLookupTable f 16 4)
                 (args   : Vector (ZKExpr f) 4)        : ZKOp f (ZKExpr f)

/-- Type for the ZK circuit builder monad. -/
def ZKBuilder (f : Type) := Free (ZKOp f)

instance : Monad (ZKBuilder f) :=
  FreeMonad (ZKOp f)

/-- Provide a `Zero` instance for `ZKExpr`. -/
instance [Zero f] : Zero (ZKExpr f) where
  zero := ZKExpr.Literal 0

namespace ZKBuilder

def witness     : ZKBuilder f (ZKExpr f) :=
  .bind _ (ZKOp.AllocWitness) .pure

def constrainEq (x y : ZKExpr f) : ZKBuilder f PUnit :=
  .bind _ (ZKOp.ConstrainEq x y) .pure

def constrainR1CS (a b c : ZKExpr f) : ZKBuilder f PUnit :=
  .bind _ (ZKOp.ConstrainR1CS a b c) .pure

def lookup (tbl : ComposedLookupTable f 16 4)
           (v   : Vector (ZKExpr f) 4) : ZKBuilder f (ZKExpr f) :=
  .bind _ (ZKOp.Lookup tbl v) .pure

end ZKBuilder

open ZKBuilder

class Witnessable (f: Type) (t: Type) where
  /-- Witness a new `t` in circuit. -/
  witness : ZKBuilder f t

/-- Algebra that *executes* one primitive, updating the state. -/
def buildAlg [Zero f] {β} (op : ZKOp f β) (st : ZKBuilderState f) : (β × ZKBuilderState f) :=
  match op with
  | ZKOp.AllocWitness =>
      let idx := st.allocated_witness_count
      (ZKExpr.WitnessVar idx, { st with allocated_witness_count := idx + 1 })
  | ZKOp.ConstrainEq x y =>
      ((), { st with constraints := (ZKExpr.Eq x y) :: st.constraints })
  | ZKOp.ConstrainR1CS a b c =>
      ((), { st with constraints := (ZKExpr.Eq (ZKExpr.Mul a b) c) :: st.constraints })
  | ZKOp.Lookup tbl args =>
      (ZKExpr.Lookup tbl (args.get 0) (args.get 1), st)

/-- Run a `ZKBuilder` program, producing its result and the final state. -/
def run [Zero f] (p : ZKBuilder f α) (st : ZKBuilderState f)
    : (α × ZKBuilderState f) :=
  match p with
  | .pure a        => (a, st)
  | .bind _ op k   =>
      let (b, st') := buildAlg op st
      run (k b) st'

instance : Witnessable f (ZKExpr f) where
  witness := ZKBuilder.witness   -- smart constructor, pure DSL

instance [Witnessable f a] : Witnessable f (Vector a n) where
  witness :=
    let rec go : (m : Nat) → ZKBuilder f (Vector a m)
      | 0 => pure (Vector.emptyWithCapacity 0)
      | Nat.succ m => do
          let w ← Witnessable.witness
          let v ← go m
          pure (Vector.push v w)
    go n
