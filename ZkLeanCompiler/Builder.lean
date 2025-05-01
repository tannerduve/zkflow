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

-- TODO: Make this a free monad?
def ZKBuilder (f:Type) := StateM (ZKBuilderState f)

-- Free Monad
inductive Free (f : Type u → Type v) (α : Type) where
  | pure : α → Free f α
  | bind : ∀ x, f x -> (x -> Free f α) → Free f α

def map {α β : Type} (func : Type u → Type v) (f : α → β) : Free func α → Free func β := λ x =>
  match x with
  | Free.pure a => Free.pure (f a)
  | Free.bind x y k => Free.bind x y (λ a => map func f (k a))

instance (f : Type u → Type v) : Functor (Free f) where
  map := map f

def bindFree {α β : Type} (f : Type u → Type v): (Free f α) → (α → Free f β) → Free f β :=
  λ x k =>
    match x with
    | Free.pure a => k a
    | Free.bind x y k' => Free.bind x y (λ a => bindFree f (k' a) k)

instance (f : Type u → Type v) : Monad (Free f) where
  pure := Free.pure
  bind := bindFree f

-- instance : LawfulMonad (Free f) where
--   pure_bind := by
--     intros α β x f'
--     simp [bind, bindFree]
--   bind_map := by
--     intros α β x f'
--     simp [bind, Seq.seq]
--   bind_pure_comp := by
--     intros α β x f'
--     simp [bind, pure, Functor.map]
--     unfold bindFree
--     induction' f' with a X a' alg ih
--     · case pure => simp [bindFree, map]
--     · simp [bindFree, map]
--       apply funext
--       intro x₁
--       specialize ih x₁
--       induction h : alg x₁ with
--         | pure a =>
--           simp [bindFree, map, h]
--         | bind X fx k' a_ih =>
--           simp [bindFree, map, h]
--           funext a
--           specialize a_ih a
--           simp [h, map] at ih
--           rw [← congr_fun ih a]
--   bind_assoc := by sorry
--   map_pure := by
--     intros α β x f'
--     simp [Functor.map, map, pure]
--   seq_pure := by
--     intro α β g x
--     simp [Seq.seq, Functor.map]
--     unfold bindFree
--     induction' g with a X a' alg ih
--     · case pure => simp [bindFree, map]
--     · case bind =>
--       simp [bindFree, map]
--       apply funext
--       intro x₁
--       specialize ih x₁
--       induction h : alg x₁ with
--         | pure a =>
--           simp [bindFree, map, h]
--         | bind X fx k' a_ih =>
--           simp [bindFree, map, h]
--           funext a
--           specialize a_ih a
--           simp [h, map] at ih
--           rw [← congr_fun ih a]
--   seq_assoc := by
--     intros α β γ g x y
--     simp [Seq.seq, Functor.map]
--     unfold bindFree
--     induction' y with a X a' alg ih
--     · case pure =>
--       simp [bindFree, map]
--       sorry
--     sorry

-- given a type α we'd get (ZkBuilder f) α = (ZkBuilderState f) -> (α, ZkBuilderState f)
-- explanation: one can read the current state and return a value and the new state


def ZKBuilderFree (α:Type) := Free (ZKBuilderState) α

instance : Monad ZKBuilderFree where
  pure := Free.pure
  bind := bindFree (ZKBuilderState)
  map := map (ZKBuilderState)

instance: Monad (ZKBuilder f) where
  pure := StateT.pure
  bind := StateT.bind

instance : MonadStateOf (ZKBuilderState f) (ZKBuilder f) where
  get := StateT.get
  set := StateT.set
  modifyGet := StateT.modifyGet

def witnessf : ZKBuilder f (ZKExpr f) := do
  let old_state <- StateT.get
  let old_count := old_state.allocated_witness_count
  let new_count := old_count +1
  StateT.set { old_state with allocated_witness_count := new_count}
  pure (ZKExpr.WitnessVar old_count)

-- A type is witnessable if it has an associated number of witnesses and
-- a function to recompose a type given a vector of values.
class Witnessable (f: Type) (t:Type) where
  witness : ZKBuilder f t

instance: Witnessable f (ZKExpr f) where
  witness := witnessf

instance [Witnessable f a]: Witnessable f (Vector a n) where
  witness :=
    let rec helper n : ZKBuilder f (Vector a n) :=
      match n with
      | 0 => pure (Vector.emptyWithCapacity 0)
      | m+1 => do
        let w <- Witnessable.witness
        let v <- helper m
        pure (Vector.push v w)
    do
      helper n

def constrain (constraint: ZKExpr f) : ZKBuilder f PUnit := do
  let old_state <- StateT.get
  StateT.set { old_state with constraints := constraint :: old_state.constraints }
  pure ()

def constrainEq (x: ZKExpr f) (y: ZKExpr f) : ZKBuilder f PUnit :=
  constrain (ZKExpr.Eq x y)

def constrainR1CS (a: ZKExpr f) (b: ZKExpr f) (c: ZKExpr f) : ZKBuilder f PUnit :=
  constrainEq (ZKExpr.Mul a b) c

def lookup (table : ComposedLookupTable f 16 4) (a: ZKExpr f) (b: ZKExpr f): ZKBuilder f (ZKExpr f) :=
  pure (ZKExpr.Lookup table a b)

class HasBitDecomposition (f : Type) (n : Nat) where
  bitDecompose : ZKExpr f → ZKBuilder f (Vector (ZKExpr f) n)
