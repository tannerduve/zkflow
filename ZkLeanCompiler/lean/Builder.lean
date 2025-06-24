import Std.Data.HashMap.Basic
import «ZkLeanCompiler».Lean.AST
import Mathlib.Tactic.Cases
import «ZkLeanCompiler».Lean.FreeMonad

structure ZKBuilderState (f : Type) where
  allocated_witness_count: Nat
  constraints: List (ZKExpr f)
  env : Std.HashMap String (ZKExpr f)
deriving instance Inhabited for ZKBuilderState

def initialZKBuilderState : ZKBuilderState f :=
  { allocated_witness_count := 0,
    constraints := [],
    env := ∅ }

/-- Primitive instructions for the circuit DSL - the effect 'functor'. -/
inductive ZKOp (f : Type) : Type → Type
| AllocWitness                         : ZKOp f (ZKExpr f)
| ConstrainEq    (x y    : ZKExpr f)   : ZKOp f PUnit
| ConstrainR1CS  (a b c  : ZKExpr f)   : ZKOp f PUnit
| Lookup : ComposedLookupTable f 16 4 → Array (ZKExpr f) → ZKOp f (ZKExpr f)

/-- Type for the ZK circuit builder monad. -/
def ZKBuilder (f : Type) := FreeM (ZKOp f)

instance : Monad (ZKBuilder f) := by
 unfold ZKBuilder
 infer_instance

instance : LawfulMonad (ZKBuilder f) := by
  unfold ZKBuilder
  infer_instance

/-- Provide a `Zero` instance for `ZKExpr`. -/
instance [Zero f] : Zero (ZKExpr f) where
  zero := ZKExpr.Literal 0

namespace ZKBuilder

def witness : ZKBuilder f (ZKExpr f) :=
  FreeM.lift ZKOp.AllocWitness

def constrainEq (x y : ZKExpr f) : ZKBuilder f PUnit :=
  FreeM.lift (ZKOp.ConstrainEq x y)

def constrainR1CS (a b c : ZKExpr f) : ZKBuilder f PUnit :=
  FreeM.lift (ZKOp.ConstrainR1CS a b c)

def lookup (tbl : ComposedLookupTable f 16 4)
           (args : Array (ZKExpr f)) : ZKBuilder f (ZKExpr f) :=
  FreeM.lift (ZKOp.Lookup tbl args)

end ZKBuilder

open ZKBuilder

class Witnessable (f: Type) (t: Type) where
  /-- Witness a new `t` in circuit. -/
  witness : ZKBuilder f t

/-- Interpreter that converts ZKOp operations to StateM operations -/
def zkOpInterp [Zero f] {β : Type} (op : ZKOp f β) : StateM (ZKBuilderState f) β :=
  match op with
  | ZKOp.AllocWitness => do
      let st ← get
      let idx := st.allocated_witness_count
      set { st with allocated_witness_count := idx + 1 }
      pure (ZKExpr.WitnessVar idx)
  | ZKOp.ConstrainEq x y => do
      let st ← get
      set { st with constraints := (ZKExpr.Eq x y) :: st.constraints }
      pure ()
  | ZKOp.ConstrainR1CS a b c => do
      let st ← get
      set { st with constraints := (ZKExpr.Eq (ZKExpr.Mul a b) c) :: st.constraints }
      pure ()
  | ZKOp.Lookup _ args => do
      let st ← get
      let idx := st.allocated_witness_count
      set { st with allocated_witness_count := idx + 1 }
      pure (ZKExpr.WitnessVar idx)

/-- Convert a `ZKBuilder` computation into a `StateM` computation. This is the canonical
interpreter derived from `mapM`. -/
def toStateM [Zero f] {α : Type} (comp : ZKBuilder f α) : StateM (ZKBuilderState f) α :=
  comp.mapM zkOpInterp

/-- Pure case of the algebra. -/
def builderPure [Zero f] {α} (a : α) : ZKBuilderState f → (α × ZKBuilderState f) :=
  fun st => (a, st)

/-
Bind case: interpret a primitive `ZKOp` and continue the catamorphism. The continuation `k`
already produces a result given the fresh value from the operation. -/
def builderStep [Zero f] {α} : {ι : Type} → ZKOp f ι → (ι → ZKBuilderState f → (α × ZKBuilderState f)) → ZKBuilderState f → (α × ZKBuilderState f)
  | _, ZKOp.AllocWitness, k =>
      fun st =>
        let idx := st.allocated_witness_count
        let st' := { st with allocated_witness_count := idx + 1 }
        k (ZKExpr.WitnessVar idx) st'
  | _, (ZKOp.ConstrainEq x y), k =>
      fun st =>
        let st' := { st with constraints := (ZKExpr.Eq x y) :: st.constraints }
        k () st'
  | _, (ZKOp.ConstrainR1CS a b c), k =>
      fun st =>
        let st' := { st with constraints := (ZKExpr.Eq (ZKExpr.Mul a b) c) :: st.constraints }
        k () st'
  | _, (ZKOp.Lookup _ _), k =>
      fun st =>
        let idx := st.allocated_witness_count
        let st' := { st with allocated_witness_count := idx + 1 }
        k (ZKExpr.WitnessVar idx) st'

/-- Run a `ZKBuilder` program, producing its result and the final state.
   Implemented via `cataFreeM`, i.e. a fold over the free-monad syntax tree. -/
def runFold [Zero f] (p : ZKBuilder f α) (st : ZKBuilderState f) : (α × ZKBuilderState f) :=
  FreeM.cataFreeM builderPure builderStep p st

instance : Witnessable f (ZKExpr f) where
  witness := ZKBuilder.witness   -- smart constructor, pure DSL

instance [Witnessable f a] : Witnessable f (Vector a n) where
  witness :=
    let rec go : (m : Nat) → ZKBuilder f (Vector a m)
      | 0 => pure (Vector.mkEmpty 0)
      | Nat.succ m => do
          let w ← Witnessable.witness
          let v ← go m
          pure (Vector.push v w)
    go n

def zkOpEval [Zero f] [Inhabited f] (op : ZKOp f β) : StateM (ZKBuilderState f × List f) β :=
  match op with
  | ZKOp.AllocWitness => do
      let (st, wvec) ← get
      let idx := st.allocated_witness_count
      let defaultVal : f := default
      let wvec' := wvec ++ [defaultVal]
      let st' := { st with allocated_witness_count := idx + 1 }
      set (st', wvec')
      pure (ZKExpr.WitnessVar idx)
  | ZKOp.ConstrainEq x y => do
      let (st, wvec) ← get
      let st' := { st with constraints := (ZKExpr.Eq x y) :: st.constraints }
      set (st', wvec)
      pure ()
  | ZKOp.ConstrainR1CS a b c => do
      let (st, wvec) ← get
      let st' := { st with constraints := (ZKExpr.Eq (ZKExpr.Mul a b) c) :: st.constraints }
      set (st', wvec)
      pure ()
  | ZKOp.Lookup _ _ => do
      let (st, wvec) ← get
      let idx := st.allocated_witness_count
      let defaultVal : f := default
      let wvec' := wvec ++ [defaultVal]
      let st' := { st with allocated_witness_count := idx + 1 }
      set (st', wvec')
      pure (ZKExpr.WitnessVar idx)
