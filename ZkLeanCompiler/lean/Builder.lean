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
| GetEnv : ZKOp f (Std.HashMap String (ZKExpr f))
| PutEnv (ρ : Std.HashMap String (ZKExpr f)) : ZKOp f PUnit

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

def getEnv : ZKBuilder f (Std.HashMap String (ZKExpr f)) :=
  FreeM.lift ZKOp.GetEnv

def putEnv (ρ : Std.HashMap String (ZKExpr f)) : ZKBuilder f PUnit :=
  FreeM.lift (ZKOp.PutEnv ρ)

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
  | ZKOp.GetEnv => do
      let st ← get
      pure st.env
  | ZKOp.PutEnv ρ => do
      let st ← get
      set { st with env := ρ }
      pure ()

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
  | _, (ZKOp.GetEnv), k =>
      fun st =>
        k st.env st
  | _, (ZKOp.PutEnv ρ), k =>
      fun st =>
        k () { st with env := ρ }

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

structure WitnessState (f : Type) where
  builder : ZKBuilderState f
  values : List f
deriving Inhabited

/-- Initial empty witness state -/
def initialWitnessState : WitnessState f :=
  { builder := initialZKBuilderState, values := [] }

/-- Interpreter that, while interpreting the `ZKOp`s, also records default witness
    values so that the final state contains a satisfying witness vector. -/
@[inline]
def zkOpInterpWitness [Zero f] {β} [Inhabited f] : ZKOp f β → StateM (WitnessState f) β
  | ZKOp.AllocWitness => do
      let s ← get
      let idx := s.builder.allocated_witness_count
      let defaultVal : f := default
      let s' : WitnessState f := {
        builder := { s.builder with allocated_witness_count := idx + 1 },
        values := s.values ++ [defaultVal]
      }
      set s'
      pure (ZKExpr.WitnessVar idx)
  | ZKOp.ConstrainEq x y => do
      let s ← get
      let s' : WitnessState f := {
        s with builder := { s.builder with constraints := ZKExpr.Eq x y :: s.builder.constraints } }
      set s'
      pure ()
  | ZKOp.ConstrainR1CS a b c => do
      let s ← get
      let s' : WitnessState f := {
        s with builder := { s.builder with constraints := ZKExpr.Eq (ZKExpr.Mul a b) c :: s.builder.constraints } }
      set s'
      pure ()
  | ZKOp.Lookup _ _ => do
      let s ← get
      let idx := s.builder.allocated_witness_count
      let defaultVal : f := default
      let s' : WitnessState f := {
        builder := { s.builder with allocated_witness_count := idx + 1 },
        values := s.values ++ [defaultVal]
      }
      set s'
      pure (ZKExpr.WitnessVar idx)
  | ZKOp.GetEnv => do
      let s ← get
      pure s.builder.env
  | ZKOp.PutEnv ρ => do
      let s ← get
      set { s with builder := { s.builder with env := ρ } }
      pure ()
/-- Pure case for the witness catamorphism. -/
@[inline]
def builderPureW [Zero f] {α} (a : α) : WitnessState f → (α × WitnessState f) :=
  fun s => (a, s)

/-- Step case: interpret one `ZKOp` and continue folding, threading the witness state. -/
@[inline]
def builderStepW [Zero f] [Inhabited f] {α}
    : {ι : Type} → ZKOp f ι → (ι → WitnessState f → (α × WitnessState f)) →
      WitnessState f → (α × WitnessState f)
  | _, ZKOp.AllocWitness, k =>
      fun s =>
        let idx := s.builder.allocated_witness_count
        let defaultVal : f := default
        let s' : WitnessState f := {
          builder := { s.builder with allocated_witness_count := idx + 1 },
          values  := s.values ++ [defaultVal]
        }
        k (ZKExpr.WitnessVar idx) s'
  | _, (ZKOp.ConstrainEq x y), k =>
      fun s =>
        let s' : WitnessState f := {
          s with builder := { s.builder with constraints := ZKExpr.Eq x y :: s.builder.constraints } }
        k () s'
  | _, (ZKOp.ConstrainR1CS a b c), k =>
      fun s =>
        let s' : WitnessState f := {
          s with builder := { s.builder with constraints := ZKExpr.Eq (ZKExpr.Mul a b) c :: s.builder.constraints } }
        k () s'
  | _, (ZKOp.Lookup _ _), k =>
      fun s =>
        let idx := s.builder.allocated_witness_count
        let defaultVal : f := default
        let s' : WitnessState f := {
          builder := { s.builder with allocated_witness_count := idx + 1 },
          values  := s.values ++ [defaultVal]
        }
        k (ZKExpr.WitnessVar idx) s'
  | _, (ZKOp.GetEnv), k =>
      fun s =>
        k s.builder.env s
  | _, (ZKOp.PutEnv ρ), k =>
      fun s =>
        k () { s with builder := { s.builder with env := ρ } }

/-- Catamorphic fold that produces both the compiled circuit and a witness skeleton. -/
@[inline]
def runWithWitness [Zero f] [Inhabited f] (p : ZKBuilder f α) : (α × WitnessState f) :=
  FreeM.cataFreeM builderPureW builderStepW p initialWitnessState
