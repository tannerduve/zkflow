import Std.Data.HashMap.Basic
import «ZkLeanCompiler».AST

structure ZKBuilderState (f : Type) where
  -- environment: Std.HashMap Ident (ZKExpr f)
  allocated_witness_count: Nat
  constraints: List (ZKExpr f)
deriving instance Inhabited for ZKBuilderState


  -- TODO: environment? AST?

-- ZKRepr ??
-- ZKRepr Jolt u32 = F128p

-- TODO: Make this a free monad?
def ZKBuilder (f:Type) := StateM (ZKBuilderState f)

-- given a type α we'd get (ZkBuilder f) α : (ZkBuilderState f) -> (α, ZkBuilderState f)
-- explanation: one can read the current state and return a value and the new state

instance: Monad (ZKBuilder f) where
  pure := StateT.pure
  bind := StateT.bind

-- structure ZKBuilder (a: Type) where
--   runBuilder: ZKBuilderState -> (a, ZKBuilderState)

-- instance : Monad ZKBuilder where
--   pure _x :=
--     {
--       environment := Std.HashMap.empty,
--     } -- TODO
--   bind _opt _next :=
--     {
--       environment := Std.HashMap.empty,
--     } -- TODO

def witnessf : ZKBuilder f (ZKExpr f) := do
  /-let old_count <- StateT.modifyGet
    (fun old_state =>
      let (p :Nat) := old_state.allocated_wire_count
      (p, {old_state with allocated_wire_count := p + 1 })
    )
    -/
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
