import Mathlib.Algebra.Field.Defs
import «ZkLeanCompiler».AST
import «ZkLeanCompiler».Builder
import «ZkLeanCompiler».LCSyntax

class JoltField (f : Type) extends Field f, BEq f, LawfulBEq f, ToString f, Inhabited f, Witnessable f (ZKExpr f), Hashable f

inductive Value (f: Type) [JoltField f] where
  | VBool : Bool -> Value f
  | VField : f -> Value f
  | None : Value f
deriving Inhabited, BEq

instance {f} [ToString f] [JoltField f] : ToString (Value f) where
  toString
    | Value.VBool b  => toString b
    | Value.VField x => toString x
    | Value.None     => "⊥"

def Val.toValue [JoltField f] : Val f → Value f
  | Val.Field x => Value.VField x
  | Val.Bool b  => Value.VField (if b then 1 else 0)

def semantics_zkexpr [JoltField f] (exprs: ZKExpr f) (witness: List f) : Value f :=
  let rec eval (e: ZKExpr f) : Value f :=
    match e with
    | ZKExpr.Literal lit => Value.VField lit
    | ZKExpr.WitnessVar id =>
      if id < witness.length
      then Value.VField (witness[id]!)
      else Value.None
    | ZKExpr.Add lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb => Value.VField (va + vb)
      | _, _ => Value.None
    | ZKExpr.Sub lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb => Value.VField (va - vb)
      | _, _ => Value.None
    | ZKExpr.Neg rhs =>
      let a := eval rhs
      match a with
      | Value.VField va => Value.VField (-va)
      | _ => Value.None
    | ZKExpr.Mul lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb => Value.VField (va * vb)
      | _, _ => Value.None
    | ZKExpr.Eq lhs rhs  =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb =>
        let b: Bool := va == vb
        Value.VBool b
      | _, _ => Value.None
    | ZKExpr.Lookup table arg1 arg2 =>
      let a := eval arg1
      let b := eval arg2
      match a,b with
      | Value.VField va, Value.VField vb =>
        let h : Even 16 := by
          exact (Even.add_self 8)
        Value.VField (evalComposedLookupTableArgs h table va vb)
      | _, _ => Value.None
  eval exprs

/-
A relational version of the operational semantics
-/
inductive ZKEval [JoltField f] : List f → ZKExpr f → Value f → Prop
| lit {witness} : ∀ (v : f), ZKEval witness (ZKExpr.Literal v) (Value.VField v)
| witvar {witness} : ∀ (id : ℕ),
  id < witness.length →
  ZKEval witness (ZKExpr.WitnessVar id) (Value.VField (witness[id]!))
| add {witness} : ∀ (lt rt : ZKExpr f) (a b : f),
  ZKEval witness lt (Value.VField a) →
  ZKEval witness rt (Value.VField b) →
  ZKEval witness (ZKExpr.Add lt rt) (Value.VField (a + b))
| sub {witness} : ∀ (lt rt : ZKExpr f) (a b : f),
  ZKEval witness lt (Value.VField a) →
  ZKEval witness rt (Value.VField b) →
  ZKEval witness (ZKExpr.Sub lt rt) (Value.VField (a - b))
| neg {witness} : ∀ (e : ZKExpr f) (a : f),
  ZKEval witness e (Value.VField a) →
  ZKEval witness (ZKExpr.Neg e) (Value.VField (- a))
| mul {witness} : ∀ (lt rt : ZKExpr f) (a b : f),
  ZKEval witness lt (Value.VField a) →
  ZKEval witness rt (Value.VField b) →
  ZKEval witness (ZKExpr.Mul lt rt) (Value.VField (a * b))
| eq {witness} : ∀ (lt rt : ZKExpr f) (a b : f),
  ZKEval witness lt (Value.VField a) →
  ZKEval witness rt (Value.VField b) →
  ZKEval witness (ZKExpr.Eq lt rt) (Value.VBool (a == b))
| lookup {witness va vb} : ∀ (table : ComposedLookupTable f 16 4) (arg1 arg2 : ZKExpr f),
  ZKEval witness arg1 (Value.VField va) →
  ZKEval witness arg2 (Value.VField vb) →
  ZKEval witness (ZKExpr.Lookup table arg1 arg2) (Value.VField (evalComposedLookupTableArgs (Even.add_self 8) table va vb))

def constraints_semantics [JoltField f] (constraints: List (ZKExpr f)) (witness: List f) : Bool :=
  match constraints with
  | [] => true
  | c :: cs =>
    let sem_c := semantics_zkexpr c witness
    match sem_c with
    | Value.VBool b =>
      if b
      then constraints_semantics cs witness
      else false
    | _ => false

inductive ConstraintsSatisfied [JoltField f]
  : List (ZKExpr f) → List f → Prop
| nil  {w} :
    ConstraintsSatisfied [] w
| cons {c cs w} :
    ZKEval w c (Value.VBool true) →
    ConstraintsSatisfied cs w →
    ConstraintsSatisfied (c :: cs) w

open Classical

noncomputable def constraints_semantics'
    [JoltField f]
    (cs : List (ZKExpr f))
    (w  : List f) : Bool :=
  decide (ConstraintsSatisfied cs w)
