import ZkLeanCompiler.Compile
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat

variable [Field F] [JoltField F]

open Term

instance : Coe Bool (Term ℚ) where
  coe b := Term.bool b

instance : Coe ℚ (Term ℚ) where
  coe q := Term.lit q

instance : OfNat (Term ℚ) n where
  ofNat := Term.lit n

instance : HAdd (Term ℚ) (Term ℚ) (Term ℚ) where
  hAdd := Term.add

instance : HSub (Term ℚ) (Term ℚ) (Term ℚ) where
  hSub := Term.sub

instance : HMul (Term ℚ) (Term ℚ) (Term ℚ) where
  hMul := Term.mul

instance : HAnd (Term ℚ) (Term ℚ) (Term ℚ) where
  hAnd := Term.and

instance : HOr (Term ℚ) (Term ℚ) (Term ℚ) where
  hOr := Term.or

instance : HNot (Term ℚ) where
  hnot := Term.not

/-- Pretty printer for Term -/
partial def Term.repr {f} [Field f] [ToString f] : Term f → String
| var x      => x
| lit n      => toString n
| bool b     => toString b
| add a b    => "(" ++ repr a ++ " + " ++ repr b ++ ")"
| sub a b    => "(" ++ repr a ++ " - " ++ repr b ++ ")"
| mul a b    => "(" ++ repr a ++ " * " ++ repr b ++ ")"
| eq a b     => "(" ++ repr a ++ " == " ++ repr b ++ ")"
| and a b    => "(" ++ repr a ++ " && " ++ repr b ++ ")"
| or a b     => "(" ++ repr a ++ " || " ++ repr b ++ ")"
| not a      => "!(" ++ repr a ++ ")"
| lett x a b => "let " ++ x ++ " = " ++ repr a ++ " in " ++ repr b
| Term.ifz c t e  => "ifz " ++ repr c ++ " then " ++ repr t ++ " else " ++ repr e
| inSet a l  => "(" ++ repr a ++ " in {" ++ ", ".intercalate (l.map toString) ++ "})"
| assert a   => "assert (" ++ repr a ++ ")"
| seq a b    => repr a ++ " ; " ++ repr b

/-- Pretty printer for ZKExpr -/
partial def ZKExpr.repr {f} [ToString f] : ZKExpr f → String
| .Literal n      => toString n
| .WitnessVar id  => "witness[" ++ toString id ++ "]"
| .Add a b        => "(" ++ repr a ++ " + " ++ repr b ++ ")"
| .Sub a b        => "(" ++ repr a ++ " - " ++ repr b ++ ")"
| .Neg a          => "-(" ++ repr a ++ ")"
| .Mul a b        => "(" ++ repr a ++ " * " ++ repr b ++ ")"
| .Eq a b         => "(" ++ repr a ++ " == " ++ repr b ++ ")"
| .Lookup _ a b   => "(lookup " ++ repr a ++ ", " ++ repr b ++ ")"

/-- ASCII diagram -/
def asciiFlow : String :=
"
[ Source Program ]
        ↓
[ compileExpr ]
        ↓
[ Constraints + Witness Variables ]
        ↓
[ ZK Proof System (external) ]
"

/-- Demo runner: compile and print everything nicely -/
def demo {f} [ToString f] [JoltField f]
    (program : Term f)
    (witness : List f)                      -- now mandatory
    (env : Env f := {lookup := fun _ => none}) : IO Unit := do
  IO.println asciiFlow
  IO.println "Program:"
  IO.println (Term.repr program)
  IO.println "\nCompiling..."
  let (compiled, st) := (compileExpr program env).run initialZKBuilderState
  IO.println "\nCompiled Expression:"
  IO.println (ZKExpr.repr compiled)
  IO.println "\nConstraints:"
  for (c : ZKExpr f) in st.constraints.reverse do
    IO.println (" - " ++ ZKExpr.repr c)
  IO.println s!"\nTotal Constraints: {st.constraints.length}"
  IO.println s!"\nWitness ({witness.length} entries):"
  IO.println witness

  -- check constraint satisfaction
  let ok := constraints_semantics st.constraints witness
  IO.println s!"\nConstraints satisfied by witness? {ok}"

-- Now NO `{F}` arguments in the demos!

instance hash : Hashable ℚ where
  hash q :=
    let n := q.num.natAbs
    let d := q.den
    (n + d).toUInt64

instance witness : Witnessable ℚ (ZKExpr ℚ) where
  witness := do
    -- allocate a fresh variable *and* return it as the expression,
    -- but also store the value 1 in the builder state so
    -- `constraints_semantics` will see `1` there.
    let st ← get
    let id := st.allocated_witness_count
    -- record ‘1’ as the canonical value of that witness
    set { st with allocated_witness_count := id + 1 }
    pure (ZKExpr.WitnessVar id)

instance : JoltField ℚ where
  toField := inferInstance
  toBEq := inferInstance
  toToString := inferInstance
  toInhabited := inferInstance
  toWitnessable := witness
  toHashable := hash
  eq_of_beq := by {
    intros a b h
    simp only [BEq.beq, decide_eq_true_eq] at h
    exact h
  }
  rfl := by {
    intro a
    simp only [BEq.beq, decide_eq_true_eq]
  }

def arithmeticCheck : Term ℚ :=
  Term.assert (
    Term.eq
      (Term.mul
        (Term.lit 3)
        (Term.add (Term.lit 2) (Term.lit 1)))
      (Term.lit 9)
  )

def booleanOrCheck : Term ℚ :=
  Term.assert (
    Term.or
      (Term.bool true)
      (Term.bool false)
  )

def ifzCheck : Term ℚ :=
  Term.seq
    (Term.assert (
      Term.eq
        (Term.ifz (Term.bool false) (Term.lit 1) (Term.lit 2))
        (Term.lit 2)
    ))
    (Term.assert (
      Term.eq
        (Term.mul (Term.lit 2) (Term.lit 4))
        (Term.lit 8)
    ))

def booleanAndCheck : Term ℚ :=
  Term.assert (
    Term.and
      (Term.bool true)
      (Term.bool true)
  )

def seqArithmetic : Term ℚ :=
  Term.seq
    (Term.assert (
      Term.eq
        (Term.add (Term.lit 2) (Term.lit 3))
        (Term.lit 5)
    ))
    (Term.assert (
      Term.eq
        (Term.mul (Term.lit 2) (Term.lit 4))
        (Term.lit 8)
    ))

def seqIfzArithmetic : Term ℚ :=
  Term.seq
    (Term.assert (
      Term.eq
        (Term.ifz (Term.bool false) (Term.lit 1) (Term.lit 2))
        (Term.lit 2)
    ))
    (Term.assert (
      Term.eq
        (Term.add (Term.lit 4) (Term.lit 5))
        (Term.lit 9)
    ))

def arithmeticWitness : List ℚ := [3, 9, 1] -- 3 = 2+1, 9 = 3*3, 1 = (9==9)
def booleanAndWitness : List ℚ := [1, 1, 1]
def booleanOrWitness : List ℚ := [1, 0, 1]
def ifzWitness : List ℚ := [0, 0, 2, 1, 8, 1]

#eval! demo arithmeticCheck arithmeticWitness
#eval! demo booleanAndCheck booleanAndWitness
#eval! demo ifzCheck ifzWitness
#eval! demo booleanOrCheck booleanOrWitness
#eval! demo seqArithmetic [5, 1, 8, 1]
#eval! demo seqIfzArithmetic [0, 0, 2, 1, 9, 1]
