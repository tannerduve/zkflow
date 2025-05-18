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
| .var x        => x
| .lit n        => toString n
| .bool b       => toString b
| .arith op a b =>
  let opStr := match op with
    | .add => " + "
    | .sub => " - "
    | .mul => " * "
  "(" ++ repr a ++ opStr ++ repr b ++ ")"
| .boolB op a b =>
  let opStr := match op with
    | .and => " && "
    | .or  => " || "
  "(" ++ repr a ++ opStr ++ repr b ++ ")"
| .eq a b       => "(" ++ repr a ++ " == " ++ repr b ++ ")"
| .not a        => "!(" ++ repr a ++ ")"
| .lett x a b   => "let " ++ x ++ " = " ++ repr a ++ " in " ++ repr b
| .ifz c t e    => "ifz " ++ repr c ++ " then " ++ repr t ++ " else " ++ repr e
| .inSet a l    => "(" ++ repr a ++ " in {" ++ ", ".intercalate (l.map toString) ++ "})"
| .assert a b     => "assert (" ++ repr a ++ ")" ++ " then " ++ repr b
| .seq a b      => repr a ++ " ; " ++ repr b


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
def demo {f} [ToString f] [JoltField f] [DecidableEq f]
    (program : Term f)
    (witness : List f)                      -- now mandatory
    (env : Env f := {lookup := fun _ => none}) (expected : Val f) : IO Unit := do
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
  let actual := semantics_zkexpr compiled witness

  IO.println s!"Compiled expression evaluates to: {actual}"
  IO.println s!"Matches expected? {actual == Val.toValue expected}"

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
  ASSERT ((3 ⊗ (2 .+. 1)) =-= 9) then (3 .+. 1)

def booleanOrCheck : Term ℚ :=
  ASSERT (Term.bool true || false) then (Term.bool true)

def ifzCheck : Term ℚ :=
  ASSERT ((ifz` false then` 1 else` 2) =-= 2) then (2 .+. 1);
  ASSERT (2 ⊗ 4 =-= 8) then (2 .+. 3)

def booleanAndCheck : Term ℚ :=
  ASSERT (Term.bool true && true) then (Term.bool true)

def seqArithmetic : Term ℚ :=
     ASSERT (2 .+. 3 =-= 5) then (Term.bool true) ;
     ASSERT (2 ⊗ 4 =-= 8) then (4 .+. 5)

def seqIfzArithmetic : Term ℚ :=
  ASSERT ((ifz` false then` 1 else` 2) =-= 2) then (2 .+. 1) ;
  ASSERT (4 .+. 5 =-= 9) then (4 .+. 5)

-- Negation and equality
def notEqCheck : Term ℚ :=
  ASSERT (~ (1 =-= 2)) then (1 .+. 2)

-- Boolean logic with inSet
def inSetCheck : Term ℚ :=
  ASSERT (3 inn [1, 2, 3]) then (3 .+. 1)

-- Let binding and reuse
def letBindingCheck : Term ℚ :=
  LET "x" := 2 .+. 3 in
  ASSERT (Term.var "x" ⊗ 2 =-= 10) then 35

-- Nested let and conditionals
def nestedLetIfzCheck : Term ℚ :=
  LET "x" := true in
  LET "y" := ifz` Term.var "x" then` 5 else` 6 in
  ASSERT (Term.var "y" =-= 5) then 1

-- Sequence with mixed arithmetic and boolean logic
def complexSeqCheck : Term ℚ :=
  ASSERT (1 .+. 2 =-= 3) then (Term.bool true) ;
  ASSERT (~ false && true) then (3 .+. 1) ;
  ASSERT (7 .-. 2 =-= 5) then (Term.bool true)

def arithmeticWitness : List ℚ := [3, 9, 1, 0, 4] -- 3 = 2+1, 9 = 3*3, 1 = (9==9)
def booleanAndWitness : List ℚ := [1, 1, 1, 1]
def booleanOrWitness : List ℚ := [1, 0, 1, 1]
def ifzWitness : List ℚ := [2, 1, 0, 3, 8, 1, 0, 5]
def notEqWitness      : List ℚ := [0, 1, 3]               -- ~false == true → 1
def inSetWitness      : List ℚ := [1, 0, 4]            -- membership check output
def letBindingWitness : List ℚ := [10, 1]           -- x = 5, x * 2 = 10, equality holds
def nestedLetWitness  : List ℚ := [1, 0]            -- x = 0, then y = 5
def complexSeqWitness : List ℚ := [3, 1, 1, 1, 4, 5, 1]    -- outputs of each expr in sequence

def mulAddCheck : Term ℚ := (2 .+. 3) ⊗ 4
def mulAddWitness : List ℚ := [5, 20]  -- 2+3 = 5, 5*4 = 20
def mulAddExpected : Val ℚ := Val.Field 20

def boolLogicCheck : Term ℚ := Term.bool true && ~ Term.bool false
def boolLogicWitness : List ℚ := [1, 1]
def boolLogicExpected : Val ℚ := Val.Bool true

def ifzTrueBranch : Term ℚ := ifz` 1 then` 42 else` 7
def ifzTrueWitness : List ℚ := [42]
def ifzTrueExpected : Val ℚ := Val.Field 42

def ifzFalseBranch : Term ℚ := ifz` 0 then` 42 else` 7
def ifzFalseWitness : List ℚ := [7]
def ifzFalseExpected : Val ℚ := Val.Field 7

def letUse : Term ℚ :=
  LET "x" := 5 in (Term.var "x" ⊗ Term.var "x")
def letUseWitness : List ℚ := [25]
def letUseExpected : Val ℚ := Val.Field 25

def inSetBool : Term ℚ := 3 inn [1, 2, 3]
def inSetBoolWitness : List ℚ := [1, 0, 1]
def inSetBoolExpected : Val ℚ := Val.Bool true

def failAssertCheck : Term ℚ :=
  ASSERT (2 .+. 2 =-= 5) then (Term.bool true)

def failAssertWitness : List ℚ := [4, 0, 1]

def failBoolCheck : Term ℚ :=
  ASSERT (Term.bool true && false) then (Term.bool true)

def failBoolWitness : List ℚ := [1, 0, 0, 1]

def failInSetCheck : Term ℚ :=
  ASSERT (4 inn [1, 2, 3]) then (Term.bool true)

def failInSetWitness : List ℚ := [4, 3, 0, 1]


#eval! demo arithmeticCheck arithmeticWitness (expected := Val.Field 4)

#eval! demo (Term.bool true && true) [(1 : ℚ)] (expected := Val.Bool true)

#eval! demo booleanAndCheck booleanAndWitness (expected := Val.Field 1)

#eval! demo ifzCheck ifzWitness (expected := Val.Field 5)

#eval! demo booleanOrCheck booleanOrWitness (expected := Val.Field 1)

#eval! demo seqArithmetic [5, 1, 0, 8, 1, 0, 9] (expected := Val.Field 9)

#eval! demo seqIfzArithmetic [2, 1, 1, 3, 9, 1, 1, 9] (expected := Val.Field 9)

#eval! demo notEqCheck [0, -1, 1, 3] (expected := Val.Field 3)

#eval! demo inSetCheck inSetWitness (expected := Val.Field 4)

#eval! demo letBindingCheck [10, 1, 0, 35] (expected := Val.Field 35)

#eval! demo nestedLetIfzCheck [1,0] (expected := Val.Field 1)

#eval! demo complexSeqCheck [3, 1, 0, 1, 1, 4, 5, 1, 0] (expected := Val.Field 1)

#eval! demo mulAddCheck mulAddWitness (expected := mulAddExpected)

#eval! demo boolLogicCheck boolLogicWitness (expected := boolLogicExpected)

#eval! demo ifzTrueBranch ifzTrueWitness (expected := ifzTrueExpected)

#eval! demo ifzFalseBranch ifzFalseWitness (expected := ifzFalseExpected)

#eval! demo letUse letUseWitness (expected := letUseExpected)

#eval! demo inSetBool inSetBoolWitness (expected := inSetBoolExpected)

#eval! demo
  (Term.seq
    (Term.assert (Term.eq (Term.lit (1 : ℚ) .+. Term.lit 2) (Term.lit 3)) true)
    (Term.seq
      (Term.assert (Term.boolB BoolBinOp.and (Term.not false) true) (3 + 1))
      (Term.assert (Term.eq (7 - 2) 5) true)))
  [3, 1, 0, 1, 1, 4, 5, 1, 0]
  (expected := Val.Field 1)

#eval! demo (Term.assert (Term.lit (1 : ℚ) =-= Term.lit 1) (Term.bool true)) [1, 1] (expected := Val.Field 1)

-- Failing tests
#eval! demo failAssertCheck failAssertWitness (expected := Val.Field 1)
#eval! demo failBoolCheck failBoolWitness (expected := Val.Field 1)
#eval! demo failInSetCheck failInSetWitness (expected := Val.Field 1)

#check LawfulFunctor
