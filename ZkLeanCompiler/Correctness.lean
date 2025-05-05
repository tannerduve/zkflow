import «ZkLeanCompiler».Compile
import «ZkLeanCompiler».Semantics
import Mathlib.Tactic.Cases
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.List.Basic

set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

variable {F} [JoltField F] [DecidableEq F]

/-
witnessIndices returns the indices of the witness variables in a ZKExpr.
-/
def witnessIndices : ZKExpr f → Finset ℕ
  | ZKExpr.Literal _        => ∅
  | ZKExpr.WitnessVar i     => {i}
  | ZKExpr.Add e₁ e₂        => witnessIndices e₁ ∪ witnessIndices e₂
  | ZKExpr.Sub e₁ e₂        => witnessIndices e₁ ∪ witnessIndices e₂
  | ZKExpr.Mul e₁ e₂        => witnessIndices e₁ ∪ witnessIndices e₂
  | ZKExpr.Neg e            => witnessIndices e
  | ZKExpr.Eq e₁ e₂         => witnessIndices e₁ ∪ witnessIndices e₂
  | ZKExpr.Lookup _ e₁ e₂   => witnessIndices e₁ ∪ witnessIndices e₂

lemma constrainR1CS_sound
  {f} [JoltField f] (a b c : ZKExpr f) (w : List f) (x y : f)
  (ha : semantics_zkexpr a w = Value.VField x)
  (hb : semantics_zkexpr b w = Value.VField y)
  (hc : semantics_zkexpr c w = Value.VField (x * y)) :
  constraints_semantics
    ((constrainR1CS a b c).run initialZKBuilderState |>.2.constraints) w = true := by
  simp [constrainR1CS, constraints_semantics, StateT.run, constrainEq,
  constrain]
  simp [semantics_zkexpr] at ha hb hc
  simp [initialZKBuilderState]
  simp only [pure, bind, StateT.get, StateT.bind, pure, StateT.set]
  simp [StateT.pure, constraints_semantics, semantics_zkexpr, semantics_zkexpr.eval]
  rw [ha, hb, hc]
  simp

lemma assertIsBool_sound
  {f} [JoltField f] (x : ZKExpr f) (w : List f) :
  (semantics_zkexpr x w = Value.VField (0 : f) ∨
   semantics_zkexpr x w = Value.VField 1) →
  constraints_semantics
    ((assertIsBool x).run initialZKBuilderState |>.2.constraints) w = true
  := by
  simp [assertIsBool, constraints_semantics, StateT.run, constrainEq, constrain]
  rintro h
  cases' h with lt rt
  · simp [StateT.run, assertIsBool_sound] at lt
    apply constrainR1CS_sound
    · apply lt
    · simp [semantics_zkexpr, semantics_zkexpr.eval] at lt ⊢
      rw [lt]
    · simp [semantics_zkexpr, semantics_zkexpr.eval] at lt ⊢
  · simp [StateT.run, assertIsBool_sound] at rt
    apply constrainR1CS_sound
    · apply rt
    · simp [semantics_zkexpr, semantics_zkexpr.eval] at rt ⊢
      rw [rt]
    · simp [semantics_zkexpr, semantics_zkexpr.eval] at rt ⊢

-- append distributes
lemma cs_append {f} [JoltField f] {c₁ c₂ : List (ZKExpr f)} {w : List f} :
  constraints_semantics (c₁ ++ c₂) w =
    (constraints_semantics c₁ w && constraints_semantics c₂ w) := by
    induction c₁
    · simp [constraints_semantics]
    · case cons h tl ih =>
      simp [constraints_semantics]
      rw [ih]
      cases hsem : semantics_zkexpr h w
      · case VBool b =>
        simp [hsem, Bool.and_assoc]
      · case VField f =>
        simp [hsem]
      · case None =>
        simp [hsem]

-- Constraint semantics are invariant under permutation of constraints
lemma constraints_semantics_perm {f} [JoltField f]
  (l₁ l₂ : List (ZKExpr f)) (w : List f)
  (h : List.Perm l₁ l₂) :
  constraints_semantics l₁ w = constraints_semantics l₂ w := by
  induction h
  · simp [constraints_semantics]
  · case cons x l₁ l₂ perm ih =>
    simp [constraints_semantics]; rw [ih]
  · case swap x y l =>
    simp [constraints_semantics]; cases' semantics_zkexpr y w with b
    simp; cases' semantics_zkexpr x w with b'
    · simp
      rw [Bool.and_comm, Bool.and_assoc, Bool.and_comm b]
    · simp
    · simp
    · case VField _ =>
      simp [semantics_zkexpr]; cases' semantics_zkexpr.eval w x with b
      · simp
      · case VField _ =>
        simp
      · case None =>
        simp
    · case None =>
      simp [semantics_zkexpr]; cases' semantics_zkexpr.eval w x with b
      all_goals {simp}
  · case trans l₁ l₂ l₃ perm₁ perm₂ ih₁ ih₂ =>
    rw [ih₁, ih₂]

lemma semantics_zkexpr_suffix_irrelevant [JoltField f] (c : ZKExpr f) (w w' : List f)
  (h : ∀ i, i ∈ witnessIndices c → i < w.length) :
  semantics_zkexpr c w = semantics_zkexpr c (w ++ w') := by
  induction' c with n i e₁ e₂ ih₁ ih₂ e₁ e₂ ih₁ ih₂ e ih e₁ e₂ ih₁ ih₂ e₁ e₂ ih₁ ih₂ table e₁ e₂ ih₁ ih₂
  · case Literal n =>
    simp [semantics_zkexpr, semantics_zkexpr.eval]
  · case WitnessVar i =>
    simp [semantics_zkexpr]; specialize h i
    have lem : i ∈ @witnessIndices f (ZKExpr.WitnessVar i) := by
      simp [witnessIndices]
    specialize h lem
    have lem2 : i < w.length + w'.length := by
      omega
    simp [semantics_zkexpr, semantics_zkexpr.eval, h, lem2]
  case Neg =>
    simp [semantics_zkexpr]; (specialize ih h); simp [semantics_zkexpr, semantics_zkexpr.eval] at *; simp [ih]
  all_goals {
    simp [semantics_zkexpr]; simp [witnessIndices] at h
    have h₁ : ∀ i, i ∈ witnessIndices e₁ → i < w.length := by
      intro i hi; (specialize h i (Or.inl hi)); exact h
    have h₂ : ∀ i, i ∈ witnessIndices e₂ → i < w.length := by
      intro i hi; (specialize h i (Or.inr hi)); exact h
    (specialize ih₁ h₁); specialize ih₂ h₂
    simp [semantics_zkexpr, semantics_zkexpr.eval] at *; simp [ih₁, ih₂]
  }

-- witness indexing
lemma get_last {α} {l₁ l₂ : List α} {x : α} [Inhabited α] :
  List.get! (l₁ ++ l₂ ++ [x]) (l₁.length + l₂.length) = x := by
  simp [List.get!]

----------------------------- WELL SCOPED LEMMAS -----------------------------
/-
These lemmas are each of the form `wellScoped t env → wellScoped (Term.op t) env` where op is some
operation on terms, eg. Term.add, etc.
-/
lemma wellScoped_of_neg_wellScoped (t : Term F) (env : Env F) :
  wellScoped (Term.not t) env ↔ wellScoped t env := by
  constructor
  · intro h
    simp [Term.not] at h
    exact h
  · intro h
    simp [Term.not] at h
    exact h

lemma wellScoped_of_arith_binop (op : ArithBinOp) (t₁ t₂ : Term F) (env : Env F) :
  wellScoped (Term.arith op t₁ t₂) env ↔ wellScoped t₁ env ∧ wellScoped t₂ env := by
  constructor
  intro h
  simp [wellScoped] at h
  constructor
  · intro x xfree
    unfold freeVars at h
    specialize h x
    simp [Set.mem_union] at h
    specialize h (Or.inl xfree)
    exact h
  · intro x xfree
    unfold freeVars at h
    specialize h x
    simp [Set.mem_union] at h
    specialize h (Or.inr xfree)
    exact h
  intro h
  cases' h with h₁ h₂
  simp [wellScoped] at h₁ h₂ ⊢
  intro x xFree
  unfold freeVars at xFree
  simp [Set.mem_union] at xFree
  cases' xFree with h₃ h₄
  specialize h₁ x h₃
  push_neg at h₁
  exact h₁
  specialize h₂ x h₄
  push_neg at h₄
  exact h₂

lemma welLScoped_of_bool_binop (op : BoolBinOp) (t₁ t₂ : Term F) (env : Env F) :
  wellScoped (Term.boolB op t₁ t₂) env → wellScoped t₁ env ∧ wellScoped t₂ env := by
  intro h
  simp [wellScoped] at h
  constructor
  · intro x xfree
    unfold freeVars at h
    specialize h x
    simp [Set.mem_union] at h
    specialize h (Or.inl xfree)
    exact h
  · intro x xfree
    unfold freeVars at h
    specialize h x
    simp [Set.mem_union] at h
    specialize h (Or.inr xfree)
    exact h

lemma wellScoped_of_eq_wellScoped (t₁ t₂ : Term F) (env : Env F) :
 wellScoped (Term.mul t₁ t₂) env → wellScoped t₁ env ∧ wellScoped t₂ env := by
  intro h
  simp [wellScoped] at h
  constructor
  · intro x xfree
    unfold freeVars at h
    specialize h x
    simp [Set.mem_union] at h
    specialize h (Or.inl xfree)
    exact h
  · intro x xfree
    unfold freeVars at h
    specialize h x
    simp [Set.mem_union] at h
    specialize h (Or.inr xfree)
    exact h

lemma wellScoped_of_ifz_wellScoped (t₁ t₂ t₃ : Term F) (env : Env F) :
  wellScoped t₁ env ∧ wellScoped t₂ env ∧ wellScoped t₃ env →
  wellScoped (Term.ifz t₁ t₂ t₃) env := by
  intro h
  cases' h with h₁ h₂
  cases' h₂ with h₂l h₂r
  simp [Term.ifz] at *
  intros x xfree
  simp [wellScoped] at h₁ h₂l h₂r
  unfold freeVars at xfree
  simp [Set.mem_union] at xfree
  cases' xfree with h₃ h₄
  specialize h₁ x h₃
  exact h₁
  cases' h₄ with lt rt
  specialize h₂l x lt
  exact h₂l
  specialize h₂r x rt
  exact h₂r

lemma weakening (env : Env F) (x₁ x₂ : String) (v : Val F) :
  x₁ ≠ x₂ →
  env.lookup x₁ = (env.insert x₂ v).lookup x₁ := by
  intro hne
  symm at hne
  simp [Env.insert, hne]

lemma wellScoped_of_lett_wellScoped (x : String) (t₁ t₂ : Term F) (env : Env F) :
  wellScoped t₁ env ∧ wellScoped t₂ (Env.insert x (Val.Field 0) env) →
  wellScoped (Term.lett x t₁ t₂) env := by
  intro h
  cases' h with h₁ h₂
  simp [Term.lett] at *
  intros y yfree
  simp [wellScoped] at h₁ h₂
  unfold freeVars at yfree
  simp [Set.mem_diff] at yfree
  cases' yfree with h₃ h₄
  specialize h₁ y h₃
  exact h₁
  push_neg at h₁
  by_cases h : (y = x)
  · subst h
    simp [h₁]
    push_neg
    specialize h₂ y h₄.1
    push_neg  at h₄
    cases' h₄ with h₄l h₄r
    contradiction
  · specialize h₂ y h₄.1
    push_neg at h₄ h
    have lookup_eq : env.lookup y = (env.insert x (Val.Field 0)).lookup y := by
      apply weakening
      exact h
    cases' h₂ with v' h₂'
    use v'
    rw [lookup_eq]
    push_neg at h₂'
    exact h₂'

lemma wellScoped_of_seq_wellScoped (t₁ t₂ : Term F) (env : Env F) :
  wellScoped t₁ env ∧ wellScoped t₂ env → wellScoped (Term.seq t₁ t₂) env := by
  intro h
  cases' h with h₁ h₂
  simp [Term.seq] at *
  intros x xfree
  simp [wellScoped] at h₁ h₂
  unfold freeVars at xfree
  simp [Set.mem_union] at xfree
  cases' xfree with h₃ h₄
  specialize h₁ x h₃
  exact h₁
  specialize h₂ x h₄
  exact h₂

lemma wellScoped_of_assert_wellScoped (t₁ t₂ : Term F) (env : Env F) :
  ((wellScoped t₁ env) ∧ (wellScoped t₂ env)) ↔ wellScoped (Term.assert t₁ t₂) env := by
  constructor
  intro h
  simp [wellScoped] at h
  intro x xfree
  unfold freeVars at xfree
  simp [Set.mem_union] at xfree
  cases' xfree with h₁ h₂
  cases' h with lt rt
  specialize lt x h₁
  push_neg at lt
  exact lt
  cases' h with lt rt
  specialize rt x h₂
  push_neg at rt
  exact rt
  intro h
  constructor
  · intro x xfree
    simp [wellScoped] at h
    unfold freeVars at h
    simp [Set.mem_union] at h
    specialize h x (Or.inl xfree)
    push_neg at h
    exact h
  · intro x xfree
    simp [wellScoped] at h
    unfold freeVars at h
    simp [Set.mem_union] at h
    specialize h x (Or.inr xfree)
    push_neg at h
    exact h

lemma wellScoped_of_inSet_wellScoped (t : Term F) (ts : List F) (env : Env F) :
  wellScoped t env ↔ wellScoped (Term.inSet t ts) env := by
  constructor
  intro h
  simp [wellScoped] at h
  intro x xfree
  unfold freeVars at xfree
  specialize h x xfree
  exact h
  intro h
  simp [wellScoped] at h
  intro x xfree
  specialize h x
  simp [freeVars] at h
  specialize h xfree
  push_neg at h
  exact h

------------------------ WELL SCOPED LEMMAS DONE ---------------------------

lemma semantics_zkexpr_VBool_true_bound {f} [JoltField f] (c : ZKExpr f) (w : List f)
  (h : semantics_zkexpr c w = Value.VBool true) :
  ∀ i ∈ witnessIndices c, i < w.length := by
  intro i hi
  induction' c
  · case Literal n =>
    simp [semantics_zkexpr] at h
    simp [witnessIndices] at hi
  · case WitnessVar i' =>
    simp [semantics_zkexpr, semantics_zkexpr.eval] at h
    simp [witnessIndices] at hi
    have lem : i' ∈ @witnessIndices f (ZKExpr.WitnessVar i') := by
      simp [witnessIndices]
    rw [hi]
    by_cases h' : (i' < w.length)
    · simp [h'] at h
    · simp [h'] at h
  · case Add e₁ e₂ ih₁ ih₂ =>
    sorry
  all_goals {sorry}

lemma constraints_semantics_suffix_irrelevant
  {f} [JoltField f]
  (cs : List (ZKExpr f)) (w w' : List f) :
  constraints_semantics cs w = true →
  constraints_semantics cs (w ++ w') = true := by
  induction cs with
  | nil => intros; simp [constraints_semantics]
  | cons c cs ih =>
    intros h
    simp only [constraints_semantics] at *
    cases hc : semantics_zkexpr c w
    case VBool b =>
      simp only [hc] at h ⊢
      simp at h
      cases' h with h₁ h₂
      specialize ih h₂
      simp at *
      cases hb : semantics_zkexpr c (w ++ w')
      have coro : semantics_zkexpr c w = semantics_zkexpr c (w ++ w') := by {
          apply semantics_zkexpr_suffix_irrelevant
          apply semantics_zkexpr_VBool_true_bound
          rw [h₁] at hc
          exact hc
      }
      · case VBool b' =>
        simp [hc]
        rw [h₁] at hc
        constructor
        · rw [coro] at hc
          rw [hc] at hb
          injection hb
          symm
          assumption
        · exact ih
      · case intro.VField f' =>
        simp
        have coro : semantics_zkexpr c w = semantics_zkexpr c (w ++ w') := by {
          apply semantics_zkexpr_suffix_irrelevant
          apply semantics_zkexpr_VBool_true_bound
          rw [h₁] at hc
          exact hc
        }
        rw [coro] at hc
        rw [hc] at hb
        injection hb
      · case None =>
        have coro : semantics_zkexpr c w = semantics_zkexpr c (w ++ w') := by {
          apply semantics_zkexpr_suffix_irrelevant
          apply semantics_zkexpr_VBool_true_bound
          rw [h₁] at hc
          exact hc
        }
        rw [coro] at hc
        rw [hc] at hb
        injection hb
    case VField f =>
      simp [hc] at h
    case None =>
      simp [hc] at h

lemma compileExpr_constraints_append
  (t : Term F) (env : Env F) (s : ZKBuilderState F) :
  (compileExpr t env s).2.constraints =
    s.constraints ++ (compileExpr t env initialZKBuilderState).2.constraints := by
    induction t
    case var x =>
      simp [compileExpr]
      cases env.lookup x
      simp [pure, StateT.pure, initialZKBuilderState]
      case some v =>
        cases v
        all_goals { simp [pure, StateT.pure, initialZKBuilderState] }
    case lit n =>
      simp [compileExpr, pure, StateT.pure, initialZKBuilderState]
    case bool b =>
      simp [compileExpr]
      simp [pure, StateT.pure, initialZKBuilderState]
    case arith op t₁ t₂ ih₁ ih₂ =>
      simp [compileExpr]
      sorry
    case boolB op t₁ t₂ ih₁ ih₂ =>
      simp [compileExpr]
      sorry
    all_goals { sorry }

/--
Correctness of the constraint compiler.

If a term `t` is well-scoped in an environment `env`, and evaluates to a value `v`
under the source semantics, then compiling `t` produces a circuit expression and a
set of constraints such that:

- The constraints are satisfied by some witness assignment,
- The compiled circuit expression evaluates to the same value `v` under that witness.

This establishes semantic preservation: the behavior of the source term is faithfully
represented by the generated constraint system and compiled ZK expression.
-/
theorem compileExpr_correct :
  ∀ (t : Term F) (env : Env F) (v : Val F),
    wellScoped t env →
    Eval F t env v →
    ∃ (witness : List F),
      let (compiledExpr, st) := (compileExpr t env).run initialZKBuilderState
      constraints_semantics st.constraints witness = true ∧
      semantics_zkexpr compiledExpr witness = Val.toValue v := by
      intro t env v hWellScoped hEval
      induction hEval
      · case var Ffield env₁ x' v' hLookup =>
        -- Case: variable
        let v'' := env₁.lookup x'
        have hLookup' : v'' = some v' := by
          simp [v'', hLookup]
        let ⟨compiled, st⟩ := (compileExpr (Term.var x') env).run initialZKBuilderState
        simp [compileExpr, hLookup]
        cases v'
        · case Field n =>
          simp [Val.toValue, semantics_zkexpr]
          use [n]
          constructor
          all_goals {constructor}
        · case Bool b =>
          simp [Val.toValue, semantics_zkexpr]
          use [if b then 1 else 0]
          constructor
          all_goals {constructor}
        · case Unit =>
          simp [Val.toValue, semantics_zkexpr]
          use []
          constructor
          · constructor
          · have contra : env₁.lookup x' ≠ some Val.Unit := by {
            simp [wellScoped] at hWellScoped
            specialize hWellScoped x'
            have ezlem : x' ∈ @freeVars F _ (Term.var x') := by simp [freeVars]
            specialize hWellScoped ezlem
            simp [hLookup] at hWellScoped
          }
            contradiction
      · case lit Ffield env₁ f =>
        -- Case: literal
        let compiled := ((compileExpr (Term.lit f) env).run initialZKBuilderState).1
        let st := ((compileExpr (Term.lit f) env).run initialZKBuilderState).2
        simp [compileExpr, Val.toValue, semantics_zkexpr]
        use [f]
        constructor
        simp [initialZKBuilderState]
        constructor
        constructor
      · case bool Ffield env₁ b =>
        -- Case: boolean
        let compiled := ((compileExpr (Term.bool b) env).run initialZKBuilderState).1
        let st := ((compileExpr (Term.bool b) env).run initialZKBuilderState).2
        simp [compileExpr]
        simp [Val.toValue, semantics_zkexpr]
        use [if b then 1 else 0]
        constructor
        simp [initialZKBuilderState]
        constructor
        constructor
      · case arith FField env' op t₁ t₂ f₁ f₂ hf₁ hf₂ ih₁ ih₂ =>
        -- Case: arithmetic operation
        let compiled := ((compileExpr (Term.arith op t₁ t₂) env').run initialZKBuilderState).1
        let st := ((compileExpr (Term.arith op t₁ t₂) env').run initialZKBuilderState).2
        simp [compileExpr]
        simp [Val.toValue, semantics_zkexpr]
        have lem1 : wellScoped t₁ env' := by
          simp [wellScoped, freeVars] at hWellScoped ⊢
          intro x xfree
          specialize hWellScoped x (Or.inl xfree)
          simp [hWellScoped]
        have lem2 : wellScoped t₂ env' := by
          simp [wellScoped, freeVars] at hWellScoped ⊢
          intro x xfree
          specialize hWellScoped x (Or.inr xfree)
          simp [hWellScoped]
        specialize ih₁ lem1
        specialize ih₂ lem2
        cases' ih₁ with witness₁ h₁
        cases' ih₂ with witness₂ h₂
        use (witness₁ ++ witness₂)
        constructor
        · simp [initialZKBuilderState]
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₁
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₂
          cases' h₁ with csem₁ h₁'
          cases' h₂ with csem₂ h₂'
          simp [StateT.run, constrainEq]
          sorry
        · sorry
      · case boolB Ffield F' env' op t₁ t₂ b₁ b₂ h₁ h₂ ih₁ ih₂ =>
        -- Case: boolean operation
        let compiled := ((compileExpr (Term.boolB op t₁ t₂) env').run initialZKBuilderState).1
        let st := ((compileExpr (Term.boolB op t₁ t₂) env').run initialZKBuilderState).2
        simp [compileExpr]
        simp [Val.toValue, semantics_zkexpr]
        have lem1 : wellScoped t₁ env' := by
          simp [wellScoped, freeVars] at hWellScoped ⊢
          intro x xfree
          specialize hWellScoped x (Or.inl xfree)
          simp [hWellScoped]
        have lem2 : wellScoped t₂ env' := by
          simp [wellScoped, freeVars] at hWellScoped ⊢
          intro x xfree
          specialize hWellScoped x (Or.inr xfree)
          simp [hWellScoped]
        specialize ih₁ lem1
        specialize ih₂ lem2
        cases' ih₁ with witness₁ h₁
        cases' ih₂ with witness₂ h₂
        use (witness₁ ++ witness₂)
        constructor
        · simp [initialZKBuilderState]
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₁
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₂
          cases' h₁ with csem₁ h₁'
          cases' h₂ with csem₂ h₂'
          simp [StateT.run, constrainEq]
          sorry
        sorry
      · case eq Ffield env' t₁ t₂ f₁ f₂ h₁ h₂ ih₁ ih₂ =>
        -- Case: equality
        let compiled := ((compileExpr (Term.eq t₁ t₂) env').run initialZKBuilderState).1
        let st := ((compileExpr (Term.eq t₁ t₂) env').run initialZKBuilderState).2
        simp [compileExpr]
        simp [Val.toValue, semantics_zkexpr]
        have lem1 : wellScoped t₁ env' := by
          simp [wellScoped, freeVars] at hWellScoped ⊢
          intro x xfree
          specialize hWellScoped x (Or.inl xfree)
          simp [hWellScoped]
        have lem2 : wellScoped t₂ env' := by
          simp [wellScoped, freeVars] at hWellScoped ⊢
          intro x xfree
          specialize hWellScoped x (Or.inr xfree)
          simp [hWellScoped]
        specialize ih₁ lem1
        specialize ih₂ lem2
        cases' ih₁ with witness₁ h₁
        cases' ih₂ with witness₂ h₂
        use (witness₁ ++ witness₂)
        constructor
        · simp [initialZKBuilderState]
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₁
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₂
          cases' h₁ with csem₁ h₁'
          cases' h₂ with csem₂ h₂'
          simp [StateT.run, constrainEq]
          sorry
        sorry
      · case not Ffield env' t b hbeval ih =>
        have lem : wellScoped t env' := by
          simp [wellScoped, freeVars] at hWellScoped ⊢
          intro x xfree
          specialize hWellScoped x xfree
          simp [hWellScoped]
        specialize ih lem
        cases' ih with witness h
        use List.map (fun x => if x == 0 then 1 else 0) witness
        constructor
        · simp [initialZKBuilderState]
          simp [initialZKBuilderState, StateT.run, compileExpr] at h
          sorry
        sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · case seq Ffield env' t₁ t₂ v₁ v₂ h₁ h₂ ih₁ ih₂ =>
        -- Case: sequential composition
        let compiled := ((compileExpr (Term.seq t₁ t₂) env').run initialZKBuilderState).1
        let st := ((compileExpr (Term.seq t₁ t₂) env').run initialZKBuilderState).2
        simp [compileExpr]
        simp [Val.toValue, semantics_zkexpr]
        have lem1 : wellScoped t₁ env' := by
          simp [wellScoped, freeVars] at hWellScoped ⊢
          intro x xfree
          specialize hWellScoped x (Or.inl xfree)
          simp [hWellScoped]
        have lem2 : wellScoped t₂ env' := by
          simp [wellScoped, freeVars] at hWellScoped ⊢
          intro x xfree
          specialize hWellScoped x (Or.inr xfree)
          simp [hWellScoped]
        specialize ih₁ lem1
        specialize ih₂ lem2
        cases' ih₁ with witness₁ h₁
        cases' ih₂ with witness₂ h₂
        use (witness₁ ++ witness₂)
        constructor
        · simp [initialZKBuilderState]
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₁
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₂
          cases' h₁ with csem₁ h₁'
          cases' h₂ with csem₂ h₂'
          simp [StateT.run, constrainEq]
          sorry
        sorry
