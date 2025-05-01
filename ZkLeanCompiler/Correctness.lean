import «ZkLeanCompiler».Compile
import «ZkLeanCompiler».Semantics
import Mathlib.Tactic.Cases
import Mathlib.Algebra.Field.Defs

set_option linter.unusedTactic false

variable {F} [JoltField F]

lemma assertIsBool_sound {f} [JoltField f]
  {x : ZKExpr f} {w : List f} :
  (semantics_zkexpr x w = Value.VField (0 : f) ∨
   semantics_zkexpr x w = Value.VField 1) →
  constraints_semantics
      [ZKExpr.Eq (ZKExpr.Mul x (ZKExpr.Sub (ZKExpr.Literal 1) x)) (ZKExpr.Literal 0)] w = true := by
  intro h
  cases' h with inl inr
  · simp [constraints_semantics, semantics_zkexpr, semantics_zkexpr.eval, semantics_zkexpr.eval] at inl ⊢
    simp [inl]
  · simp [constraints_semantics, semantics_zkexpr, semantics_zkexpr.eval, semantics_zkexpr.eval] at inr ⊢
    simp [inr]

lemma r1cs_sound {f} [JoltField f] {x y z : ZKExpr f} {w : List f}
  {a b : f} (hx : semantics_zkexpr x w = Value.VField a)
           (hy : semantics_zkexpr y w = Value.VField b)
           (hz : semantics_zkexpr z w = Value.VField (a*b)) :
  constraints_semantics [ZKExpr.Eq (ZKExpr.Mul x y) z] w = true := by
  simp [constraints_semantics, hx, hy, hz]
  dsimp [semantics_zkexpr, semantics_zkexpr.eval]
  simp [semantics_zkexpr] at hz hy hx
  rw [hx, hy, hz]
  cases semantics_zkexpr.eval w z
  · case VBool b' =>
    simp
  · case VField f' =>
    simp
  · case None =>
    simp

lemma constrainR1CS_sound
  {f} [JoltField f] (a b c : ZKExpr f) (w : List f) (x y : f)
  (ha : semantics_zkexpr a w = Value.VField x)
  (hb : semantics_zkexpr b w = Value.VField y)
  (hc : semantics_zkexpr c w = Value.VField (x * y)) :
  constraints_semantics
    ((constrainR1CS a b c).run initialZKBuilderState |>.2.constraints) w = true := by
  simp [constrainR1CS, constraints_semantics, StateT.run, constrainEq,
  constrain]







lemma assertIsBool_sound_monad
  {f} [JoltField f] (x : ZKExpr f) (w : List f) :
  (semantics_zkexpr x w = Value.VField (0 : f) ∨
   semantics_zkexpr x w = Value.VField 1) →
  constraints_semantics
    ((assertIsBool x).run initialZKBuilderState |>.2.constraints) w = true
  := by sorry


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

lemma wellScoped_of_and_wellScoped (t₁ t₂ : Term F) (env : Env F) :
 wellScoped t₁ env ∧ wellScoped t₂ env → wellScoped (Term.and t₁ t₂) env := by
  intro h
  cases' h with h₁ h₂
  simp [Term.and] at *
  intros x xfree
  simp [wellScoped] at h₁ h₂
  unfold freeVars at xfree
  simp [Set.mem_union] at xfree
  cases' xfree with h₃ h₄
  specialize h₁ x h₃
  exact h₁
  specialize h₂ x h₄
  exact h₂

lemma wellScoped_of_or_wellScoped (t₁ t₂ : Term F) (env : Env F) :
  wellScoped t₁ env ∧ wellScoped t₂ env → wellScoped (Term.or t₁ t₂) env := by
  intro h
  cases' h with h₁ h₂
  simp [Term.or] at *
  intros x xfree
  simp [wellScoped] at h₁ h₂
  unfold freeVars at xfree
  simp [Set.mem_union] at xfree
  cases' xfree with h₃ h₄
  specialize h₁ x h₃
  exact h₁
  specialize h₂ x h₄
  exact h₂

lemma wellScoped_of_add_wellScoped (t₁ t₂ : Term F) (env : Env F) :
  wellScoped t₁ env ∧ wellScoped t₂ env → wellScoped (Term.add t₁ t₂) env := by
  intro h
  cases' h with h₁ h₂
  simp [Term.add] at *
  intros x xfree
  simp [wellScoped] at h₁ h₂
  unfold freeVars at xfree
  simp [Set.mem_union] at xfree
  cases' xfree with h₃ h₄
  specialize h₁ x h₃
  exact h₁
  specialize h₂ x h₄
  exact h₂

lemma wellScoped_of_sub_wellScoped (t₁ t₂ : Term F) (env : Env F) :
  wellScoped t₁ env ∧ wellScoped t₂ env → wellScoped (Term.sub t₁ t₂) env := by
  intro h
  cases' h with h₁ h₂
  simp [Term.sub] at *
  intros x xfree
  simp [wellScoped] at h₁ h₂
  unfold freeVars at xfree
  simp [Set.mem_union] at xfree
  cases' xfree with h₃ h₄
  specialize h₁ x h₃
  exact h₁
  specialize h₂ x h₄
  exact h₂

lemma wellScoped_of_mul_wellScoped (t₁ t₂ : Term F) (env : Env F) :
  wellScoped t₁ env ∧ wellScoped t₂ env → wellScoped (Term.mul t₁ t₂) env := by
  intro h
  cases' h with h₁ h₂
  simp [Term.mul] at *
  intros x xfree
  simp [wellScoped] at h₁ h₂
  unfold freeVars at xfree
  simp [Set.mem_union] at xfree
  cases' xfree with h₃ h₄
  specialize h₁ x h₃
  exact h₁
  specialize h₂ x h₄
  exact h₂

lemma wellScoped_of_eq_wellScoped (t₁ t₂ : Term F) (env : Env F) :
  wellScoped t₁ env ∧ wellScoped t₂ env → wellScoped (Term.eq t₁ t₂) env := by
  intro h
  cases' h with h₁ h₂
  simp [Term.eq] at *
  intros x xfree
  simp [wellScoped] at h₁ h₂
  unfold freeVars at xfree
  simp [Set.mem_union] at xfree
  cases' xfree with h₃ h₄
  specialize h₁ x h₃
  exact h₁
  specialize h₂ x h₄
  exact h₂

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

lemma wellScoped_of_assert_wellScoped (t : Term F) (env : Env F) :
  wellScoped t env → wellScoped (Term.assert t) env := by
  intro h
  simp [wellScoped] at h
  intro x xfree
  unfold freeVars at xfree
  specialize h x xfree
  simp
  exact h

lemma wellScoped_of_inSet_wellScoped (t : Term F) (ts : List F) (env : Env F) :
  wellScoped t env → wellScoped (Term.inSet t ts) env := by
  intro h
  simp [wellScoped] at h
  intro x xfree
  unfold freeVars at xfree
  specialize h x xfree
  exact h

------------------------ WELL SCOPED LEMMAS ---------------------------

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
        simp [compileExpr]
        simp [hLookup]
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
        simp [compileExpr]
        simp [Val.toValue, semantics_zkexpr]
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
      · case add FField env' t₁ t₂ f₁ f₂ hf₁ hf₂ ih₁ ih₂ =>
        -- Case: addition
        let compiled := ((compileExpr (Term.add t₁ t₂) env').run initialZKBuilderState).1
        let st := ((compileExpr (Term.add t₁ t₂) env').run initialZKBuilderState).2
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
        · simp [initialZKBuilderState, StateT.run, compileExpr] at h₁
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₂
          cases' h₁ with csem₁ h₁'
          cases' h₂ with csem₂ h₂'
          simp [StateT.run, semantics_zkexpr, semantics_zkexpr.eval]
          sorry
      · case sub Ffield env' t₁ t₂ f₁ f₂ hf₁ hf₂ ih₁ ih₂ =>
        -- Case: subtraction
        let compiled := ((compileExpr (Term.sub t₁ t₂) env').run initialZKBuilderState).1
        let st := ((compileExpr (Term.sub t₁ t₂) env').run initialZKBuilderState).2
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
        · simp [initialZKBuilderState, StateT.run, compileExpr] at h₁
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₂
          cases' h₁ with csem₁ h₁'
          cases' h₂ with csem₂ h₂'
          simp [StateT.run, semantics_zkexpr, semantics_zkexpr.eval]
          sorry
      · sorry
      · case eq FField env' t₁ t₂ v₁ v₂ hf₁ hf₂ ih₁ ih₂ =>
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
        · cases' h₂ with h₂l h₂r
          simp [initialZKBuilderState]
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₁
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₂l
          cases' h₁ with csem₁ h₁'
          sorry
        sorry
      · case and Ffield env' t₁ t₂ b₁ b₂ hf₁ hf₂ ih₁ ih₂ =>
        -- Case: conjunction
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
        cases' ih₁ with w₁ h₁
        cases' ih₂ with w₂ h₂
        let z_val : F := if b₁ && b₂ then 1 else 0
        let w := w₁ ++ w₂ ++ [z_val]
        refine ⟨w, ?constraints, ?value⟩
        let xExpr : ZKExpr F := (compileExpr t₁ env' initialZKBuilderState).1
        have hBx :
        constraints_semantics [ZKExpr.Eq (ZKExpr.Mul xExpr (ZKExpr.Sub (ZKExpr.Literal 1) xExpr)) (ZKExpr.Literal 0) ] w = true := by
          apply assertIsBool_sound
          simp [xExpr]
          simp [initialZKBuilderState, StateT.run, compileExpr] at h₁ ⊢
          cases' h₁ with csem₁ h₁'
          sorry
        all_goals {sorry}
      · sorry
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
      · case seq Ffield env' t₁ t₂ v₁ h₁ h₂ ih₁ ih₂ =>
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
