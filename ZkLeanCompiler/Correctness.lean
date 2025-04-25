import «ZkLeanCompiler».Compile
import «ZkLeanCompiler».Semantics
import Mathlib.Tactic.Cases
import Mathlib.Algebra.Field.Defs

set_option linter.unusedTactic false

variable {F} [JoltField F]

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
theorem compileExpr_correct
  [JoltField F] :
  ∀ (t : Term F) (env : Env F) (v : Val F),
    wellScoped t env →
    Eval F t env v →
    ∃ (witness : List F),
      let (compiledExpr, st) := (compileExpr t env).run initialZKBuilderState
      constraints_semantics st.constraints witness = true ∧
      semantics_zkexpr compiledExpr witness = Val.toValue v := by
      intro t env v hWellScoped hEval
      induction hEval
      case var Ffield env₁ x' v' hLookup =>
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
          ·
            sorry
      all_goals {sorry}
