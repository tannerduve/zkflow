import «ZkLeanCompiler».Compile
import Mathlib.Tactic.Cases

/-
Correctness claim: iF t evaluates to v in env, then For some witness, the compiled ZK expression
evaluates to v in the ZK semantics.
-/

theorem compiler_correctness {F} [JoltField F] [BEq F] [ToString F]
  (t : Term F) (env : Env F) (v : Val F)
  (h : Eval F t env v) :
  ∃ (witness : List F),
    let t' := normalize t env
    let (ir, _) := (normalizeToIR t' IR.Env.empty).run 0
    let (compiled, state) := (compileIR ir).run ⟨0, []⟩
    semantics_zkexpr compiled witness = v.toValue := by
    induction h
    · case var env' x v₂ sevalv =>
      let t' := normalize (Term.var x) env'
      let ir₁:= ((normalizeToIR t' IR.Env.empty).run 0).1
      let compiled := ((compileIR ir₁).run ⟨0, []⟩).1
      let s := ((compileIR ir₁).run ⟨0, []⟩).2
      simp only [t']
      obtain ⟨ir₂, k⟩ := StateT.run (normalizeToIR t' IR.Env.empty) 0
      let ir' := (StateT.run (normalizeToIR t' IR.Env.empty) 0).1
      simp
      obtain ⟨zk, s'⟩ := (StateT.run (compileIR ir₂) { allocated_witness_count := 0, constraints := [] })
      let zk' := (StateT.run (compileIR ir₂) { allocated_witness_count := 0, constraints := [] }).1
      simp
      cases' v₂ with f b tm env₂
      · use []
        simp [semantics_zkexpr]
        have lem : t' = Term.lit f := by
          simp [t']
          simp [normalize]
          rw [sevalv]
        sorry
      sorry
      sorry
    all_goals {sorry}
