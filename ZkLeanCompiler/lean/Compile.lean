import «ZkLeanCompiler».Lean.LCSemantics
import «ZkLeanCompiler».Lean.Semantics
import «ZkLeanCompiler».Lean.Program
import Std.Data.HashMap
import «ZkLeanCompiler».Lean.Builder

open ZKBuilder

def assertIsBool {f} [Field f] (x : ZKExpr f) : ZKBuilder f Unit :=
  constrainR1CS x (ZKExpr.Sub (ZKExpr.Literal 1) x) (ZKExpr.Literal 0)

def ArithBinOp.toZKExpr {f} [Field f]
(op : ArithBinOp) :
ZKExpr f → ZKExpr f → ZKExpr f :=
  match op with
  | .add => ZKExpr.Add
  | .sub => ZKExpr.Sub
  | .mul => ZKExpr.Mul

def ArithBinOp.toValueOp [JoltField f]
(op : ArithBinOp) :
Value f → Value f → Value f :=
  match op with
  | .add => (λ a b =>
              match a, b with
              | Value.VField a, Value.VField b => (Value.VField (a + b))
              | _, _ => Value.None
              )
  | .sub => (λ a b =>
              match a, b with
              | Value.VField a, Value.VField b => (Value.VField (a - b))
              | _, _ => Value.None
              )
  | .mul => (λ a b =>
              match a, b with
              | Value.VField a, Value.VField b => (Value.VField (a * b))
              | _, _ => Value.None
              )

def ArithBinOp.toValOp [JoltField f]
(op : ArithBinOp) :
Val f → Val f → Val f :=
  match op with
  | .add => (λ a b =>
              match a, b with
              | Val.Field a, Val.Field b => (Val.Field (a + b))
              | _, _ => Val.None
              )
  | .sub => (λ a b =>
              match a, b with
              | Val.Field a, Val.Field b => (Val.Field (a - b))
              | _, _ => Val.None
              )
  | .mul => (λ a b =>
              match a, b with
              | Val.Field a, Val.Field b => (Val.Field (a * b))
              | _, _ => Val.None
              )

def ArithBinOp.toFieldOp {f} [Field f] (op : ArithBinOp) :
  f → f → f :=
  match op with
  | .add => (λ a b => a + b)
  | .sub => (λ a b => a - b)
  | .mul => (λ a b => a * b)

def BoolBinOp.liftM
    {f} [Field f] [JoltField f] [DecidableEq f] :
    BoolBinOp → ZKExpr f → ZKExpr f → ZKBuilder f (ZKExpr f)
  | .and, a, b => do
      let z ← Witnessable.witness
      constrainR1CS a b z             -- z = a * b
      assertIsBool z
      pure z
  | .or , a, b => do
      let z ← Witnessable.witness
      -- z = a + b - a * b   (Boolean OR over {0,1})
      constrainEq (ZKExpr.Sub (ZKExpr.Add a b) (ZKExpr.Mul a b)) z
      assertIsBool z
      pure z

def liftOpM {f} [Field f]
[JoltField f]
[DecidableEq f] :
    ArithBinOp → ZKExpr f → ZKExpr f →
    ZKBuilder f (ZKExpr f)
  | op, ea, eb => do
      let w ← Witnessable.witness
      constrainEq (op.toZKExpr ea eb) w
      pure w

def compileExpr {f} [JoltField f] [DecidableEq f] (t : Term f) (env : Env f) : ZKBuilder f (ZKExpr f) :=
  match t with
  | Term.var x =>
      match env.lookup x with
      | some (Val.Field n) => pure (ZKExpr.Literal n)
      | some (Val.Bool b)  => pure (ZKExpr.Literal (if b then 1 else 0))
      | _    => panic s!"Variable {x} not found in environment"
  | Term.lit n => pure (ZKExpr.Literal n)
  | Term.bool b => pure (ZKExpr.Literal (if b then 1 else 0))
  | Term.arith op t1 t2 => do
    let a ← compileExpr t1 env
    let b ← compileExpr t2 env
    liftOpM op a b
  | Term.boolB op t1 t2 => do
    let a ← compileExpr t1 env
    let b ← compileExpr t2 env
    BoolBinOp.liftM op a b
  | Term.eq t1 t2 => do
    let a ← compileExpr t1 env
    let b ← compileExpr t2 env
    -- z  : boolean result  (0 ⇒ false, 1 ⇒ true)
    -- inv: multiplicative inverse of (a‑b) when they differ
    let z   ← Witnessable.witness
    let inv ← Witnessable.witness
    -- If a ≠ b, then (a‑b) ≠ 0 ⇒ first constraint forces z = 0
    constrainR1CS z (ZKExpr.Sub a b) (ZKExpr.Literal 0)          -- z·(a‑b) = 0
    -- If a = b, then (a‑b)=0 ⇒ second constraint forces z = 1
    --    Otherwise it defines inv = (a‑b)⁻¹
    constrainEq
      (ZKExpr.Sub (ZKExpr.Literal 1) z)                          -- 1‑z
      (ZKExpr.Mul (ZKExpr.Sub a b) inv)                          -- (a‑b)·inv
    -- z must be 0 or 1 (booleanity)
    assertIsBool z
    return z
  | Term.ifz c t1 t2 => do
    let cond ← compileExpr c env
    let thenV ← compileExpr t1 env
    let elseV ← compileExpr t2 env
    assertIsBool cond
    let out ← Witnessable.witness
    constrainEq
      (ZKExpr.Add (ZKExpr.Mul cond thenV)
                (ZKExpr.Mul (ZKExpr.Sub (ZKExpr.Literal 1) cond) elseV))
      out
    pure out
  | Term.not e => do
    let x ← compileExpr e env
    assertIsBool x
    let z ← Witnessable.witness
    constrainEq (ZKExpr.Sub (ZKExpr.Literal 1) x) z
    assertIsBool z
    return z
  | Term.inSet t ts => do
    -- 1) compile the inner term
    let x ← compileExpr t env
    -- 2) build product P = ∏ (x - c)
    let prod ← ts.foldlM
                (fun acc c => pure (ZKExpr.Mul acc (ZKExpr.Sub x (ZKExpr.Literal c))))
                ((ZKExpr.Literal 1))
     -- 3) allocate witnesses
    let b   ← Witnessable.witness      -- Boolean result
    let inv ← Witnessable.witness      -- inverse of prod when prod ≠ 0
    -- 4) add constraints
    constrainEq (ZKExpr.Mul b prod) (ZKExpr.Literal 0)           -- b * P = 0
    constrainEq (ZKExpr.Mul prod inv)
              (ZKExpr.Sub (ZKExpr.Literal 1) b)                -- P * inv = 1 - b
    assertIsBool b                                               -- b ∈ {0,1}
     -- 5) return Boolean indicator
    return b

inductive Compiles {f} [JoltField f] [DecidableEq f] :
    Env f → Term f → ZKBuilder f (ZKExpr f) → Prop
| var_field {env x n} :
    env.lookup x = some (Val.Field n) →
    Compiles env (Term.var x) (pure (ZKExpr.Literal n))
| var_bool  {env x b} :
    env.lookup x = some (Val.Bool  b) →
    Compiles env (Term.var x) (pure (ZKExpr.Literal (if b then 1 else 0)))
| lit       {env n} :
    Compiles env (Term.lit n) (pure (ZKExpr.Literal n))
| bool      {env b} :
    Compiles env (Term.bool b) (pure (ZKExpr.Literal (if b then 1 else 0)))
| arith {env op t₁ t₂ a b} :
    Compiles env t₁ a → Compiles env t₂ b →
    Compiles env (Term.arith op t₁ t₂)
      (a >>= fun x => b >>= fun y => liftOpM op x y)
| boolB {env op t₁ t₂ a b} :
    Compiles env t₁ a → Compiles env t₂ b →
    Compiles env (Term.boolB op t₁ t₂)
      (do
        let x ← a
        let y ← b
        BoolBinOp.liftM op x y)
| eq {env t₁ t₂ a b} :
    Compiles env t₁ a → Compiles env t₂ b →
    Compiles env (Term.eq t₁ t₂)
      (do
        let x ← a
        let y ← b
        let z   ← Witnessable.witness
        let inv ← Witnessable.witness
        constrainR1CS z (ZKExpr.Sub x y) (ZKExpr.Literal 0)
        constrainEq (ZKExpr.Sub (ZKExpr.Literal 1) z) (ZKExpr.Mul (ZKExpr.Sub x y) inv)
        assertIsBool z
        pure z)
| ifz {env c t₁ t₂ ic ia ib} :
    Compiles env c  ic → Compiles env t₁ ia → Compiles env t₂ ib →
    Compiles env (Term.ifz c t₁ t₂)
      (do
        let cond ← ic
        let v₁ ← ia
        let v₂ ← ib
        assertIsBool cond
        let out ← Witnessable.witness
        constrainEq (ZKExpr.Add (ZKExpr.Mul cond v₁)
                          (ZKExpr.Mul (ZKExpr.Sub (ZKExpr.Literal 1) cond) v₂)) out
        pure out)
| not {env e ie} :
    Compiles env e ie →
    Compiles env (Term.not e)
      (do
        let x ← ie
        assertIsBool x
        let z ← Witnessable.witness
        constrainEq (ZKExpr.Sub (ZKExpr.Literal 1) x) z
        assertIsBool z
        pure z)
| inSet {env t ts it} :
    Compiles env t it →
    Compiles env (Term.inSet t ts)
      (do
        let x ← it
        let prod ← ts.foldlM
          (fun acc c => pure (ZKExpr.Mul acc (ZKExpr.Sub x (ZKExpr.Literal c))))
          (ZKExpr.Literal 1)
        let b   ← Witnessable.witness
        let inv ← Witnessable.witness
        constrainEq (ZKExpr.Mul b prod) (ZKExpr.Literal 0)
        constrainEq (ZKExpr.Mul prod inv) (ZKExpr.Sub (ZKExpr.Literal 1) b)
        assertIsBool b
        pure b)

lemma compilers_match
  {f} (instJF : JoltField f) (instDEq : DecidableEq f)
  {env t a} :
  @Compiles f instJF instDEq env t a →
  @compileExpr f instJF instDEq t env = a := by
  intros compilesPred
  induction compilesPred
  · case var_field hlookup =>
    rw [Env.lookup] at hlookup
    rw [compileExpr]
    simp [hlookup]
  · case var_bool hlookup =>
    rw [Env.lookup] at hlookup
    rw [compileExpr]
    simp [hlookup]
  · case lit =>
    rw [compileExpr]
  · case bool =>
    rw [compileExpr]
  · case arith ha hb =>
    rw [compileExpr]
    simp [ha, hb]
  · case boolB ha hb =>
    rw [compileExpr]
    simp [ha, hb]
  · case eq ha hb =>
    rw [compileExpr]
    simp [ha, hb]
  · case ifz ihc iht ihe =>
      simp [compileExpr, ihc, iht, ihe]
  · case not ha =>
    rw [compileExpr]
    simp [ha]
  · case inSet hcomp =>
    rw [compileExpr]
    simp [hcomp]

/-- Translate one effect into `ZKBuilder`. Keeps the same result type. -/
def compileEff [JoltField f] [DecidableEq f]
  (ρ : Env f) : {α : Type} → Eff f α → ZKBuilder f α
| _, .Assert (.eq a b) => do               -- α = PUnit
    let a' ← compileExpr a ρ
    let b' ← compileExpr b ρ
    constrainEq a' b'
    pure ()
| _, .Assert _        => panic! "ASSERT must be equality"
| _, .LetBinding x t  => do                -- α = Term f
  let t' ← compileExpr t ρ            -- compile RHS
  let w  ← witness                    -- fresh field witness
  constrainEq w t'
  let γ ← getEnv             -- update builder env
  putEnv (γ.insert x w)
  pure (Term.var x)

/-- Interpret a whole `Program` using the handler above. -/
def compileProgram [JoltField f] [DecidableEq f] {α}
  (p  : Program f α)
  (ρ  : Env f) : ZKBuilder f α :=
  p.mapM (compileEff ρ)
