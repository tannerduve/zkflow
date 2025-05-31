import «ZkLeanCompiler».LCSemantics
import «ZkLeanCompiler».Semantics
import Std.Data.HashMap

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

def ArithBinOp.toValOp [JoltField f]
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
  | Term.lett x t1 t2 => do
    -- 1.  evaluate / constant–fold the bound expression
    match eval t1 env with
    | some v =>
        -- 2. extend the environment before compiling the body
        let env' := env.insert x v
        compileExpr t2 env'
    | none =>
        -- could not evaluate at compile time → just ignore the binding
        compileExpr t2 env
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
  | Term.assert t₁ t₂ => do
    let cond ← compileExpr t₁ env
    assertIsBool cond
    constrainEq cond (ZKExpr.Literal 1)
    compileExpr t₂ env
  | Term.seq t1 t2 => do
    let _ ← compileExpr t1 env
    compileExpr t2 env

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
| lett_eval {env x t₁ t₂ v body} :
    eval t₁ env = some v →
    Compiles (env.insert x v) t₂ body →
    Compiles env (Term.lett x t₁ t₂) body
| lett_skip {env x t₁ t₂ body} :
    eval t₁ env = none →
    Compiles env t₂ body →
    Compiles env (Term.lett x t₁ t₂) body
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
| assert {env cond body ic ib} :
    Compiles env cond ic → Compiles env body ib →
    Compiles env (Term.assert cond body)
      (do
        let c ← ic
        assertIsBool c
        constrainEq c (ZKExpr.Literal 1)
        ib)
| seq {env t₁ t₂ ia ib} :
    Compiles env t₁ ia → Compiles env t₂ ib →
    Compiles env (Term.seq t₁ t₂)
      (do
        let _ ← ia
        ib)

lemma compilers_match
  {f} (instJF : JoltField f) (instDEq : DecidableEq f)
  {env t a} :
  @Compiles f instJF instDEq env t a →
  @compileExpr f instJF instDEq t env = a := by
  intros compilesPred
  induction compilesPred
  · case var_field env' x n hlookup =>
    rw [Env.lookup] at hlookup
    rw [compileExpr]
    simp [hlookup]
  · case var_bool env' x b hlookup =>
    rw [Env.lookup] at hlookup
    rw [compileExpr]
    simp [hlookup]
  · case lit env' n =>
    rw [compileExpr]
  · case bool env' b =>
    rw [compileExpr]
  · case arith env' op t₁ t₂ a b ha hb =>
    rw [compileExpr]
    simp [ha, hb]
  · case boolB env' op t₁ t₂ a b ha hb =>
    rw [compileExpr]
    simp [ha, hb]
  · case eq env' t₁ t₂ a b ha hb =>
    rw [compileExpr]
    simp [ha, hb]
  · case ifz env c t₁ t₂ ic ia ib ihc iht ihe =>
      simp [compileExpr, ihc, iht, ihe]
  · case not env' e ie ha =>
    rw [compileExpr]
    simp [ha]
  · case lett_eval env' x t₁ t₂ v body heval hcomp hexpr =>
    rw [compileExpr]
    simp [heval, hcomp]
    exact hexpr
  · case lett_skip body env' x t₁ t₂ heval hcomp hexpr =>
    rw [compileExpr]
    simp [heval, hcomp]
    exact hexpr
  · case inSet env' t ts it hcomp =>
    rw [compileExpr]
    simp [hcomp]
  · case assert env' cond body ic ib hcomp hbody =>
    rw [compileExpr]
    simp [hcomp, hbody]
  · case seq env' t₁ t₂ ia ib ha hb =>
    rw [compileExpr]
    simp [ha, hb]
