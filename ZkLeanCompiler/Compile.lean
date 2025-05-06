import «ZkLeanCompiler».LCSemantics
import «ZkLeanCompiler».Semantics
import Std.Data.HashMap

def assertIsBool {f} [Field f] (x : ZKExpr f) : ZKBuilder f Unit :=
  constrainR1CS x (ZKExpr.Sub (ZKExpr.Literal 1) x) (ZKExpr.Literal 0)

def withBinding (x : String) (v : ZKExpr f) (m : ZKBuilder f α) : ZKBuilder f α := do
  let st ← get
  let oldEnv := st.env
  set { st with env := oldEnv.insert x v }
  let result ← m
  modify fun st' => { st' with env := oldEnv }
  return result

def ArithBinOp.toZKExpr {f} [Field f]
(op : ArithBinOp) :
ZKExpr f → ZKExpr f → ZKExpr f :=
  match op with
  | .add => ZKExpr.Add
  | .sub => ZKExpr.Sub
  | .mul => ZKExpr.Mul


def ArithBinOp.toFieldOp [JoltField f]
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
    --    Otherwise it merely defines inv = (a‑b)⁻¹
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
