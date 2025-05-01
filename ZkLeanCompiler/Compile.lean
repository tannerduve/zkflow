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

def compileExpr {f} [Field f] (t : Term f) (env : Env f) : ZKBuilder f (ZKExpr f) :=
  match t with
  | Term.var x =>
      match env.lookup x with
      | some (Val.Field n) => pure (ZKExpr.Literal n)
      | some (Val.Bool b)  => pure (ZKExpr.Literal (if b then 1 else 0))
      | some (Val.Unit)    => pure (ZKExpr.Literal 0)
      | none               => pure (ZKExpr.Literal 0)
  | Term.lit n => pure (ZKExpr.Literal n)
  | Term.bool b => pure (ZKExpr.Literal (if b then 1 else 0))
  | Term.add t1 t2 => do
      let a ← compileExpr t1 env
      let b ← compileExpr t2 env
      let c ← Witnessable.witness
      constrainEq (ZKExpr.Add a b) c
      return c
  | Term.mul t1 t2 => do
    let a ← compileExpr t1 env
    let b ← compileExpr t2 env
    let z ← Witnessable.witness
    constrainR1CS a b z
    return z
  | Term.sub t1 t2 => do
      let a ← compileExpr t1 env
      let b ← compileExpr t2 env
      let c ← Witnessable.witness
      constrainEq (ZKExpr.Sub a b) c
      return c
  | Term.eq t1 t2 => do
    let a ← compileExpr t1 env
    let b ← compileExpr t2 env
    let z ← Witnessable.witness
    constrainR1CS z (ZKExpr.Sub a b) (ZKExpr.Literal 0)
    assertIsBool z
    return z
  | Term.ifz c t1 t2 => do
      let cond ← compileExpr c env
      let thenV ← compileExpr t1 env
      let elseV ← compileExpr t2 env
      -- Witnesses
      let isNonZero ← Witnessable.witness
      let inv ← Witnessable.witness
      let out ← Witnessable.witness
      -- cond * inv = isNonZero
      constrainEq (ZKExpr.Mul cond inv) isNonZero
      -- cond * (1 - isNonZero) = 0
      constrainEq (ZKExpr.Mul cond (ZKExpr.Sub (ZKExpr.Literal 1) isNonZero)) (ZKExpr.Literal 0)
      -- out = isNonZero * thenV + (1 - isNonZero) * elseV
      constrainEq
        (ZKExpr.Add (ZKExpr.Mul isNonZero thenV)
                  (ZKExpr.Mul (ZKExpr.Sub (ZKExpr.Literal 1) isNonZero) elseV))
        out
      pure out
  | Term.and e₁ e₂ => do
    let x ← compileExpr e₁ env
    let y ← compileExpr e₂ env
  -- Ensure x and y are boolean
    assertIsBool x
    assertIsBool y
  -- Allocate result witness
    let z ← Witnessable.witness
  -- Enforce z = x * y
    constrainR1CS x y z
  -- Enforce z is boolean
    assertIsBool z
    return z
  | Term.or e₁ e₂ => do
    let x ← compileExpr e₁ env
    let y ← compileExpr e₂ env
    assertIsBool x
    assertIsBool y
    let z ← Witnessable.witness
    constrainEq (ZKExpr.Sub (ZKExpr.Add x y) (ZKExpr.Mul x y)) z
    assertIsBool z
    return z
  | Term.not e => do
    let x ← compileExpr e env
    assertIsBool x
    let z ← Witnessable.witness
    constrainEq (ZKExpr.Neg x) z
    assertIsBool z
    return z
  | Term.lett x t1 t2 => do
    let xVal ← compileExpr t1 env
    withBinding x xVal (compileExpr t2 env)
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
  | Term.assert t => do
    let x ← compileExpr t env
    assertIsBool x
    constrainEq x (ZKExpr.Literal 1)
    return (ZKExpr.Literal 0) -- dummy value
  | Term.seq t1 t2 => do
    let _ ← compileExpr t1 env
    compileExpr t2 env
