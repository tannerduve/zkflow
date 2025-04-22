import «ZkLeanCompiler».LCSemantics

mutual
inductive IRExpr (f : Type) [Field f] [BEq f] : Type u where
  | Const : f → IRExpr f
  | Bool  : Bool → IRExpr f
  | Add   : IRExpr f → IRExpr f → IRExpr f
  | Mul   : IRExpr f → IRExpr f → IRExpr f
  | Sub   : IRExpr f → IRExpr f → IRExpr f
  | Eq    : IRExpr f → IRExpr f → IRExpr f
  | Hash  : IRExpr f → IRExpr f
  | IfZero : IRExpr f → IRExpr f → IRExpr f → IRExpr f
deriving Inhabited

structure IR.Env (f : Type) [Field f] [BEq f] : Type u where
  lookup : String → Option (IRExpr f)
end

def IR.Env.empty {f : Type} [Field f] [BEq f] : IR.Env f :=
  { lookup := fun _ => none }

def IR.Env.insert {f : Type} [Field f] [BEq f] (x : String) (v : IRExpr f) (ρ : IR.Env f) : IR.Env f :=
  { lookup := fun y => if x == y then some v else ρ.lookup y }

partial def normalize [Field f] (t : Term f) (env : Env f) : Term f :=
  match t with
  | Term.var x =>
      match env.lookup x with
      | some (Val.Closure body cloEnv) => normalize body cloEnv
      | some (Val.Field n) => Term.lit n
      | some (Val.Bool b)  => Term.bool b
      | none => Term.var x
  | Term.app f a =>
      match normalize f env with
      | Term.lam x body =>
          let argVal := normalize a env
          let env' := Env.insert x (Val.Closure argVal env) env
          normalize body env'
      | _ => panic! "application of non-lambda"
  | Term.lam _ _ => panic! "lambda should not appear after normalization"
  | Term.add t1 t2 => Term.add (normalize t1 env) (normalize t2 env)
  | Term.mul t1 t2 => Term.mul (normalize t1 env) (normalize t2 env)
  | Term.sub t1 t2 => Term.sub (normalize t1 env) (normalize t2 env)
  | Term.hash t => Term.hash (normalize t env)
  | Term.eq t1 t2 => Term.eq (normalize t1 env) (normalize t2 env)
  | Term.ifz c t1 t2 => Term.ifz (normalize c env) (normalize t1 env) (normalize t2 env)
  | Term.lit n => Term.lit n
  | Term.bool b => Term.bool b

partial def normalizeToIR [Field f] [BEq f] [ToString f] :
  Term f → IR.Env f → StateM Nat (IRExpr f)
| Term.var x, env =>
    match env.lookup x with
    | some v => pure v
    | none => panic! s!"unbound variable: {x}"
| Term.lit n, _ => pure (IRExpr.Const n)
| Term.bool b, _ => pure (IRExpr.Bool b)
| Term.add t1 t2, env => do
    let e1 ← normalizeToIR t1 env
    let e2 ← normalizeToIR t2 env
    pure (IRExpr.Add e1 e2)
| Term.mul t1 t2, env => do
    let e1 ← normalizeToIR t1 env
    let e2 ← normalizeToIR t2 env
    pure (IRExpr.Mul e1 e2)
| Term.sub t1 t2, env => do
    let e1 ← normalizeToIR t1 env
    let e2 ← normalizeToIR t2 env
    pure (IRExpr.Sub e1 e2)
| Term.hash t, env => do
    let e ← normalizeToIR t env
    pure (IRExpr.Hash e)
| Term.eq t1 t2, env => do
    let e1 ← normalizeToIR t1 env
    let e2 ← normalizeToIR t2 env
    pure (IRExpr.Eq e1 e2)
| Term.ifz c t1 t2, env => do
    let ec ← normalizeToIR c env
    let et1 ← normalizeToIR t1 env
    let et2 ← normalizeToIR t2 env
    pure (IRExpr.IfZero ec et1 et2)
| Term.lam _ _, _ =>
    panic! "normalizeToIR: lambda abstraction not allowed in normalized IR"
| Term.app f arg, env => do
    match f with
    | Term.lam x body =>
        let argIR ← normalizeToIR arg env
        let newEnv := IR.Env.insert x argIR env
        normalizeToIR body newEnv
    | _ =>
        panic! s!"normalizeToIR: cannot apply non-lambda term"
