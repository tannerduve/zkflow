import «ZkLeanCompiler».LCSemantics

variable {F} [Field F] [BEq F] [ToString F] [Inhabited F]

def context := String → (Option Ty)

def context.empty : context :=
  fun _ => none

def context.insert (Γ : context) (x : String) (T : Option Ty) : context :=
  fun y => if x == y then T else Γ y

inductive has_type : context → Term F → Ty → Prop where
  | T_Var : ∀ Γ x T,
      Γ x = some T →
      has_type Γ (Term.var x) T
  | T_Bool : ∀ Γ b,
      has_type Γ (Term.bool b) Ty.bool
  | T_Lit : ∀ Γ n,
      has_type Γ (Term.lit n) Ty.base
  | T_Abs : ∀ x T1 T2 t1 Γ,
      has_type (Γ.insert x (some T2)) t1 T1 →
      has_type Γ (Term.lam x T1 y) (Ty.arrow T2 T1)
  | T_App : ∀ Γ t1 t2 T1 T2,
      has_type Γ t1 (Ty.arrow T2 T1) →
      has_type Γ t2 T2 →
      has_type Γ (t1 ∘ t2) T1
  | T_Add : ∀ Γ t1 t2,
      has_type Γ t1 Ty.base →
      has_type Γ t2 Ty.base →
      has_type Γ (t1 ⊕ t2) Ty.base
  | T_Sub : ∀ Γ t1 t2,
      has_type Γ t1 Ty.base →
      has_type Γ t2 Ty.base →
      has_type Γ (t1 ∼ t2) Ty.base
  | T_Mul : ∀ Γ t1 t2,
      has_type Γ t1 Ty.base →
      has_type Γ t2 Ty.base →
      has_type Γ (t1 ⊗ t2) Ty.base
  | T_Eq : ∀ Γ t1 t2,
      has_type Γ t1 Ty.base →
      has_type Γ t2 Ty.base →
      has_type Γ (t1 =-= t2) Ty.bool
  | T_Ifz : ∀ Γ t1 t2 T1 T2 t3,
      has_type Γ t1 Ty.bool →
      has_type Γ t2 T1 →
      has_type Γ t3 T2 →
      has_type Γ (Term.ifz t1 t2 t3) Ty.base
