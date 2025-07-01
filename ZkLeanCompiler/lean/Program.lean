import ZkLeanCompiler.Lean.LCSyntax
import ZkLeanCompiler.Lean.Builder

abbrev Program (f : Type) := FreeM (Eff f)

instance : Monad (Program f) := by
  unfold Program
  infer_instance

instance : LawfulMonad (Program f) := by
  unfold Program
  infer_instance

instance [Zero f] : Zero (Term f) where
  zero := Term.lit 0

def assert {f} (t : Term f) : Program f PUnit :=
  FreeM.lift (Eff.Assert t)

def letBinding {f} (x : String) (t : Term f) : Program f (Term f) :=
  FreeM.lift (Eff.LetBinding x t)
