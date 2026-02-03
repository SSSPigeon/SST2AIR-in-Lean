import LeanVerus.Typ
import LeanVerus.Typing
import LeanVerus.Exp
import LeanVerus.Domain

open VerusLean typing

variable (tenv : typ_env)  (dom_aux : ClosedTyp → Type)

def val_vars tenv (Γ: context) dom_aux :=  (i : Nat) → (_ : i < Γ.length) → domain dom_aux (typ_subst tenv Γ[i])


def exp_rep Γ tenv (venv: val_vars tenv Γ dom_aux) dom_aux (t : Typ) (e : Exp) (hty : Γ ⊢ e : t): typ_interp tenv dom_aux t:=
  sorry
  -- match e with
  -- | .Const c =>
  --   match c with
  --   | .Bool b => b
  --   | .Int i =>
  --     match i with
  --     | IntRange.Int => sorry
  --     | IntRange.Nat => sorry
  --     | IntRange.U u => sorry
  --     | IntRange.I i => sorry
  --     | IntRange.USize => sorry
  --     | IntRange.ISize => sorry
  --     | IntRange.Char => sorry
  --   | .Float32 f => f
  --   | .Float64 f => f
  --   | _ => sorry
  -- | _ => sorry
