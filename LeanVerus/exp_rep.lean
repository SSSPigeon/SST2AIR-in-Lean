import LeanVerus.Typ
import LeanVerus.Typing
import LeanVerus.Exp
import LeanVerus.Domain

open VerusLean typing

variable (tenv : typ_env)  (dom_aux : ClosedTyp → Type)

def val_vars tenv (Γ: context) dom_aux :=  (i : Nat) → (_ : i < Γ.length) → domain dom_aux (typ_subst tenv Γ[i])


def exp_rep Γ tenv (venv: val_vars tenv Γ dom_aux) dom_aux (t : Typ) (e : Exp) (hty : Γ ⊢ e : t): typ_interp tenv dom_aux t:=
  match e with
  | .Const c =>
    match c with
    | .Bool b =>
      cast_typ_interp (ty_constbool_inv b hty).symm (cast interp_bool.symm b)
    | .Int i =>
      cast_typ_interp (ty_constint_inv i hty).symm (cast interp_int.symm i)
    | .Char c =>
      cast_typ_interp (ty_constchar_inv c hty).symm (cast interp_char.symm c)
    | .Float32 f => sorry
    | .Float64 f => sorry
    | .StrSlice s =>
      cast_typ_interp (ty_conststrslice_inv s hty).symm (cast interp_strslice.symm s)
  | _ => sorry
