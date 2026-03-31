import LeanVerus.Sst.Typ
import LeanVerus.Sst.Typing
import LeanVerus.Sst.Exp
import LeanVerus.Sst.Domain
import LeanVerus.Sst.Exp_Rep
import LeanVerus.Air_ast.«Air-ast»
import LeanVerus.Trans.Trans

open sst typing MSFirstOrder MSLanguage AirSorts airFunc BoundedFormula


-- The sorted carrier (AirSorts → Type) of an AirMod model.
abbrev AirMod.toFam (P T F : Type) [AirMod P T F] : AirSorts → Type := AirCarrier P T F

variable (tenv : typ_env) (dom_aux : ClosedTyp → Type)

theorem trans_sound
  {Γ : context} {t : Typ} {dom_aux : ClosedTyp → Type}
  (e₁ e₂ : sst.Exp)
  (hty₁ : Γ ⊢ e₁ : t) (hty₂ : Γ ⊢ e₂ : t)
  -- the two translations land in the same sort
  (h_sort : (trans_exp e₁ ∅).1.1 = (trans_exp e₂ ∅).1.1)
  -- in every AIR model satisfying the generated axioms, the translations evaluate equally
  (h_air : ∀ (P T F : Type) [AirMod P T F],
    AirMod.toFam P T F ⊨ (trans_exp e₁ ∅).2 ∪ (trans_exp e₂ ∅).2 →
    ∀ (v : TransVarFam →ₛ AirMod.toFam P T F),
      ((trans_exp e₁ ∅).1.2.equal (h_sort ▸ (trans_exp e₂ ∅).1.2)).Realize v) :
  -- [e₁] = [e₂]: the SST denotations agree for all variable environments
  ∀ (venv : val_vars tenv Γ dom_aux),
    exp_rep dom_aux Γ tenv venv t e₁ hty₁ = exp_rep dom_aux Γ tenv venv t e₂ hty₂ := sorry
