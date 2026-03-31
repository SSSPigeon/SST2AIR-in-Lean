import LeanVerus.Sst.Typ
import LeanVerus.Sst.Typing
import LeanVerus.Sst.Exp
import LeanVerus.Sst.Domain
import LeanVerus.Sst.Exp_Rep
import LeanVerus.Air_ast.«Air-ast»
import LeanVerus.Trans.Trans
import LeanVerus.Trans.Axioms

open sst typing MSFirstOrder MSLanguage AirSorts airFunc BoundedFormula


-- The sorted carrier (AirSorts → Type) of an AirMod model.
abbrev AirMod.toFam (P T F : Type) [AirMod P T F] : AirSorts → Type := AirCarrier P T F
abbrev AirMod.toFam' (P T F : Type) : AirSorts → Type := AirCarrier P T F
variable (tenv : typ_env) (dom_aux : ClosedTyp → Type)

lemma trans_sort_correspondence {Γ : context} {t : Typ}
  (e₁ e₂ : sst.Exp)
  (hty₁ : Γ ⊢ e₁ : t) (hty₂ : Γ ⊢ e₂ : t):
  (trans_exp e₁ preludeAxioms).1.1 = (trans_exp e₂ preludeAxioms).1.1 := sorry

-- TODO: define a toy example


theorem trans_sound
  {Γ : context} {t : Typ} {dom_aux : ClosedTyp → Type}
  (e₁ e₂ : sst.Exp)
  (hty₁ : Γ ⊢ e₁ : t) (hty₂ : Γ ⊢ e₂ : t)
  -- in every AIR model satisfying the generated axioms, the translations evaluate equally
  (h_air : ∀ (P T F : Type) [AirMod P T F],
    AirMod.toFam P T F ⊨ (trans_exp e₁ preludeAxioms).2 ∪ (trans_exp e₂ preludeAxioms).2 →
    ∀ (v : TransVarFam →ₛ AirMod.toFam P T F),
      ((trans_exp e₁ preludeAxioms).1.2.equal ((trans_sort_correspondence e₁ e₂ hty₁ hty₂) ▸ (trans_exp e₂ preludeAxioms).1.2)).Realize v) :
  -- [e₁] = [e₂]: the SST denotations agree for all variable environments
  ∀ (venv : val_vars tenv Γ dom_aux),
    -- TODO: some relations between v and venv
    exp_rep dom_aux Γ tenv venv t e₁ hty₁ = exp_rep dom_aux Γ tenv venv t e₂ hty₂ := sorry
