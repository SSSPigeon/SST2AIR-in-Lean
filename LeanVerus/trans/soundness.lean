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

variable (tenv : typ_env) (dom_aux : ClosedTyp → Type)



-- TODO: define a toy example

/-- Encoding from SST semantic values to AIR carrier values at the translated sort.
    For the base types:
      - Bool       → Bool  (identity)
      - Int .Int   → Int   (identity)
      - Int .Nat   → Int   (Int.ofNat coercion)
      - Int .Char  → Int   (Char.val coercion)
    For polymorphic/compound types the encoding is left as a `sorry`. -/
noncomputable def encode (t : Typ) {P T F : Type} :
    typ_interp tenv dom_aux t → AirCarrier P T F (trans_typ t) := sorry

/-- An AIR variable assignment `v` is *coherent* with an SST valuation `venv` when,
    for every de Bruijn index `i` in context `Γ`, the AIR value
      `v (trans_typ Γ[i]) i : AirCarrier P T F (trans_typ Γ[i])`
    equals the encoding of the SST value `venv i hi`. -/
def CoherentAssignment {Γ : context}
    (venv : val_vars tenv Γ dom_aux) {P T F : Type}
    (v : TransVarFam →ₛ AirCarrier P T F) : Prop :=
  ∀ (i : Nat) (hi : i < Γ.length),
    v (trans_typ Γ[i]) i = encode tenv dom_aux Γ[i] (venv i hi)

/-- Semantic equivalence of two AIR results (`.1` of `trans_exp`) under a
    variable assignment.  Handles both result shapes:
    - `.inr φ`: the expression translated to a proposition — check `φ₁ ↔ φ₂`.
    - `.inl ⟨s, tm⟩`: the expression translated to a term — check the
      evaluated values agree after aligning sorts.
    Mismatched shapes are `falsum`; for a type-directed translation of two
    expressions at the same SST type this case never arises. -/
def AirResultEquiv {Γ : context} {t : Typ}
    (e₁ e₂ : sst.Exp) (hty₁ : Γ ⊢ e₁ : t) (hty₂ : Γ ⊢ e₂ : t) : TransFormula :=
  match (trans_exp e₁ t hty₁ preludeAxioms).1, (trans_exp e₂ t hty₂ preludeAxioms).1 with
  | .inr φ₁, .inr φ₂ =>
      -- Both are propositions (e.g. boolean expressions): logical equivalence
      biff φ₁ φ₂
  | .inl ⟨s₁, tm₁⟩, .inl ⟨s₂, tm₂⟩ =>
      -- Both are terms (e.g. integer expressions): value equality
      have hty : s₁ = s₂ := by sorry
      Term.equal tm₁ (hty ▸ tm₂)
  | _, _ => falsum

theorem trans_sound
  {Γ : context} {t : Typ} {dom_aux : ClosedTyp → Type}
  (e₁ e₂ : sst.Exp)
  (hty₁ : Γ ⊢ e₁ : t) (hty₂ : Γ ⊢ e₂ : t)
  (aenv : TransAxioms)
  (venv : val_vars tenv Γ dom_aux)
  -- In every AIR model, for every AIR assignment coherent with `venv`,
  -- if the model satisfies the generated axioms, the translations are equivalent:
  (h_air : ∀ (P T F : Type) [AirMod P T F]
      (v : TransVarFam →ₛ AirMod.toFam P T F),
      CoherentAssignment tenv dom_aux venv v →
      AirMod.toFam P T F ⊨
        (trans_exp e₁ t hty₁ aenv).2 ∪ (trans_exp e₂ t hty₂ aenv).2 →
      (AirResultEquiv e₁ e₂ hty₁ hty₂).Realize v) :
  -- The SST denotations agree:
  exp_rep dom_aux Γ tenv venv t e₁ hty₁ = exp_rep dom_aux Γ tenv venv t e₂ hty₂ := sorry
