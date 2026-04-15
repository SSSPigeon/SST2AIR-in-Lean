import LeanVerus.Sst.Typ
import LeanVerus.Sst.Typing
import LeanVerus.Sst.Exp
import LeanVerus.Sst.Domain
import LeanVerus.Sst.Exp_Rep
import LeanVerus.Air_ast.«Air-ast»
import LeanVerus.Trans.Trans
import LeanVerus.Trans.Axioms

open sst typing MSFirstOrder MSLanguage MSStructure AirSorts airFunc BoundedFormula


-- The sorted carrier (AirSorts → Type) of an AirMod model.
abbrev AirMod.toFam (P T F : Type) [AirMod P T F] : AirSorts → Type := AirCarrier P T F

variable (tenv : typ_env) (dom_aux : ClosedTyp → Type)

def Poly_domain: Type :=  Σ i : String, domain dom_aux (tenv i)

def embed (i : String) : domain dom_aux (tenv i) → Poly_domain tenv dom_aux :=
  fun x => ⟨ i, x ⟩

-- TODO: define a toy example

/-- Encoding from SST semantic values to AIR carrier values at the translated sort.
    For the base types:
      - Bool       → Bool  (identity cast)
      - Int .Int   → Int   (identity cast)
      - Int .Nat   → Int   (Int.ofNat coercion)
      - Int .Char  → Int   (Char.val.toNat coercion)
      - Float 32   → Int   (UInt32.toNat coercion)
      - Float 64   → Int   (UInt64.toNat coercion)
    For polymorphic/compound types the encoding is left as a `sorry`. -/
noncomputable def encode (t : Typ) {T F : Type}:
    /- Boxing function: maps any SST value at a closed type into the Poly carrier `P`.
    Required for type-parameter variables; should agree with AIR's `ofI`/`ofB`
    on the base types (left as a TODO coherence condition). -/
    typ_interp tenv dom_aux t → AirCarrier (Poly_domain tenv dom_aux) T F (trans_typ t) :=
  match t with
  | ._Bool       => fun v => cast interp_bool v
  | .Int .Int    => fun v => cast interp_int v
  | .Int .Nat    => fun v => Int.ofNat (cast interp_nat v)
  | .Int .Char   => fun v => Int.ofNat (cast interp_char v).val.toNat
  | .Float 32    => fun v => Int.ofNat (cast interp_float32 v).toNat
  | .Float 64    => fun v => Int.ofNat (cast interp_float64 v).toNat
  | .TypParam i  => fun v => embed tenv dom_aux i v
  | .Int (.U _)  | .Int (.I _) | .Int .USize | .Int .ISize
  | .Float _     | .StrSlice   | .Array _
  | .Tuple _ _   | .Decorated _ _ | .Struct _ _ | .Enum _ _
  | .AnonymousClosure _ _ | .SpecFn _ _ | .FnDef _ _ | .Air _ => sorry

/-- An AIR variable assignment `v` is *coherent* with an SST valuation `venv` when,
  for every de Bruijn index `i` in context `Γ`, the AIR value `v (trans_typ Γ[i]) i : AirCarrier P T F ` equals the encoding of the SST value `venv i hi`
-/
def CoherentAssignment {Γ : context}
    (venv : val_vars tenv Γ dom_aux) {T F : Type}
    (v : TransVarFam →ₛ AirCarrier (Poly_domain tenv dom_aux) T F) : Prop :=
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
  (h_air : ∀ (T F : Type) [M : AirMod (Poly_domain tenv dom_aux) T F]
      (v : TransVarFam →ₛ AirMod.toFam (Poly_domain tenv dom_aux) T F),
      CoherentAssignment tenv dom_aux venv v →
      AirMod.toFam (Poly_domain tenv dom_aux) T F ⊨
        (trans_exp e₁ t hty₁ aenv).2 ∪ (trans_exp e₂ t hty₂ aenv).2 →
      (AirResultEquiv e₁ e₂ hty₁ hty₂).Realize v) :
  -- The SST denotations agree:
  exp_rep dom_aux Γ tenv venv t e₁ hty₁ = exp_rep dom_aux Γ tenv venv t e₂ hty₂ := by sorry
