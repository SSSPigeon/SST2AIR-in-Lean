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

-- def Poly_domain: Type :=  Σ i : String, type_env i
def Poly_domain: Type :=  Σ i : String, domain dom_aux (tenv i)

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
  | .TypParam i  => fun v => ⟨ i, v ⟩
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

/-- Coherence for `typ_rep` valuations: an AIR assignment `v` agrees with a
    `val_vars'` valuation `venv'` when, for every de Bruijn index `i` in `Γ`,
    the AIR value at sort `trans_typ Γ[i]` equals `encode'` applied to the
    `typ_rep` value `venv' i hi`. -/
def CoherentAssignment' {type_env : String → Type}
    {dom_aux' : (String → Type) → Typ → Type}
    {Γ : context}
    (venv' : @val_vars' type_env Γ dom_aux') {T F : Type}
    (v : TransVarFam →ₛ AirCarrier (Poly_rep type_env) T F) : Prop :=
  ∀ (i : Nat) (hi : i < Γ.length),
    v (trans_typ Γ[i]) i = encode' type_env dom_aux' Γ[i] (venv' i hi)

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
  | .inl ⟨s, tm⟩, .inr φ | .inr φ, .inl ⟨s, tm⟩ =>
    if h : s = .Bool
    then
      biff φ
        (Term.equal (h ▸ tm) (Term.func [] .Bool (show air_ast.Functions [] .Bool from .True) (fun j => Fin.elim0 j)))
    else falsum




/-!
## Sort-preservation of `trans_exp`

The following theorems state that `trans_exp` is *sort-preserving*:
the `.1` component of the result matches the expected shape at sort `trans_typ t`.
-/
section trans_exp_sort

variable {Γ : context} (aenv : TransAxioms)

/-- A boolean constant `b : Bool` translates to a *formula* (`.inr`):
    `True` for `b = true`, `falsum` for `b = false`.
    (Bool terms are lifted to formulas in the current encoding.) -/
theorem trans_exp_bool_const (b : Bool)
    (hty : Γ ⊢ .Const (.Bool b) : ._Bool) :
    (trans_exp (.Const (.Bool b)) ._Bool hty aenv).1 =
      .inr (if b then truth else falsum) := by
  simp [trans_exp]
  split_ifs <;> simp_all

/-- An integer constant `i : Int` (at SST type `Int.Int`) translates to an
    `Int`-sorted term (`.inl ⟨AirSorts.Int, tm⟩`). -/
theorem trans_exp_int_const (i : Int)
    (hty : Γ ⊢ .Const (.Int i) : .Int .Int) :
    ∃ tm : air_ast.Term TransVarFam AirSorts.Int,
    (trans_exp (.Const (.Int i)) (.Int .Int) hty aenv).1 = .inl ⟨AirSorts.Int, tm⟩ := by
  simp [trans_exp]
  split_ifs <;> exact ⟨_, rfl⟩

/-- A natural-number constant `n : Nat` (represented as a non-negative `Int` at
    SST type `Int.Nat`) also translates to an `Int`-sorted term. -/
theorem trans_exp_nat_const (n : Nat)
    (hty : Γ ⊢ .Const (.Int (Int.ofNat n)) : .Int .Nat) :
    ∃ tm : air_ast.Term TransVarFam AirSorts.Int,
    (trans_exp (.Const (.Int (Int.ofNat n))) (.Int .Nat) hty aenv).1 =
      .inl ⟨AirSorts.Int, tm⟩ := by
  simp [trans_exp]

/-- A variable at de Bruijn index `idx` with SST type `t` translates to a term
    at sort `trans_typ t` — the variable `idx` itself, coerced to that sort. -/
theorem trans_exp_var (idx : Nat) (t : Typ)
    (hty : Γ ⊢ .Var idx : t) :
    (trans_exp (.Var idx) t hty aenv).1 =
      .inl ⟨trans_typ t, Term.var (trans_typ t) idx⟩ := by
  simp [trans_exp]
  cases t <;> simp [trans_typ]

end trans_exp_sort

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
  exp_rep dom_aux Γ tenv venv t e₁ hty₁ =
  exp_rep dom_aux Γ tenv venv t e₂ hty₂
  := by sorry

/-- `typ_rep`-based soundness: same statement as `trans_sound` but for open type
    environments.  Uses `CoherentAssignment'` (w.r.t. `encode'` / `Poly_rep`) and
    concludes that the `exp_rep'` denotations agree. -/
theorem trans_sound'
  {type_env : String → Type} {dom_aux' : (String → Type) → Typ → Type}
  {Γ : context} {t : Typ}
  (e₁ e₂ : sst.Exp)
  (hty₁ : Γ ⊢ e₁ : t) (hty₂ : Γ ⊢ e₂ : t)
  (aenv : TransAxioms)
  (venv' : @val_vars' type_env Γ dom_aux')
  (h_air : ∀ (T F : Type) [M : AirMod (Poly_rep type_env) T F]
      (v : TransVarFam →ₛ AirMod.toFam (Poly_rep type_env) T F),
      CoherentAssignment' venv' v →
      AirMod.toFam (Poly_rep type_env) T F ⊨
        (trans_exp e₁ t hty₁ aenv).2 ∪ (trans_exp e₂ t hty₂ aenv).2 →
      (AirResultEquiv e₁ e₂ hty₁ hty₂).Realize v) :
  -- The typ_rep denotations agree:
  @exp_rep' type_env dom_aux' Γ venv' t e₁ hty₁ =
  @exp_rep' type_env dom_aux' Γ venv' t e₂ hty₂
  := by sorry
