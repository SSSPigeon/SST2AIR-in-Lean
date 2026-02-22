import LeanVerus.Sst.Typ
import LeanVerus.Sst.Exp
import LeanVerus.Sst.Autosubst

import Mathlib.Tactic.Lift

namespace typing
open sst

abbrev context := List Typ

declare_syntax_cat judgment
scoped syntax:50 term:51 : judgment
scoped syntax:50 term:51 " : " term:51 : judgment

syntax:25 term:51 " ⊢" judgment:50 : term
syntax:25 term:51 " ⊢.{" level "} " judgment:50 : term

set_option hygiene false in
macro_rules
  | `($Γ ⊢ $A:term) => `(WfTp $Γ $A)
  | `($Γ ⊢ $t:term : $A:term) => `(WfTm $Γ $A $t)
  | `($Γ ⊢.{ $u } $t:term : $A:term) => `(WfTm.{ $u } $Γ $A $t)


mutual
/-- All types in the given context are well-formed. -/
inductive WfCtx : context → Prop
  | nil : WfCtx []
  | snoc {Γ A} :
    WfCtx Γ →
    Γ ⊢ A →
    WfCtx (A :: Γ)

/-- From Why3-Coq: no types with type variables can ever be valid. -/
inductive WfTp : context → Typ → Prop
  | bool :
    ∀ Γ, Γ ⊢ ._Bool

  | int :
    ∀ Γ i, Γ ⊢ .Int i

  | float :
    ∀ Γ i, Γ ⊢ .Float i

  | array :
    ∀ Γ t, Γ ⊢ t → Γ ⊢ .Array t

  | strslice :
    ∀ Γ, Γ ⊢ .StrSlice

  | decorated :
    ∀ Γ d t, Γ ⊢ t → Γ ⊢ .Decorated d t

  -- | primitive :
  --   ∀ Γ p t, Γ ⊢ t → Γ ⊢ .Primitive p t

  | tuple :
    ∀ Γ l, ∀ t ∈ l, Γ ⊢ t → Γ ⊢ .Tuple l

  | struct :
    ∀ Γ n l, ∀ t ∈ l, Γ ⊢ t → Γ ⊢ .Struct n l

  | anonymous_closure :
    ∀ Γ l t', ∀ t ∈ l, Γ ⊢ t → Γ ⊢ t' → Γ ⊢ .AnonymousClosure l t'

  | fn_def :
    ∀ Γ n l, ∀ t ∈ l, Γ ⊢ t → Γ ⊢ .FnDef n l

  | air_named :
    ∀ Γ s, Γ ⊢ .AirNamed s
end


/--
From HoTTLean:
`Lookup Γ i A` means that `A = A'[↑ⁱ⁺¹]` where `Γ[i] = A'`.
Together with `⊢ Γ`, this implies `Γ ⊢[l] .bvar i : A`. -/
inductive Lookup : context → Nat → Typ  → Prop where
  | zero (Γ A) : Lookup (A :: Γ) 0 A
  | succ (Γ A i B) : Lookup Γ i A → Lookup (B :: Γ) (i+1) A

inductive Lookup_field : List (String × Exp) → List Typ → String → Typ → Prop where
  | head {n : String} {e : Exp} {t : Typ} {fs : List (String × Exp)} {tys : List Typ} :
    Lookup_field ((n, e) :: fs) (t :: tys) n t
  | cons {n : String} {e : Exp} {t : Typ} {fs : List (String × Exp)} {tys : List Typ}
      {field : String} {t' : Typ} :
    Lookup_field fs tys field t → Lookup_field ((n, e) :: fs) (t' :: tys) field t

set_option pp.universes true

#check Typ
#check context
#check Exp
inductive WfTm : context → Typ → Exp → Prop
  | T_bool :
    ∀ Γ b, Γ ⊢ Exp.Const (.Bool b) : Typ._Bool

  | T_int :
    ∀ Γ i, Γ ⊢ Exp.Const (.Int i) : (.Int .Int)

  | T_char :
    ∀ Γ c, Γ ⊢ Exp.Const (.Char c) : (.Int .Char)

  | T_float32 :
    ∀ Γ f, Γ ⊢ Exp.Const (.Float32 f) : (.Float 32)

  | T_float64 :
    ∀ Γ f, Γ ⊢ Exp.Const (.Float64 f) : (.Float 64)

  | T_tuple :
    ∀ Γ s (l_ty : List Typ) l_exp, (_ : l_ty.length = l_exp.length) →
    ∀ i, (_ : i ≥ 0 ∧ i < l_ty.length) → Γ ⊢ l_exp[i] : l_ty[i] →
    Γ ⊢ .TupleCtor s l_exp : (.Tuple l_ty)

  | T_array :
    ∀ Γ l A, (∀ e ∈ l, Γ ⊢ e : A) → Γ ⊢ .ArrayLiteral l : .Array A

  | T_strslice :
    ∀ Γ s, Γ ⊢ Exp.Const (.StrSlice s) : .StrSlice

  | T_if :
    ∀ Γ c b₁ b₂ A, Γ ⊢ c : Typ._Bool → Γ ⊢ b₁ : A → Γ ⊢ b₂ : A →
    Γ ⊢ .If c b₁ b₂ : A

  | T_and :
    ∀ Γ b₁ b₂, Γ ⊢ b₁ : Typ._Bool → Γ ⊢ b₂ : Typ._Bool →
    Γ ⊢ .Binary .And b₁ b₂ : Typ._Bool

  | T_or :
    ∀ Γ b₁ b₂, Γ ⊢ b₁ : Typ._Bool → Γ ⊢ b₂ : Typ._Bool →
    Γ ⊢ .Binary .Or b₁ b₂ : Typ._Bool

  | T_xor :
    ∀ Γ b₁ b₂, Γ ⊢ b₁ : Typ._Bool → Γ ⊢ b₂ : Typ._Bool →
    Γ ⊢ .Binary .Xor b₁ b₂ : Typ._Bool

  | T_implies :
    ∀ Γ b₁ b₂, Γ ⊢ b₁ : Typ._Bool → Γ ⊢ b₂ : Typ._Bool →
    Γ ⊢ .Binary .Implies b₁ b₂ : Typ._Bool

  | T_eq :
    ∀ Γ b₁ b₂, Γ ⊢ b₁ : Typ._Bool → Γ ⊢ b₂ : Typ._Bool →
    Γ ⊢ .Binary (.Eq _) b₁ b₂ : Typ._Bool

  | T_ineq :
    ∀ Γ b₁ b₂ A, Γ ⊢ b₁ : A → Γ ⊢ b₂ : A →
    Γ ⊢ .Binary (.Inequality _) b₁ b₂ : Typ._Bool

  /-- TODO: Add more possibilities, e.g., Γ ⊢ b₁ : Float -/
  | T_arith :
    ∀ Γ b₁ b₂, Γ ⊢ b₁ : .Int .Int → Γ ⊢ b₂ : .Int .Int →
    Γ ⊢ .Binary (.Arith _ _) b₁ b₂ : .Int .Int

  | T_bitwise :
    ∀ Γ b₁ b₂, Γ ⊢ b₁ : .Int .Int → Γ ⊢ b₂ : .Int .Int →
    Γ ⊢ .Binary (.Bitwise _ _) b₁ b₂ : .Int .Int

  /--TODO: Can i be of other types, like usize? -/
  | T_index :
    ∀ Γ a i A, Γ ⊢ a : .Array A → Γ ⊢ i : .Int .Int →
    Γ ⊢ .Binary (.Index _ _) a i : A

  | T_let :
    ∀ Γ (l_ty : List Typ) l_exp body A, (_ : l_ty.length = l_exp.length) →
    ∀ i, (_ : i ≥ 0 ∧ i < l_ty.length) → Γ ⊢ l_exp[i] : l_ty[i] →
    l_ty.reverse.append Γ ⊢ body : A → Γ ⊢ .Let l_ty l_exp body : A

  /-- Only closures in spec and proof mode are turned into λ-expressions. See the examples closure.rs, and closure_exec.rs-/
  | T_lambda :
    ∀ Γ A e B, A :: Γ ⊢ e : B → Γ ⊢ .Lambda A e : Typ.SpecFn [A] B

  | T_quant :
    ∀ Γ A e B, A :: Γ ⊢ e : B → Γ ⊢ .Quant _ A e : Typ._Bool

  | T_call :
    ∀ Γ fn (l_ty : List Typ) l_exp ty, (_ : l_ty.length = l_exp.length) →
    ∀ i, (_ : i ≥ 0 ∧ i < l_ty.length) → Γ ⊢ l_exp[i] : l_ty[i] →
    Γ ⊢ .Call fn l_ty l_exp ty : ty

  | T_callLambda :
    ∀ Γ lam A B e, Γ ⊢ lam : Typ.SpecFn [A] B → Γ ⊢ e : A →
    Γ ⊢ .CallLambda lam e : B

  | T_var :
    ∀ Γ i A, Lookup Γ i A → Γ ⊢ .Var i : A

  | T_not :
    ∀ Γ b, Γ ⊢ b : Typ._Bool → Γ ⊢ .Unary .Not b : Typ._Bool

  /-- TODO: Add more possibilities of i -/
  | T_bitnot :
    ∀ Γ i, Γ ⊢ i : .Int .Int → Γ ⊢ .Unary (.BitNot _) i : .Int .Int

  /-- TODO: Add more possibilities of i -/
  | T_clip :
    ∀ Γ i, Γ ⊢ i : .Int .Int → Γ ⊢ .Unary (.Clip _ _) i : .Int .Int

  | T_floatToBits32 :
    ∀ Γ f, Γ ⊢ f : .Float 32 → Γ ⊢ .Unary .FloatToBits f : .Int .Int

  | T_floatToBits64 :
    ∀ Γ f, Γ ⊢ f : .Float 64 → Γ ⊢ .Unary .FloatToBits f : .Int .Int

  | T_box :
    ∀ Γ e A, Γ ⊢ e : A → Γ ⊢ .Unaryr (.Box A) e : .Decorated .Box A

  | T_unbox :
    ∀ Γ e A, Γ ⊢ e : .Decorated .Box A → Γ ⊢ .Unaryr (.Unbox A) e : A

  | T_hasType :
    ∀ Γ e t, Γ ⊢ .Unaryr (.HasType t) e : Typ._Bool

  | T_isVariant :
    ∀ Γ e, Γ ⊢ e : _ → Γ ⊢ .Unaryr (.IsVariant _ _) e : Typ._Bool

  | T_structCtor :
    ∀ Γ dt fields l_ty, (_ : l_ty.length = fields.length) →
    ∀ i, (_ : i ≥ 0 ∧ i < l_ty.length) → Γ ⊢ fields[i].2 : l_ty[i] →
    Γ ⊢ .StructCtor dt fields : .Struct dt l_ty

  | T_proj :
    ∀ Γ e A fields field l_ty, Γ ⊢ e : .Struct _ l_ty →
    Lookup_field fields l_ty field A →
    Γ ⊢ .Unaryr (.Proj field) e : A


variable {Γ : context} {e : Exp} {t : Typ}

lemma ty_constbool_inv (b : Bool)(h : Γ ⊢ Exp.Const (.Bool b) : t) : t = Typ._Bool := by
  match h with
  | WfTm.T_bool _ _ => rfl

lemma ty_constint_inv (i : Int)(h : Γ ⊢ Exp.Const (.Int i) : t) : t = Typ.Int .Int := by
  match h with
  | WfTm.T_int _ _ => rfl

lemma ty_constchar_inv (c : Char)(h : Γ ⊢ Exp.Const (.Char c) : t) : t = Typ.Int .Char := by
  match h with
  | WfTm.T_char _ _ => rfl

lemma ty_constfloat32_inv (f : UInt32)(h : Γ ⊢ Exp.Const (.Float32 f) : t) : t = Typ.Float 32 := by
  match h with
  | WfTm.T_float32 _ _ => rfl

lemma ty_constfloat64_inv (f : UInt64)(h : Γ ⊢ Exp.Const (.Float64 f) : t) : t = Typ.Float 64 := by
  match h with
  | WfTm.T_float64 _ _ => rfl

lemma ty_strslice_inv (s : String)(h : Γ ⊢ Exp.Const (.StrSlice s) : t) : t = Typ.StrSlice := by
  match h with
  | WfTm.T_strslice _ _ => rfl

lemma ty_var_withinbound (i : Nat)(h : Γ ⊢ .Var i : t) : i < Γ.length := by
  match h with
  | WfTm.T_var _ _ _ h =>
    induction h with
    | zero _ _ => simp
    | succ Γ A i B h ih =>
      simp
      expose_names
      exact ih (WfTm.T_var Γ i A h_1)

lemma ty_var_inv (i : Nat)(h : Γ ⊢ .Var i : t) :  t = Γ[i]'(ty_var_withinbound i h) := by
  match h with
  | WfTm.T_var _ _ _ h =>
    induction h with
    | zero _ _ => rfl
    | succ Γ A i B h ih =>
      simp
      expose_names
      exact ih (WfTm.T_var Γ i A h_1)

-- def array_elem_typ (l : List Exp)(h : Γ ⊢ .ArrayLiteral l : t) : Typ :=
--   match h with
--   | WfTm.T_array _ _ A _ _ _ => A

-- def ty_array_inv (l : List Exp)(h : Γ ⊢ .ArrayLiteral l : t) : Σ A : Typ, PLift (t = .Array A) :=
--   match h with
--   | WfTm.T_array _ _ A _ _ _ => ⟨A, PLift.up rfl⟩

-- def ty_array_inv (l : List Exp)(h : Γ ⊢ .ArrayLiteral l : t) : { A : Typ // (t = .Array A) }:=
--   match h with
--   | WfTm.T_array _ _ A h' => ⟨A, rfl⟩

set_option pp.universes true
lemma ty_array_inv (l : List Exp)(h : Γ ⊢ Exp.ArrayLiteral l : t) : ∃ A : Typ, t = .Array A ∧ (∀ e ∈ l, Γ ⊢ e : A) :=
  match h with
  | WfTm.T_array _ _ A h' =>
    ⟨A, rfl, h'⟩

-- noncomputable
-- def array_elem_typ (l : List Exp)(h : Γ ⊢ .ArrayLiteral l : t) : Typ :=
--   Classical.choose (ty_array_inv l h)

-- set_option pp.universes true

-- def array_elem_typing (l : List Exp)(h : Γ ⊢ .ArrayLiteral l : t) : (∀ e ∈ l, Γ ⊢ e : array_elem_typ l h) := by
--   intros e he
--   match h with
--   | .T_array _ _ A h' =>
--     have : array_elem_typ l (WfTm.T_array Γ l A h') = A := by
--       have := (Classical.choose_spec (ty_array_inv l (WfTm.T_array Γ l A h'))).symm
--       injection this
--     rw[this]
--     --change WfTm.{u_1} Γ A e
--     --exact h' e he
--     sorry

lemma ty_hasType_inv (e : Exp)(A B: Typ)(h : Γ ⊢ .Unaryr (.HasType A) e : B) : B = ._Bool :=
  match h with
  | WfTm.T_hasType _ _ h' => rfl

lemma ty_not_inv (b : Exp) (h : Γ ⊢ .Unary .Not b : t) : t = ._Bool ∧ (Γ ⊢ b : t) :=
  match h with
  | WfTm.T_not _ _ h => ⟨ rfl, h ⟩

-- lemma ty_floatToBits_inv (f : Exp) (h : Γ ⊢.{u} .Unary .FloatToBits f : t) : (Γ ⊢.{u} f : .Float 32) ∨ (Γ ⊢.{u} f : .Float 64) :=
--   match h with
--   | WfTm.T_floatToBits32 _ _ h => Or.inl h
--   | WfTm.T_floatToBits64 _ _ h => Or.inr h

-- def ty_floatToBits_inv (f : Exp) (h : Γ ⊢.{u} .Unary .FloatToBits f : t) : UInt32 :=
--   match h with
--   | WfTm.T_floatToBits32 _ _ h => Or.inl h
--   | WfTm.T_floatToBits64 _ _ h => Or.inr h

end typing
