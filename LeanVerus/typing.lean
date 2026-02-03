import LeanVerus.Typ
import LeanVerus.Exp
import LeanVerus.Autosubst

namespace typing
open VerusLean

abbrev context := List Typ

declare_syntax_cat judgment
scoped syntax:50 term:51 : judgment
scoped syntax:50 term:51 " : " term:51 : judgment

syntax:25 term:51 " ⊢" judgment:50 : term

set_option hygiene false in
macro_rules
  | `($Γ ⊢ $A:term) => `(WfTp $Γ $A)
  | `($Γ ⊢ $t:term : $A:term) => `(WfTm $Γ $A $t)

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

  | decorated :
    ∀ Γ d t, Γ ⊢ t → Γ ⊢ .Decorated d t

  | primitive :
    ∀ Γ p t, Γ ⊢ t → Γ ⊢ .Primitive p t

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
  | succ {Γ A i} (B) : Lookup Γ i A → Lookup (B :: Γ) (i+1) A

inductive Lookup_field : List (String × Exp) → List Typ → String → Typ → Prop where
  | head {n : String} {e : Exp} {t : Typ} {fs : List (String × Exp)} {tys : List Typ} :
    Lookup_field ((n, e) :: fs) (t :: tys) n t
  | cons {n : String} {e : Exp} {t : Typ} {fs : List (String × Exp)} {tys : List Typ}
      {field : String} {t' : Typ} :
    Lookup_field fs tys field t → Lookup_field ((n, e) :: fs) (t' :: tys) field t


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
    ∀ Γ l A, ∀ e ∈ l, Γ ⊢ e : A → Γ ⊢ .ArrayLiteral l : .Array A

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
    ∀ Γ tys (l_ty : List Typ) l_exp body A, (_ : l_ty.length = l_exp.length) →
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
    ∀ Γ e, Γ ⊢ e : _ → Γ ⊢ .Unaryr (.HasType _) e : Typ._Bool

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
