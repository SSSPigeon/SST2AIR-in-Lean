import LeanVerus.Typ
import LeanVerus.Exp
import LeanVerus.Autosubst

namespace typing
open VerusLean

def context := List Typ

declare_syntax_cat judgment
scoped syntax:50 term:51 : judgment
scoped syntax:50 term:51 " : " term:51 : judgment

local syntax:25 term:51 " ⊢" judgment:50 : term

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
`Lookup Γ i A l` means that `A = A'[↑ⁱ⁺¹]` where `Γ[i] = (A', l)`.
Together with `⊢ Γ`, this implies `Γ ⊢[l] .bvar i : A`. -/
inductive Lookup : context → Nat → Typ  → Prop where
  | zero (Γ A) : Lookup (A :: Γ) 0 A
  | succ {Γ A i} (B) : Lookup Γ i A → Lookup (B :: Γ) (i+1) A

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
    ∀ Γ b₁ b₂, Γ ⊢ b₁ : A → Γ ⊢ b₂ : A →
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

  -- | Var (x : Nat)
  -- | Call (fn : CallFun) (typs : List Typ) (exps : List Exp)
  -- | CallLambda (lam : Exp) (args : List Exp)
  -- | StructCtor (dt : Ident) (fields : List (String × Exp))
  -- | Unary (op : UnaryOp) (arg : Exp)
  -- | Unaryr (op : UnaryOpr) (arg : Exp)
  -- | Let (tys : List Typ) (es : List Exp) (body : Exp)
  -- | Quant (q : Quant) (var : Typ) (body : Exp)
  -- | Lambda (var : Typ) (exp : Exp)
