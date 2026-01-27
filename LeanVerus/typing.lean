import LeanVerus.Typ
import LeanVerus.Exp
import LeanVerus.Domain
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
    ∀ Γ t₁ t₂, Γ ⊢ t₁ → Γ ⊢ t₂ → Γ ⊢ .Tuple t₁ t₂

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

  -- | Var (x : Nat)
  -- /-- Call to spec function -/
  -- | Call (fn : CallFun) (typs : List Typ) (exps : List Exp)
  -- | CallLambda (lam : Exp) (args : List Exp)
  -- /-- A struct constructor -/
  -- | StructCtor (dt : Ident) (fields : List (String × Exp))
  -- /-- A constructor for the datatype with the name `dt` and the given `fields`. -/
  -- -- TODO: fix the fields of EnumCtor
  -- --| EnumCtor (dt : Ident) (variant : String) (data : List (String × Exp))
  -- /- TODO -/
  -- | TupleCtor (size : Nat) (data : List Exp)
  -- /-- Primitive unary function application. -/
  -- | Unary (op : UnaryOp) (arg : Exp)
  -- | Unaryr (op : UnaryOpr) (arg : Exp)
  -- /-- Primitive binary function application. -/
  -- | Binary (op : BinaryOp) (arg₁ arg₂ : Exp)
  -- -- | Binaryr (op : BinaryOpr) (arg₁ arg₂ : Exp)
  -- | If (cond branch₁ branch₂ : Exp)
  -- | Let (tys : List Typ) (es : List Exp) (body : Exp)
  -- | Quant (q : Quant) (var : Typ) (body : Exp)
  -- | Lambda (var : Typ) (exp : Exp)
  -- --TODO: figure out what this means
  -- | ArrayLiteral (elems : List Exp)
