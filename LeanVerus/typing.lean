import LeanVerus.Typ
import LeanVerus.Exp
import LeanVerus.Domain

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
  | bool { Γ } :
    Γ ⊢ ._Bool

  | int { Γ i } :
    Γ ⊢ .Int i

  | float { Γ i } :
    Γ ⊢ .Float i

  | array { Γ t } :
    Γ ⊢ t → Γ ⊢ .Array t

  | decorated { Γ d t } :
    Γ ⊢ t → Γ ⊢ .Decorated d t

  | primitive { Γ p t } :
    Γ ⊢ t → Γ ⊢ .Primitive p t

  | tuple { Γ t₁ t₂ } :
    Γ ⊢ t₁ → Γ ⊢ t₂ → Γ ⊢ .Tuple t₁ t₂

  | struct { Γ n l } :
    ∀ t ∈ l, Γ ⊢ t → Γ ⊢ .Struct n l

  | anonymous_closure { Γ l t' } :
    ∀ t ∈ l, Γ ⊢ t → Γ ⊢ t' → Γ ⊢ .AnonymousClosure l t'

  | fn_def { Γ n l } :
    ∀ t ∈ l, Γ ⊢ t → Γ ⊢ .FnDef n l

  | air_named { Γ s } :
    Γ ⊢ .AirNamed s
end

-- inductive WfTm : context → Exp → Typ → Prop
