import LeanVerus.Hlist
import LeanVerus.Typ
import LeanVerus.Typing
import Mathlib.Logic.IsEmpty

open VerusLean

def arg_list (domain: ClosedTyp → Type) := hlist domain

section preinterpretation
-- TODO: Consider choosing Option Type as the output type
def domain (dom_aux : ClosedTyp → Type) (t: ClosedTyp): Type :=
  match t with
  | ⟨._Bool, _⟩ => Bool
  | ⟨.Int i, _⟩ =>
    match i with
    | IntRange.Int => Int
    | IntRange.Nat => Nat
    | IntRange.U u => sorry
    | IntRange.I i => sorry
    | IntRange.USize => sorry
    | IntRange.ISize => sorry
    | IntRange.Char => Char
  | ⟨.Float w, _⟩ =>
    if w = 32 then Float32
    else if w = 64 then Float
    else Empty
  | ⟨.TypParam p, h⟩ =>
    False.elim <|
    show False from by
      have h₁ : Typ.is_closed (Typ.TypParam p) = false := rfl
      exact Bool.noConfusion (h₁.symm.trans h)
  | ⟨.Array t', h⟩ =>
    have h' : Typ.is_closed t' := by
      simp[Typ.is_closed] at h
      exact h
    List (domain dom_aux ⟨ t', h ⟩)
  | ⟨.SpecFn params ret, h⟩ => sorry
  | ⟨.Decorated dec t, h⟩ => sorry
  | ⟨.Primitive prm t, h⟩ => sorry
  | ⟨.Tuple l, h⟩ => sorry
    -- match type_rep t₁ typ_env, type_rep t₂ typ_env with
    -- | some t₁', some t₂' => some (t₁' × t₂')
    -- | _, _ => none
  | ⟨.Struct name fields, h⟩ => sorry
    -- match list_to_finType fields typ_env with
    -- | none => none
    -- | some (n, Ts) =>
    --   some (DynStruct name fields.length Ts)
  | ⟨.Enum name params, h⟩ => sorry
  | ⟨.AnonymousClosure typs typ, h⟩ => sorry
  | ⟨.FnDef fn typs, h⟩ => sorry
  | ⟨.AirNamed str, h⟩ => sorry
termination_by t.val

inductive domain_nonempty (domain : ClosedTyp -> Type) (s : ClosedTyp) : Type where
  | DE : forall (_ : domain s), domain_nonempty domain s

structure pi_dom (t: ClosedTyp) where
  dom_aux : ClosedTyp → Type
  domain_ne: forall s, domain_nonempty (domain dom_aux) s

end preinterpretation

def typ_interp (te : typ_env) (dom_aux : ClosedTyp → Type) (t : Typ) :=
  domain dom_aux (typ_subst te t)


section casting

def cast_typ_interp {te : typ_env} {dom_aux : ClosedTyp → Type} {t1 t2 : Typ} (h : t1 = t2) (e : typ_interp te dom_aux t1) :
  typ_interp te dom_aux t2 :=
  match h with
  | rfl => e

end casting
