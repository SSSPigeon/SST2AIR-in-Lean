import LeanVerus.Util.Hlist
import LeanVerus.Sst.Typ
import LeanVerus.Sst.Typing
import LeanVerus.Air_ast.«Air-ast»
import LeanVerus.Trans.Trans
-- import Mathlib.Logic.IsEmpty

open sst

def arg_list (domain: ClosedTyp → Type) := hlist domain

section preinterpretation

inductive TypeError : Type where
  | UninterpretedType

inductive ExpError : Type where
  | RuntimeErr

def typ_rep (type_env : String → Type) (dom_aux : (String → Type) → Typ → Type) (t: Typ): Type :=
  match t with
  | ._Bool => Bool
  | .Int i =>
    match i with
    | IntRange.Int => Int
    | IntRange.Nat => Nat
    | IntRange.U u => sorry
    | IntRange.I i => sorry
    | IntRange.USize => sorry
    | IntRange.ISize => sorry
    | IntRange.Char => Char
  | .Float w =>
    if w = 32 then UInt32
    else if w = 64 then UInt64
    else TypeError
  | .TypParam p => type_env p
  | .Array t' =>
    List (typ_rep type_env dom_aux t')
  | .StrSlice => String
  | .Tuple t₁ t₂ =>
    (typ_rep type_env dom_aux t₁) × (typ_rep type_env dom_aux t₂)
  | _ => sorry
termination_by t

-- TODO: Consider choosing Option Type as the output type
def domain (dom_aux : ClosedTyp → Type) (t: ClosedTyp): Type :=
  match t with
  -- | .Typparam i => type_env i
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
    if w = 32 then UInt32
    else if w = 64 then UInt64
    else TypeError
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
  | ⟨.StrSlice, _⟩ => String
  | ⟨.SpecFn params ret, h⟩ => sorry
  | ⟨.Decorated dec t, h⟩ => sorry
  -- |  ⟨.Primitive prm t, h⟩ =>
  --   match prm with
  --   | .Array => sorry
  --   | .StrSlice => String
  | ⟨.Tuple t₁ t₂, h⟩ =>
    (domain dom_aux ⟨ t₁, by simp[Typ.is_closed] at h; exact h.1 ⟩) × (domain dom_aux ⟨ t₂, by simp[Typ.is_closed] at h; exact h.2 ⟩ )
  | ⟨.Struct name fields, h⟩ => sorry
    -- match list_to_finType fields typ_env with
    -- | none => none
    -- | some (n, Ts) =>
    --   some (DynStruct name fields.length Ts)
  | ⟨.Enum name params, h⟩ => sorry
  | ⟨.AnonymousClosure typs typ, h⟩ => sorry
  | ⟨.FnDef fn typs, h⟩ => sorry
  | ⟨.Air asort, h⟩ => sorry
termination_by t.val

inductive domain_nonempty (domain : ClosedTyp -> Type) (s : ClosedTyp) : Type where
  | DE : forall (_ : domain s), domain_nonempty domain s

structure pi_dom (t: ClosedTyp) where
  dom_aux : ClosedTyp → Type
  domain_ne: forall s, domain_nonempty (domain dom_aux) s

end preinterpretation

def typ_interp (te : typ_env) (dom_aux : ClosedTyp → Type) (t : Typ): Type :=
  domain dom_aux (typ_subst te t)

section interp_results

variable {tenv : typ_env} {dom_aux : ClosedTyp → Type} {t1 t2 : Typ}
{type_env : String → Type} {dom_aux' : (String → Type) → Typ → Type}

def interp_bool' : typ_rep type_env dom_aux' Typ._Bool = Bool := by
  simp[typ_rep]

def interp_int' : typ_rep type_env dom_aux' (Typ.Int .Int) = Int := by
  simp[typ_rep]

def interp_nat' : typ_rep type_env dom_aux' (Typ.Int .Nat) = Nat := by
  simp[typ_rep]

def interp_char' : typ_rep type_env dom_aux' (Typ.Int .Char) = Char := by
  simp[typ_rep]

def interp_float32' : typ_rep type_env dom_aux' (Typ.Float 32) = UInt32 := by
  simp[typ_rep]

def interp_float64' : typ_rep type_env dom_aux' (Typ.Float 64) = UInt64 := by
  simp[typ_rep]

def interp_strslice' : typ_rep type_env dom_aux' Typ.StrSlice = String := by
  simp[typ_rep]

def interp_typparam' (p : String) : typ_rep type_env dom_aux' (Typ.TypParam p) = type_env p := by
  simp[typ_rep]

def interp_bool : typ_interp tenv dom_aux Typ._Bool = Bool := by
  simp[typ_interp, typ_subst, domain]

def interp_int : typ_interp tenv dom_aux (Typ.Int .Int) = Int := by
  simp[typ_interp, typ_subst, domain]

def interp_nat : typ_interp tenv dom_aux (Typ.Int .Nat) = Nat := by
  simp[typ_interp, typ_subst, domain]

def interp_char : typ_interp tenv dom_aux (Typ.Int .Char) = Char := by
  simp[typ_interp, typ_subst, domain]

def interp_float32 : typ_interp tenv dom_aux (Typ.Float 32) = UInt32 := by
  simp[typ_interp, typ_subst, domain]

def interp_float64 : typ_interp tenv dom_aux (Typ.Float 64) = UInt64 := by
  simp[typ_interp, typ_subst, domain]

def interp_strslice : typ_interp tenv dom_aux Typ.StrSlice = String := by
  simp[typ_interp, typ_subst, domain]

def interp_array (t : Typ) : typ_interp tenv dom_aux (Typ.Array t) = List (typ_interp tenv dom_aux t) := by
  simp[typ_interp, typ_subst, domain]

def interp_tuple (t₁ t₂ : Typ) : typ_interp tenv dom_aux (Typ.Tuple t₁ t₂) = ((typ_interp tenv dom_aux t₁) × (typ_interp tenv dom_aux t₂)) := by
  simp[typ_interp, typ_subst, domain]


end interp_results

section casting

def cast_typ_interp {te : typ_env} {dom_aux : ClosedTyp → Type} {t1 t2 : Typ} (h : t1 = t2) (e : typ_interp te dom_aux t1) :
  typ_interp te dom_aux t2 :=
  match h with
  | rfl => e

end casting

section encode'

open MSFirstOrder MSLanguage AirSorts

/-- Poly carrier for `typ_rep`: packages type-parameter values. -/
def Poly_rep (type_env : String → Type) : Type := Σ i : String, type_env i

/-- Encode a `typ_rep` value into the AIR carrier at the translated sort. -/
def encode' (type_env : String → Type)
    (dom_aux' : (String → Type) → Typ → Type)
    (t : Typ) {T F : Type} :
    typ_rep type_env dom_aux' t →
    MSLanguage.AirCarrier (Poly_rep type_env) T F (trans_typ t) :=
  match t with
  | ._Bool      => fun v => cast interp_bool' v
  | .Int .Int   => fun v => cast interp_int' v
  | .Int .Nat   => fun v => Int.ofNat (cast interp_nat' v)
  | .Int .Char  => fun v => Int.ofNat (cast interp_char' v).val.toNat
  | .Float 32   => fun v => Int.ofNat (cast interp_float32' v).toNat
  | .Float 64   => fun v => Int.ofNat (cast interp_float64' v).toNat
  | .TypParam p => fun v => ⟨p, cast (interp_typparam' p) v⟩
  | _           => sorry

end encode'
