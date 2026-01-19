import LeanVerus.My_sst

open VerusLean

namespace sst_semantics



structure DynStruct (name : Ident) (n : Nat) (Ts : Fin n → Type) where
  fields : (i : Fin n) → Ts i

mutual
def type_rep (t : Typ) (typ_env : String → Typ):  Option Type :=
  match t with
  | ._Bool => some Bool
  | .Int i =>
    match i with
    | IntRange.Int => some Int
    | IntRange.Nat => some Nat
    | IntRange.U u => sorry
    | IntRange.I i => sorry
    | IntRange.USize => sorry
    | IntRange.ISize => sorry
    | IntRange.Char => some Char
  | .Float w =>
    if w = 32 then some Float32
    else if w = 64 then some Float
    else none
  | .Array t =>
    match type_rep t typ_env with
    | some t' => some (Array t')
    | none => none
  | .TypParam p => type_rep (typ_env p) typ_env
  | .SpecFn params ret => sorry
  --TODO: corresponding expressions in my_sst?
  | .Decorated dec t => sorry
  --TODO: check this in verus.src, and see if I need this
  | .Primitive prm t => sorry
  | .Tuple t₁ t₂ =>
    match type_rep t₁ typ_env, type_rep t₂ typ_env with
    | some t₁', some t₂' => some (t₁' × t₂')
    | _, _ => none
  | .Struct name fields =>
    match list_to_finType fields typ_env with
    | none => none
    | some (n, Ts) =>
      some (DynStruct name fields.length Ts)
  | .Enum name params => sorry
  | .AnonymousClosure typs typ => sorry
  | .FnDef fn typs => sorry
  | .AirNamed str => sorry

def list_to_finType (ts : List Typ) (typ_env : String → Typ) :
  Option (Nat × (Fin ts.length → Type)) :=
match ts with
| []      => some ⟨0, (fun i => nomatch i)⟩
| t :: ts =>
  match type_rep t typ_env with
  | none => none
  | some t' =>
    match list_to_finType ts typ_env with
    | none => none
    | some ⟨n, Ts⟩ =>
      some ⟨n+1, fun
                  | ⟨0, _⟩   => t'
                  | ⟨i+1, h⟩ => Ts ⟨i, Nat.lt_of_succ_lt_succ h⟩⟩
end
