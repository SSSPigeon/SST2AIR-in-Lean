import LeanVerus.My_sst

open VerusLean

namespace sst_semantics



structure DynStruct (name : Ident) (n : Nat) (Ts : Fin n → Type) where
  fields : (i : Fin n) → Ts i

mutual
def type_rep (t : Typ) (typ_env : String → Typ):  Type :=
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
  | .Float w => sorry
  | .Array t => List (type_rep t typ_env)
  | .TypParam p => type_rep (typ_env p) typ_env
  | .SpecFn params ret => sorry
  --TODO: corresponding expressions in my_sst?
  | .Decorated dec t => sorry
  --TODO: check this in verus.src, and see if I need this
  | .Primitive pem t => sorry
  | .Tuple t₁ t₂ => type_rep t₁ typ_env × type_rep t₂ typ_env
  | .Struct name fields => DynStruct name fields.length (list_to_finType fields typ_env).2

def list_to_finType (ts : List Typ) (typ_env : String → Typ) :
  Nat × (Fin ts.length → Type) :=
match ts with
| []      => ⟨0, (fun i => nomatch i)⟩
| t :: ts =>
  let ⟨n, Ts⟩ := list_to_finType ts typ_env
  ⟨n+1, fun
    | ⟨0, _⟩   => type_rep t typ_env
    | ⟨i+1, h⟩ => Ts ⟨i, Nat.lt_of_succ_lt_succ h⟩⟩
end
