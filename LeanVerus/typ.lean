import Lean.Meta.Tactic.Simp

namespace VerusLean

open Lean (Json ToJson FromJson)

/-- Alias for `Lean.Name`. -/
abbrev Ident := Lean.Name

-- def Ident.toString : Ident → String :=
--   -- fun i => if i == Lean.Name.anonymous then "" else
--   Lean.Name.toString (escape := false)

-- instance Ident.instToString : ToString Ident :=
--   ⟨Ident.toString⟩

-- instance Ident.coeString : Coe Ident String :=
--   ⟨Ident.toString⟩

def Ident.head : Ident → String
  | .anonymous => "anonymous"
  | .str .anonymous s => s
  | .str n _ => Ident.head n
  | _ => "unknown"

-- def Ident.uncons : Ident → (String × Ident)
--   | .anonymous => ("anonymous", .anonymous)
--   | .str .anonymous s => ("anonymous", .str .anonymous s)
--   | .str (.str .anonymous s₁) s₂ => (s₁, .str .anonymous s₂)
--   | .str n s =>
--     let ⟨head, tail⟩ := Ident.uncons n
--     (head, .str tail s)
--   | _ => ("unknown", .anonymous)

-- def Ident.mapTail (f : String → String) : Ident → Ident
--   | .str n s => .str n (f s)
--   | i => i

-- def Ident.numSegments : Ident → Nat
--   | .anonymous => 0
--   | .str n _ => Ident.numSegments n + 1
--   | _ => 0

inductive Mode where
  | Spec
  | Proof
  | Exec
deriving Repr, DecidableEq, Inhabited, Hashable

/-- Describes integer types -/
inductive IntRange where
  /-- The set of all mathematical integers Z (..., -2, -1, 0, 1, 2, ...) -/
  | Int --y
  /-- The set of all natural numbers N (0, 1, 2, ...) -/
  | Nat --y
  /-- n-bit unsigned numbers (natural numbers up to 2^n - 1) for the specified n: u32 -/
  | U : UInt32 → IntRange
  /-- n-bit signed numbers (integers -2^(n-1), ..., 2^(n-1) - 1) for the specified n: u32 -/
  | I : UInt32 → IntRange
  /-- Rust's USize type -/
  | USize
  /-- Rust's isize type -/
  | ISize
  | Char
deriving Repr, Inhabited, DecidableEq, Hashable

/--
  Rust and Verus type decorations.

  Type decorations mark the reference/mutability of a type.
  In Lean, we largely ignore these.
-/
inductive TypDecoration where
  | Ref       -- `&T`
  | MutRef    -- `&mut T`
  | Box       -- `Box<T>`
  | Rc        -- `Rc<T>`
  | Arc       -- `Arc<T>`
  | Ghost     -- `Ghost<T>`
  | Tracked   -- `Tracked<T>`
  | Never     -- !, represented as `Never<()>`
  | ConstPtr  -- `*const T` when applied to `*mut T`
deriving Repr, Inhabited, DecidableEq, Hashable

inductive Primitive where
  | Array
  /-- StrSlice type. Currently the vstd StrSlice struct is "seen" as this type
      despite the fact that it is in fact a datatype
      rsg: do I need this? -/
  | StrSlice
deriving Repr, Inhabited, DecidableEq, Hashable

/-- Rust type, but without Box, Rc, Arc, etc. -/
inductive Typ where
  | _Bool
  | Int (i: IntRange)
  | Float (width: UInt32)
  | Array (t : Typ)       /- Array, ignore length in Rust     -/
  | TypParam (i : String)  /- Type parameter. For example, `α` in `List α`. -/
  | SpecFn (params : List Typ) (ret : Typ)    /-`spec_fn` type (t1, ..., tn) -> t0. -/
  | Decorated (dec : TypDecoration) (ty : Typ)
  | Primitive (prm: Primitive) (ty: Typ)
  /-- Tuple, Enum, and Struct are simple cases of Dt in Rust -/
  | Tuple (l : List Typ) /- In Lean, these are `Prod`s. -/
  /--
    Rust structs, corresponding to Lean `structure`s.

    Note that these are closed-term type "references" to a struct,
    not a definition of a struct. (That would be a `Decl`, defined below.)

    In Rust, structs can be polymorphic in other types (i.e., `params`).
    In most cases, `params` will be empty.

    To refer to the actual declaration/definition of the struct,
    use the datatype map in `Parser.lean`.
  -/
  | Struct (name : Ident) (fields : List Typ)
  /--
    Rust enums, corresponding to Lean `inductive` types.

    Note that these are closed-term type "references" to an enum,
    not a definition of an enum. (That would be a `Decl`, defined below.)

    In Rust, enums can be polymorphic in other types (i.e., `params`).
    In most cases, `params` will be empty.

    To refer to the actual declaration/definition of the enum,
    use the datatype map in `Parser.lean`.
  -/
  | Enum (name : Ident) (params : List Typ)
  | AnonymousClosure (typs: List Typ) (typ: Typ) --SR: also a usize parameter. Don't know what it's for.
  | FnDef (fn: Ident) (typs: List Typ)
  | AirNamed (str : String)
deriving Repr, Inhabited, Hashable, BEq

mutual
def Typ.is_closed (t : Typ): Bool :=
  match t with
  | ._Bool => true
  | .Int _ => true
  | .Float _ => true
  | .Array t' => is_closed t'
  | .TypParam _ => false
  | .SpecFn params ret => is_closed ret && is_closed_list params
  | .Decorated _ t' => is_closed t'
  | .Primitive _ t' => is_closed t'
  | .Tuple l => is_closed_list l
  | .Struct _ fields => is_closed_list fields
  | .Enum _ params => is_closed_list params
  | .AnonymousClosure ts t => is_closed t && is_closed_list ts
  | .FnDef _ ts => is_closed_list ts
  | .AirNamed _ => true

def Typ.is_closed_list (ts : List Typ) : Bool :=
  match ts with
  | [] => true
  | t :: ts' => is_closed t && is_closed_list ts'
end

def ClosedTyp := { t : Typ // Typ.is_closed t }

mutual
def Typ.hasDecEq (t t' : Typ) : Decidable (t = t') := by
  cases t <;> cases t' <;>
  try { apply isFalse ; intro h ; injection h }
  case _Bool._Bool => apply isTrue; rfl
  case Int.Int v₁ v₂ | Float.Float v₁ v₂ | TypParam.TypParam v₁ v₂ | AirNamed.AirNamed v₁ v₂ =>
    exact match decEq v₁ v₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case Array.Array v₁ v₂ =>
    exact match Typ.hasDecEq v₁ v₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case Decorated.Decorated p₁ ty₁ p₂ ty₂ | Primitive.Primitive p₁ ty₁ p₂ ty₂ =>
    exact match decEq p₁ p₂, Typ.hasDecEq ty₁ ty₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)
  case Tuple.Tuple v₁ v₂ =>
    exact match Typ.hasListDec v₁ v₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse h  =>
      isFalse (by intro h; injection h; contradiction)
  case Struct.Struct n₁ p₁ n₂ p₂ | Enum.Enum n₁ p₁ n₂ p₂ | FnDef.FnDef n₁ p₁ n₂ p₂ =>
    exact match decEq n₁ n₂, Typ.hasListDec p₁ p₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)
  case SpecFn n₁ p₁ n₂ p₂ | AnonymousClosure.AnonymousClosure n₁ p₁ n₂ p₂=>
    exact match Typ.hasListDec n₁ n₂, Typ.hasDecEq p₁ p₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)

def Typ.hasListDec (ts₁ ts₂ : List Typ) : Decidable (ts₁ = ts₂) :=
  match ts₁, ts₂ with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | t₁ :: tl₁, t₂ :: tl₂ =>
    match Typ.hasDecEq t₁ t₂ with
    | isTrue h₁ =>
        match Typ.hasListDec tl₁ tl₂ with
        | isTrue h₂ => isTrue (by subst h₁ h₂; rfl)
        | isFalse _ => isFalse (by simp; intros; assumption)
    | isFalse _ => isFalse (by simp; intros; contradiction)
end

instance : DecidableEq Typ := Typ.hasDecEq


mutual
def Typ.syntactic_eq (t t': Typ) : Option Bool :=
  match t, t' with
  | _Bool, _Bool => some true
  | Int i₁, Int i₂ => some (i₁ = i₂)
  | TypParam s₁, TypParam s₂ =>
      if s₁ = s₂ then some true else none
  | AirNamed s₁, AirNamed s₂ => some (s₁ = s₂)
  | SpecFn args₁ r₁, SpecFn args₂ r₂ =>
      match Typ.syntactic_eq r₁ r₂ with
      | some true =>
          match Typ.syntactic_eq_list args₁ args₂ with
          | some true => some true
          | some false => some false
          | none => none
      | some false => some false
      | none => none
  | _, _ => some false

def Typ.syntactic_eq_list (ts₁ ts₂ : List Typ) : Option Bool :=
  match ts₁, ts₂ with
  | [], [] => some true
  | _::_, [] | [], _::_ => some false
  | t₁ :: tl₁, t₂ :: tl₂ =>
    match Typ.syntactic_eq t₁ t₂ with
    | some true => Typ.syntactic_eq_list tl₁ tl₂
    | some false => some false
    | none => none
end

abbrev typ_env := String → ClosedTyp

mutual
def typ_subst (env : typ_env) (t : Typ) : ClosedTyp :=
  match t with
  | ._Bool => ⟨ ._Bool, by rfl ⟩
  | .Int i => ⟨ .Int i, by rfl ⟩
  | .Float w => ⟨ .Float w, by rfl ⟩
  | .Array t' =>
    ⟨ .Array (typ_subst env t').1, by
      simp [Typ.is_closed]; exact (typ_subst env t').2⟩
  | .TypParam t => env t
  | .SpecFn params ret =>
    let r  := typ_subst env ret
    let ps := typ_subst_list env params
    ⟨.SpecFn ps.1 r.1, by
      simp [Typ.is_closed, r.2, ps.2]⟩
  | .Decorated d t' =>
    ⟨ .Decorated d (typ_subst env t').1, by
      simp [Typ.is_closed]; exact (typ_subst env t').2⟩
  | .Primitive p t' =>
    ⟨ .Primitive p (typ_subst env t').1, by
      simp [Typ.is_closed]; exact (typ_subst env t').2⟩
  | .Tuple l =>
    let l' := typ_subst_list env l
    ⟨.Tuple l'.1, by
      simp [Typ.is_closed, l'.2]⟩
  | .Struct s fields =>
    let fs := typ_subst_list env fields
    ⟨.Struct s fs.1, by
      simp [Typ.is_closed, fs.2]⟩
  | .Enum e params =>
    let ps := typ_subst_list env params
    ⟨.Struct e ps.1, by
      simp [Typ.is_closed, ps.2]⟩
  | .AnonymousClosure ts t =>
    let r  := typ_subst env t
    let ps := typ_subst_list env ts
    ⟨.AnonymousClosure ps.1 r.1, by
      simp [Typ.is_closed, r.2, ps.2]⟩
  | .FnDef fn ts =>
    let ps := typ_subst_list env ts
    ⟨.FnDef fn ps.1, by
      simp [Typ.is_closed, ps.2]⟩
  | .AirNamed a => ⟨ .AirNamed a , by rfl ⟩

def typ_subst_list (env : typ_env) (ts : List Typ) : { us : List Typ // Typ.is_closed_list us } :=
  match ts with
  | [] => ⟨[], by rfl⟩
  | t :: ts' =>
    let u  := typ_subst env t
    let us := typ_subst_list env ts'
    ⟨u.1 :: us.1, by
      simp [Typ.is_closed_list, u.2, us.2]⟩
end
