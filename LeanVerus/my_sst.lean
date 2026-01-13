/-
  Verus-Lean intermediate representation (VLIR).

  The "common language" shared by Verus and Lean.
  Statements in Verus and Lean are communicated with a serialization into JSON.
  In Verus, this is the statement syntax tree (SST) level.
  See `source/vir/src/sst.rs`.
-/

import Lean.Meta.Tactic.Simp
-- import VerusLean.Basic

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
  | Bool
  | Int (i: IntRange)
  | Float (width: UInt32)
  | Array (t : Typ)       /- Array, ignore length in Rust     -/
  | TypParam (i : String)  /- Type parameter. For example, `α` in `List α`. -/
  | SpecFn (params : List Typ) (ret : Typ)    /-`spec_fn` type (t1, ..., tn) -> t0. -/
  | Decorated (dec : TypDecoration) (ty : Typ)
  | Primitive (prm: Primitive) (ty: Typ)
  /-- Tuple, Enum, and Struct are simple cases of Dt in Rust -/
  | Tuple (ty₁ ty₂ : Typ) /- In Lean, these are `Prod`s. -/
  /--
    Rust structs, corresponding to Lean `structure`s.

    Note that these are closed-term type "references" to a struct,
    not a definition of a struct. (That would be a `Decl`, defined below.)

    In Rust, structs can be polymorphic in other types (i.e., `params`).
    In most cases, `params` will be empty.

    To refer to the actual declaration/definition of the struct,
    use the datatype map in `Parser.lean`.
  -/
  | Struct (name : Ident) (params : List Typ)
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
def Typ.hasDecEq (t t' : Typ) : Decidable (t = t') := by
  cases t <;> cases t' <;>
  try { apply isFalse ; intro h ; injection h }
  case Bool.Bool => apply isTrue; rfl
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
  case Tuple.Tuple v₁ v₂ v₁' v₂' =>
    exact match Typ.hasDecEq v₁ v₁', Typ.hasDecEq v₂ v₂' with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)
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

/-- Constant value literals -/
inductive Const
  /-- Booleans. Uses Rust's built-in `bool` type. -/
  | Bool (b : Bool)
  /-- Integers of arbitrary size. Rust encodes these as a sign bit plus a vector of `u64`s. -/
  | Int (i : Int)
  /-- String slices. Verus encodes this as an `Arc<String>`, a reference-counted pointer to a string in the heap. -/
  | StrSlice (s : String)
  /-- UTF-8 Unicode chars. In Rust, these are always four bytes. -/
  | Char (c : Char)
  /-- Rust representation of f32 constant as u32 bits -/
  | Float32 (f: UInt32)
  /-- Rust representation of f64 constant as u64 bits -/
  | Float64 (f: UInt64)
deriving Repr, Inhabited, DecidableEq, Hashable

/-- Bitwise operations.  -/
inductive BitwiseOp
  | BitXor
  | BitAnd
  | BitOr
  | Shr (width : Nat) -- CC: Replace width with enum later?
  /-- True = sign-extend, False = zero-extend -/
  | Shl (width : Nat) (signExtend : Bool)
deriving Repr, Inhabited, DecidableEq, Hashable

/-- Arithmetic operations that might fail due to overflow or divide by zero. -/
inductive ArithOp
  /-- Addition on `IntRange`. -/
  | Add
  /-- Subtraction on `IntRange`. -/
  | Sub
  /-- Multiplication on `IntRange`. -/
  | Mul
  /-- Euclidean division on `IntRange` (round towards -inf, not round-towards-zero truncation). -/
  | EuclideanDiv
  /-- Euclidean mod (non-negative result, even for negative divisors). -/
  | EuclideanMod
deriving Repr, Inhabited, DecidableEq, Hashable

/-- Arithmetic inequality operations. -/
inductive InequalityOp
  | Le
  | Ge
  | Lt
  | Gt
deriving Repr, Inhabited, DecidableEq, Hashable

/-- Primitive unary operations
 (not arbitrary user-defined functions -- these are represented by Expr::Call)
See UnaryOpr, UnaryOp in: verus/source/vir/src/ast.rs -/
inductive UnaryOp where
  /-- Boolean not -/
  | Not
  /-- Bitwise not -/
  | BitNot (width? : Option Nat)
  /-- Force integer value into range given by IntRange (e.g. by using mod). -/
  | Clip (range : IntRange) (truncate : Bool)   --y
  /-
  StrLen, // Str Slices
  StrIsAscii, // strslice_is_ascii
  InferSpecForLoopIter { print_hint: Bool }, // loops?
  CastToInteger, // coercion after casting to an integer (type argument?)
  -/
  /--
    Quantifier trigger annotations, used to guide SMT solvers.

    Note: These are largely ignored by Lean. We keep them, though, for two
    reasons. First, they simplify parsing, so we don't need to special-case
    on whether we encounter a trigger or not. Second, if Lean ever *does*
    use SMT solvers to discharge the goals, the trigger information is
    useful to have around.

    But for the most part, when creating Lean code from serialized objects,
    we drop trigger information.
  -/
  | Trigger
  /-- Return raw bits of a float as an int -/
  | FloatToBits
deriving Repr, Inhabited, Hashable, DecidableEq


  /-- SR: TODO: add IntegerTypeBound? -/
inductive UnaryOpr where
  /--
    A field projection out of a structure. For example `p.fst`.

    In Verus, this is called a `Field`, and is defined under `UnaryOpr`.
  -/
  | Proj (field : String)
  /--
    Determines whether the element matches a given variant of an enum.

    In Verus, this is defined under `UnaryOpr`.
  -/
  | IsVariant (dt : Ident) (variant : String)
  /--
    coerce Typ --> Boxed(Typ)

    In Verus, this is defined under `UnaryOpr`.
  -/
  | Box (t : Typ)
  /--
    coerce Boxed(Typ) --> Typ

    In Verus, this is defined under `UnaryOpr`.
  -/
  | Unbox (t : Typ)
  | HasType (t : Typ)
deriving Repr, Inhabited, Hashable

def UnaryOpr.hasDecEq (op₁ op₂ : UnaryOpr) : Decidable (op₁ = op₂) := by
  cases op₁ <;> cases op₂ <;>
  try { apply isFalse ; intro h ; injection h }
  case Proj.Proj f₁ f₂ =>
    exact match decEq f₁ f₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case Box.Box t₁ t₂ | Unbox.Unbox t₁ t₂ | HasType.HasType t₁ t₂ =>
    exact match Typ.hasDecEq t₁ t₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case IsVariant.IsVariant dt₁ var₁ dt₂ var₂ =>
    exact match decEq dt₁ dt₂, decEq var₁ var₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)

/--
  Primitive binary operations.

  All integer operations are on mathematical integers (`IntRange::Int`).
  Finite-width operations are represented with a combination of `IntRange::Int` operations
  and `UnaryOp.Clip` operations.
-/
inductive BinaryOp
  /-- Boolean AND. Short-circuits. -/
  | And
  /-- Boolean OR. Short-circuits. -/
  | Or
  /-- Boolean XOR. No short-circuiting. -/
  | Xor
  /-- Boolean implication. Short-circuiting (RHS evaluated only if LHS is true). -/
  | Implies
  /-- SMT equality for types. Equality differs based on the mode.
      Some types only support compilable equality (Mode == Exec),
        while others only support spec equality (Mode == Spec). -/
  | Eq (mode : Mode)
  /-- Not equals. (Verus doesn't have a mode option here?) -/
  | Ne
  /-- Arithmetic inequality -/
  | Inequality (op : InequalityOp)
  /-- Arithmetic operations. Overflow checking is done when `mode = Exec`. -/
  | Arith (op : ArithOp) (mode : Mode)
  /-- Bitwise operations. Overflow checking is done when `mode = Exec`. -/
  | Bitwise (op : BitwiseOp) (mode : Mode)
  /-- rsg: Used only for handling verus_builtin::array_index -/
  | ArrayIndex
deriving Repr, Inhabited, DecidableEq, Hashable

inductive Quant where
  | Forall
  | Exists
deriving Repr, Inhabited, DecidableEq, Hashable

inductive CallFun where
  | Fun (fn : Ident) -- an optional resolved Fun for methods currently not implemented
  | Recursive (name : Ident)
  -- | InternalFun (name : Ident)
deriving Repr, Inhabited, DecidableEq, Hashable



-- inductive Bind where
--   -- CC: Verus says this is a `VarBinders`, but for now, we say that each `let x := e` has a single variable binding
--   | Let (ty : Typ) (e : Exp)
--   | Quant (q : Quant) (vars : List Typ)
--   | Lambda (vars : List Typ)
--   -- CC: Ignore choose for now
--   -- | Choose ()
-- deriving Repr, Inhabited, Hashable

/--
  Flattened Verus expressions.

  Expressions have return values.
-/
inductive Exp where
  /-- Constant value literals. -/
  | Const (c : Const)
  /-- Local variables, as a right-hand side of an expression. -/
  | Var (x : Nat)
  /-- Call to spec function -/
  | Call (fn : CallFun) (typs : List Typ) (exps : List Exp)
  | CallLambda (lam : Exp) (args : List Exp)
  /-- A struct constructor -/
  | StructCtor (dt : Ident) (fields : List (String × Exp))
  /-- A constructor for the datatype with the name `dt` and the given `fields`. -/
  -- TODO: fix the fields of EnumCtor
  --| EnumCtor (dt : Ident) (variant : String) (data : List (String × Exp))
  /- TODO -/
  | TupleCtor (size : Nat) (data : List Exp)
  /-- Primitive unary function application. -/
  | Unary (op : UnaryOp) (arg : Exp)
  | Unaryr (op : UnaryOpr) (arg : Exp)
  /-- Primitive binary function application. -/
  | Binary (op : BinaryOp) (arg₁ arg₂ : Exp)
  | If (cond branch₁ branch₂ : Exp)
  | Let (ty : List Typ) (e : List Exp) (exp : Exp)
  | Quant (q : Quant) (var : Typ) (exp : Exp)
  | Lambda (var : Typ) (exp : Exp)
  --TODO: figure out what this means
  | ArrayLiteral (elems : List Exp)
  --| MatchBlock (scrutinee : Exp × Typ) (body : Exp)
deriving Repr, Inhabited, Hashable

mutual
def Exp.hasDecEq (e₁ e₂ : Exp) : Decidable (e₁ = e₂) := by
  cases e₁ <;> cases e₂ <;>
  try { apply isFalse ; intro h ; injection h }
  case Const.Const c₁ c₂ =>
    exact match decEq c₁ c₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case Var.Var x₁ x₂ => exact match decEq x₁ x₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case Unary.Unary op₁ arg₁ op₂ arg₂ =>
    exact match decEq op₁ op₂, Exp.hasDecEq arg₁ arg₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)
  case Unaryr.Unaryr op₁ arg₁ op₂ arg₂ =>
    exact match UnaryOpr.hasDecEq op₁ op₂, Exp.hasDecEq arg₁ arg₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)
  case Binary.Binary op₁ arg₁₁ arg₂₁ op₂ arg₁₂ arg₂₂ =>
    exact match decEq op₁ op₂, Exp.hasDecEq arg₁₁ arg₁₂, Exp.hasDecEq arg₂₁ arg₂₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse h₁, _,  _ | _, isFalse h₁, _ | _, _, isFalse h₁ =>
      isFalse (by intro h₃; simp [h₁] at h₃)
  case If.If c₁ b₁₁ b₁₂ c₂ b₂₁ b₂₂ =>
    exact match Exp.hasDecEq c₁ c₂, Exp.hasDecEq b₁₁ b₂₁, Exp.hasDecEq b₁₂ b₂₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse h₁, _,  _ | _, isFalse h₁, _ | _, _, isFalse h₁ =>
      isFalse (by intro h₃; simp [h₁] at h₃)
  case Quant.Quant q₁ var₁ exp₁ q₂ var₂ exp₂ =>
    exact match decEq q₁ q₂, Typ.hasDecEq var₁ var₂, Exp.hasDecEq exp₁ exp₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse h₁, _,  _ | _, isFalse h₁, _ | _, _,  isFalse h₁ =>
      isFalse (by intro h₃; simp [h₁] at h₃)
  case Lambda.Lambda var₁ exp₁ var₂ exp₂ =>
    exact match Typ.hasDecEq var₁ var₂, Exp.hasDecEq exp₁ exp₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)
  case TupleCtor.TupleCtor size₁ data₁ size₂ data₂ =>
    exact match decEq size₁ size₂, Exp.hasListDec data₁ data₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)
  case StructCtor.StructCtor dt₁ fields₁ dt₂ fields₂ =>
    exact match decEq dt₁ dt₂, Exp.hasFieldsDec fields₁ fields₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)
  case Call.Call fn₁ typs₁ exps₁ fn₂ typs₂ exps₂ =>
    exact match decEq fn₁ fn₂, Typ.hasListDec typs₁ typs₂, Exp.hasListDec exps₁ exps₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse h₁, _,  _ | _, isFalse h₁, _ | _, _, isFalse h₁ =>
      isFalse (by intro h₃; simp [h₁] at h₃)
  case CallLambda.CallLambda lam₁ args₁ lam₂ args₂ =>
    exact match Exp.hasDecEq lam₁ lam₂, Exp.hasListDec args₁ args₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)
  case Let.Let ty₁ es₁ exp₁ ty₂ es₂ exp₂ =>
    exact match Typ.hasListDec ty₁ ty₂, Exp.hasListDec es₁ es₂, Exp.hasDecEq exp₁ exp₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse h₁, _,  _ | _, isFalse h₁, _ | _, _, isFalse h₁ =>
      isFalse (by intro h₃; simp [h₁] at h₃)
  case ArrayLiteral.ArrayLiteral elems₁ elems₂ =>
    exact match Exp.hasListDec elems₁ elems₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def Exp.hasListDec (es₁ es₂ : List Exp) : Decidable (es₁ = es₂) :=
  match es₁, es₂ with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | e₁ :: el₁, e₂ :: el₂ =>
    match Exp.hasDecEq e₁ e₂ with
    | isTrue h₁ =>
        match Exp.hasListDec el₁ el₂ with
        | isTrue h₂ => isTrue (by subst h₁ h₂; rfl)
        | isFalse _ => isFalse (by simp; intros; assumption)
    | isFalse _ => isFalse (by simp; intros; contradiction)

def Exp.hasFieldsDec (fs₁ fs₂ : List (String × Exp)) : Decidable (fs₁ = fs₂) :=
  match fs₁, fs₂ with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (f₁, e₁) :: fl₁, (f₂, e₂) :: fl₂ =>
    match decEq f₁ f₂, Exp.hasDecEq e₁ e₂, Exp.hasFieldsDec fl₁ fl₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse h₁, _,  _ | _, isFalse h₁, _ | _, _,  isFalse h₁ =>
      isFalse (by intro h₃; simp [h₁] at h₃)
end

/--
Induction rule for `TermType`: the default induction tactic doesn't yet support
nested or mutual induction types.
-/
@[induction_eliminator, elab_as_elim]
theorem Exp.induct {P : Exp → Prop}
  (_exp : ∀c, P (.Const c))
  (_var : ∀x, P (.Var x))
  (_call : ∀fn typs exps, (∀ e ∈ exps, P e) → P (.Call fn typs exps))
  (_calllambda : ∀body args, (∀ e ∈ args, P e) → (P body) → P (.CallLambda body args))
  (_structctor : ∀dt fields, (∀ p ∈ fields, P p.2) → P (.StructCtor dt fields))
  (_tuplector : ∀size data, (∀ _e ∈ data, P _e) → P (.TupleCtor size data))
  (_unary : ∀op arg, P arg → P (.Unary op arg))
  (_unaryr : ∀op arg, P arg → P (.Unaryr op arg))
  (_binary : ∀op arg₁ arg₂, P arg₁ → P arg₂ → P (.Binary op arg₁ arg₂))
  (_if : ∀cond branch₁ branch₂, P cond → P branch₁ → P branch₂ → P (.If cond branch₁ branch₂))
  (_let : ∀tys es exp, (∀ e ∈ es, P e) → P exp → P (.Let tys es exp))
  (_quant : ∀q var exp, P exp → P (.Quant q var exp))
  (_lambda : ∀var exp, P exp → P (.Lambda var exp))
  (_arrayliteral : ∀elems, (∀ _e ∈ elems, P _e) → P (.ArrayLiteral elems))
  : ∀ e, P e := by sorry

register_simp_attr autosubst
