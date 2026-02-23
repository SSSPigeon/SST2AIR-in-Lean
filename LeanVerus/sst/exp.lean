import Lean.Meta.Tactic.Simp
import LeanVerus.Sst.Typ

namespace sst

open Lean (Json ToJson FromJson)

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
  -- IntRange::Int <=
  | Le
  -- IntRange::Int >=
  | Ge
  -- IntRange::Int <
  | Lt
  -- IntRange::Int >
  | Gt
deriving Repr, Inhabited, DecidableEq, Hashable

/-- Primitive unary operations
 (not arbitrary user-defined functions -- these are represented by Expr::Call)
See UnaryOpr, UnaryOp in: verus/source/vir/src/ast.rs -/
inductive UnaryOp where
  /-- Boolean not -/
  | Not
  /-- Bitwise not -/
  | BitNot (width : Option Nat)
  /-- Force integer value into range given by IntRange (e.g. by using mod). -/
  | Clip (range : IntRange) (truncate : Bool)   --y
  /-
  StrLen, // Str Slices
  StrIsAscii, // strslice_is_ascii
  InferSpecForLoopIter { print_hint: Bool }, // loops?
  CastToInteger, // coercion after casting to an integer (type argument?)
  -/
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
  -/
  | IsVariant (dt : Ident) (variant : String)
  /--
    coerce Typ --> Boxed(Typ)
  -/
  | Box (t : Typ)
  /--
    coerce Boxed(Typ) --> Typ
  -/
  | Unbox (t : Typ)
  | HasType (t : Typ)
deriving Repr, Inhabited, Hashable, DecidableEq


inductive ArrayKind
  | Array
  | Slice
deriving Repr, Inhabited, DecidableEq, Hashable


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
  /-- Arithmetic operations. -/
  | Arith (op : ArithOp)
  /-- Bitwise operations. Overflow checking is done when `mode = Exec`. -/
  | Bitwise (op : BitwiseOp) (mode : Mode)
  /-- Index into an array or slice, no bounds-checking.
    `verus_builtin::array_index` lowers to this.
    In SST, this can also be used as a Loc. -/
  | Index (ak : ArrayKind)
deriving Repr, Inhabited, DecidableEq, Hashable

inductive Quant where
  | Forall
  | Exists
deriving Repr, Inhabited, DecidableEq, Hashable

inductive CallFun where
  | Fun (fn : Ident) -- an optional resolved Fun for methods currently not implemented
  | Recursive (fn : Ident)
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
  | Call (fn : CallFun) (typs : List Typ) (exps : List Exp) (ret : Typ)
  | CallLambda (lam : Exp) (arg : Exp)
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
  -- | Binaryr (op : BinaryOpr) (arg₁ arg₂ : Exp)
  | If (cond branch₁ branch₂ : Exp)
  | Let (tys : List Typ) (es : List Exp) (body : Exp)
  | Quant (q : Quant) (var : Typ) (body : Exp)
  | Lambda (var : Typ) (exp : Exp)
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
    exact match decEq op₁ op₂, Exp.hasDecEq arg₁ arg₂ with
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
  case Call.Call fn₁ typs₁ exps₁ ty₁ fn₂ typs₂ exps₂ ty₂ =>
    exact match decEq fn₁ fn₂, Typ.hasListDec typs₁ typs₂, Exp.hasListDec exps₁ exps₂, decEq ty₁ ty₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃, isTrue h₄ => isTrue (by rw [h₁, h₂, h₃, h₄])
    | isFalse h₁, _,  _, _ | _, isFalse h₁, _, _ | _, _, isFalse h₁, _ | _, _, _, isFalse h₁ =>
      isFalse (by intro h₄; simp [h₁] at h₄)
  case CallLambda.CallLambda lam₁ arg₁ lam₂ arg₂ =>
    exact match Exp.hasDecEq lam₁ lam₂, Exp.hasDecEq arg₁ arg₂ with
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

instance : DecidableEq Exp := Exp.hasDecEq

mutual
def Exp.syntactic_eq (e e' : Exp) : Option Bool :=
  let def_eq (b : Bool) : Option Bool := if b then some true else some false
  match e, e' with
  | Const c₁, Const c₂ =>
      match c₁, c₂ with
      | Const.Bool b₁, Const.Bool b₂ => some (b₁ = b₂)
      | Const.Int i₁, Const.Int i₂ => some (i₁ = i₂)
      | Const.StrSlice s₁, Const.StrSlice s₂ => some (s₁ = s₂)
      | Const.Char c₁, Const.Char c₂ => some (c₁ = c₂)
      | _, _ => none
  | Var x₁, Var x₂ => def_eq (x₁ = x₂)
  | Unary op₁ arg₁, Unary op₂ arg₂ =>
    match Exp.syntactic_eq arg₁ arg₂ with
    | some true => some (op₁ = op₂)
    | some false => some false
    | none => none
  | Unaryr op₁ arg₁, Unaryr op₂ arg₂ =>
    let arg_eq := Exp.syntactic_eq arg₁ arg₂
    let op_eq :=
      match op₁, op₂ with
      | .HasType l₁, .HasType l₂ =>
        match (Typ.syntactic_eq l₁ l₂) with
        | some b => def_eq b
        | none => none
      | .IsVariant dt₁ var₁, .IsVariant dt₂ var₂ =>
        def_eq (dt₁ = dt₂ && var₁ = var₂)
      | .Proj f₁, .Proj f₂ => def_eq (f₁ = f₂)
      | _, _ => some false
    match arg_eq, op_eq with
    | some b₁, some b₂ => def_eq (b₁ && b₂)
    | _, _ => none
  | Binary op₁ arg₁₁ arg₁₂, Binary op₂ arg₂₁ arg₂₂ =>
    let arg₁_eq := Exp.syntactic_eq arg₁₁ arg₂₁
    let arg₂_eq := Exp.syntactic_eq arg₁₂ arg₂₂
    let op_eq := op₁ = op₂
    match arg₁_eq, arg₂_eq with
    | some b₁, some b₂ => def_eq (b₁ && b₂ && op_eq)
    | _, _ => none
  | If c₁ b₁₁ b₁₂, If c₂ b₂₁ b₂₂ =>
    let c_eq := Exp.syntactic_eq c₁ c₂
    let b₁_eq := Exp.syntactic_eq b₁₁ b₂₁
    let b₂_eq := Exp.syntactic_eq b₁₂ b₂₂
    match c_eq, b₁_eq, b₂_eq with
    | some b₁, some b₂, some b₃ => def_eq (b₁ && b₂ && b₃)
    | _, _, _ => none
  | CallLambda lam₁ arg₁, CallLambda lam₂ arg₂ =>
    let lam_eq := Exp.syntactic_eq lam₁ lam₂
    let arg_eq := Exp.syntactic_eq arg₁ arg₂
    match lam_eq, arg_eq with
    | some b₁, some b₂ => def_eq (b₁ && b₂)
    | _, _ => none
  | Call fn₁ _ exps₁ _, Call fn₂ _ exps₂ _=>
    let fn_eq := fn₁ = fn₂
    if exps₁.length == exps₂.length then
      let exps_eq := Exp.syntactic_eq_list exps₁ exps₂
      match exps_eq with
      | some b₂ => def_eq (fn_eq && b₂)
      | _ => none
    else none
  | _, _ => none

def Exp.syntactic_eq_list (es₁ es₂ : List Exp) : Option Bool :=
  match es₁, es₂ with
  | [], [] => some true
  | _::_, [] | [], _::_ => some false
  | e₁ :: el₁, e₂ :: el₂ =>
    match Exp.syntactic_eq e₁ e₂ with
    | some true => Exp.syntactic_eq_list el₁ el₂
    | some false => some false
    | none => none
end

/--
Induction rule for `TermType`: the default induction tactic doesn't yet support
nested or mutual induction types.
-/
@[induction_eliminator, elab_as_elim]
theorem Exp.induct {P : Exp → Prop}
  (_exp : ∀c, P (.Const c))
  (_var : ∀x, P (.Var x))
  (_call : ∀fn typs exps ty, (∀ e ∈ exps, P e) → P (.Call fn typs exps ty))
  (_calllambda : ∀body arg, P arg → (P body) → P (.CallLambda body arg))
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
