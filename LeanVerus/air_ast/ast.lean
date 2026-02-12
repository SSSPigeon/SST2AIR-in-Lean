import Init.Prelude
import Init.Data
import LeanVerus.Sst.Typ
import LeanVerus.Sst.Exp

namespace airast

open sst

inductive TypX
  | Bool
  | Int
  | Fun
  | Named (name: Ident)
  | BitVec (width: UInt32)
deriving Repr, Inhabited, DecidableEq, Hashable


inductive Constant
  | Bool (b: Bool)
  | Nat (i: String) -- In verus, i has type string
  | BitVec (s: List Nat) (width: UInt32) -- In verus, s is string
deriving Repr, Inhabited, DecidableEq, Hashable

inductive UnaryOp
  | Not
  | BitNot
  | BitExtract (high: UInt32) (low: UInt32)
  | BitZeroExtend (fr: UInt32)
  | BitSignExtend (fr: UInt32)
deriving Repr, Inhabited, DecidableEq, Hashable

inductive Relation
  | PartialOrder
  | LinearOrder
  | TreeOrder
  | PiecewiseOrder
deriving Repr, Inhabited, DecidableEq, Hashable

inductive Binop
  | Implies
  | Eq
  | Le
  | Ge
  | Lt
  | Gt
  | EuclideanDiv
  | EuclideanMod
  | Relation (rel: Relation) (idx: UInt64)
  | BitXor
  | BitAnd
  | BitOr
  | BitAdd
  | BitSub
  | BitMul
  | BitUDiv
  | BitUMod
  | BitULt
  | BitUGt
  | BitULe
  | BitUGe
  | BitSLt
  | BitSGt
  | BitSLe
  | BitSGe
  | AShr
  | LShr
  | Shl
  | BitConcat
  -- In Verus, ident: String
  | FieldUpdate (ident: Ident)
deriving Repr, Inhabited, DecidableEq, Hashable

inductive MultiOp
  | And
  | Or
  | Xor
  | Add
  | Sub
  | Mul
  | Distinct --?
deriving Repr, Inhabited, DecidableEq, Hashable

-- structure Binder (A : Type) where
--   name : Ident
--   a : A
-- deriving Repr, Inhabited, DecidableEq, Hashable

-- abbrev Binders (A : Type) := List (Binder A)

inductive Quant
  | Forall
  | Exists
deriving Repr, Inhabited, DecidableEq, Hashable

def Qid := Option Ident
deriving Repr, Inhabited, DecidableEq, Hashable

mutual


-- inductive BindX where
--   -- | Let (binders: Binders Expr)
--   | Let (binder: List (Binder Expr))
--   | Quant (q: Quant) (binders: Binders TypX) (triggers: List (List Expr)) (qid: Qid)
--   | Lambda (binders: Binders TypX)  --(triggers: List (List Expr)) (qid: Qid)
--   | Choose (binders: Binders TypX)  --(triggers: List (List Expr)) (qid: Qid) (body: Expr)
-- deriving Repr, Inhabited, Hashable

inductive Expr where
  | Const (c: Constant)
  | Var (name: Nat)
  | Old (i1: Ident) (i2: Ident)
  | Apply (i: String) (args: List Expr)
  | ApplyFun (tp: Typ) (f: Expr) (args: List Expr)
  | Unary (op: UnaryOp) (e: Expr)
  | Binary (op: Binop) (e1: Expr) (e2: Expr)
  | Multi (op: MultiOp) (es: List Expr)
  | IfElse (cond: Expr) (then_: Expr) (else_: Expr)
  | Array (es: List Expr)
  | Let (tys : List TypX) (es : List Expr) (body : Expr)
  | Quant (q: Quant) (var : TypX) (body : Expr)
  | Lambda (var : TypX) (exp : Expr)
  --| Choose (binders: Binders TypX)  --(triggers: List (List Expr)) (qid: Qid) (body: Expr)
  -- | Bind (b: BindX) (body: Expr)
deriving Repr, Inhabited, Hashable

end --(mutual)


inductive Stmt
  | Assume (e: Expr) (proof: Option Expr)
  | Assert (e: Expr) --Option<AssertId>, ArcDynMessage, AxiomInfoFilter
  | Havoc (i: Ident)
  | Assign (lhs: Ident) (rhs: Expr)
  | Snapshot (i: Ident)
  | DeadEnd (s: Stmt)
  | Breakable (i: Ident) (s: Stmt)
  | Break (i: Ident)
  | Block (ss: List Stmt)
  | Switch (ss: List Stmt)
deriving Repr, Inhabited, Hashable

def Stmts := List Stmt
deriving Repr, Inhabited, Hashable

def Axiom := Expr
deriving Repr, Inhabited, Hashable

-- def Field := Binder TypX
-- deriving Repr, Inhabited, Hashable

-- def Fields := List Field
-- deriving Repr, Inhabited, Hashable

-- def Variant := Binder Fields
-- deriving Repr, Inhabited, Hashable

-- def Variants := Binders Fields
-- deriving Repr, Inhabited, Hashable

-- def Datatype := Binder Variants
-- deriving Repr, Inhabited, Hashable

-- def Datatypes := Binders Variants
-- deriving Repr, Inhabited, Hashable

-- inductive Decl
--   | Sort (i: Ident)
--   | Datatypes (dts: Datatypes)
--   | Const (i: Ident) (tp: TypX)
--   | Fun (i: Ident) (tps: List TypX) (ret: TypX)
--   | Var (i: Ident) (tp: TypX)
--   | Axiom (ax: Axiom)
-- deriving Repr, Inhabited, Hashable

-- def Decls := List Decl
-- deriving Repr, Inhabited, Hashable

-- structure Query where
--   _local: Decls
--   assertion: Stmt
-- deriving Repr, Inhabited, Hashable

-- structure SingularQuery where
--   _local: Decls
--   requires: Stmts
--   ensures: Stmts
-- deriving Repr, Inhabited, Hashable

-- inductive CommandX
--   | Push
--   | Pop
--   | SetOption (i1: Ident) (i2: Ident)
--   | Global (d: Decl)
--   | CheckValid (q: Query)
--   | CheckSingular (sq: SingularQuery)
-- deriving Repr, Inhabited, Hashable

end airast
