import MultisortedLogic.Semantics
--import Init.Data.BitVec.Bitblast

namespace MSFirstOrder

namespace MSLanguage

open MSLanguage

universe u

inductive AirSorts where
  | Bool
  | Int
  | Fun
  | Named (name: String)
  | Bitvec (width: UInt32)
deriving Repr, Inhabited, DecidableEq, Hashable

abbrev Poly := AirSorts.Named "Poly"
abbrev TYPE := AirSorts.Named "TYPE"
abbrev FnDef := AirSorts.Named "FNDEF_TYPE"

variable {α : AirSorts → Type*}

open AirSorts

inductive airFunc : List AirSorts → AirSorts → Type
  -- air-ast :: Const
  | True : airFunc [] Bool
  | False : airFunc [] Bool
  | Nat : (i : String) → airFunc [] Int
  | BitVector : (bits : List Nat) → (width: UInt32) → airFunc [] (Bitvec width)

  -- air-ast :: Binop
  | Implies : airFunc [Bool, Bool] Bool
  | Eq : airFunc [Int, Int] Bool
  | Le : airFunc [Int, Int] Bool
  | Ge : airFunc [Int, Int] Bool
  | Lt : airFunc [Int, Int] Bool
  | Gt : airFunc [Int, Int] Bool
  | EuclideanDiv : airFunc [Int, Int] Int
  | EuclideanMod : airFunc [Int, Int] Int
  -- | Relation (rel: Relation) (idx: UInt64)
  -- | BitXor
  -- | BitAnd
  -- | BitOr
  -- | BitAdd
  -- | BitSub
  -- | BitMul
  -- | BitUDiv
  -- | BitUMod
  | BitShr : airFunc [Poly, Poly] Int
  | Bitshl : airFunc [Poly, Poly] Int
  -- | BitConcat : (w w': UInt32) → airFunc [BitVec w, BitVec w'] (BitVec (w+w'))
  --| FieldUpdate (ident: String)

  -- air-ast :: UnaryOp
  | Not : airFunc [Bool] Bool
  | BitNot : airFunc [Poly] Int
  -- | BitExtract (high: UInt32) (low: UInt32)
  -- | BitZeroExtend (fr: UInt32)
  -- | BitSignExtend (fr: UInt32)

  -- air-ast :: MultiOp
  -- TODO
  | And : (n : Nat) → airFunc (List.replicate n Bool) Bool
  | Or : (n : Nat) → airFunc (List.replicate n Bool) Bool
  | Xor : (n : Nat) → airFunc (List.replicate n Bool) Bool
  | Add : (n : Nat) → airFunc (List.replicate n Int) Int
  | Sub : (n : Nat) → airFunc (List.replicate n Int) Int
  | Mul : (n : Nat) → airFunc (List.replicate n Int) Int

  -- Uninterpreted function symbols (linked to built-ins via axioms)
  | ADD : airFunc [Int, Int] Int
  | SUB : airFunc [Int, Int] Int
  | MUL : airFunc [Int, Int] Int
  | EucDIV : airFunc [Int, Int] Int
  | EucMOD : airFunc [Int, Int] Int

  -- Functions in air examples:

  -- 1. Related to hastype:
  | BOOL : airFunc [] TYPE
  | INT : airFunc [] TYPE
  | NAT : airFunc [] TYPE
  | CHAR : airFunc [] TYPE
  | USIZE : airFunc [] TYPE
  | ISIZE : airFunc [] TYPE
  | UINT : airFunc [Int] TYPE
  | SINT : airFunc [Int] TYPE
  | FLOAT : airFunc [Int] TYPE
  | CONST_INT : airFunc [Int] TYPE
  | CONST_BOOL : airFunc [Bool] TYPE

  -- 2. array
  -- (declare-fun ARRAY (Dcr Type Dcr Type) Type)
  | ARRAY : airFunc [TYPE, TYPE] TYPE
  -- (declare-fun array_index (Dcr Type Dcr Type Fun Poly) Poly)
  | ARRAY_INDEX : airFunc [Fun, Poly] Poly

  -- 3. convert to/from POLY
  | ofI : airFunc [Int] Poly   -- I
  | ofB : airFunc [Bool] Poly  -- B
  | toI : airFunc [Poly] Int   -- %I
  | toB : airFunc [Poly] Bool  -- %B


def air_ast : MSLanguage AirSorts := {
  Functions := airFunc
  Relations := fun _ => Empty
}


/-!
## Carrier type assignment

We interpret:
- `AirSorts.Bool` as Lean's `Bool`
- `AirSorts.Int`  as Lean's `Int`
- `AirSorts.BitVec w` as `BitVec w.toNat`
-/
abbrev AirCarrier (P T F : Type) : AirSorts → Type
  | AirSorts.Bool      => Bool
  | AirSorts.Int       => Int
  | AirSorts.Named "Poly"   => P
  | AirSorts.Named "TYPE"   => T
  | AirSorts.Fun       => F
  | AirSorts.Bitvec w  => BitVec w.toNat
  | _ => sorry

/-!
## Helper: fold a SortedTuple of Bools

For the n-ary `And`, `Or`, `Xor` we need to fold over a `SortedTuple` whose
signature is `List.replicate n Bool`. We extract elements via `toMap` and fold.
-/

open SortedTuple airFunc

variable {P T F : Type}

variable [S : air_ast.MSStructure (AirCarrier P T F)]
/-- Fold a binary Boolean operation over a SortedTuple of n Bools. -/
def foldBools (op : Bool → Bool → Bool) (init : Bool)
    {n : Nat} (xs : SortedTuple (List.replicate n AirSorts.Bool) (AirCarrier P T F)) : Bool :=
  List.foldl op init <| List.ofFn fun (i : Fin n) =>
    let i' : Fin (List.replicate n AirSorts.Bool).length := ⟨i.val, by simp⟩
    have h : (List.replicate n AirSorts.Bool).get i' = AirSorts.Bool := by simp
    cast (congrArg (AirCarrier P T F) h) (xs.toMap i')

/-- Fold a binary Int operation over a SortedTuple of n Ints. -/
def foldInts (op : Int → Int → Int) (init : Int)
    {n : Nat} (xs : SortedTuple (List.replicate n AirSorts.Int) (AirCarrier P T F)) : Int :=
  List.foldl op init <| List.ofFn fun (i : Fin n) =>
    let i' : Fin (List.replicate n AirSorts.Int).length := ⟨i.val, by simp⟩
    have h : (List.replicate n AirSorts.Int).get i' = AirSorts.Int := by simp
    cast (congrArg (AirCarrier P T F) h) (xs.toMap i')

def toIntList {n : Nat} (xs : SortedTuple (List.replicate n AirSorts.Int) (AirCarrier P T F)) : List Int :=
  List.ofFn fun (i : Fin n) =>
    let i' : Fin (List.replicate n AirSorts.Int).length := ⟨i.val, by simp⟩
    have h : (List.replicate n AirSorts.Int).get i' = AirSorts.Int := by simp
    cast (congrArg (AirCarrier P T F) h) (xs.toMap i')

/-- SMT-LIB-style subtraction: unary `-x` for n=1, left-associative `x - y - …` for n≥2. -/
def subInts {n : Nat} (xs : SortedTuple (List.replicate n AirSorts.Int) (AirCarrier P T F)) : Int :=
  match toIntList xs with
  | []        => 0
  | [x]       => -x
  | x :: rest => List.foldl (· - ·) x rest

class AirMod (P T F : Type) extends air_ast.MSStructure (AirCarrier P T F) where
  -- Pin down the Bool/Int operations:
  funMap_true  : ∀ xs, funMap airFunc.True xs = true
  funMap_false : ∀ xs, funMap airFunc.False xs = false
  funMap_nat   : ∀ (i : String) xs, funMap (airFunc.Nat i) xs = i.toInt?.getD 0
  --TODO: funMap_bitvec

  funMap_implies : ∀ xs, funMap airFunc.Implies xs = (!xs.eval₂₁ || xs.eval₂₂)
  funMap_not   : ∀ xs, funMap airFunc.Not xs = !xs.eval₁

  funMap_eq    : ∀ xs, funMap airFunc.Eq xs = decide (xs.eval₂₁ = xs.eval₂₂)
  funMap_le    : ∀ xs, funMap airFunc.Le xs = decide (xs.eval₂₁ ≤ xs.eval₂₂)
  funMap_ge    : ∀ xs, funMap airFunc.Ge xs = decide (xs.eval₂₁ ≥ xs.eval₂₂)
  funMap_lt    : ∀ xs, funMap airFunc.Lt xs = decide (xs.eval₂₁ < xs.eval₂₂)
  funMap_gt    : ∀ xs, funMap airFunc.Gt xs = decide (xs.eval₂₁ > xs.eval₂₂)

  -- EuclideanDiv/Mod are only specified when the denominator is non-zero.
  -- When xs.eval₂₂ = 0 there is no axiom constraining the result, so the behavior is unspecified.
  funMap_euclideanDiv : ∀ xs, xs.eval₂₂ ≠ 0 → funMap airFunc.EuclideanDiv xs = xs.eval₂₁ / xs.eval₂₂
  funMap_euclideanMod : ∀ xs, xs.eval₂₂ ≠ 0 → funMap airFunc.EuclideanMod xs = xs.eval₂₁ % xs.eval₂₂


  funMap_add   : ∀ (n : Nat) xs, funMap (airFunc.Add n) xs = foldInts (· + ·) 0 xs
  funMap_sub   : ∀ (n : Nat) xs, funMap (airFunc.Sub n) xs = subInts xs
  funMap_mul   : ∀ (n : Nat) xs, funMap (airFunc.Mul n) xs = foldInts (· * ·) 1 xs



  funMap_and   : ∀ (n : Nat) xs, funMap (airFunc.And n) xs = foldBools (· && ·) true xs
  funMap_or    : ∀ (n : Nat) xs, funMap (airFunc.Or n) xs = foldBools (· || ·) false xs
  funMap_xor   : ∀ (n : Nat) xs, funMap (airFunc.Xor n) xs = foldBools (· ^^ ·) false xs

  -- Leave Poly/TYPE/Fun operations abstract — axioms constrain them

#check AirMod
#check AirCarrier


end MSLanguage

end MSFirstOrder
