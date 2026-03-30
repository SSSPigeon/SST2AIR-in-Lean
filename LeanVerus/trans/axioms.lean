import LeanVerus.Air_ast.Ast
import Mathlib.Data.Set.Basic
import LeanVerus.Air_ast.«Air-ast»

open MSFirstOrder MSLanguage AirSorts BoundedFormula airFunc


-- Prelude axioms: https://github.com/verus-lang/verus/blob/788fbe2526336161902df2f42b89687f8a015602/source/vir/src/prelude.rs

section ArithAxioms
--  ∀ (x : Int) (y : Int), ADD(x, y) = Add(x, y)
--   pos = 0  →  x  (outer ∀)
--   pos = 1  →  y  (inner ∀)
def arithAxiomArgs (i : Fin 2) :
  air_ast.Term
    ((fun _ => Empty) ⊕ₛ [AirSorts.Int, AirSorts.Int].toFam)
    ([AirSorts.Int, AirSorts.Int].get i) :=
  match i with
  | ⟨0, _⟩ => Term.var AirSorts.Int
      (Sum.inr ⟨⟨0, by simp⟩, rfl⟩)
  | ⟨1, _⟩ => Term.var AirSorts.Int
      (Sum.inr ⟨⟨1, by simp⟩, rfl⟩)
  | ⟨_ + 2, h⟩ => absurd h (by omega)

-- ∀ (x : Int) (y : Int), ADD(x, y) = Add(x, y)
-- airFunc.ADD is the uninterpreted symbol; airFunc.Add is the built-in addition.
def ADD_axiom : air_ast.Sentence :=
  all (s := Int)
    (all (s := Int)
      (equal
        (Term.func [AirSorts.Int, Int] Int ADD arithAxiomArgs)
        (Term.func [AirSorts.Int, Int] Int (Add 2) arithAxiomArgs)
      )
    )

def SUB_axiom : air_ast.Sentence :=
  all (s := Int)
    (all (s := Int)
      (equal
        (Term.func [AirSorts.Int, Int] Int SUB arithAxiomArgs)
        (Term.func [AirSorts.Int, Int] Int (Sub 2) arithAxiomArgs)
      )
    )

def MUL_axiom : air_ast.Sentence :=
  all (s := Int)
    (all (s := Int)
      (equal
        (Term.func [AirSorts.Int, Int] Int MUL arithAxiomArgs)
        (Term.func [AirSorts.Int, Int] Int (Mul 2) arithAxiomArgs)
      )
    )

def DIV_axiom : air_ast.Sentence :=
  all (s := Int)
    (all (s := Int)
        (equal
          (Term.func [AirSorts.Int, Int] Int EucDIV arithAxiomArgs)
          (Term.func [AirSorts.Int, Int] Int EuclideanDiv arithAxiomArgs)
        )
      )

def MOD_axiom : air_ast.Sentence :=
  all (s := Int)
    (all (s := Int)
        (equal
          (Term.func [AirSorts.Int, Int] Int EucMOD arithAxiomArgs)
          (Term.func [AirSorts.Int, Int] Int EuclideanMod arithAxiomArgs)
        )
      )



-- https://github.com/verus-lang/verus/blob/788fbe2526336161902df2f42b89687f8a015602/source/vir/src/prelude.rs#L825
-- These axioms are important to make sure that the nonlinear operations commute with casting-to-ints (e.g., (a * b) as int == (a as int) * (b as int)) where applicable.

-- Helpers for building terms in the same 2-Int-variable context as arithAxiomArgs
-- pos 0 = x (outer ∀), pos 1 = y (inner ∀)
abbrev Ctx2 := (fun (_ : AirSorts) => Empty) ⊕ₛ [AirSorts.Int, AirSorts.Int].toFam

def const0 : air_ast.Term Ctx2 AirSorts.Int :=
  Term.func [] AirSorts.Int (airFunc.Nat "0") (fun i => absurd i.isLt (by simp))

def constTrue : air_ast.Term Ctx2 AirSorts.Bool :=
  Term.func [] AirSorts.Bool airFunc.True (fun i => absurd i.isLt (by simp))

def le (a b : air_ast.Term Ctx2 AirSorts.Int) : air_ast.Term Ctx2 AirSorts.Bool :=
  Term.func [AirSorts.Int, AirSorts.Int] AirSorts.Bool airFunc.Le
    fun i =>
      match i with
      | ⟨0, _⟩ => a
      | ⟨1, _⟩ => b
      | ⟨_ + 2, h⟩ => absurd h (by simp)

def lt (a b : air_ast.Term Ctx2 AirSorts.Int) : air_ast.Term Ctx2 AirSorts.Bool :=
  Term.func [AirSorts.Int, AirSorts.Int] AirSorts.Bool airFunc.Lt
    fun i =>
      match i with
      | ⟨0, _⟩ => a
      | ⟨1, _⟩ => b
      | ⟨_ + 2, h⟩ => absurd h (by simp)

def binAnd (a b : air_ast.Term Ctx2 AirSorts.Bool) : air_ast.Term Ctx2 AirSorts.Bool :=
  Term.func (List.replicate 2 AirSorts.Bool) AirSorts.Bool (airFunc.And 2)
    fun i =>
      match i with
      | ⟨0, _⟩ => a
      | ⟨1, _⟩ => b
      | ⟨_ + 2, h⟩ => absurd h (by simp)

def varX : air_ast.Term Ctx2 AirSorts.Int := arithAxiomArgs ⟨0, by simp⟩
def varY : air_ast.Term Ctx2 AirSorts.Int := arithAxiomArgs ⟨1, by simp⟩

def _Mul : air_ast.Term Ctx2 AirSorts.Int :=
  Term.func [AirSorts.Int, AirSorts.Int] AirSorts.Int (Mul 2) arithAxiomArgs

def eucDiv : air_ast.Term Ctx2 AirSorts.Int :=
  Term.func [AirSorts.Int, AirSorts.Int] AirSorts.Int EucDIV arithAxiomArgs

def eucMod : air_ast.Term Ctx2 AirSorts.Int :=
  Term.func [AirSorts.Int, AirSorts.Int] AirSorts.Int EucMOD arithAxiomArgs

-- Axioms to ensure multiplication of nats are in-bounds
-- TODO: https://github.com/verus-lang/verus/blob/788fbe2526336161902df2f42b89687f8a015602/source/vir/src/prelude.rs#L836
def Mul_unsigned_bounds : air_ast.Sentence :=
  all (s := Int) <| all (s := Int) <|
    imp
      (equal (binAnd (le const0 varX) (lt const0 varY)) constTrue)
      (equal (binAnd (le const0 _Mul) (le _Mul varX)) constTrue)


-- Axioms to ensure division of unsigned types are in-bounds
-- https://github.com/verus-lang/verus/blob/788fbe2526336161902df2f42b89687f8a015602/source/vir/src/prelude.rs#L851
-- ∀ x y : Int, (0 ≤ x ∧ 0 < y) → (0 ≤ EucDIV(x,y) ∧ EucDIV(x,y) ≤ x)
def EucDiv_unsigned_bounds : air_ast.Sentence :=
  all (s := Int) <| all (s := Int) <|
    imp
      (equal (binAnd (le const0 varX) (lt const0 varY)) constTrue)
      (equal (binAnd (le const0 eucDiv) (le eucDiv varX)) constTrue)


-- Axiom to ensure modulo of unsigned types are in-bounds
-- https://github.com/verus-lang/verus/blob/788fbe2526336161902df2f42b89687f8a015602/source/vir/src/prelude.rs#L864
-- ∀ x y : Int, (0 ≤ x ∧ 0 < y) → (0 ≤ EucMOD(x,y) ∧ EucMOD(x,y) < y)
def EucMod_unsigned_bounds : air_ast.Sentence :=
  all (s := Int) <| all (s := Int) <|
    imp
      (equal (binAnd (le const0 varX) (lt const0 varY)) constTrue)
      (equal (binAnd (le const0 eucMod) (lt eucMod varY)) constTrue)

end ArithAxioms

section PloyCastingAxioms

end PloyCastingAxioms

-- TODO: look at type invariants at https://github.com/verus-lang/verus/blob/788fbe2526336161902df2f42b89687f8a015602/source/vir/src/prelude.rs#L603

-- TODO: ask about this: https://github.com/verus-lang/verus/blob/788fbe2526336161902df2f42b89687f8a015602/source/vir/src/prelude.rs#L758
