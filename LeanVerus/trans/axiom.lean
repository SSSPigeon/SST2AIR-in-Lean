import LeanVerus.Air_ast.Ast
import Mathlib.Data.Set.Basic
import LeanVerus.Air_ast.«Air-ast»

open airast

def axioms := Set Axiom

--  ∀ (x : Int) (y : Int), ADD(x, y) = Add(x, y)
--   pos = 0  →  x  (outer ∀)
--   pos = 1  →  y  (inner ∀)
open MSFirstOrder MSLanguage AirSorts BoundedFormula airFunc

def addAxiomArgs (i : Fin 2) :
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
def ADD_axiom_air : air_ast.Sentence :=
  all (s := Int)
    (all (s := Int)
      (equal
        (Term.func [AirSorts.Int, Int] Int ADD addAxiomArgs)
        (Term.func [AirSorts.Int, Int] Int Add addAxiomArgs)
      )
    )
