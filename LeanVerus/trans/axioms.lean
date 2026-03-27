import LeanVerus.Air_ast.Ast
import Mathlib.Data.Set.Basic
import LeanVerus.Air_ast.«Air-ast»

open MSFirstOrder MSLanguage AirSorts BoundedFormula airFunc


-- Prelude axioms: https://github.com/verus-lang/verus/blob/788fbe2526336161902df2f42b89687f8a015602/source/vir/src/prelude.rs

--  ∀ (x : Int) (y : Int), ADD(x, y) = Add(x, y)
--   pos = 0  →  x  (outer ∀)
--   pos = 1  →  y  (inner ∀)
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

-- TODO: look at type invariants at https://github.com/verus-lang/verus/blob/788fbe2526336161902df2f42b89687f8a015602/source/vir/src/prelude.rs#L603

-- TODO: ask about this: https://github.com/verus-lang/verus/blob/788fbe2526336161902df2f42b89687f8a015602/source/vir/src/prelude.rs#L758
