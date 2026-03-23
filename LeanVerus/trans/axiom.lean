import LeanVerus.Air_ast.Ast
import Mathlib.Data.Set.Basic
import LeanVerus.Air_ast.«Air-ast»

open airast

def axioms := Set Axiom

-- ADD_axiom using ast.lean (Expr-based representation)
-- Semantics: ∀ (x : Int) (y : Int), ADD(x, y) = Add(x, y)
def ADD_axiom : Axiom :=
  .Quant .Forall .Int
    (.Quant .Forall .Int (.Binary .Eq
      (.Apply "ADD" [.Var 1, .Var 0])
      (.Multi .Add [.Var 1, .Var 0])))

--
-- In the multisorted framework an axiom is an `air_ast.Sentence`:
--   Sentence L = BoundedFormula L (fun _ => Empty) []
--
-- Quantifiers use BoundedFormula.all, which appends one sort to the
-- bound-variable list σ.  After two `all (s := Int)` steps σ = [Int, Int].
--
-- In BoundedFormula air_ast (fun _ => Empty) [Int, Int], each term has
-- variable family  ((fun _ => Empty) ⊕ₛ [Int, Int].toFam).
-- For sort Int this is   Empty ⊕ {n : Fin 2 // [Int,Int].get n = Int},
-- i.e. bound variables accessed via Sum.inr ⟨⟨pos, _⟩, rfl⟩.
--   pos = 0  →  x  (outer ∀)
--   pos = 1  →  y  (inner ∀)
--
-- airFunc.ADD is the uninterpreted symbol; airFunc.Add is the built-in
-- addition.  The axiom links them: ∀ x y, ADD(x, y) = Add(x, y).

open MSFirstOrder MSLanguage AirSorts

-- Maps argument position i ∈ {0,1} to the i-th bound Int variable.
-- We match on i explicitly so Lean can reduce List.get [Int,Int] ⟨0,_⟩ = Int
-- definitionally in each branch, avoiding the over-eager rewrite of h ▸.
private def addAxiomArgTerms
    (i : Fin 2)
    : air_ast.Term ((fun _ => Empty) ⊕ₛ [AirSorts.Int, AirSorts.Int].toFam)
                   ([AirSorts.Int, AirSorts.Int].get i) :=
  match i with
  | ⟨0, h⟩ => Term.var AirSorts.Int
      (Sum.inr (⟨⟨0, h⟩, rfl⟩ : [AirSorts.Int, AirSorts.Int].toFam AirSorts.Int))
  | ⟨1, h⟩ => Term.var AirSorts.Int
      (Sum.inr (⟨⟨1, h⟩, rfl⟩ : [AirSorts.Int, AirSorts.Int].toFam AirSorts.Int))
  | ⟨n + 2, h⟩ => absurd h (by omega)

-- ADD_axiom using air-ast.lean
-- Semantics: ∀ (x : Int) (y : Int), ADD(x, y) = Add(x, y)
def ADD_axiom_air : air_ast.Sentence :=
  BoundedFormula.all (s := AirSorts.Int)
    (BoundedFormula.all (s := AirSorts.Int)
      (BoundedFormula.equal
        (Term.func [AirSorts.Int, AirSorts.Int] AirSorts.Int airFunc.ADD addAxiomArgTerms)
        (Term.func [AirSorts.Int, AirSorts.Int] AirSorts.Int airFunc.Add addAxiomArgTerms)))
