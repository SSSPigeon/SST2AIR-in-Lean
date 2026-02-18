import LeanVerus.Air_ast.Ast
import Mathlib.Data.Set.Basic

open airast

def axioms := Set Axiom

def ADD_axiom : Axiom :=
  .Quant .Forall .Int
    (.Quant .Forall .Int (.Binary .Eq
      (.Apply "ADD" [.Var 1, .Var 0])
      (.Multi .Add [.Var 1, .Var 0])))

def ARRAY_INDEX_axiom : Axiom := sorry
  -- .Quant .Forall .Array (.Quant .Forall .Nat (.Binary .Eq
  --   (.Apply "ARRAY_INDEX" [.Var 1, .Var 0])
  --   (.Apply "ARRAY_INDEX" [.Var 1, .Var 0])))
