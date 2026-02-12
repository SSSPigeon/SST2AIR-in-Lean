import LeanVerus.Typ
import LeanVerus.Typing
import LeanVerus.Exp
import LeanVerus.Domain
import LeanVerus.Ast
import LeanVerus.Axiom

open sst typing airast Std

variable (tenv : typ_env)  (dom_aux : ClosedTyp → Type)

def transf (e : sst.Exp) (aenv : axioms) : Expr × axioms:=
  match e with
  | .Const c =>
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L749
    match c with
    | .Bool b => ⟨.Const (.Bool b), aenv ⟩
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L296
    | .Int i =>
        if i ≥ 0 then ⟨.Const (.Nat i.repr), aenv⟩
        else ⟨.Multi .Sub [.Const (.Nat "0"), .Const (.Nat (-i).repr)], aenv⟩
    | .StrSlice s => sorry
    | .Char c => ⟨.Const (.Nat (toString c.val)), aenv⟩
    | .Float32 f => ⟨.Const (.Nat (toString f)), aenv⟩
    | .Float64 f => ⟨.Const (.Nat (toString f)), aenv⟩

  | .Var idx => ⟨.Var idx, aenv⟩

  | .Binary op e₁ e₂ =>
    match op with
    | .Arith op' _ =>
      match op' with
      -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L1253
      | .Add => ⟨.Apply "ADD" [(transf e₁ aenv).1, (transf e₂ aenv).1], aenv.insert ADD_axiom⟩
      | _ => sorry
    | .And => ⟨.Multi .And [(transf e₁ aenv).1, (transf e₂ aenv).1], aenv⟩
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L1311
    | .Index _ _ => ⟨.Apply "ARRAY_INDEX" [(transf e₁ aenv).1, (transf e₂ aenv).1], aenv.insert ARRAY_INDEX_axiom⟩
    | _ => sorry

   | _ => sorry
