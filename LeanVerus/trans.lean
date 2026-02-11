import LeanVerus.Typ
import LeanVerus.Typing
import LeanVerus.Exp
import LeanVerus.Domain
import LeanVerus.Ast

open sst typing airast Std

variable (tenv : typ_env)  (dom_aux : ClosedTyp → Type)

def transf (e : sst.Exp) : Expr :=
  match e with
  | .Const c =>
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L749
    match c with
    | .Bool b => .Const (.Bool b)
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L296
    | .Int i =>
        if i ≥ 0 then .Const (.Nat i.repr)
        else .Multi .Sub [.Const (.Nat "0"), .Const (.Nat (-i).repr)]
    | .StrSlice s => sorry
    | .Char c => .Const (.Nat (toString c.val))
    | .Float32 f => .Const (.Nat (toString f))
    | .Float64 f => .Const (.Nat (toString f))
  | .Var idx => .Var idx
  | .Binary op e₁ e₂ =>
    match op with
    | .Arith op' _ =>
      match op' with
      -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L1253
      | .Add => .Apply "ADD" [transf e₁, transf e₂]
      | _ => sorry
    | .And => .Multi .And [transf e₁, transf e₂]
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L1311
    | .Index _ _ => .Apply "ARRAY_INDEX" [transf e₁, transf e₂]
    | _ => sorry

   | _ => sorry
