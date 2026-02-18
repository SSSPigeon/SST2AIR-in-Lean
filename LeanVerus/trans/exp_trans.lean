import LeanVerus.Sst.Typ
import LeanVerus.Sst.Typing
import LeanVerus.Sst.Exp
import LeanVerus.Sst.Domain
import LeanVerus.Air_ast.Ast
import LeanVerus.Trans.Axiom

open sst typing airast Std

variable (tenv : typ_env)  (dom_aux : ClosedTyp → Type)

/--
  In Why3-Coq,
  Γ : types, function definitions, predicate definitions
  Δ : axioms
  I : full interpretation of Γ
  Soundness: If Γ', Δ' ⊨ g', then Γ, Δ ⊨ g (∀ I, I ⊨ Δ => I ⊨ g)

  In our case,
  Γ : function definitions
  Δ : axioms
  I : full interpretation of Γ
  Soundness:
    (a) in sst, Δ = ∅
    (b) after translation, we have Δ' containing axioms introduced during translation
    (c) Γ' = Γ
    (d) I' is the full interpretation of Γ that satisfies Δ'
    Given: I, define I'
      I(e) ≃ I'(e') for all e ∈ Sst.Exp
-/

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
