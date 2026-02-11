import LeanVerus.Exp

open sst Std List

inductive WsTm : Nat → Exp → Prop
  | const : ∀ n c,
    WsTm n (.Const c)

  | var : ∀ n i,
    i < n →
    WsTm n (.Var i)

  | call : ∀ n fn typs exps,
    (∀ e ∈ exps, WsTm n e) →
    WsTm n (.Call fn typs exps)

  | callLambda : ∀ n lam args,
    WsTm n lam →
    (∀ e ∈ args, WsTm n e) →
    WsTm n (.CallLambda lam args)

  | structctor : ∀ n dt fields,
    (∀ p ∈ fields, WsTm n p.2) →
    WsTm n (.StructCtor dt fields)

  | tuplector : ∀ n size data,
    (∀ e ∈ data, WsTm n e) →
    WsTm n (.TupleCtor size data)

  | unary : ∀ n op arg,
    WsTm n arg →
    WsTm n (.Unary op arg)

  | unaryr : ∀ n op arg,
    WsTm n arg →
    WsTm n (.Unaryr op arg)

  | binary : ∀ n op arg₁ arg₂,
    WsTm n arg₁ →
    WsTm n arg₂ →
    WsTm n (.Binary op arg₁ arg₂)

  | _if : ∀ n cond b₁ b₂,
    WsTm n cond →
    WsTm n b₁ →
    WsTm n b₂ →
    WsTm n (.If cond b₁ b₂)

  | _let : ∀ n tys es exp,
    (∀ e ∈ es, WsTm n e) →
    WsTm (n + List.length es) exp →
    WsTm n (.Let tys es exp)

  | quant : ∀ n q var exp,
    WsTm (n + 1) exp →
    WsTm n (.Quant q var exp)

  | lambda : ∀ n var exp,
    WsTm (n + 1) exp →
    WsTm n (.Lambda var exp)

  | arrayLiteral : ∀ n elems,
    (∀ e ∈ elems, WsTm n e) →
    WsTm n (.ArrayLiteral elems)

namespace Inversion

attribute [local grind] WsTm

theorem ws_increase (n m : Nat) (e : Exp) : WsTm n e → WsTm (n + m) e := by
  induction e generalizing n
  all_goals try grind
  . intro h
    cases h
    next foo =>
      expose_names
      constructor
      . intro e hmem
        apply h
        exact hmem
        apply foo
        exact hmem

theorem inv_var : ∀ n i,  WsTm n (.Var i) → i < n := by grind
theorem inv_call : ∀ n fn typs exps, WsTm n (.Call fn typs exps) →
  (∀ e ∈ exps, WsTm n e) := by grind
theorem inv_callLambda : ∀ n lam args, WsTm n (.CallLambda lam args) →
  WsTm n lam ∧ (∀ e ∈ args, WsTm n e) := by grind
theorem inv_structctor : ∀ n dt fields, WsTm n (.StructCtor dt fields) →
  (∀ p ∈ fields, WsTm n p.2) := by grind
theorem inv_tuplector : ∀ n size data, WsTm n (.TupleCtor size data) →
  (∀ e ∈ data, WsTm n e) := by grind
theorem inv_unary : ∀ n op arg, WsTm n (.Unary op arg) →
  WsTm n arg := by grind
theorem inv_unaryr : ∀ n op arg, WsTm n (.Unaryr op arg) →
  WsTm n arg := by grind
theorem inv_binary : ∀ n op arg₁ arg₂, WsTm n (.Binary op arg₁ arg₂) →
  WsTm n arg₁ ∧ WsTm n arg₂ := by grind
theorem inv_if : ∀ n cond b₁ b₂, WsTm n (.If cond b₁ b₂) →
  WsTm n cond ∧ WsTm n b₁ ∧ WsTm n b₂ := by grind
theorem inv_let : ∀ n tys es exp, WsTm n (.Let tys es exp) →
  (∀ e ∈ es, WsTm n e) ∧ WsTm (n + List.length es) exp := by grind
theorem inv_quant : ∀ n q var exp, WsTm n (.Quant q var exp) →
  WsTm (n + 1) exp := by grind
theorem inv_lambda : ∀ n var exp, WsTm n (.Lambda var exp) →
  WsTm (n + 1) exp := by grind
theorem inv_arrayLiteral : ∀ n elems, WsTm n (.ArrayLiteral elems) →
  (∀ e ∈ elems, WsTm n e) := by grind

end Inversion
