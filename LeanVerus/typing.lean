import LeanVerus.My_sst

open VerusLean Std List

inductive WsTm : Nat → Exp → Prop
  | const : ∀ n c,
    WsTm n (.Const c)

  | var : ∀ n i,
    i < n →
    WsTm n (.Var i)

  | call : ∀ n fn typs exps,
    ∀ e ∈ exps, WsTm n e →
    WsTm n (.Call fn typs exps)

  | callLambda : ∀ n lam args,
    WsTm n lam →
    ∀ e ∈ args, WsTm n e →
    WsTm n (.CallLambda lam args)

  | structor : ∀ n dt fields,
    ∀ p ∈ fields, WsTm n p.2 →
    WsTm n (.StructCtor dt fields)

  | tuplector : ∀ n size data,
    ∀ e ∈ data, WsTm n e →
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
    ∀ e ∈ es, WsTm (n + List.length es) e →
    WsTm (n + List.length es) exp →
    WsTm n (.Let tys es exp)

  | quant : ∀ n q var exp,
    WsTm (n + 1) exp →
    WsTm n (.Quant q var exp)

  | lambda : ∀ n var exp,
    WsTm (n + 1) exp →
    WsTm n (.Lambda var exp)

  | arrayLiteral : ∀ n elems,
    ∀ e ∈ elems, WsTm n e →
    WsTm n (.ArrayLiteral elems)
