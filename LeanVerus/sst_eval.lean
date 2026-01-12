import LeanVerus.My_sst
import LeanVerus.Typing

open VerusLean Std

abbrev var_env := List Exp

abbrev typ_env := Typ → Typ

abbrev func_env := Typ → Exp


inductive Eval: var_env → func_env → Exp → Exp → Prop where
  | const: ∀ (v: var_env) (f: func_env) (c: Const),
    WsTm v.length (.Const c) →
    Eval v f (.Const c) (.Const c)

  | var: ∀ (v: var_env) (f: func_env) (i: Nat) (e: Exp),
    WsTm v.length (.Var i) →
    v[i]? = e →
    Eval v f (.Var i) e

  -- | call: ∀ (v: var_env) (f: func_env) (fn: String) (typs: List Typ) (exps: List Exp) (res: Exp),
  --   WsTm v.length (.Call fn typs exps) →
  --   (∀ e ∈ exps, ∃ r, Eval v f e r) →
  --   f (Typ.Call fn typs) = .Some res →
  --   Eval v f (.Call fn typs exps) res
