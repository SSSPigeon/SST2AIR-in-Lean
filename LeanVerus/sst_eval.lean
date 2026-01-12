import LeanVerus.My_sst
import LeanVerus.Typing

open VerusLean Std

abbrev var_env := List Exp

abbrev typ_env := Typ → Typ

abbrev func_env := Typ → Exp


inductive Eval: var_env → func_env → Exp → Exp → Prop where
  | const:
      ∀ (v: var_env) (f: func_env) (c: Const),
      WsTm v.length (.Const c) →
      Eval v f (.Const c) (.Const c)

  | var:
      ∀ (v: var_env) (f: func_env) (i: Nat) (e: Exp),
      WsTm v.length (.Var i) →
      v[i]? = e →
      Eval v f (.Var i) e

  /-- Unary -/
  | unary_not_true :
      ∀ (v : var_env) (f : func_env) (arg : Exp),
      WsTm v.length (.Unary .Not arg) →
      Eval v f arg (.Const (.Bool true)) →
      Eval v f (.Unary .Not arg) (.Const (.Bool false))

  | unary_not_false :
      ∀ (v : var_env) (f : func_env) (arg : Exp),
      WsTm v.length (.Unary .Not arg) →
      Eval v f arg (.Const (.Bool false)) →
      Eval v f (.Unary .Not arg) (.Const (.Bool true))

  | unary_not_other:
      ∀ (v: var_env) (f: func_env) (arg arg_res: Exp),
      WsTm v.length (.Unary .Not arg) →
      Eval v f arg arg_res →
      Eval v f (.Unary .Not arg) (.Unary .Not arg_res)

  /- TODO : bitnot i128 -/
  | unary_bitnot_none :
      ∀ (v : var_env) (f : func_env) (i : Int) (i' : Int),
      WsTm v.length (.Unary (.BitNot none) (.Const (.Int i))) →
      Eval v f (.Const (.Int i)) (.Const (.Int i')) →
      Eval v f (.Unary (.BitNot none) (.Const (.Int i)))
              (.Const (.Int (~~~i')))

  | unary_bitnot_width :
      ∀ (v : var_env) (f : func_env) (w : Nat) (i : Int) (i' : Int),
      WsTm v.length (.Unary (.BitNot (some w)) (.Const (.Int i))) →
      Eval v f (.Const (.Int i)) (.Const (.Int i')) →
      Eval v f (.Unary (.BitNot (some w)) (.Const (.Int i)))
              (.Const (.Int (~~~i' <<< w)))

  | unary_bitnot_other :
      ∀ (v : var_env) (f : func_env) (w : Option Nat) (arg arg_res : Exp),
      WsTm v.length (.Unary (.BitNot w) arg) →
      Eval v f arg arg_res →
      Eval v f (.Unary (.BitNot w) arg) (.Unary (.BitNot w) arg_res)

  | unary_clip_other:
      ∀ (v : var_env) (f : func_env) (range : IntRange) (truncate : Bool)
        (arg arg_res : Exp),
      WsTm v.length (.Unary (.Clip range truncate) arg) →
      Eval v f arg arg_res →
      Eval v f (.Unary (.Clip range truncate) arg)
                (.Unary (.Clip range truncate) arg_res)

  /-- Unaryr -/
  | unary_hasType :
      ∀ (v : var_env) (f : func_env) (τ : Typ) (e e' : Exp),
      WsTm v.length (.Unaryr (.HasType τ) e) →
      Eval v f e e' →
      Eval v f (.Unaryr (.HasType τ) e) (.Unaryr (.HasType τ) e')

  | unary_isVariant :
      ∀ (v : var_env) (f : func_env) (e : Exp)
        (dt dt': Ident) (var: String) (fields: List (String × Exp)),
      WsTm v.length (.Unaryr (.IsVariant dt var) e) →
      Eval v f e (.StructCtor dt' fields) →
      Eval v f (.Unaryr (.IsVariant dt var) e)
        (.Const (.Bool (dt = dt' ∧ fields.any (fun p => p.1 = var))))

  | unary_proj :
      ∀ (v : var_env) (f : func_env) (e : Exp)
        (dt: Ident) (field: String) (fields: List (String × Exp)),
      WsTm v.length (.Unaryr (.Proj field) e) →
      Eval v f e (.StructCtor dt fields) →
      Eval v f (.Unaryr (.Proj field) e)
        ((fields.find? (fun p => p.1 = field)).getD ("dummy", (.StructCtor dt fields))).2
