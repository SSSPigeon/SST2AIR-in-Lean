import LeanVerus.My_sst
import LeanVerus.Typing

open VerusLean Std

abbrev var_env := List Exp

abbrev typ_env := Typ → Typ --String → Typ

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
    Eval v f arg arg_res → arg_res ≠ .Const (.Bool true) → arg_res ≠ .Const (.Bool false) →
    Eval v f (.Unary .Not arg) (.Unary .Not arg_res)

  /- TODO : bitnot i128 -/
  | unary_bitnot_nwidth :
    ∀ (v : var_env) (f : func_env) (i : Int) (arg : Exp) ,
    WsTm v.length (.Unary (.BitNot none) (.Const (.Int i))) →
    Eval v f arg (.Const (.Int i)) →
    Eval v f (.Unary (.BitNot none) arg)
            (.Const (.Int (~~~i)))

  | unary_bitnot_width :
    ∀ (v : var_env) (f : func_env) (w : Nat) (i : Int) (arg : Exp),
    WsTm v.length (.Unary (.BitNot (some w)) (.Const (.Int i))) →
    Eval v f arg (.Const (.Int i)) →
    Eval v f (.Unary (.BitNot (some w)) arg)
            (.Const (.Int (~~~i <<< w)))

  | unary_bitnot_other :
    ∀ (v : var_env) (f : func_env) (w : Option Nat) (arg arg_res : Exp),
    WsTm v.length (.Unary (.BitNot w) arg) →
    Eval v f arg arg_res →
    Eval v f (.Unary (.BitNot w) arg) (.Unary (.BitNot w) arg_res)

--   TODO : clip
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

  /-- Binary -/
  | binary_and_fst_true :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ : Exp),
    WsTm v.length (.Binary .And arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Bool true)) →
    Eval v f arg₂ arg₃ →
    Eval v f (.Binary .And arg₁ arg₂) arg₃

  | binary_and_fst_false :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ : Exp),
    WsTm v.length (.Binary .And arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Bool false)) →
    Eval v f (.Binary .And arg₁ arg₂) (.Const (.Bool false))

  | binary_and_snd_true :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ : Exp),
    WsTm v.length (.Binary .And arg₁ arg₂) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f arg₂ (.Const (.Bool true)) →
    Eval v f (.Binary .And arg₁ arg₂) arg₃

  | binary_and_snd_false :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ : Exp),
    WsTm v.length (.Binary .And arg₁ arg₂) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f arg₂ (.Const (.Bool false)) →
    Eval v f (.Binary .And arg₁ arg₂) (.Const (.Bool false))

  | binary_and_other :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄: Exp),
    WsTm v.length (.Binary .And arg₁ arg₂) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f arg₂ arg₄ → arg₄ ≠ .Const (.Bool true) → arg₄ ≠ .Const (.Bool false) →
    Eval v f (.Binary .And arg₁ arg₂) (.Binary .And arg₃ arg₄)

  | binary_or_fst_true :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ : Exp),
    WsTm v.length (.Binary .Or arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Bool true)) →
    Eval v f (.Binary .Or arg₁ arg₂) (.Const (.Bool true))

  | binary_or_fst_false :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ : Exp),
    WsTm v.length (.Binary .Or arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Bool false)) →
    Eval v f arg₂ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f (.Binary .Or arg₁ arg₂) arg₃

  | binary_or_snd_true :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ : Exp),
    WsTm v.length (.Binary .Or arg₁ arg₂) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f arg₂ (.Const (.Bool true)) →
    Eval v f (.Binary .Or arg₁ arg₂) (.Const (.Bool true))

  | binary_or_snd_false :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ : Exp),
    WsTm v.length (.Binary .Or arg₁ arg₂) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f arg₂ (.Const (.Bool false)) →
    Eval v f (.Binary .Or arg₁ arg₂) arg₃

  | binary_or_other :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄: Exp),
    WsTm v.length (.Binary .Or arg₁ arg₂) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f arg₂ arg₄ → arg₄ ≠ .Const (.Bool true) → arg₄ ≠ .Const (.Bool false) →
    Eval v f (.Binary .Or arg₁ arg₂) (.Binary .Or arg₃ arg₄)

  | binary_xor_both :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂: Exp) (b₁ b₂ : Bool),
    WsTm v.length (.Binary .Xor arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Bool b₁)) →
    Eval v f arg₂ (.Const (.Bool b₂)) →
    Eval v f (.Binary .Xor arg₁ arg₂) (.Unary .Not (.Const (.Bool ((b₁ ∧ ¬ b₂) ∨(¬ b₁ ∧ b₂)))))

  | binary_xor_fst_true :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃: Exp),
    WsTm v.length (.Binary .Xor arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Bool true)) →
    Eval v f arg₂ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f (.Binary .Xor arg₁ arg₂) (.Unary .Not arg₃)

  | binary_xor_fst_false :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃: Exp),
    WsTm v.length (.Binary .Xor arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Bool false)) →
    Eval v f arg₂ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f (.Binary .Xor arg₁ arg₂) arg₃

  | binary_xor_snd_true :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃: Exp),
    WsTm v.length (.Binary .Xor arg₁ arg₂) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f arg₂ (.Const (.Bool true)) →
    Eval v f (.Binary .Xor arg₁ arg₂) (.Unary .Not arg₃)

  | binary_xor_snd_false :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃: Exp),
    WsTm v.length (.Binary .Xor arg₁ arg₂) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f arg₂ (.Const (.Bool false)) →
    Eval v f (.Binary .Xor arg₁ arg₂) arg₃

  | binary_implies_fst_true :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃: Exp),
    WsTm v.length (.Binary .Implies arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Bool true)) →
    Eval v f arg₂ arg₃ →
    Eval v f (.Binary .Implies arg₁ arg₂) arg₃

  | binary_implies_fst_false :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ : Exp),
    WsTm v.length (.Binary .Implies arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Bool false)) →
    Eval v f (.Binary .Implies arg₁ arg₂) (.Const (.Bool true))

  -- https://github.com/verus-lang/verus/blob/main/source/vir/src/interpreter.rs#L1422
  | binary_implies_snd_true :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃: Exp),
    WsTm v.length (.Binary .Implies arg₁ arg₂) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f arg₂ (.Const (.Bool true)) →
    Eval v f (.Binary .Implies arg₁ arg₂) (.Const (.Bool true))

  | binary_implies_snd_false :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃: Exp),
    WsTm v.length (.Binary .Implies arg₁ arg₂) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool false) →
    Eval v f arg₂ (.Const (.Bool false)) →
    Eval v f (.Binary .Implies arg₁ arg₂) (.Unary .Not arg₃)

  | binary_implies_other :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄ : Exp),
    WsTm v.length (.Binary .Implies arg₁ arg₂) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Bool true) → arg₃ ≠ .Const (.Bool  false) →
    Eval v f arg₂ arg₄ → arg₄ ≠ .Const (.Bool true) → arg₄ ≠ .Const (.Bool false) →
    Eval v f (.Binary .Implies arg₁ arg₂) (.Binary .Implies arg₃ arg₄)

  | binary_eq_definite :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄ : Exp) (b : Bool),
    WsTm v.length (.Binary (.Eq _) arg₁ arg₂) →
    Eval v f arg₁ arg₃ →
    Eval v f arg₂ arg₄ →
    Exp.syntactic_eq arg₃ arg₄ = some b →
    Eval v f (.Binary (.Eq _) arg₁ arg₂) (.Const (.Bool b))

  | binary_eq_other :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄ : Exp),
    WsTm v.length (.Binary (.Eq _) arg₁ arg₂) →
    Eval v f arg₁ arg₃ →
    Eval v f arg₂ arg₄ →
    Exp.syntactic_eq arg₃ arg₄ = none →
    Eval v f (.Binary (.Eq _) arg₁ arg₂) (.Binary (.Eq _) arg₃ arg₄)

  | binary_ne_definite :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄ : Exp) (b : Bool),
    WsTm v.length (.Binary .Ne arg₁ arg₂) →
    Eval v f arg₁ arg₃ →
    Eval v f arg₂ arg₄ →
    Exp.syntactic_eq arg₃ arg₄ = some b →
    Eval v f (.Binary .Ne arg₁ arg₂) (.Const (.Bool ¬ b))

  | binary_ne_other :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄ : Exp),
    WsTm v.length (.Binary .Ne arg₁ arg₂) →
    Eval v f arg₁ arg₃ →
    Eval v f arg₂ arg₄ →
    Exp.syntactic_eq arg₃ arg₄ = none →
    Eval v f (.Binary .Ne arg₁ arg₂) (.Binary .Ne arg₃ arg₄)

  | binary_le_ints :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ : Exp) (i₁ i₂ : Int),
    WsTm v.length (.Binary (.Inequality .Le) arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Int i₁)) →
    Eval v f arg₂ (.Const (.Int i₂)) →
    Eval v f (.Binary (.Inequality .Le) arg₁ arg₂) (.Const (.Bool (i₁ ≤ i₂)))

  | binary_le_other :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄ : Exp),
    WsTm v.length (.Binary (.Inequality .Le) arg₁ arg₂) →
    Eval v f arg₁ arg₃ →
    Eval v f arg₂ arg₄ →
    Eval v f (.Binary (.Inequality .Le) arg₁ arg₂) (.Binary (.Inequality .Le) arg₃ arg₄)

  | binary_lt_ints :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ : Exp) (i₁ i₂ : Int),
    WsTm v.length (.Binary (.Inequality .Lt) arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Int i₁)) →
    Eval v f arg₂ (.Const (.Int i₂)) →
    Eval v f (.Binary (.Inequality .Lt) arg₁ arg₂) (.Const (.Bool (i₁ < i₂)))

  | binary_lt_other :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄ : Exp),
    WsTm v.length (.Binary (.Inequality .Lt) arg₁ arg₂) →
    Eval v f arg₁ arg₃ →
    Eval v f arg₂ arg₄ →
    Eval v f (.Binary (.Inequality .Lt) arg₁ arg₂) (.Binary (.Inequality .Lt) arg₃ arg₄)

  | binary_ge_ints :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ : Exp) (i₁ i₂ : Int),
    WsTm v.length (.Binary (.Inequality .Ge) arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Int i₁)) →
    Eval v f arg₂ (.Const (.Int i₂)) →
    Eval v f (.Binary (.Inequality .Ge) arg₁ arg₂) (.Const (.Bool (i₁ ≥ i₂)))

  | binary_ge_other :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄ : Exp),
    WsTm v.length (.Binary (.Inequality .Ge) arg₁ arg₂) →
    Eval v f arg₁ arg₃ →
    Eval v f arg₂ arg₄ →
    Eval v f (.Binary (.Inequality .Ge) arg₁ arg₂) (.Binary (.Inequality .Ge) arg₃ arg₄)

  | binary_gt_ints :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ : Exp) (i₁ i₂ : Int),
    WsTm v.length (.Binary (.Inequality .Gt) arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Int i₁)) →
    Eval v f arg₂ (.Const (.Int i₂)) →
    Eval v f (.Binary (.Inequality .Gt) arg₁ arg₂) (.Const (.Bool (i₁ > i₂)))

  | binary_gt_other :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄ : Exp),
    WsTm v.length (.Binary (.Inequality .Gt) arg₁ arg₂) →
    Eval v f arg₁ arg₃ →
    Eval v f arg₂ arg₄ →
    Eval v f (.Binary (.Inequality .Gt) arg₁ arg₂) (.Binary (.Inequality .Gt) arg₃ arg₄)

  | binary_add_ints :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ : Exp) (i₁ i₂ : Int),
    WsTm v.length (.Binary (.Arith .Add .Allow) arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Int i₁)) →
    Eval v f arg₂ (.Const (.Int i₂)) →
    Eval v f (.Binary (.Arith .Add .Allow) arg₁ arg₂) (.Const (.Int (i₁ + i₂)))

  | binary_add_folding1 :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ : Exp) (i : Int),
    WsTm v.length (.Binary (.Arith .Add .Allow) arg₁ arg₂) →
    Eval v f arg₁ (.Const (.Int 0)) →
    Eval v f arg₂ arg₃ → arg₃ ≠ .Const (.Int i) →
    Eval v f (.Binary (.Arith .Add .Allow) arg₁ arg₂) arg₃

  | binary_add_folding2 :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ : Exp) (i : Int),
    WsTm v.length (.Binary (.Arith .Add .Allow) arg₁ arg₂) →
    Eval v f arg₂ (.Const (.Int 0)) →
    Eval v f arg₁ arg₃ → arg₃ ≠ .Const (.Int i) →
    Eval v f (.Binary (.Arith .Add .Allow) arg₁ arg₂) arg₃

  | binary_add_other :
    ∀ (v : var_env) (f : func_env) (arg₁ arg₂ arg₃ arg₄ : Exp),
    WsTm v.length (.Binary (.Arith .Add .Allow) arg₁ arg₂) →
    Eval v f arg₁ arg₃ →
    Eval v f arg₂ arg₄ →
    Eval v f (.Binary (.Arith .Add .Allow) arg₁ arg₂) (.Binary (.Arith .Add .Allow) arg₃ arg₄)

  | binaryr_ext_eq :
    ∀ (v : var_env) (f : func_env) (arg arg_res : Exp),
    WsTm v.length (.Binaryr (.ExtEq) arg) →
    Eval v f arg arg_res →
    Eval v f (.Binaryr (.ExtEq) arg) (.Binaryr (.ExtEq) arg_res)
