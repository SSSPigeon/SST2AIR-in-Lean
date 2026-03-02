import LeanVerus.Sst.Typ
import LeanVerus.Sst.Typing
import LeanVerus.Sst.Exp
import LeanVerus.Sst.Domain


open sst typing

variable (tenv : typ_env)  (dom_aux : ClosedTyp → Type)

def val_vars tenv (Γ: context) dom_aux :=  (i : Nat) → (_ : i < Γ.length) → typ_interp tenv dom_aux Γ[i] ⊕ ExpError

noncomputable
def exp_rep Γ tenv (venv: val_vars tenv Γ dom_aux) (t : Typ) (e : Exp) (hty : Γ ⊢ e : t): typ_interp tenv dom_aux t ⊕ ExpError:=
  match e with
  | .Const c =>
    match c with
    | .Bool b =>
      cast_typ_interp (ty_constbool_inv b hty).symm (cast interp_bool.symm b)
      |> .inl
    | .Int i =>
      cast_typ_interp (ty_constint_inv i hty).symm (cast interp_int.symm i)
      |> .inl
    | .Char c =>
      cast_typ_interp (ty_constchar_inv c hty).symm (cast interp_char.symm c)
      |> .inl
    | .Float32 f =>
      cast_typ_interp (ty_constfloat32_inv f hty).symm (cast interp_float32.symm f)
      |> .inl
    | .Float64 f =>
      cast_typ_interp (ty_constfloat64_inv f hty).symm (cast interp_float64.symm f)
      |> .inl
    | .StrSlice s =>
      cast_typ_interp (ty_strslice_inv s hty).symm (cast interp_strslice.symm s)
      |> .inl

  | .Var i =>
    match (venv i (ty_var_withinbound i hty)) with
    | .inl v => cast_typ_interp (ty_var_inv i hty).symm v |> Sum.inl
    | .inr e => Sum.inr e

  | .ArrayLiteral es =>
    let A: Typ := Classical.choose (ty_array_inv es hty)
    let hA : t = .Array A := (Classical.choose_spec (ty_array_inv es hty)).1
    -- (fun e ls =>
    --   match e with
    --   | none => .inr .RuntimeErr
    --   | some e' => e' :: ls) []
    let res :=
      es.attach.map (fun e : { x: Exp // x ∈ es } =>
        have helem :  WfTm Γ A e.1 := (Classical.choose_spec (ty_array_inv es hty)).2 e.1 e.2
        have : sizeOf e.val < 1 + sizeOf es := by
          refine Nat.lt_add_left 1 ?_;
          refine List.sizeOf_lt_of_mem ?_;
          exact e.property
        exp_rep Γ tenv venv A e.1 helem)
    let f : List (typ_interp tenv dom_aux A ⊕ ExpError) → List (typ_interp tenv dom_aux A) ⊕ ExpError := sorry
    sorry
  | .Unaryr op arg =>
    match op with
    | .HasType t' =>
      let A: Typ := Classical.choose (ty_hasType_inv arg t' t hty).2
      let hA := Classical.choose_spec (ty_hasType_inv arg t' t hty).2
      match (exp_rep Γ tenv venv A arg hA) with
      | .inl _ =>
        cast_typ_interp (ty_hasType_inv arg t' t hty).1.symm (cast interp_bool.symm ((typ_subst tenv A).1 = (typ_subst tenv t').1)) |> .inl
      | .inr e => .inr e
    | .Box t' => sorry
    | .Unbox t' => sorry
    | .IsVariant dt var => sorry
    | .Proj field => sorry

  | .Unary op arg =>
    match op with
    | .Not =>
      match (exp_rep Γ tenv venv t arg (ty_not_inv arg hty).2) with
      | .inl r =>
        let res_bool :=
          cast_typ_interp (ty_not_inv arg hty).1 r
          |> cast interp_bool
        cast_typ_interp (ty_not_inv arg hty).1.symm (cast interp_bool.symm ¬res_bool)
        |> .inl
      | .inr e => .inr e

    | .FloatToBits =>
      match arg with
      | _ => sorry
    | .BitNot (width : Option Nat) => sorry
    | .Clip (range : IntRange) (truncate : Bool) => sorry


  | .Binary op arg₁ arg₂ =>
    match op with
    | .And =>
      match (exp_rep Γ tenv venv t arg₁ (ty_and_inv arg₁ arg₂ hty).2.1), (exp_rep Γ tenv venv t arg₂ (ty_and_inv arg₁ arg₂ hty).2.2) with
      | .inl r₁, .inl r₂ =>
        let l_bool :=
          cast_typ_interp (ty_and_inv arg₁ arg₂ hty).1 r₁
          |> cast interp_bool
        let r_bool :=
          cast_typ_interp (ty_and_inv arg₁ arg₂ hty).1 r₂
          |> cast interp_bool
        cast_typ_interp (ty_and_inv arg₁ arg₂ hty).1.symm (cast interp_bool.symm (l_bool ∧ r_bool))
        |> .inl
      | .inl _, .inr e | .inr e, .inl _ | .inr e, .inr _ => .inr e


    | .Or =>
      match (exp_rep Γ tenv venv t arg₁ (ty_or_inv arg₁ arg₂ hty).2.1), (exp_rep Γ tenv venv t arg₂ (ty_or_inv arg₁ arg₂ hty).2.2) with
      | .inl r₁, .inl r₂ =>
        let l_bool :=
          cast_typ_interp (ty_or_inv arg₁ arg₂ hty).1 r₁
          |> cast interp_bool
        let r_bool :=
          cast_typ_interp (ty_or_inv arg₁ arg₂ hty).1 r₂
          |> cast interp_bool
        cast_typ_interp (ty_or_inv arg₁ arg₂ hty).1.symm (cast interp_bool.symm (l_bool ∨ r_bool))
        |> .inl
      | .inl _, .inr e | .inr e, .inl _ | .inr e, .inr _ => .inr e

    | .Xor =>
      match (exp_rep Γ tenv venv t arg₁ (ty_xor_inv arg₁ arg₂ hty).2.1), (exp_rep Γ tenv venv t arg₂ (ty_xor_inv arg₁ arg₂ hty).2.2) with
      | .inl r₁, .inl r₂ =>
        let l_bool :=
          cast_typ_interp (ty_xor_inv arg₁ arg₂ hty).1 r₁
          |> cast interp_bool
        let r_bool :=
          cast_typ_interp (ty_xor_inv arg₁ arg₂ hty).1 r₂
          |> cast interp_bool
        cast_typ_interp (ty_xor_inv arg₁ arg₂ hty).1.symm (cast interp_bool.symm (Xor' l_bool r_bool))
        |> .inl
      | .inl _, .inr e | .inr e, .inl _ | .inr e, .inr _ => .inr e

    | .Implies =>
      match (exp_rep Γ tenv venv t arg₁ (ty_implies_inv arg₁ arg₂ hty).2.1), (exp_rep Γ tenv venv t arg₂ (ty_implies_inv arg₁ arg₂ hty).2.2) with
      | .inl r₁, .inl r₂ =>
        let l_bool :=
          cast_typ_interp (ty_implies_inv arg₁ arg₂ hty).1 r₁
          |> cast interp_bool
        let r_bool :=
          cast_typ_interp (ty_implies_inv arg₁ arg₂ hty).1 r₂
          |> cast interp_bool
        cast_typ_interp (ty_implies_inv arg₁ arg₂ hty).1.symm (cast interp_bool.symm (l_bool → r_bool))
        |> .inl
      | .inl _, .inr e | .inr e, .inl _ | .inr e, .inr _ => .inr e

    | .Inequality (op : InequalityOp) =>
      let l_res := exp_rep Γ tenv venv (Typ.Int .Int) arg₁ (ty_ineq_inv arg₁ arg₂ op hty).2.1
      let r_res := exp_rep Γ tenv venv (Typ.Int .Int) arg₂ (ty_ineq_inv arg₁ arg₂ op hty).2.2
      match l_res, r_res with
      | .inl r₁, .inl r₂ =>
        let l_int := cast interp_int r₁
        let r_int := cast interp_int r₂
        let res :=
          match op with
          | .Le => l_int <= r_int
          | .Ge => l_int >= r_int
          | .Lt => l_int < r_int
          | .Gt => l_int > r_int
        cast_typ_interp (ty_ineq_inv arg₁ arg₂ op hty).1.symm (cast interp_bool.symm res) |> .inl
      | .inl _, .inr e | .inr e, .inl _ | .inr e, .inr _ => .inr e

    | .Ne =>
      let A: Typ := Classical.choose (ty_ne_inv arg₁ arg₂ hty).2
      let hty₁ : Γ ⊢ arg₁ : A := (Classical.choose_spec (ty_ne_inv arg₁ arg₂ hty).2).1
      let hty₂ : Γ ⊢ arg₂ : A := (Classical.choose_spec (ty_ne_inv arg₁ arg₂ hty).2).2
      match (exp_rep Γ tenv venv A arg₁ hty₁), (exp_rep Γ tenv venv A arg₂ hty₂) with
      | .inl r₁, .inl r₂ => sorry
        --cast_typ_interp (ty_ne_inv arg₁ arg₂ hty).1.symm (cast interp_bool.symm (r₁ ≠ r₂)) |> .inl
      | .inl _, .inr e | .inr e, .inl _ | .inr e, .inr _ => .inr e

    | .Eq m =>
      let A: Typ := Classical.choose (ty_eq_inv arg₁ arg₂ m hty).2
      let hty₁ : Γ ⊢ arg₁ : A := (Classical.choose_spec (ty_eq_inv arg₁ arg₂ m hty).2).1
      let hty₂ : Γ ⊢ arg₂ : A := (Classical.choose_spec (ty_eq_inv arg₁ arg₂ m hty).2).2
      match (exp_rep Γ tenv venv A arg₁ hty₁), (exp_rep Γ tenv venv A arg₂ hty₂) with
      | .inl r₁, .inl r₂ => sorry
        -- cast_typ_interp (ty_eq_inv arg₁ arg₂ m hty).1.symm (cast interp_bool.symm (r₁ = r₂)) |> .inl
      | .inl _, .inr e | .inr e, .inl _ | .inr e, .inr _ => .inr e

    -- bound checking?
    | .Index (ak : ArrayKind) =>
      match ak with
      | .Slice => sorry
      | .Array => sorry

    | .Arith op =>
      match op with
      | .Add =>
        match t with
        | .Int .Int =>
          let l_res := exp_rep Γ tenv venv (Typ.Int .Int) arg₁ (ty_add_inv arg₁ arg₂ (.Int .Int) hty).2.1
          let r_res := exp_rep Γ tenv venv (Typ.Int .Int) arg₂ (ty_add_inv arg₁ arg₂ (.Int .Int) hty).2.2
          match l_res, r_res with
          | .inl r₁, .inl r₂ =>
            let l_int := cast interp_int r₁
            let r_int := cast interp_int r₂
            cast interp_int.symm (l_int + r_int) |> .inl
          | .inl _, .inr e | .inr e, .inl _ | .inr e, .inr _ => .inr e
        | .Int .Nat =>
          let l_res := exp_rep Γ tenv venv (Typ.Int .Nat) arg₁ (ty_add_inv arg₁ arg₂ (.Int .Nat) hty).2.1
          let r_res := exp_rep Γ tenv venv (Typ.Int .Nat) arg₂ (ty_add_inv arg₁ arg₂ (.Int .Nat) hty).2.2
          match l_res, r_res with
          | .inl r₁, .inl r₂ =>
            let l_nat := cast interp_nat r₁
            let r_nat := cast interp_nat r₂
            cast interp_nat.symm (l_nat + r_nat) |> .inl
          | .inl _, .inr e | .inr e, .inl _ | .inr e, .inr _ => .inr e
        | _ => sorry
      | _ => sorry
    | .Bitwise (op : BitwiseOp) (mode : Mode) => sorry

  | .If c b₁ b₂ =>
    let c_res := exp_rep Γ tenv venv Typ._Bool c (ty_if_inv c b₁ b₂ t hty).1
    let b₁_res := exp_rep Γ tenv venv t b₁ (ty_if_inv c b₁ b₂ t hty).2.1
    let b₂_res := exp_rep Γ tenv venv t b₂ (ty_if_inv c b₁ b₂ t hty).2.2
    match c_res, b₁_res, b₂_res with
    | .inl c', .inl b₁', .inl b₂' =>
      let c_bool := cast interp_bool c'
      (if c_bool then b₁' else b₂') |> .inl
    | .inr e, _, _ | _, .inr e, _ | _, _, .inr e => .inr e
  | .Let (tys : List Typ) (es : List Exp) (body : Exp) => sorry
  | .Quant (q : Quant) (var : Typ) (body : Exp) => sorry
  | .TupleCtor (size : Nat) (data : List Exp) => sorry


  | .Call (fn : CallFun) (typs : List Typ) (exps : List Exp) (ret : Typ) => sorry
  | .CallLambda (lam : Exp) (arg : Exp) => sorry
  | .StructCtor (dt : Ident) (fields : List (String × Exp)) => sorry
  | .Lambda (var : Typ) (exp : Exp) => sorry

termination_by sizeOf e
