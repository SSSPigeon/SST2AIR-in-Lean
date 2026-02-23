import LeanVerus.Sst.Typ
import LeanVerus.Sst.Typing
import LeanVerus.Sst.Exp
import LeanVerus.Sst.Domain


open sst typing

variable (tenv : typ_env)  (dom_aux : ClosedTyp → Type)

def val_vars tenv (Γ: context) dom_aux :=  (i : Nat) → (_ : i < Γ.length) → typ_interp tenv dom_aux Γ[i]

noncomputable
def exp_rep Γ tenv (venv: val_vars tenv Γ dom_aux) (t : Typ) (e : Exp) (hty : Γ ⊢ e : t): typ_interp tenv dom_aux t:=
  match e with
  | .Const c =>
    match c with
    | .Bool b =>
      cast_typ_interp (ty_constbool_inv b hty).symm (cast interp_bool.symm b)
    | .Int i =>
      cast_typ_interp (ty_constint_inv i hty).symm (cast interp_int.symm i)
    | .Char c =>
      cast_typ_interp (ty_constchar_inv c hty).symm (cast interp_char.symm c)
    | .Float32 f =>
      cast_typ_interp (ty_constfloat32_inv f hty).symm (cast interp_float32.symm f)
    | .Float64 f =>
      cast_typ_interp (ty_constfloat64_inv f hty).symm (cast interp_float64.symm f)
    | .StrSlice s =>
      cast_typ_interp (ty_strslice_inv s hty).symm (cast interp_strslice.symm s)

  | .Var i =>
    cast_typ_interp (ty_var_inv i hty).symm (venv i (ty_var_withinbound i hty))

  | .ArrayLiteral es =>
    let A: Typ := Classical.choose (ty_array_inv es hty)
    let hA : t = .Array A := (Classical.choose_spec (ty_array_inv es hty)).1
    cast_typ_interp hA.symm
      (cast (interp_array A).symm
        (es.attach.map (fun e : { x: Exp // x ∈ es } =>
          have helem :  WfTm Γ A e.1 := (Classical.choose_spec (ty_array_inv es hty)).2 e.1 e.2
          have : sizeOf e.val < 1 + sizeOf es := by
            refine Nat.lt_add_left 1 ?_;
            refine List.sizeOf_lt_of_mem ?_;
            exact e.property
          exp_rep Γ tenv venv A e.1 helem)))

  | .Unaryr op arg =>
    match op with
    | .HasType t' =>
      cast_typ_interp (ty_hasType_inv arg t' t hty).symm (cast interp_bool.symm (Γ ⊢ arg : t'))
    | .Box t' => sorry
    | .Unbox t' => sorry
    | .IsVariant dt var => sorry
    | .Proj field => sorry

  | .Unary op arg =>
    match op with
    | .Not =>
      let res_bool :=
        cast_typ_interp
          (ty_not_inv arg hty).1
          (exp_rep Γ tenv venv t arg (ty_not_inv arg hty).2)
        |> cast interp_bool
      cast_typ_interp (ty_not_inv arg hty).1.symm (cast interp_bool.symm ¬res_bool)

    | .FloatToBits =>
      match arg with
      | _ => sorry
      -- match (ty_floatToBits_inv arg hty) with
      -- | Or.inl hl => sorry
      -- | Or.inr hr => sorry
    | .BitNot (width : Option Nat) => sorry
    | .Clip (range : IntRange) (truncate : Bool) => sorry


  | .Binary op arg₁ arg₂ =>
    match op with
    | .And =>
      let l_bool :=
        cast_typ_interp
          (ty_and_inv arg₁ arg₂ hty).1
          (exp_rep Γ tenv venv t arg₁ (ty_and_inv arg₁ arg₂ hty).2.1)
        |> cast interp_bool
      let r_bool :=
        cast_typ_interp
          (ty_and_inv arg₁ arg₂ hty).1
          (exp_rep Γ tenv venv t arg₂ (ty_and_inv arg₁ arg₂ hty).2.2)
        |> cast interp_bool
      cast_typ_interp (ty_and_inv arg₁ arg₂ hty).1.symm (cast interp_bool.symm (l_bool ∧ r_bool))

    | .Or =>
      let l_bool :=
        cast_typ_interp
          (ty_or_inv arg₁ arg₂ hty).1
          (exp_rep Γ tenv venv t arg₁ (ty_or_inv arg₁ arg₂ hty).2.1)
        |> cast interp_bool
      let r_bool :=
        cast_typ_interp
          (ty_or_inv arg₁ arg₂ hty).1
          (exp_rep Γ tenv venv t arg₂ (ty_or_inv arg₁ arg₂ hty).2.2)
        |> cast interp_bool
      cast_typ_interp (ty_or_inv arg₁ arg₂ hty).1.symm (cast interp_bool.symm (l_bool ∨ r_bool))

    | .Xor =>
      let l_bool :=
        cast_typ_interp
          (ty_xor_inv arg₁ arg₂ hty).1
          (exp_rep Γ tenv venv t arg₁ (ty_xor_inv arg₁ arg₂ hty).2.1)
        |> cast interp_bool
      let r_bool :=
        cast_typ_interp
          (ty_xor_inv arg₁ arg₂ hty).1
          (exp_rep Γ tenv venv t arg₂ (ty_xor_inv arg₁ arg₂ hty).2.2)
        |> cast interp_bool
      cast_typ_interp (ty_xor_inv arg₁ arg₂ hty).1.symm (cast interp_bool.symm (Xor' l_bool r_bool))

    | .Implies =>
      let l_bool :=
        cast_typ_interp
          (ty_implies_inv arg₁ arg₂ hty).1
          (exp_rep Γ tenv venv t arg₁ (ty_implies_inv arg₁ arg₂ hty).2.1)
        |> cast interp_bool
      let r_bool :=
        cast_typ_interp
          (ty_implies_inv arg₁ arg₂ hty).1
          (exp_rep Γ tenv venv t arg₂ (ty_implies_inv arg₁ arg₂ hty).2.2)
        |> cast interp_bool
      cast_typ_interp (ty_implies_inv arg₁ arg₂ hty).1.symm (cast interp_bool.symm (l_bool → r_bool))

    | .Inequality (op : InequalityOp) =>
      let l_int :=
        exp_rep Γ tenv venv (Typ.Int .Int) arg₁ (ty_ineq_inv arg₁ arg₂ op hty).2.1
        |> cast interp_int
      let r_int :=
        exp_rep Γ tenv venv (Typ.Int .Int) arg₂ (ty_ineq_inv arg₁ arg₂ op hty).2.2
        |> cast interp_int
      let res :=
        match op with
        | .Le => l_int <= r_int
        | .Ge => l_int >= r_int
        | .Lt => l_int < r_int
        | .Gt => l_int > r_int
      cast_typ_interp (ty_ineq_inv arg₁ arg₂ op hty).1.symm (cast interp_bool.symm res)

    | .Ne =>
      let A: Typ := Classical.choose (ty_ne_inv arg₁ arg₂ hty).2
      let hty₁ : Γ ⊢ arg₁ : A := (Classical.choose_spec (ty_ne_inv arg₁ arg₂ hty).2).1
      let hty₂ : Γ ⊢ arg₂ : A := (Classical.choose_spec (ty_ne_inv arg₁ arg₂ hty).2).2
      let rep₁ := exp_rep Γ tenv venv A arg₁ hty₁
      let rep₂ := exp_rep Γ tenv venv A arg₂ hty₂
      cast_typ_interp (ty_ne_inv arg₁ arg₂ hty).1.symm (cast interp_bool.symm (rep₁ = rep₂))

    | .Eq m =>
      let A: Typ := Classical.choose (ty_eq_inv arg₁ arg₂ m hty).2
      let hty₁ : Γ ⊢ arg₁ : A := (Classical.choose_spec (ty_eq_inv arg₁ arg₂ m hty).2).1
      let hty₂ : Γ ⊢ arg₂ : A := (Classical.choose_spec (ty_eq_inv arg₁ arg₂ m hty).2).2
      let rep₁ := exp_rep Γ tenv venv A arg₁ hty₁
      let rep₂ := exp_rep Γ tenv venv A arg₂ hty₂
      cast_typ_interp (ty_eq_inv arg₁ arg₂ m hty).1.symm (cast interp_bool.symm (rep₁ = rep₂))

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
          let l_int :=
            exp_rep Γ tenv venv (Typ.Int .Int) arg₁ (ty_add_inv arg₁ arg₂ (.Int .Int) hty).2.1
            |> cast interp_int
          let r_int :=
            exp_rep Γ tenv venv (Typ.Int .Int) arg₂ (ty_add_inv arg₁ arg₂ (.Int .Int) hty).2.2
            |> cast interp_int
          cast interp_int.symm (l_int + r_int)
        | .Int .Nat =>
          let l_nat :=
            exp_rep Γ tenv venv (Typ.Int .Nat) arg₁ (ty_add_inv arg₁ arg₂ (.Int .Nat) hty).2.1
            |> cast interp_nat
          let r_nat :=
            exp_rep Γ tenv venv (Typ.Int .Nat) arg₂ (ty_add_inv arg₁ arg₂ (.Int .Nat) hty).2.2
            |> cast interp_nat
          cast interp_nat.symm (l_nat + r_nat)
        | _ => sorry
      | _ => sorry
    | .Bitwise (op : BitwiseOp) (mode : Mode) => sorry

  | .If c b₁ b₂ => sorry
  | .Let (tys : List Typ) (es : List Exp) (body : Exp) => sorry
  | .Quant (q : Quant) (var : Typ) (body : Exp) => sorry
  | .TupleCtor (size : Nat) (data : List Exp) => sorry


  | .Call (fn : CallFun) (typs : List Typ) (exps : List Exp) (ret : Typ) => sorry
  | .CallLambda (lam : Exp) (arg : Exp) => sorry
  | .StructCtor (dt : Ident) (fields : List (String × Exp)) => sorry
  | .Lambda (var : Typ) (exp : Exp) => sorry

termination_by sizeOf e
