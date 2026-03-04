import LeanVerus.Sst.Typ
import LeanVerus.Sst.Typing
import LeanVerus.Sst.Exp
import LeanVerus.Sst.Domain


open sst typing

variable (tenv : typ_env)  (dom_aux : ClosedTyp → Type)

def val_vars tenv (Γ: context) dom_aux :=  (i : Nat) → (_ : i < Γ.length) → typ_interp tenv dom_aux Γ[i] --⊕ ExpError

axiom div_zero_unspecified_value_int : Int → Int

noncomputable def div_totalized_int (x y : Int) : Int :=
  if y = 0 then div_zero_unspecified_value_int x else x / y

axiom div_zero_unspecified_value_nat : Nat → Nat

noncomputable def div_totalized_nat (x y : Nat) : Nat :=
  if y = 0 then div_zero_unspecified_value_nat x else x / y

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
      let A: Typ := Classical.choose (ty_hasType_inv arg t' t hty).2
      let hA := Classical.choose_spec (ty_hasType_inv arg t' t hty).2
      cast_typ_interp (ty_hasType_inv arg t' t hty).1.symm (cast interp_bool.symm ((typ_subst tenv A).1 = (typ_subst tenv t').1))

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

    -- TODO: Ask Wojciech
    | .FloatToBits => sorry

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
      cast_typ_interp (ty_ne_inv arg₁ arg₂ hty).1.symm (cast interp_bool.symm (@Decidable.decide (rep₁ = rep₂) (Classical.propDecidable (rep₁ = rep₂))))

    | .Eq m =>
      let A: Typ := Classical.choose (ty_eq_inv arg₁ arg₂ m hty).2
      let hty₁ : Γ ⊢ arg₁ : A := (Classical.choose_spec (ty_eq_inv arg₁ arg₂ m hty).2).1
      let hty₂ : Γ ⊢ arg₂ : A := (Classical.choose_spec (ty_eq_inv arg₁ arg₂ m hty).2).2
      let rep₁ := exp_rep Γ tenv venv A arg₁ hty₁
      let rep₂ := exp_rep Γ tenv venv A arg₂ hty₂
      cast_typ_interp (ty_eq_inv arg₁ arg₂ m hty).1.symm (cast interp_bool.symm (@Decidable.decide (rep₁ = rep₂) (Classical.propDecidable (rep₁ = rep₂))))

    -- In air : array_index_get
    | .Index (ak : ArrayKind) =>
      match ak with
      | .Array =>
        let htya := (ty_index_array_inv arg₁ arg₂ t hty).1
        let htyi := (ty_index_array_inv arg₁ arg₂ t hty).2
        let rep_a := exp_rep Γ tenv venv (.Array t) arg₁ htya
        let rep_i := exp_rep Γ tenv venv (.Int .Nat) arg₂ htyi
        let rep_a' := cast (interp_array t) rep_a
        let rep_i' := cast interp_nat rep_i
        let res := rep_a'[rep_i']?
        -- TODO
        sorry
      | .Slice => sorry


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

        | .Int (.U _) | .Int (.I _) | .Int .Char | .Int .USize | .Int .ISize
        | .Float _ | .Array _ | .StrSlice | .TypParam _
        | .SpecFn _ _ | .Decorated _ _ | .Tuple _ _ | .Struct _ _
        | .Enum _ _ | .AnonymousClosure _ _ | .FnDef _ _ | .AirNamed _ => nomatch hty


      | .EuclideanDiv =>
        match t with
        | .Int .Int =>
          let l_int :=
            exp_rep Γ tenv venv (Typ.Int .Int) arg₁ (ty_div_inv arg₁ arg₂ (.Int .Int) hty).2.1
            |> cast interp_int
          let r_int :=
            exp_rep Γ tenv venv (Typ.Int .Int) arg₂ (ty_div_inv arg₁ arg₂ (.Int .Int) hty).2.2
            |> cast interp_int
          cast interp_int.symm (div_totalized_int l_int r_int)
        | .Int .Nat =>
          let l_nat :=
            exp_rep Γ tenv venv (Typ.Int .Nat) arg₁ (ty_div_inv arg₁ arg₂ (.Int .Nat) hty).2.1
            |> cast interp_nat
          let r_nat :=
            exp_rep Γ tenv venv (Typ.Int .Nat) arg₂ (ty_div_inv arg₁ arg₂ (.Int .Nat) hty).2.2
            |> cast interp_nat
          cast interp_nat.symm (div_totalized_nat l_nat r_nat)
        | .Int (.U _) | .Int (.I _) | .Int .Char | .Int .USize | .Int .ISize
        | .Float _ | .Array _ | .StrSlice | .TypParam _
        | .SpecFn _ _ | .Decorated _ _ | .Tuple _ _ | .Struct _ _
        | .Enum _ _ | .AnonymousClosure _ _ | .FnDef _ _ | .AirNamed _ => nomatch hty


      | _ => sorry
    | .Bitwise (op : BitwiseOp) (mode : Mode) => sorry

  | .If c b₁ b₂ =>
    let c_res := exp_rep Γ tenv venv Typ._Bool c (ty_if_inv c b₁ b₂ t hty).1
    let b₁_res := exp_rep Γ tenv venv t b₁ (ty_if_inv c b₁ b₂ t hty).2.1
    let b₂_res := exp_rep Γ tenv venv t b₂ (ty_if_inv c b₁ b₂ t hty).2.2
    let c_bool := cast interp_bool c_res
    if c_bool then b₁_res else b₂_res

  | .TupleCtor arg₁ arg₂ =>
    let A: Typ := Classical.choose (ty_tuple_inv arg₁ arg₂ t hty)
    let B := Classical.choose (Classical.choose_spec (ty_tuple_inv arg₁ arg₂ t hty))
    let spec := Classical.choose_spec (Classical.choose_spec (ty_tuple_inv arg₁ arg₂ t hty))
    let hty₁ := spec.2.1
    let hty₂ := spec.2.2
    let rep₁ := exp_rep Γ tenv venv A arg₁ hty₁
    let rep₂ := exp_rep Γ tenv venv B arg₂ hty₂
    cast_typ_interp spec.1.symm (cast (interp_tuple A B).symm (rep₁, rep₂))


  | .Let (tys : List Typ) (es : List Exp) (body : Exp) => sorry
  | .Quant (q : Quant) (var : Typ) (body : Exp) => sorry



  | .Call (fn : CallFun) (typs : List Typ) (exps : List Exp) (ret : Typ) => sorry
  | .CallLambda (lam : Exp) (arg : Exp) => sorry
  | .StructCtor (dt : Ident) (fields : List (String × Exp)) => sorry
  | .Lambda (var : Typ) (exp : Exp) => sorry
