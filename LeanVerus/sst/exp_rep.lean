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
    | .Box t' => sorry
    | .Unbox t' => sorry
    | .IsVariant dt var => sorry
    | .Proj field => sorry
    | .HasType t' =>
      -- have : Γ ⊢ .Unaryr (.HasType t') arg : t := by sorry
      have := ty_hasType_inv arg t' t hty
      --decide this.2

      --cast_typ_interp (ty_hasType_inv e t' hty).symm interp_hasType
      sorry
  | .Unary op arg => sorry



  | _ => sorry
termination_by sizeOf e
