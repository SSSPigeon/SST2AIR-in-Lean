import LeanVerus.Sst.Typ
import LeanVerus.Sst.Typing
import LeanVerus.Sst.Exp
import LeanVerus.Air_ast.«Air-ast»
import LeanVerus.Trans.Axioms

open sst typing MSFirstOrder MSLanguage AirSorts airFunc

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

 Variable family for open terms produced by transf.
    SST variables are de Bruijn indices (Nat), and we treat every sort uniformly. -/
abbrev TransVarFam : AirSorts → Type := fun _ => Nat

example : TransVarFam Poly = _root_.Nat := by simp

/-- A translated term paired with its AIR sort. -/
abbrev TransTerm := Σ s : AirSorts, air_ast.Term TransVarFam s

/-- The set of sentences (axioms) accumulated during translation. -/
abbrev TransAxioms := air_ast.Theory

/-- Apply a nullary airFunc symbol (a constant). -/
def constTerm {t : AirSorts} (f : airFunc [] t) : air_ast.Term TransVarFam t :=
  Term.func [] t f (fun i => Fin.elim0 i)

/-- Apply a binary airFunc symbol to two already-translated terms. -/
def binFuncTerm {s₁ s₂ t : AirSorts}
    (f  : airFunc [s₁, s₂] t)
    (tm₁ : air_ast.Term TransVarFam s₁)
    (tm₂ : air_ast.Term TransVarFam s₂) : air_ast.Term TransVarFam t :=
  Term.func [s₁, s₂] t f
  fun i =>
    match i with
    | ⟨0, _⟩     => tm₁
    | ⟨1, _⟩     => tm₂
    | ⟨_ + 2, h⟩ => absurd h (by simp)

variable (tenv : typ_env) (dom_aux : ClosedTyp → Type)

def trans_typ (t : sst.Typ): AirSorts :=
  match t with
  | ._Bool => Bool
  | .Int _ | .Float _ => Int
  | .Array _ => Fun
  | .TypParam (i : String)  => Poly
  | .SpecFn _ _ => Fun
  | .FnDef _ _ => FnDef
  | .Air (asort : AirSorts) => asort
  -- TODO
  | .Tuple t₁ t₂ => sorry

  | .StrSlice => sorry
  | .Decorated (dec : TypDecoration) (ty : Typ) => sorry
  | .Struct (name : Ident) (fields : List Typ) => sorry
  | .Enum (name : Ident) (params : List Typ) => sorry
  | .AnonymousClosure (typs: List Typ) (typ: Typ) => sorry


-- TODO: add types and typing judgments as arguments
def trans_exp {Γ: context} (e : sst.Exp) (t : sst.Typ) (hty : Γ ⊢ e : t )(aenv : TransAxioms) : TransTerm × TransAxioms :=
  match e with
  | .Const c =>
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L749
    match c with
    | .Bool b =>
      ⟨⟨Bool, constTerm (if b then airFunc.True else airFunc.False)⟩, aenv⟩
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L296
    | .Int i =>
      if i ≥ 0 then
        ⟨⟨Int, constTerm (airFunc.Nat i.repr)⟩, aenv⟩
      else
        ⟨⟨Int, binFuncTerm (airFunc.Sub 2) (constTerm (airFunc.Nat "0"))
                                    (constTerm (airFunc.Nat (-i).repr))⟩, aenv⟩
    | .Char c =>
      ⟨⟨Int, constTerm (airFunc.Nat (toString c.val))⟩, aenv⟩
    | .Float32 f =>
      ⟨⟨Int, constTerm (airFunc.Nat (toString f))⟩, aenv⟩
    | .Float64 f =>
      ⟨⟨Int, constTerm (airFunc.Nat (toString f))⟩, aenv⟩
    | .StrSlice _ => sorry

  -- Variables: sort cannot be determined without tenv
  -- TODO: add the type of e as an argument to transf
  | .Var idx => ⟨⟨Int, Term.var AirSorts.Int idx⟩, aenv⟩

  | .Binary op e₁ e₂ =>
    -- Thread the axiom environment through both sub-expressions.
    let ⟨t₁, aenv₁⟩ := trans_exp e₁ aenv
    let ⟨t₂, aenv₂⟩ := trans_exp e₂ aenv₁
    match op with
    | .Arith op' =>
      match op' with
      -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L1253
      | .Add =>
        match t₁, t₂ with
        | ⟨AirSorts.Int, tm₁⟩, ⟨AirSorts.Int, tm₂⟩ =>
          ⟨⟨Int, binFuncTerm airFunc.ADD tm₁ tm₂⟩, aenv₂⟩
        | _, _ => sorry
      | _ => sorry
    | .And =>
      match t₁, t₂ with
      | ⟨AirSorts.Bool, tm₁⟩, ⟨AirSorts.Bool, tm₂⟩ =>
        ⟨⟨Bool, binFuncTerm (airFunc.And 2) tm₁ tm₂⟩, aenv₂⟩
      | _, _ => sorry
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L1311
    | .Index _ => sorry
    | _ => sorry

  | _ => sorry
