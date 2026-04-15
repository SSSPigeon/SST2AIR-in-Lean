import LeanVerus.Sst.Typ
import LeanVerus.Sst.Typing
import LeanVerus.Sst.Exp
import LeanVerus.Air_ast.«Air-ast»
import LeanVerus.Trans.Axioms

open sst typing MSFirstOrder MSLanguage AirSorts airFunc BoundedFormula

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

abbrev TransFormula := air_ast.Formula TransVarFam

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

-- ⊤
abbrev truth: TransFormula := imp falsum falsum
-- Boolean connectives derived from falsum and imp
-- ¬p  ≡  p → ⊥
abbrev bnot (p : TransFormula) : TransFormula := imp p falsum
-- p ∧ q  ≡  ¬(p → ¬q)  ≡  (p → (q → ⊥)) → ⊥
abbrev band (p q : TransFormula) : TransFormula := bnot (imp p (bnot q))
-- p ∨ q  ≡  ¬p → q
abbrev bor (p q : TransFormula) : TransFormula := imp (bnot p) q
-- p ↔ q  ≡  (p → q) ∧ (q → p)
abbrev biff (p q : TransFormula) : TransFormula := band (imp p q) (imp q p)
-- ∃x:s, p(x)  ≡  ¬∀x:s, ¬p(x)
-- abbrev bexists {s : AirSorts} (f : BoundedFormula air_ast TransVarFam [s]) : TransFormula :=
--   bnot (all (imp f falsum))

def trans_exp {Γ: context} (e : sst.Exp) (t : sst.Typ) (hty : Γ ⊢ e : t )(aenv : TransAxioms) : (TransTerm ⊕ TransFormula) × TransAxioms :=
-- air_ast.Term TransVarFam (trans_typ t)
  match e with
  | .Const c =>
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L749
    match c with
    | .Bool b =>
      if b then ⟨.inr truth, aenv⟩ else ⟨.inr falsum, aenv⟩

      --⟨.inl ⟨Bool, constTerm (if b then airFunc.True else airFunc.False)⟩, aenv⟩
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L296
    | .Int i =>
      if i ≥ 0 then
        ⟨.inl ⟨Int, constTerm (airFunc.Nat i.repr)⟩, aenv⟩
      else
        ⟨.inl ⟨Int, binFuncTerm (airFunc.Sub 2) (constTerm (airFunc.Nat "0"))
                                    (constTerm (airFunc.Nat (-i).repr))⟩, aenv⟩
    | .Char c =>
      ⟨.inl ⟨Int, constTerm (airFunc.Nat (toString c.val))⟩, aenv⟩
    | .Float32 f =>
      ⟨.inl ⟨Int, constTerm (airFunc.Nat (toString f))⟩, aenv⟩
    | .Float64 f =>
      ⟨.inl ⟨Int, constTerm (airFunc.Nat (toString f))⟩, aenv⟩
    | .StrSlice _ => sorry

  | .Var idx =>
    match t with
    | .TypParam p =>
      -- v has sort Poly; add sentence (has_type (VarConst idx) (TypParamConst p))
      -- Sentences must be ground, so we use VarConst idx rather than Term.var Poly idx.
      -- The soundness proof connects VarConst idx to the actual variable assignment.
      let v_term : air_ast.Term TransVarFam Poly := Term.var Poly idx
      let ht_axiom : air_ast.Sentence :=
        equal
          (Term.func [Poly, TYPE] Bool airFunc.HAS_TYPE
            fun i => match i with
              | ⟨0, _⟩     => Term.func [] Poly (airFunc.VarConst idx) (fun j => Fin.elim0 j)
              | ⟨1, _⟩     => Term.func [] TYPE (airFunc.TypParamConst p) (fun j => Fin.elim0 j)
              | ⟨_ + 2, h⟩ => absurd h (by simp))
          (Term.func [] AirSorts.Bool airFunc.True (fun j => Fin.elim0 j))
      ⟨.inl ⟨Poly, v_term⟩, aenv ∪ {ht_axiom}⟩
    | _ =>
      -- For all concrete types the sort is determined by trans_typ
      ⟨.inl ⟨trans_typ t, Term.var (trans_typ t) idx⟩, aenv⟩
  | .Binary op e₁ e₂ =>
    -- Thread the axiom environment through both sub-expressions.
    match op with
    | .Arith op' =>
      match op' with
      -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L1253
      | .Add =>
        match t with
        | .Int .Int =>
          have ⟨h₁, h₂⟩ := add_same_type e₁ e₂ (.Int .Int) hty
          let ⟨t₁, aenv₁⟩ := trans_exp e₁ (.Int .Int) h₁ aenv
          let ⟨t₂, aenv₂⟩ := trans_exp e₂ (.Int .Int) h₂ aenv₁
          match t₁, t₂ with
          | .inl ⟨AirSorts.Int, tm₁⟩, .inl ⟨AirSorts.Int, tm₂⟩ =>
            ⟨.inl ⟨Int, binFuncTerm airFunc.ADD tm₁ tm₂⟩, aenv₂⟩
          | _, _ => unreachable!
        | .Int .Nat =>
          have ⟨h₁, h₂⟩ := add_same_type e₁ e₂ (.Int .Nat) hty
          let ⟨t₁, aenv₁⟩ := trans_exp e₁ (.Int .Nat) h₁ aenv
          let ⟨t₂, aenv₂⟩ := trans_exp e₂ (.Int .Nat) h₂ aenv₁
          match t₁, t₂ with
          | .inl ⟨AirSorts.Int, tm₁⟩, .inl ⟨AirSorts.Int, tm₂⟩ =>
            ⟨.inl ⟨Int, binFuncTerm airFunc.ADD tm₁ tm₂⟩, aenv₂⟩
          | _, _ => sorry
        | .Int (.U _) | .Int (.I _) | .Int .Char | .Int .USize | .Int .ISize
        | .Float _ | .Array _ | .StrSlice | .TypParam _
        | .SpecFn _ _ | .Decorated _ _ | .Tuple _ _ | .Struct _ _
        | .Enum _ _ | .AnonymousClosure _ _ | .FnDef _ _ | .Air _ => nomatch hty
      | _ => sorry
    | .And =>
      have ⟨h₁, h₂⟩ := and_same_type e₁ e₂ t hty
      let ⟨t₁, aenv₁⟩ := trans_exp e₁ t h₁ aenv
      let ⟨t₂, aenv₂⟩ := trans_exp e₂ t h₂ aenv₁
      match t₁, t₂ with
      | .inl ⟨AirSorts.Bool, tm₁⟩, .inl ⟨AirSorts.Bool, tm₂⟩ =>
        ⟨.inl ⟨Bool, binFuncTerm (airFunc.And 2) tm₁ tm₂⟩, aenv₂⟩
      | _, _ => sorry
    -- https://github.com/verus-lang/verus/blob/main/source/vir/src/sst_to_air.rs#L1311
    | .Index _ => sorry
    | _ => sorry

  | _ => sorry



-- /-- The AIR sort of a translated expression equals `trans_typ` of its SST type. -/
-- def trans_exp_sort {Γ : context} (e : sst.Exp) (t : sst.Typ) (hty : Γ ⊢ e : t) (aenv : TransAxioms) : (trans_exp e t hty aenv).1 = trans_typ t := by sorry
