import Mathlib.Tactic.Convert
import LeanVerus.My_sst

/-- Append an element to a substitution or a renaming.
```
Δ ⊢ σ : Γ  Γ ⊢ A  Δ ⊢ t : A[σ]
------------------------------
Δ ⊢ σ.t : Γ.A
``` -/
def snoc.{u} {X : Sort u} (σ : Nat → X) (x : X) : Nat → X
  | 0   => x
  | n+1 => σ n

@[simp]
theorem snoc_zero {X} (σ : Nat → X) (x : X) : snoc σ x 0 = x := rfl

@[simp]
theorem snoc_succ {X} (σ : Nat → X) (x : X) (n) : snoc σ x (n + 1) = σ n := rfl

/-- Lift a renaming under a binder. See `up`. -/
def upr (ξ : Nat → Nat) (n: Nat): Nat → Nat :=
  match n with
  | 0 => ξ
  -- snoc (fun i => ξ i + 1) 0
  | .succ n => snoc (fun i => (upr ξ n) i + 1) 0



@[simp]
theorem upr_id (n: Nat) : upr id n = id := by
  induction n with
  | zero => rfl
  | succ n ih => ext ⟨⟩ <;> simp [upr, ih]

@[simp]
theorem upr_one (ξ : Nat → Nat) : upr ξ 1 = snoc (fun i => ξ i + 1) 0 := by
  simp only [upr]

namespace VerusLean.Exp


def rename_exp (ξ : Nat → Nat) : Exp → Exp
  | .Const c => .Const c
  | .Var x => .Var (ξ x)
  | .Call fn type exps => .Call fn type (exps.map (rename_exp ξ))
  | .CallLambda lam args =>
    .CallLambda (rename_exp ξ lam) (args.map (rename_exp ξ))
  | .StructCtor dt fields =>
    .StructCtor dt (fields.attach.map
      fun ⟨(name, e), h⟩ =>
        have : sizeOf e < sizeOf fields := by
          have := List.sizeOf_lt_of_mem h
          grind [Prod.mk.sizeOf_spec]
        (name, rename_exp ξ e))
    -- match fields with
    -- | [] => .StructCtor dt []
    -- | (name, e) :: rest =>
      -- let renamed_e := rename_exp ξ e
      -- -- To make the definition terminate, we must use dt, instead of some new name here.
      -- -- I'm not sure whether this will cause problems later.
      -- -- TODO: check this.
      -- let renamed_rest := rename_exp ξ (.StructCtor dt rest)
      -- let renamed_fields :=
      --   match renamed_rest with
      --   | .StructCtor _ rest_fields => (name, renamed_e) :: rest_fields
      --   | _ => [(name, renamed_e)]  -- This case should not happen
      -- .StructCtor dt renamed_fields
  | .TupleCtor size data => .TupleCtor size (data.map (rename_exp ξ))
  | .Unary op arg => .Unary op (rename_exp ξ arg)
  | .Unaryr op arg => .Unaryr op (rename_exp ξ arg)
  | .Binary op arg₁ arg₂ => .Binary op (rename_exp ξ arg₁) (rename_exp ξ arg₂)
  | .If cond branch₁ branch₂ => .If (rename_exp ξ cond) (rename_exp ξ branch₁) (rename_exp ξ branch₂)
  | .Let tys es exp=>
    let renamed_exp := rename_exp (upr ξ es.length) exp
    let renamed_es := es.map (rename_exp ξ)
    .Let tys renamed_es renamed_exp --rename_exp (upr ξ args.length) body
  | .Quant q var exp=>
    let renamed_exp := rename_exp (upr ξ 1) exp
    .Quant q var renamed_exp
  | .Lambda ty exp=>
    let renamed_exp := rename_exp (upr ξ 1) exp
    .Lambda ty renamed_exp
  | .ArrayLiteral elems => .ArrayLiteral (elems.map (rename_exp ξ))


/-! ## Substitution -/

/-- Lift a substitution under a binder.
```
Δ ⊢ σ : Γ  Γ ⊢ A
------------------------
Δ.A[σ] ⊢ (↑≫σ).v₀ : Γ.A
```

Warning: don't unfold this definition! Use `up_eq_snoc` instead. -/
--@[irreducible]
def up (σ : Nat → Exp) (n: Nat): Nat → Exp :=
  match n with
  | 0 => σ -- This shouldn't happen
  --| 1 => snoc (rename_exp Nat.succ ∘ σ) (.Var 0)
  | .succ n => snoc (rename_exp Nat.succ ∘ (up σ n)) (.Var 0)

/-- TODO: generalize 1 to n-/
@[simp]
theorem up_var (n: Nat): up Exp.Var n = Exp.Var:= by
  induction n with
  | zero => rfl
  | succ n ih => ext ⟨⟩ <;> simp [up, snoc, ih, rename_exp]

def subst_exp (σ : Nat → Exp) : Exp → Exp
  | .Const c => .Const c
  | .Var x => σ x
  | .Call fn type exps => .Call fn type (exps.map (subst_exp σ))
  | .CallLambda body args =>
    .CallLambda (subst_exp σ body) (args.map (subst_exp σ))
  | .StructCtor dt fields =>
    .StructCtor dt (fields.attach.map
      fun ⟨(name, e), h⟩ =>
        have : sizeOf e < sizeOf fields := by
          have := List.sizeOf_lt_of_mem h
          grind [Prod.mk.sizeOf_spec]
        (name, subst_exp σ e))
  | .TupleCtor size data => .TupleCtor size (data.map (subst_exp σ))
  | .Unary op arg => .Unary op (subst_exp σ arg)
  | .Unaryr op arg => .Unaryr op (subst_exp σ arg)
  | .Binary op arg₁ arg₂ => .Binary op (subst_exp σ arg₁) (subst_exp σ arg₂)
  | .If cond branch₁ branch₂ => .If (subst_exp σ cond) (subst_exp σ branch₁) (subst_exp σ branch₂)
  | .Let ty es exp =>
      let renamed_exp := subst_exp (up σ es.length) exp
      let renamed_e := es.map (subst_exp σ)
      .Let ty renamed_e renamed_exp
  | .Quant q var exp =>
    let renamed_exp := subst_exp (up σ 1) exp
    .Quant q var renamed_exp
  | .Lambda vars exp =>
    let renamed_exp := subst_exp (up σ 1) exp
    .Lambda vars renamed_exp
  | .ArrayLiteral elems => .ArrayLiteral (elems.map (subst_exp σ))
termination_by e => sizeOf e

@[simp]
theorem map_id''_mem {f : α → α} (l : List α) (h : ∀ x ∈ l, f x = x)  : List.map f l = l := by
  induction l
  all_goals grind

@[simp]
theorem subst_var : subst_exp Exp.Var = id := by
  ext t; induction t
  all_goals try
    simp only [subst_exp, List.map_attach_eq_pmap, List.pmap_eq_map] <;>
    grind [subst_exp, up_var, List.map_attach_eq_pmap, List.pmap_eq_map, map_id''_mem]
  -- this works
  --   simp only [subst_exp, List.map_attach_eq_pmap, List.pmap_eq_map];
  --   grind [subst_exp, up_var, List.map_attach_eq_pmap, List.pmap_eq_map, map_id''_mem]
  -- this doesn't work
  --  grind [subst_exp, up_var, List.map_attach_eq_pmap, List.pmap_eq_map, map_id''_mem]

  -- let motive₁ : Exp → Prop := fun e => subst_exp Exp.Var e = e
  -- let motive₂ : List Exp → Prop := fun es => es.map (subst_exp Exp.Var) = es
  -- let motive₃ : List (String × Exp) → Prop :=
  --   fun fs => fs.map (fun (p : String × Exp) => (p.fst, subst_exp Exp.Var p.snd)) = fs
  -- let motive₄ : (String × Exp) → Prop := fun p => (p.fst, subst_exp Exp.Var p.snd) = p
  -- -- Prove the needed helper lemmas for lists/pairs
  -- have nil₂ : motive₂ [] := rfl
  -- have cons₂ : ∀ (head : Exp) (tail : List Exp),
  --   motive₁ head → motive₂ tail → motive₂ (head :: tail) := by
  --   intros head tail h₁ h₂; unfold motive₁ at h₁; simp [motive₂, h₂, h₁]
  -- have nil₃ : motive₃ [] := rfl
  -- have cons₃ : ∀ (head : String × Exp) (tail : List (String × Exp)),
  --   motive₄ head → motive₃ tail → motive₃ (head :: tail) := by
  --   intros head tail h₁ h₂; unfold motive₄ at h₁; simp [motive₃, h₂, h₁]
  -- have pair₄ : ∀ (s : String) (e: Exp), motive₁ e → motive₄ (s, e) := by
  --   intros s e h; unfold motive₄; simp [motive₁, h]
  -- ext t; dsimp
  -- apply @Exp.recOn (motive_1 := motive₁) (motive_2 := motive₂) (motive_3 := motive₃) (motive_4 := motive₄)
  -- all_goals grind [subst_exp, up_var, List.map_attach_eq_pmap, List.pmap_eq_map]


@[simp]
theorem subst_snoc_zero (σ : Nat → Exp) (t : Exp) : subst_exp (snoc σ t) (.Var 0) = t := by
  simp [subst_exp, snoc]

/-- Turn a renaming into a substitution. -/
def ofRen (ξ : Nat → Nat) : Nat → Exp :=
  fun i => Exp.Var (ξ i)

@[simp]
theorem ofRen_id : ofRen id = Exp.Var := rfl

theorem ofRen_upr (n ξ) : ofRen (upr ξ n) = up (ofRen ξ) n := by
  induction n generalizing ξ with
  | zero => rfl
  | succ n ih =>
    ext ⟨⟩  --simp [ofRen, upr, up, snoc]; sorry
    . simp [ofRen, upr, up, snoc]
    . rename_i k
      conv => lhs; simp [ofRen, upr, up, snoc]
      rw[← ofRen_id];
      let ξ' := fun i => upr ξ n i + 1
      have ih := ih ξ';
      conv => lhs; unfold ofRen; dsimp [upr, up, snoc];
      unfold up snoc;
      have ih_at_k := congrArg (fun f => f k) ih
      simp at ih_at_k
      unfold ofRen at ih_at_k; simp
      rename_i ih'
      have : rename_exp Nat.succ (up (ofRen ξ) n k) = rename_exp Nat.succ (ofRen (upr ξ n) k) := by simp[ih']
      rw[this]; simp[ofRen, rename_exp]



#check List.mem_map
#check List.ext_getElem
#check @List.getElem_of_eq
theorem rename_eq_subst_ofRen (ξ : Nat → Nat) : rename_exp ξ = subst_exp (ofRen ξ) := by
  ext t; induction t generalizing ξ
  all_goals try
    simp only [ofRen, rename_exp, subst_exp, List.map_attach_eq_pmap, List.pmap_eq_map, Call.injEq, CallLambda.injEq, TupleCtor.injEq, ArrayLiteral.injEq, List.map_inj_left, true_and] <;>
    grind [ofRen,rename_exp, subst_exp, up_var, List.map_attach_eq_pmap, List.pmap_eq_map, map_id''_mem]
  . rename_i dt fields h
    simp [rename_exp, subst_exp]
    intro a b h_mem
    exact h ⟨a, b⟩ h_mem ξ
  . simp [rename_exp, subst_exp]
    rename_i ty e exp he hexp
    constructor
    . intro a h_mem; exact he a h_mem ξ  --exact he
    . rw[← ofRen_upr e.length ξ]
      exact hexp (upr ξ e.length)
  . simp [rename_exp, subst_exp]
    rename_i _ _ _ h
    rw[← ofRen_upr 1 ξ, ← upr_one]
    exact h (upr ξ 1)
  . simp [rename_exp, upr_one, subst_exp]
    rename_i _ _ h
    rw[← ofRen_upr 1 ξ, ← upr_one]
    exact h (upr ξ 1)



  -- let motive₁ : Exp → Prop := fun e => rename_exp ξ e = subst_exp (ofRen ξ) e
  -- let motive₂ : List Exp → Prop := fun es => es.map (rename_exp ξ) = es.map (subst_exp (ofRen ξ))
  -- let motive₃ : List (String × Exp) → Prop :=
  --   fun fs => fs.map (fun (p : String × Exp) => (p.fst, rename_exp ξ p.snd)) = fs.map (fun (p : String × Exp) => (p.fst, subst_exp (ofRen ξ) p.snd))
  -- let motive₄ : (String × Exp) → Prop := fun p => (p.fst, subst_exp Exp.Var p.snd) = (p.fst, rename_exp ξ p.snd)
  -- -- Prove the needed helper lemmas for lists/pairs
  -- have nil₂ : motive₂ [] := rfl
  -- have cons₂ : ∀ (head : Exp) (tail : List Exp),
  --   motive₁ head → motive₂ tail → motive₂ (head :: tail) := by
  --   intros head tail h₁ h₂; unfold motive₁ at h₁; unfold motive₂ at h₂; simp [motive₂, h₁]
  --   intro a h; have h_idx := List.get_of_mem h
  --   rcases h_idx with ⟨idx, h_eq⟩; simp [← h_eq]
  --   have := @List.getElem_of_eq _ (List.map (rename_exp ξ) tail) (List.map (subst_exp (ofRen ξ)) tail) h₂ ↑idx
  --   simp at this; exact this
  -- have nil₃ : motive₃ [] := rfl
  -- have cons₃ : ∀ (head : String × Exp) (tail : List (String × Exp)),
  --   motive₄ head → motive₃ tail → motive₃ (head :: tail) := by
  --   intros head tail h₁ h₂; unfold motive₄ at h₁; simp [motive₃]; intro a b h
  --   rcases h with ⟨h_head, h_tail⟩
  --   . simp at h₁
  --   . sorry
  -- have pair₄ : ∀ (s : String) (e: Exp), motive₁ e → motive₄ (s, e) := by
  --   intros s e h; unfold motive₄; simp [motive₁, h]
  -- ext t
  -- apply @Exp.recOn


/-- Compose two substitutions.
```
Θ ⊢ σ : Δ  Δ ⊢ τ : Γ
--------------------
Θ ⊢ σ≫τ : Γ
``` -/
def comp (σ τ : Nat → Exp) : Nat → Exp :=
  subst_exp σ ∘ τ

@[simp]
theorem var_comp (σ : Nat → Exp) : comp Exp.Var σ = σ := by
  ext i; simp [comp]

@[simp]
theorem comp_var (σ : Nat → Exp) : comp σ Exp.Var = σ := by
  ext i; simp [comp, subst_exp]

/-- TODO: generalize 1 to n-/
theorem up_comp_ren_sb (n: Nat) (ξ : Nat → Nat) (σ : Nat → Exp) :
    up (σ ∘ ξ) n = up σ n ∘ upr ξ n:= by
  induction n with
  | zero => rfl
  | succ n ih => sorry --ext ⟨⟩ <;> (unfold up; dsimp [snoc, upr])

theorem rename_subst (σ ξ) (t : Exp) : (t.rename_exp ξ).subst_exp σ = t.subst_exp (σ ∘ ξ) := by
  induction t generalizing σ ξ
  all_goals sorry
  --all_goals grind [rename_exp, subst_exp, up_comp_ren_sb]


/-- TODO: generalize 1 to n-/
theorem up_comp_sb_ren (n: Nat) (σ : Nat → Exp) (ξ : Nat → Nat) :
    up (rename_exp ξ ∘ σ) n = rename_exp (upr ξ 1) ∘ up σ n:= by
  ext ⟨⟩ <;> (unfold up; dsimp [snoc, rename_exp, upr])
  sorry
  sorry
  -- conv => lhs; rw [rename_eq_subst_ofRen, rename_subst]
  -- conv => rhs; rw [rename_eq_subst_ofRen, rename_subst]
  -- rfl

theorem subst_rename (ξ σ) (t : Exp) :
    (t.subst_exp σ).rename_exp ξ = t.subst_exp (rename_exp ξ ∘ σ) := by
  induction t generalizing ξ σ
  all_goals sorry
  --all_goals grind [subst_exp, rename_exp, up_comp_sb_ren]

theorem up_comp (n: Nat) (σ τ : Nat → Exp) :
    up (comp σ τ) n = comp (up σ n) (up τ n) := by
  induction n with
  | zero => rfl
  | succ n ih => sorry


theorem subst_subst (σ τ : Nat → Exp) (t : Exp) :
    (t.subst_exp τ).subst_exp σ = t.subst_exp (comp σ τ) := by
  induction t generalizing σ τ
  all_goals sorry --grind [subst_exp, up_comp]

theorem comp_assoc (σ τ ρ : Nat → Exp) : comp σ (comp τ ρ) = comp (comp σ τ) ρ := by
  ext i
  conv => rhs; enter [0]; unfold comp
  dsimp; rw [← subst_subst]; dsimp [comp]

theorem comp_snoc (σ τ : Nat → Exp) (t : Exp) :
    comp σ (snoc τ t) = snoc (comp σ τ) (t.subst_exp σ) := by
  ext ⟨⟩ <;> dsimp [comp, snoc]

/-- The weakening substitution.
```
Γ ⊢ A
------------
Γ.A ⊢ ↑ : Γ
``` -/
def wk : Nat → Exp :=
  ofRen Nat.succ

@[simp]
theorem ofRen_succ : ofRen Nat.succ = wk := rfl

theorem up1_eq_snoc (σ : Nat → Exp) : up σ 1 = snoc (comp wk σ) (.Var 0) := by
  ext i; unfold up comp; congr 1; ext j
  rw [rename_eq_subst_ofRen]; congr 1

@[simp]
theorem snoc_comp_wk (σ : Nat → Exp) (t) : comp (snoc σ t) wk = σ := by
  ext ⟨⟩ <;> simp [comp, snoc, wk, ofRen, subst_exp, -ofRen_succ]

@[simp]
theorem snoc_wk_zero : snoc wk (.Var 0) = .Var := by
  ext ⟨⟩ <;> dsimp [snoc, wk, ofRen, -ofRen_succ]

theorem snoc_comp_wk_succ (σ : Nat → Exp) (n) :
    snoc (comp wk σ) (.Var (n + 1)) = comp wk (snoc σ (.Var n)) := by
  ext ⟨⟩ <;> simp [comp, snoc, wk, -ofRen_succ, subst_exp, ofRen]

/-- A substitution that instantiates one binder.
```
Γ ⊢ t : A
--------------
Γ ⊢ id.t : Γ.A
``` -/
def toSb (t : Exp) : Nat → Exp :=
  snoc Exp.Var t

/-! ## Decision procedure -/

theorem snoc_comp_wk_zero_subst (σ : Nat → Exp) :
    snoc (comp σ Exp.wk) ((Exp.Var 0).subst_exp σ) = σ := by
  ext ⟨⟩ <;> simp [snoc, comp, subst_exp, wk, ofRen, -ofRen_succ]

theorem ofRen_comp (ξ₁ ξ₂ : Nat → Nat): ofRen (ξ₁ ∘ ξ₂) = comp (ofRen ξ₁) (ofRen ξ₂) := by
  simp [comp]; grind [ofRen, subst_exp]

@[simp]
theorem wk_app (n) : wk n = .Var (n + 1) := by
  rw [wk, ofRen]

-- register_simp_attr autosubst

-- Rules from Fig. 1 in the paper.
attribute [autosubst low]
  subst_exp
attribute [autosubst]
  subst_snoc_zero
  snoc_comp_wk
  subst_var
  snoc_comp_wk_zero_subst
  comp_var
  var_comp
  comp_assoc
  comp_snoc
  subst_subst
  snoc_wk_zero

-- Rules that are not in the paper,
-- but allow us to prove more stuff.
attribute [autosubst]
  snoc_zero
  snoc_succ
  snoc_comp_wk_succ
  wk_app

-- Rules to unfold abbreviations.
attribute [autosubst high]
  up1_eq_snoc
  toSb

-- More rules to deal with renamings. These are ad-hoc, not from paper.
attribute [autosubst low]
  rename_exp
attribute [autosubst]
  rename_eq_subst_ofRen
  ofRen_id
  ofRen_comp
  ofRen_succ
  ofRen_upr

-- Cleanup rules.
attribute [autosubst]
  id_eq

/-- Decides equality of substitutions applied to expressions. -/
macro "autosubst" : tactic => `(tactic| simp only [autosubst])

/-- Use a term modulo `autosubst` conversion. -/
macro "autosubst% " t:term : term => `(by convert ($t) using 1 <;> autosubst)

/-! ## Closed expressions -/

/-- The expression uses only indices up to `k`. -/
def isClosed (k : Nat := 0) (e: Exp): Bool:=
  match e with
  | Const _ => true
  | Var i => i < k
  | Call fn typs exps =>
    List.foldl (fun acc exp => acc && isClosed k exp) true exps
  | CallLambda body args =>
    isClosed k body &&
    List.foldl (fun acc exp => acc && isClosed k exp) true args
  | StructCtor dt fields =>
    fields.attach.all (fun ⟨(name, e), h⟩ =>
      have : sizeOf e < sizeOf fields := by
        have := List.sizeOf_lt_of_mem h
        grind [Prod.mk.sizeOf_spec]
      isClosed k e)
  | TupleCtor _ data => List.foldl (fun acc exp => acc && isClosed k exp) true data
  | Unary _ arg => isClosed k arg
  | Unaryr _ arg => isClosed k arg
  | Binary _ arg₁ arg₂ => isClosed k arg₁ && isClosed k arg₂
  | If cond branch₁ branch₂ =>
    isClosed k cond && isClosed k branch₁ && isClosed k branch₂
  | Let ty es exp => List.foldl (fun acc e => acc && isClosed k e) (isClosed (k + es.length) exp) es
  | Quant _ _ exp | Lambda _ exp => isClosed (k + 1) exp
  | ArrayLiteral elems => List.foldl (fun acc exp => acc && isClosed k exp) true elems

/-- The substitution acts via identity on indices strictly below `n`. -/
def SbIsVar (σ : Nat → Exp) (n : Nat) :=
  ∀ ⦃i⦄, i < n → σ i = .Var i


theorem SbIsVar.up {σ : Nat → Exp} {n k} : SbIsVar σ n → SbIsVar (Exp.up σ k) (n + k) := by sorry
  -- rintro σk ⟨⟩ lt
  -- . simp [Exp.up1_eq_snoc]
  -- . have := σk (Nat.succ_lt_succ_iff.mp lt)
  --   simp [Exp.up1_eq_snoc, Exp.comp, this, Exp.subst_exp]

theorem SbIsBvar.zero (σ : Nat → Exp) : SbIsVar σ 0 := nofun

theorem subst_of_isClosed' {e : Exp} {k} {σ : Nat → Exp} :
    e.isClosed k → SbIsVar σ k → e.subst_exp σ = e := by
  intro h hσ
  induction e generalizing k σ
  -- case bvar =>
  --   simp only [isClosed, decide_eq_true_eq] at h
  --   simp [subst, hσ h]
  --all_goals grind [subst_exp, isClosed, → SbIsVar.up]
  all_goals sorry

theorem subst_of_isClosed {e : Exp} (σ : Nat → Exp) : e.isClosed → e.subst_exp σ = e := sorry
  --fun h => e.subst_of_isClosed' h (.zero _)
