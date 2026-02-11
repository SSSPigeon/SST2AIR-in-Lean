import Mathlib.Tactic.Convert
import LeanVerus.Typ
import LeanVerus.Exp

/-- Append an element to a substitution or a renaming.
```
Δ ⊢ σ : Γ  Γ ⊢ A  Δ ⊢ t : A[σ]
------------------------------
Δ ⊢ σ.t : Γ.A
``` -/
def snoc.{u} {X : Sort u} (σ : Nat → X) (x : X) : Nat → X
  | 0   => x
  | n+1 => σ n

def multi_snoc {X} (σ : Nat → X) (xs : List X) : Nat → X :=
  List.foldl snoc σ xs

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

namespace sst.Exp


def rename_exp (ξ : Nat → Nat) : Exp → Exp
  | .Const c => .Const c
  | .Var x => .Var (ξ x)
  | .Call fn type exps ty=> .Call fn type (exps.map (rename_exp ξ)) ty
  | .CallLambda lam arg =>
    .CallLambda (rename_exp ξ lam) (rename_exp ξ arg)
  | .StructCtor dt fields =>
    .StructCtor dt (fields.attach.map
      fun ⟨(name, e), h⟩ =>
        have : sizeOf e < sizeOf fields := by
          have := List.sizeOf_lt_of_mem h
          grind [Prod.mk.sizeOf_spec]
        (name, rename_exp ξ e))
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

@[simp]
theorem up_var (n: Nat): up Exp.Var n = Exp.Var:= by
  induction n with
  | zero => rfl
  | succ n ih => ext ⟨⟩ <;> simp [up, snoc, ih, rename_exp]

def subst_exp (σ : Nat → Exp) : Exp → Exp
  | .Const c => .Const c
  | .Var x => σ x
  | .Call fn type exps ty=> .Call fn type (exps.map (subst_exp σ)) ty
  | .CallLambda body arg =>
    .CallLambda (subst_exp σ body) (subst_exp σ arg)
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
    ext ⟨⟩ <;> simp [ofRen, upr, up, snoc]
    . rw[← ih]; simp [ofRen, rename_exp]

theorem rename_eq_subst_ofRen (ξ : Nat → Nat) : rename_exp ξ = subst_exp (ofRen ξ) := by
  ext t; --fun_induction rename_exp
  induction t generalizing ξ
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
    . intro a h_mem; exact he a h_mem ξ
    . rw[← ofRen_upr e.length ξ]
      exact hexp (upr ξ e.length)
  all_goals
    simp [rename_exp, subst_exp]
    rw[← ofRen_upr 1 ξ, ← upr_one]
    expose_names
    exact h (upr ξ 1)




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

theorem up_comp_ren_sb (n: Nat) (ξ : Nat → Nat) (σ : Nat → Exp) :
    up (σ ∘ ξ) n = up σ n ∘ upr ξ n:= by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext ⟨⟩ <;> (unfold up; simp [snoc, upr, ih, Function.comp_apply])

theorem rename_subst (σ ξ) (t : Exp) : (t.rename_exp ξ).subst_exp σ = t.subst_exp (σ ∘ ξ) := by
  induction t generalizing σ ξ
  all_goals try simp[rename_exp, subst_exp]<;> grind
  . rename_i dt fields h
    simp [subst_exp, List.map_attach_eq_pmap, List.pmap_eq_map]
    apply Eq.symm
    calc
      StructCtor dt (List.map (fun a ↦ (a.fst, subst_exp (σ ∘ ξ) a.snd)) fields) =
      StructCtor dt (List.map (fun a ↦ (a.fst, subst_exp σ (rename_exp ξ a.snd))) fields) := by
        simp; intro a b h_mem; simp only [h ⟨a, b⟩ h_mem σ ξ]
      _ = subst_exp σ (StructCtor dt (List.map (fun a ↦ (a.fst, rename_exp ξ a.snd)) fields)) := by
        simp [subst_exp, List.map_attach_eq_pmap, List.pmap_eq_map]
      _ = subst_exp σ (rename_exp ξ (StructCtor dt fields)) := by
        simp [rename_exp, List.map_attach_eq_pmap, List.pmap_eq_map]
  . rename_i _ es _ hes he
    simp only [subst_exp]
    rw[up_comp_ren_sb es.length ξ σ, ← he (up σ es.length) (upr ξ es.length)]
    simp [rename_exp, subst_exp]
    intro a hmem; exact hes a hmem σ ξ
  all_goals
    expose_names
    simp only [subst_exp]
    rw[up_comp_ren_sb 1 ξ σ, ← h (up σ 1) (upr ξ 1)]
    simp only [rename_exp, upr_one, subst_exp]

theorem up_comp_sb_ren (n: Nat) (σ : Nat → Exp) (ξ : Nat → Nat) :
    up (rename_exp ξ ∘ σ) n = rename_exp (upr ξ n) ∘ up σ n:= by
  induction n generalizing σ ξ with
  | zero => rfl
  | succ n ih =>
    ext ⟨⟩
    . simp [up, snoc, rename_exp, upr]
    . rename_i k
      conv => lhs; simp [up]
      have hk := congrArg (fun f => f k) (ih σ ξ)
      simp at hk
      rw[hk]; simp[up, snoc, upr]
      conv => lhs; rw [rename_eq_subst_ofRen, rename_subst]
      conv => rhs; rw [rename_eq_subst_ofRen, rename_subst]
      rfl

theorem subst_rename (ξ σ) (t : Exp) :
    (t.subst_exp σ).rename_exp ξ = t.subst_exp (rename_exp ξ ∘ σ) := by
  induction t generalizing ξ σ
  all_goals try simp [subst_exp, rename_exp, up_comp_sb_ren]; grind
  . simp [rename_exp, subst_exp]
  . simp [subst_exp]
  . simp [rename_exp, subst_exp, List.map_attach_eq_pmap, List.pmap_eq_map]
    intros a b hmem
    rename_i _ _ h
    exact h ⟨a, b⟩ hmem ξ σ

theorem up_comp (n: Nat) (σ τ : Nat → Exp) :
    up (comp σ τ) n = comp (up σ n) (up τ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext ⟨⟩
    . unfold up comp; simp [snoc]
    . rename_i k
      simp [up, snoc, comp] at *
      have hk := congrArg (fun f => f k) ih
      simp at hk
      rw[hk]; simp[subst_rename]
      rw[rename_subst (snoc (rename_exp Nat.succ ∘ up σ n) (Exp.Var 0)) Nat.succ (up τ n k)]
      congr



theorem subst_subst (σ τ : Nat → Exp) (t : Exp) :
    (t.subst_exp τ).subst_exp σ = t.subst_exp (comp σ τ) := by
  induction t generalizing σ τ
  all_goals try simp[subst_exp] <;> grind [subst_exp, up_comp]
  . simp only [subst_exp, comp, Function.comp_apply]
  . rename_i _ _ ih
    simp [subst_exp, List.map_attach_eq_pmap, List.pmap_eq_map]
    intro a b h_mem
    exact ih ⟨a, b⟩ h_mem σ τ


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
  | Call fn _ exps ty =>
    exps.attach.all (fun e =>
      have : sizeOf e.val < sizeOf exps := by
         have := List.sizeOf_lt_of_mem e.property
         grind [Prod.mk.sizeOf_spec]
    isClosed k e)
    --List.foldl (fun acc exp => acc && isClosed k exp) true exps
  | CallLambda lam arg => isClosed k lam && isClosed k arg
  | StructCtor dt fields =>
    fields.attach.all (fun ⟨(name, e), h⟩ =>
      have : sizeOf e < sizeOf fields := by
        have := List.sizeOf_lt_of_mem h
        grind [Prod.mk.sizeOf_spec]
      isClosed k e)
  | TupleCtor _ data => --List.foldl (fun acc exp => acc && isClosed k exp) true data
    data.attach.all (fun e =>
      have : sizeOf e.val < sizeOf data := by
         have := List.sizeOf_lt_of_mem e.property
         grind [Prod.mk.sizeOf_spec]
    isClosed k e)
  | Unary _ arg => isClosed k arg
  | Unaryr _ arg => isClosed k arg
  | Binary _ arg₁ arg₂ => isClosed k arg₁ && isClosed k arg₂
  | If cond branch₁ branch₂ =>
    isClosed k cond && isClosed k branch₁ && isClosed k branch₂
  | Let ty es exp => --List.foldl (fun acc e => acc && isClosed k e) (isClosed (k + es.length) exp) es
    (isClosed (k + es.length) exp) &&
    es.attach.all (fun e =>
      have : sizeOf e.val < sizeOf es := by
         have := List.sizeOf_lt_of_mem e.property
         grind [Prod.mk.sizeOf_spec]
    isClosed k e)
  | Quant _ _ exp | Lambda _ exp => isClosed (k + 1) exp
  | ArrayLiteral elems => --List.foldl (fun acc exp => acc && isClosed k exp) true elems
    elems.attach.all (fun e =>
      have : sizeOf e.val < sizeOf elems := by
         have := List.sizeOf_lt_of_mem e.property
         grind [Prod.mk.sizeOf_spec]
    isClosed k e)
  termination_by e

/-- The substitution acts via identity on indices strictly below `n`. -/
def SbIsVar (σ : Nat → Exp) (n : Nat) :=
  ∀ ⦃i⦄, i < n → σ i = .Var i


theorem SbIsVar.up {σ : Nat → Exp} {n k} : SbIsVar σ n → SbIsVar (Exp.up σ k) (n + k) := by
  induction k with
  | zero => rintro σk ⟨⟩ lt <;> simp [Exp.up, σk lt]
  | succ k ih =>
    rintro σk ⟨⟩ lt
    . simp only [Exp.up, snoc_zero]
    . simp [Exp.up]
      have:= ih σk
      unfold SbIsVar at this
      specialize this (Nat.succ_lt_succ_iff.mp lt)
      rw[this]
      simp[rename_exp]


theorem SbIsVar.zero (σ : Nat → Exp) : SbIsVar σ 0 := nofun

theorem subst_of_isClosed' {e : Exp} {k} {σ : Nat → Exp} :
    e.isClosed k → SbIsVar σ k → e.subst_exp σ = e := by
  intro h hσ; induction e generalizing k σ
  all_goals try simp[subst_exp] <;> grind[SbIsVar, isClosed]
  all_goals simp[subst_exp]; expose_names; simp [isClosed] at h
  case _structctor =>
    simp [List.map_attach_eq_pmap, List.pmap_eq_map]
    apply map_id''_mem
    intro x hmem
    exact Prod.ext rfl (h_1 x hmem (h x.fst x.snd hmem) hσ)
  case _let =>
    constructor
    . apply map_id''_mem; intro x hmem
      grind
    . exact @h_2 (k + es.length) (up σ es.length) h.1 ((@SbIsVar.up σ k es.length) hσ)
  case _quant | _lambda => exact @h_1 (k+1) (up σ 1) h ((@SbIsVar.up σ k 1) hσ)
  all_goals apply map_id''_mem; intro x hmem; grind


theorem subst_of_isClosed {e : Exp} (σ : Nat → Exp) : e.isClosed → e.subst_exp σ = e :=
  fun h => e.subst_of_isClosed' h (.zero _)
