/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExpr
public import Strata.DL.Util.List

/-!
## Properties of Well-formed Lambda Expressions

Theorems about the well-formedness predicates, substitution operations, and
beta reduction defined in `Strata.DL.Lambda.LExprWF` (`freeVars`, `varOpen`,
`varClose`, `lcAt`, `WF`, `liftBVars`, `substFvar(s)`, `substK`,
`betaReduce(K)`, `betaReduceRedexesFuel` and its wrappers).

### Local closedness (`varOpen` / `varClose` / `lcAt`)
`varOpen` preserves `sizeOf`, `varClose`/`varOpen` are mutually inverse on fresh
and locally-closed terms (`varClose_of_varOpen`, `varOpen_varClose_when_lcAt`,
`varOpen_of_varClose`), and `lcAt` is reflected through opening under binders
(`lcAt_substK_inv`, `lcAt_varOpen_inv`, `lcAt_varOpen_abs`, `lcAt_varOpen_quant`).

### `liftBVars` / `substFvars`: bvar handling
`liftBVars` is the identity on locally-closed terms (`liftBVars_eq_of_lcAt`), and
`substFvars` coincides with its lifting variant when every replacement is locally
closed (`substFvars_eq_substFvarsLifting_of_lcAt`).

### `substFvars` unfolding
`substFvars_unfold` rewrites `substFvars` to a single structural recursion
(bypassing the `isEmpty` guard); the `@[simp]` per-constructor corollaries
(`substFvars_const'`, `substFvars_app`, `substFvars_abs`, …) follow from it.

### `substFvars` and `eraseMetadata`
`freeVars` and `substFvars` commute with `eraseMetadata` (`freeVars_eraseMetadata`,
`substFvars_eraseMetadata_congr`, `substFvars_eraseMetadata_values_congr`), and
`substFvars` depends only on `Map.find?` (`substFvars_congr_find`). Also
included: the `.fvar` lookup lemmas `substFvars_fvar_find` /
`substFvars_fvar_none`.

### `liftBVars` / `substK` and `eraseMetadata`
`liftBVars`, `substK`, and `varOpen` each preserve `eraseMetadata` equality.

### `getVars` and `freeVars`
`getVars` is the identifier projection of `freeVars` (`getVars_eq_freeVars_idents`),
so closed terms have no `getVars` (`closed_implies_getVars_nil`).

### Beta reduction (`betaReduce` / `betaReduceRedexes*`)
On a locally-closed redex, the lifting/decrementing reduction coincides with
plain `subst` (`betaReduceWith_eq_subst_of_lc` for any metadata-indexed
replacement family; `betaReduce_eq_subst_of_lc` for the single-argument case).
The non-erasing redex walker preserves every operator occurrence — the
call-preservation statement `getOps_subset_betaReduceRedexesPreservingArgs`
(via `getOps_subset_betaReduceRedexesFuel`, at every fuel budget); the
analogous statement for the erasing walker is provably false, because a
constant-lambda redex erases its argument's operators
(`getOps_betaReduce_of_not_bvarUsed`; alias redexes preserve them,
`getOps_body_subset_betaReduce` / `getOps_arg_subset_betaReduce`).
-/

namespace Lambda
open Std (ToFormat Format format)

namespace LExpr

variable {T : LExprParams} [DecidableEq T.IDMeta]

/-! ### Local closedness: `varOpen` / `varClose` / `lcAt` -/

theorem varOpen_sizeOf {T}:
  ∀ (x:IdentT GenericTy T.IDMeta) e k,
    (varOpen (T := T) k x e).sizeOf = e.sizeOf := by
  intros x e
  induction e
  case const _ _ | op _ _ _ | fvar _ _ _ =>
    unfold varOpen substK; solve | simp
  case bvar _ n =>
    intro k
    unfold varOpen substK
    split <;> solve | simp
  case abs _ ty e IH =>
    unfold varOpen substK
    intro k
    simp only [sizeOf]
    unfold varOpen at IH
    grind
  case quant _ ty e trigger x_IH trigger_IH =>
    unfold varOpen substK
    intro k
    simp only [sizeOf]
    unfold varOpen at x_IH trigger_IH
    grind
  case app _ _ lhs_IH rhs_IH  | eq _ _ lhs_IH rhs_IH =>
    unfold varOpen substK
    unfold varOpen at lhs_IH rhs_IH
    simp only [sizeOf]
    grind
  case ite _ _ c_IH then_IH else_IH =>
    unfold varOpen substK
    unfold varOpen at c_IH then_IH else_IH
    simp only [sizeOf]
    grind

theorem varClose_of_varOpen [LawfulBEq T.IDMeta] [BEq T.Metadata] [ReflBEq T.Metadata] [BEq GenericTy] [ReflBEq GenericTy] [LawfulBEq GenericTy]  (h : fresh x e) :
  varClose (T := T) (GenericTy := GenericTy) i x (varOpen i x e) = e := by
  induction e generalizing i x
  all_goals try simp_all [fresh, varOpen, LExpr.substK, varClose, freeVars]
  case bvar _ j =>
    by_cases hi : j = i <;>
    simp_all [varClose]
  case fvar _ name ty =>
    intro h1
    have ⟨x1, x2⟩ := x
    simp at h h1
    exact fun a => h h1 (id (Eq.symm a))
  done

---------------------------------------------------------------------

theorem varOpen_varClose_when_lcAt [DecidableEq GenericTy] [BEq T.Metadata] [LawfulBEq T.Metadata]
  (h1 : lcAt k e) (h2 : k <= i) :
  (varOpen i x (varClose (T := T) (GenericTy := GenericTy) i x e)) = e := by
  induction e generalizing k i x
  case const c ty =>
    simp! [lcAt, varOpen, substK]
  case op o ty =>
    simp! [lcAt, varOpen, substK]
  case bvar j =>
    simp_all! [lcAt, varOpen, substK]; omega
  case fvar name ty =>
    simp_all [lcAt, varOpen, varClose]
    by_cases hx: x.fst = name <;> simp_all[substK]
    by_cases ht: ty = x.snd <;> simp_all [substK]
  case abs e e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih (k + 1) (i + 1) x.fst]
  case quant qk e tr_ih e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih (k + 1) (i + 1) x.fst, @tr_ih (k + 1) (i + 1) x.fst]
  case app fn e fn_ih e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih k i x.fst, @fn_ih k i x.fst]
  case ite c t e c_ih t_ih e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih k i x.fst, @c_ih k i x.fst, @t_ih k i x.fst]
  case eq e1 e2 e1_ih e2_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e1_ih k i x.fst, @e2_ih k i x.fst]
  done

theorem lcAt_substK_inv (he: lcAt k (substK i s e)) (hik: k ≤ i) : lcAt (i + 1) e := by
  induction e generalizing i k s <;> simp_all[lcAt, substK] <;> try grind
  case bvar id j =>
    by_cases j = i
    case pos hji => omega
    case neg hji => rw[if_neg hji] at he; simp[lcAt] at he; omega

theorem lcAt_varOpen_inv (hs: lcAt k (varOpen i x e)) (hik: k ≤ i) : lcAt (i + 1) e := by
  unfold varOpen at hs; exact (lcAt_substK_inv hs hik)

theorem lcAt_varOpen_abs
  (h1 : lcAt k (varOpen i x y)) (h2 : k <= i) :
  lcAt i (abs m name ty y) := by
  simp[lcAt]; apply (@lcAt_varOpen_inv k i)<;> assumption

theorem lcAt_varOpen_quant
  (hy : lcAt k (varOpen i x y)) (hki : k <= i)
  (htr: lcAt k (varOpen i x tr)) :
  lcAt i (quant m qk name ty tr y) := by
  simp[lcAt]; constructor<;> apply (@lcAt_varOpen_inv k i) <;> assumption

theorem varOpen_of_varClose {T} {GenericTy} [BEq T.Metadata] [LawfulBEq T.Metadata] [DecidableEq T.IDMeta] [DecidableEq GenericTy] {i : Nat} {x : IdentT GenericTy T.IDMeta} {e : LExpr ⟨T, GenericTy⟩} (h : LExpr.WF e) :
  varOpen i x (varClose i x e) = e := by
  simp_all [LExpr.WF]
  rename_i r1 r2 r3
  have c := varOpen_varClose_when_lcAt (GenericTy:=GenericTy) (k:=0) (e:=e) (i:=i) (x:=x) h
  simp at c
  exact c

---------------------------------------------------------------------

/-! ### `liftBVars` / `substFvars`: bvar handling -/

omit [DecidableEq T.IDMeta] in
/-- `liftBVars` is the identity on expressions with no dangling bvars at or above `cutoff`. -/
theorem liftBVars_eq_of_lcAt
    {e : LExpr T.mono} {cutoff : Nat}
    (h : lcAt cutoff e = true) (n : Nat)
    : liftBVars n e cutoff = e := by
  induction e generalizing cutoff with
  | const | op | fvar => rfl
  | bvar => simp [liftBVars, lcAt] at h ⊢; omega
  | abs _ _ _ _ ih => simp [liftBVars, lcAt] at h ⊢; exact ih h
  | quant _ _ _ _ _ _ ih_tr ih_body => simp [liftBVars, lcAt] at h ⊢; exact ⟨ih_tr h.1, ih_body h.2⟩
  | app _ _ _ ih1 ih2 => simp [liftBVars, lcAt] at h ⊢; exact ⟨ih1 h.1, ih2 h.2⟩
  | ite _ _ _ _ ih1 ih2 ih3 => simp [liftBVars, lcAt] at h ⊢; exact ⟨ih1 h.1.1, ih2 h.1.2, ih3 h.2⟩
  | eq _ _ _ ih1 ih2 => simp [liftBVars, lcAt] at h ⊢; exact ⟨ih1 h.1, ih2 h.2⟩

private theorem substFvarsAux_eq_go_of_lcAt
    (e : LExpr T.mono) (sm : Map T.Identifier (LExpr T.mono)) (depth : Nat)
    (h : ∀ (k : T.Identifier) (v : LExpr T.mono), Map.find? sm k = some v → lcAt 0 v = true)
    : substFvars.substFvarsAux e sm = substFvarsLifting.go sm e depth := by
  induction e generalizing depth with
  | const | op | bvar => simp [substFvars.substFvarsAux, substFvarsLifting.go]
  | fvar _ name _ =>
    simp only [substFvars.substFvarsAux, substFvarsLifting.go]
    split
    · rename_i to hfind
      rw [liftBVars_eq_of_lcAt (h name to hfind)]
    · rfl
  | abs _ _ _ _ ih =>
    simp only [substFvars.substFvarsAux, substFvarsLifting.go]
    exact congrArg _ (ih (depth + 1))
  | quant _ _ _ _ _ _ ih_tr ih_body =>
    simp only [substFvars.substFvarsAux, substFvarsLifting.go]
    rw [ih_tr (depth + 1), ih_body (depth + 1)]
  | app _ _ _ ih1 ih2 =>
    simp only [substFvars.substFvarsAux, substFvarsLifting.go]
    rw [ih1 depth, ih2 depth]
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [substFvars.substFvarsAux, substFvarsLifting.go]
    rw [ih1 depth, ih2 depth, ih3 depth]
  | eq _ _ _ ih1 ih2 =>
    simp only [substFvars.substFvarsAux, substFvarsLifting.go]
    rw [ih1 depth, ih2 depth]

/-- `substFvars` and `substFvarsLifting` coincide when all replacement values are locally closed. -/
theorem substFvars_eq_substFvarsLifting_of_lcAt
    {e : LExpr T.mono} {sm : Map T.Identifier (LExpr T.mono)}
    (h : ∀ (k : T.Identifier) (v : LExpr T.mono), Map.find? sm k = some v → lcAt 0 v = true)
    : substFvars e sm = substFvarsLifting e sm := by
  simp only [substFvars, substFvarsLifting]
  split
  · rfl
  · exact substFvarsAux_eq_go_of_lcAt e sm 0 h

---------------------------------------------------------------------

/-! ### `substFvars` unfolding -/

/-- `substFvars` unfolds to a structural recursion, bypassing the `isEmpty` guard.
    The `isEmpty` check is an optimization; when `sm` is empty, `substFvarsAux`
    is the identity anyway. This single lemma subsumes the per-constructor
    unfolding lemmas (`substFvars_const'`, `substFvars_app`, etc.). -/
theorem substFvars_unfold
    (e : LExpr T.mono) (sm : Map T.Identifier (LExpr T.mono)) :
    LExpr.substFvars e sm = match e with
      | .const _ _ => e | .bvar _ _ => e | .op _ _ _ => e
      | .fvar _ name _ => match sm.find? name with | some to => to | none => e
      | .abs m name ty e' => .abs m name ty (LExpr.substFvars e' sm)
      | .quant m qk name ty tr' e' =>
          .quant m qk name ty (LExpr.substFvars tr' sm) (LExpr.substFvars e' sm)
      | .app m fn e' => .app m (LExpr.substFvars fn sm) (LExpr.substFvars e' sm)
      | .ite m c t e' =>
          .ite m (LExpr.substFvars c sm) (LExpr.substFvars t sm) (LExpr.substFvars e' sm)
      | .eq m e1 e2 => .eq m (LExpr.substFvars e1 sm) (LExpr.substFvars e2 sm) := by
  simp only [LExpr.substFvars]; split
  · -- sm.isEmpty = true: both sides reduce to e (with recursive substFvars = id)
    rename_i h_empty
    have h_find_none : ∀ (n : T.Identifier), sm.find? n = none := by
      intro n; cases sm with | nil => rfl | cons _ _ => simp [Map.isEmpty] at h_empty
    cases e <;> simp [h_find_none]
  · -- sm.isEmpty = false: substFvars = substFvarsAux, structurally matching the RHS
    rename_i h_ne
    cases e with
    | fvar m name ty =>
      simp only [LExpr.substFvars.substFvarsAux]
      cases sm.find? name <;> rfl
    | _ => simp [LExpr.substFvars.substFvarsAux]

@[simp] theorem substFvars_const' (m : T.Metadata) (c : LConst) (sm : Map T.Identifier (LExpr T.mono)) :
    LExpr.substFvars (LExpr.const m c) sm = LExpr.const m c := by rw [substFvars_unfold]
@[simp] theorem substFvars_op' (m : T.Metadata) (n : Identifier T.IDMeta) (t : Option T.mono.TypeType) (sm : Map T.Identifier (LExpr T.mono)) :
    LExpr.substFvars (LExpr.op m n t) sm = LExpr.op m n t := by rw [substFvars_unfold]
@[simp] theorem substFvars_bvar (m : T.Metadata) (i : Nat) (sm : Map T.Identifier (LExpr T.mono)) :
    LExpr.substFvars (LExpr.bvar m i) sm = LExpr.bvar m i := by rw [substFvars_unfold]
@[simp] theorem substFvars_ite (m : T.Metadata) (c t f : LExpr T.mono) (sm : Map T.Identifier (LExpr T.mono)) :
    LExpr.substFvars (LExpr.ite m c t f) sm =
      LExpr.ite m (LExpr.substFvars c sm) (LExpr.substFvars t sm) (LExpr.substFvars f sm) := by rw [substFvars_unfold]
@[simp] theorem substFvars_eq (m : T.Metadata) (e1 e2 : LExpr T.mono) (sm : Map T.Identifier (LExpr T.mono)) :
    LExpr.substFvars (LExpr.eq m e1 e2) sm =
      LExpr.eq m (LExpr.substFvars e1 sm) (LExpr.substFvars e2 sm) := by rw [substFvars_unfold]
@[simp] theorem substFvars_app (m : T.Metadata) (e1 e2 : LExpr T.mono) (sm : Map T.Identifier (LExpr T.mono)) :
    LExpr.substFvars (LExpr.app m e1 e2) sm =
      LExpr.app m (LExpr.substFvars e1 sm) (LExpr.substFvars e2 sm) := by rw [substFvars_unfold]
@[simp] theorem substFvars_abs (m : T.Metadata) (name : String) (ty : Option LMonoTy) (body : LExpr T.mono) (sm : Map T.Identifier (LExpr T.mono)) :
    LExpr.substFvars (.abs m name ty body) sm = .abs m name ty (LExpr.substFvars body sm) := by rw [substFvars_unfold]
@[simp] theorem substFvars_quant (m : T.Metadata) (qk : QuantifierKind) (name : String) (ty : Option LMonoTy) (tr body : LExpr T.mono) (sm : Map T.Identifier (LExpr T.mono)) :
    LExpr.substFvars (.quant m qk name ty tr body) sm =
      .quant m qk name ty (LExpr.substFvars tr sm) (LExpr.substFvars body sm) := by rw [substFvars_unfold]

/-! ### `substFvars` and `eraseMetadata` -/

/-- freeVars is invariant under eraseMetadata. -/
theorem freeVars_eraseMetadata {T : LExprParamsT}
    (e : LExpr T) :
    LExpr.freeVars e.eraseMetadata = LExpr.freeVars e := by
  induction e with
  | const | op | bvar | fvar => rfl
  | abs _ _ _ _ ih => exact ih
  | app _ _ _ ih1 ih2 => show _ ++ _ = _ ++ _; exact congr (congrArg _ ih1) ih2
  | quant _ _ _ _ _ _ ih1 ih2 => show _ ++ _ = _ ++ _; exact congr (congrArg _ ih1) ih2
  | ite _ _ _ _ ih1 ih2 ih3 =>
    show _ ++ _ ++ _ = _ ++ _ ++ _
    unfold LExpr.eraseMetadata at ih1 ih2 ih3; rw [ih1, ih2, ih3]
  | eq _ _ _ ih1 ih2 => show _ ++ _ = _ ++ _; exact congr (congrArg _ ih1) ih2

/-- If two expressions have the same eraseMetadata, they have the same freeVars. -/
theorem freeVars_of_eraseMetadata_eq {T : LExprParamsT}
    (e₁ e₂ : LExpr T) (h : e₁.eraseMetadata = e₂.eraseMetadata) :
    LExpr.freeVars e₁ = LExpr.freeVars e₂ := by
  have h1 := freeVars_eraseMetadata e₁
  have h2 := freeVars_eraseMetadata e₂
  rw [h] at h1; rw [← h1, h2]

/-- substFvars preserves eraseMetadata equality. -/
theorem substFvars_eraseMetadata_congr
    (e₁ e₂ : LExpr T.mono)
    (sm : Map T.Identifier (LExpr T.mono))
    (h : e₁.eraseMetadata = e₂.eraseMetadata) :
    (LExpr.substFvars e₁ sm).eraseMetadata = (LExpr.substFvars e₂ sm).eraseMetadata := by
  cases sm with
  | nil => simp [LExpr.substFvars, Map.isEmpty]; exact h
  | cons p rest =>
  -- sm is nonempty, so substFvars = substFvarsAux
  suffices hsuff : ∀ (e₁ e₂ : LExpr T.mono) (sm : Map T.Identifier (LExpr T.mono)),
      e₁.eraseMetadata = e₂.eraseMetadata →
      (LExpr.substFvars.substFvarsAux e₁ sm).eraseMetadata =
      (LExpr.substFvars.substFvarsAux e₂ sm).eraseMetadata by
    change (LExpr.substFvars.substFvarsAux e₁ (p :: rest)).eraseMetadata =
           (LExpr.substFvars.substFvarsAux e₂ (p :: rest)).eraseMetadata
    exact hsuff e₁ e₂ (p :: rest) h
  intro e₁ e₂ sm h
  induction e₁ generalizing e₂ sm with
  | const m c =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    injection h; subst_vars
    simp [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | op m n t =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    injection h; subst_vars
    simp [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | bvar m i =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    injection h; subst_vars
    simp [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | fvar m x ty =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂; injection h; subst_vars
    simp only [LExpr.substFvars.substFvarsAux]
    split <;> (first | rfl | simp [LExpr.eraseMetadata, LExpr.replaceMetadata])
  | abs m n t b ih =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ n₂ t₂ b₂; injection h; subst_vars
    simp only [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
    congr 1; exact ih b₂ sm (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption)
  | app m f a ihf iha =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ f₂ a₂; injection h
    simp only [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
    exact congr (congrArg _ (ihf f₂ sm (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption)))
                (iha a₂ sm (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
  | eq m l r ihl ihr =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ l₂ r₂; injection h
    simp only [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
    exact congr (congrArg _ (ihl l₂ sm (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption)))
                (ihr r₂ sm (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
  | quant m qk n ty tr b iht ihb =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ qk₂ n₂ ty₂ tr₂ b₂; injection h; subst_vars
    simp only [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
    exact congr (congrArg _ (iht tr₂ sm (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption)))
                (ihb b₂ sm (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
  | ite m c t f ihc iht ihf =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ c₂ t₂ f₂; injection h
    simp only [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
    exact congr (congr (congrArg _ (ihc c₂ sm (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption)))
                       (iht t₂ sm (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption)))
                (ihf f₂ sm (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))

/-- substFvars with eraseMetadata-equivalent values gives eraseMetadata-equivalent results.
If two substitution maps have the same keys and their values have the same eraseMetadata,
then substFvars produces the same eraseMetadata. -/
theorem substFvars_eraseMetadata_values_congr
    (e : LExpr T.mono)
    (sm₁ sm₂ : Map T.Identifier (LExpr T.mono))
    (h_len : sm₁.length = sm₂.length)
    (h_keys : sm₁.map Prod.fst = sm₂.map Prod.fst)
    (h_vals : sm₁.map (fun p => p.2.eraseMetadata) = sm₂.map (fun p => p.2.eraseMetadata)) :
    (LExpr.substFvars e sm₁).eraseMetadata = (LExpr.substFvars e sm₂).eraseMetadata := by
  -- Helper: Map.find? on maps with same keys and eM-equiv values
  have find_congr : ∀ (x : T.Identifier),
      (Map.find? sm₁ x).map LExpr.eraseMetadata = (Map.find? sm₂ x).map LExpr.eraseMetadata := by
    intro x
    induction sm₁ generalizing sm₂ with
    | nil => cases sm₂ <;> simp_all [Map.find?]
    | cons p₁ rest₁ ih =>
      cases sm₂ with
      | nil => simp at h_len
      | cons p₂ rest₂ =>
        simp only [List.map_cons, List.cons.injEq] at h_keys h_vals
        simp only [Map.find?]
        rw [h_keys.1]
        split
        · simp [h_vals.1]
        · exact ih rest₂ (by simp [List.length_cons] at h_len; exact h_len) h_keys.2 h_vals.2
  -- Main proof: structural induction on e
  cases sm₁ with
  | nil =>
    cases sm₂ with
    | nil => rfl
    | cons _ _ => simp at h_len
  | cons p₁ rest₁ =>
    cases sm₂ with
    | nil => simp at h_len
    | cons p₂ rest₂ =>
    suffices hsuff : ∀ (e : LExpr T.mono),
        (LExpr.substFvars.substFvarsAux e (p₁ :: rest₁)).eraseMetadata =
        (LExpr.substFvars.substFvarsAux e (p₂ :: rest₂)).eraseMetadata by
      simp only [LExpr.substFvars, Map.isEmpty]; exact hsuff e
    intro e
    induction e with
    | const m c => simp [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
    | op m n t => simp [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
    | bvar m i => simp [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
    | fvar m x ty =>
      simp only [LExpr.substFvars.substFvarsAux]
      have hfc := find_congr x
      cases h1 : Map.find? (p₁ :: rest₁) x with
      | none =>
        cases h2 : Map.find? (p₂ :: rest₂) x with
        | none => simp [LExpr.eraseMetadata, LExpr.replaceMetadata]
        | some v₂ => simp [h1, h2] at hfc
      | some v₁ =>
        cases h2 : Map.find? (p₂ :: rest₂) x with
        | none => simp [h1, h2] at hfc
        | some v₂ => simp [h1, h2] at hfc; exact hfc
    | abs m n t b ih =>
      simp only [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
      exact congrArg _ ih
    | app m f a ihf iha =>
      simp only [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
      exact congr (congrArg _ ihf) iha
    | eq m l r ihl ihr =>
      simp only [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
      exact congr (congrArg _ ihl) ihr
    | quant m qk n ty tr b iht ihb =>
      simp only [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
      exact congr (congrArg _ iht) ihb
    | ite m c t f ihc iht ihf =>
      simp only [LExpr.substFvars.substFvarsAux, LExpr.eraseMetadata, LExpr.replaceMetadata]
      exact congr (congr (congrArg _ ihc) iht) ihf

/-- If `Map.find? sm e = some e`, then `substFvars (.fvar m x ty) sm = e`. -/
theorem substFvars_fvar_find
    (m_meta : T.Metadata) (x : Identifier T.IDMeta) (ty : Option LMonoTy)
    (sm : Map (Identifier T.IDMeta) (LExpr T.mono))
    (v : LExpr T.mono)
    (h_find : Map.find? sm x = some v) :
    LExpr.substFvars (.fvar m_meta x ty) sm = v := by
  simp only [LExpr.substFvars]
  split
  · -- sm.isEmpty = true, so sm = []
    cases sm
    · simp [Map.find?] at h_find
    · simp [Map.isEmpty] at *
  · -- sm.isEmpty = false, use substFvarsAux
    simp [LExpr.substFvars.substFvarsAux, h_find]

/-- If `Map.find?` returns `none`, substFvars on a `.fvar` is the identity. -/
theorem substFvars_fvar_none
    (m_meta : T.Metadata) (x : Identifier T.IDMeta) (ty : Option LMonoTy)
    (sm : Map (Identifier T.IDMeta) (LExpr T.mono))
    (h_find : Map.find? sm x = none) :
    LExpr.substFvars (.fvar m_meta x ty) sm = .fvar m_meta x ty := by
  simp only [LExpr.substFvars]
  split
  · rfl
  · simp [LExpr.substFvars.substFvarsAux, h_find]

/-- `substFvars` depends only on `Map.find?`, so maps with the same `find?` give the same result. -/
theorem substFvars_congr_find
    (e : LExpr T.mono) (m₁ m₂ : Map T.Identifier (LExpr T.mono))
    (h : ∀ k, Map.find? m₁ k = Map.find? m₂ k)
    : LExpr.substFvars e m₁ = LExpr.substFvars e m₂ := by
  induction e <;> rw [substFvars_unfold, substFvars_unfold] <;> grind

/-! ### `liftBVars` / `substK` and `eraseMetadata` -/

omit [DecidableEq T.IDMeta] in
/-- `liftBVars` preserves `eraseMetadata` equality. -/
theorem liftBVars_eraseMetadata_congr
    (n : Nat) (e₁ e₂ : LExpr T.mono) (cutoff : Nat)
    (h : e₁.eraseMetadata = e₂.eraseMetadata) :
    (LExpr.liftBVars n e₁ cutoff).eraseMetadata = (LExpr.liftBVars n e₂ cutoff).eraseMetadata := by
  induction e₁ generalizing e₂ cutoff with
  | const m c =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    injection h; subst_vars; simp [LExpr.liftBVars, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | op m nm t =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    injection h; subst_vars; simp [LExpr.liftBVars, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | bvar m i =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    injection h; subst_vars
    simp only [LExpr.liftBVars]; split <;> simp [LExpr.eraseMetadata, LExpr.replaceMetadata]
  | fvar m x ty =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    injection h; subst_vars; simp [LExpr.liftBVars, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | abs m nm t b ih =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ nm₂ t₂ b₂; injection h; subst_vars
    simp only [LExpr.liftBVars, LExpr.eraseMetadata, LExpr.replaceMetadata]
    exact congrArg _ (ih b₂ _ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
  | app m f a ihf iha =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ f₂ a₂; injection h
    simp only [LExpr.liftBVars, LExpr.eraseMetadata, LExpr.replaceMetadata]
    exact congr (congrArg _ (ihf f₂ _ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption)))
      (iha a₂ _ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
  | eq m l r ihl ihr =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ l₂ r₂; injection h
    simp only [LExpr.liftBVars, LExpr.eraseMetadata, LExpr.replaceMetadata]
    exact congr (congrArg _ (ihl l₂ _ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption)))
      (ihr r₂ _ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
  | quant m qk n ty tr b iht ihb =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ qk₂ n₂ ty₂ tr₂ b₂; injection h; subst_vars
    simp only [LExpr.liftBVars, LExpr.eraseMetadata, LExpr.replaceMetadata]
    exact congr (congrArg _ (iht tr₂ _ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption)))
      (ihb b₂ _ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
  | ite m c t f ihc iht ihf =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ c₂ t₂ f₂; injection h
    simp only [LExpr.liftBVars, LExpr.eraseMetadata, LExpr.replaceMetadata]
    exact congr (congr (congrArg _ (ihc c₂ _ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption)))
      (iht t₂ _ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption)))
      (ihf f₂ _ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))

---------------------------------------------------------------------

omit [DecidableEq T.IDMeta] in
/-- substK commutes with eraseMetadata: if two expressions have the same
eraseMetadata and the substitution function produces the same eraseMetadata
regardless of its metadata argument, then substK preserves eraseMetadata equality. -/
theorem substK_eraseMetadata_congr
    (e₁ : LExpr T.mono) (e₂ : LExpr T.mono) (k : Nat)
    (s : T.Metadata → LExpr T.mono)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata)
    (h_s : ∀ m₁ m₂, (s m₁).eraseMetadata = (s m₂).eraseMetadata) :
    (LExpr.substK k s e₁).eraseMetadata = (LExpr.substK k s e₂).eraseMetadata := by
  -- The result follows from: substK preserves the structural shape (same eraseMetadata).
  -- Proof by structural induction on e₁, matching on e₂.
  induction e₁ generalizing e₂ k with
  | const m₁ c =>
    cases e₂ <;> simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_eM <;> try contradiction
    rename_i c'; subst_vars
    simp [LExpr.substK, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | op m₁ n t =>
    cases e₂ <;> simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_eM <;> try contradiction
    have ⟨hn, ht⟩ := h_eM; subst_vars
    simp [LExpr.substK, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | bvar m₁ i =>
    cases e₂ <;> simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_eM <;> try contradiction
    rename_i m₂ i'; subst i'
    simp only [LExpr.substK]
    split
    · simp [LExpr.eraseMetadata]; exact h_s _ _
    · simp [LExpr.eraseMetadata, LExpr.replaceMetadata]
  | fvar m₁ x ty =>
    cases e₂ <;> simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_eM <;> try contradiction
    have ⟨hx, hty⟩ := h_eM; subst_vars
    simp [LExpr.substK, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | abs m₁ n t b ih =>
    cases e₂ <;> simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_eM <;> try contradiction
    rename_i m₂ n₂ t₂ b₂
    have ⟨hn, ht, hb⟩ := h_eM; subst_vars
    simp only [LExpr.substK, LExpr.eraseMetadata, LExpr.replaceMetadata]
    congr 1; apply ih; exact hb
  | quant m₁ qk n ty tr b ihtr ihb =>
    cases e₂ <;> simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_eM <;> try contradiction
    rename_i m₂ qk₂ n₂ ty₂ tr₂ b₂
    have ⟨hqk, hn, hty, htr, hb⟩ := h_eM; subst_vars
    simp only [LExpr.substK, LExpr.eraseMetadata, LExpr.replaceMetadata]
    congr 1
    · apply ihtr; exact htr
    · apply ihb; exact hb
  | app m₁ f a ihf iha =>
    cases e₂ <;> simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_eM <;> try contradiction
    rename_i m₂ f₂ a₂
    have ⟨hf, ha⟩ := h_eM
    simp only [LExpr.substK, LExpr.eraseMetadata, LExpr.replaceMetadata]
    congr 1
    · apply ihf; exact hf
    · apply iha; exact ha
  | ite m₁ c t f ihc iht ihf =>
    cases e₂ <;> simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_eM <;> try contradiction
    rename_i m₂ c₂ t₂ f₂
    have ⟨hc, ht, hf⟩ := h_eM
    simp only [LExpr.substK, LExpr.eraseMetadata, LExpr.replaceMetadata]
    congr 1
    · apply ihc; exact hc
    · apply iht; exact ht
    · apply ihf; exact hf
  | eq m₁ l r ihl ihr =>
    cases e₂ <;> simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_eM <;> try contradiction
    rename_i m₂ l₂ r₂
    have ⟨hl, hr⟩ := h_eM
    simp only [LExpr.substK, LExpr.eraseMetadata, LExpr.replaceMetadata]
    congr 1
    · apply ihl; exact hl
    · apply ihr; exact hr

omit [DecidableEq T.IDMeta] in
/-- varOpen preserves eraseMetadata equality. -/
theorem varOpen_eraseMetadata_congr
    {e₁ e₂ : LExpr T.mono} {k : Nat}
    {x : T.Identifier × Option LMonoTy}
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata) :
    (LExpr.varOpen k x e₁).eraseMetadata = (LExpr.varOpen k x e₂).eraseMetadata := by
  simp only [LExpr.varOpen]
  exact substK_eraseMetadata_congr _ _ _ _ h_eM (fun _ _ => by simp [LExpr.eraseMetadata, LExpr.replaceMetadata])

---------------------------------------------------------------------

end LExpr

/-! ### `getVars` and `freeVars` -/

theorem getVars_eq_freeVars_idents {T : LExprParams} (e : LExpr T.mono) :
    LExpr.LExpr.getVars e = (LExpr.freeVars e).map Prod.fst := by
  induction e with
  | const => rfl
  | bvar => rfl
  | op => rfl
  | fvar => rfl
  | abs _ _ _ _ ih => simp [LExpr.LExpr.getVars, LExpr.freeVars, ih]
  | quant _ _ _ _ _ _ trih eih => simp [LExpr.LExpr.getVars, LExpr.freeVars, trih, eih, List.map_append]
  | app _ _ _ ih1 ih2 => simp [LExpr.LExpr.getVars, LExpr.freeVars, ih1, ih2, List.map_append]
  | ite _ _ _ _ cih tih eih => simp [LExpr.LExpr.getVars, LExpr.freeVars, cih, tih, eih, List.map_append]
  | eq _ _ _ ih1 ih2 => simp [LExpr.LExpr.getVars, LExpr.freeVars, ih1, ih2, List.map_append]

theorem closed_implies_getVars_nil {T : LExprParams} (e : LExpr T.mono)
    (hc : LExpr.closed e = true) :
    LExpr.LExpr.getVars e = [] := by
  rw [getVars_eq_freeVars_idents]
  simp [LExpr.closed, List.isEmpty_iff] at hc
  simp [hc]

/-! ## Properties of beta reduction

Properties of the beta-reduction definitions in `Strata.DL.Lambda.LExprWF`
(`betaReduce`, `betaReduceK`, `betaReduceRedexesFuel`, and the
`betaReduceRedexes` / `betaReduceRedexesPreservingArgs` wrappers).

Key results:

- `betaReduceWith_eq_subst_of_lc` (via `betaReduceK_eq_substK_of_lc`) and its
  single-argument corollary `betaReduce_eq_subst_of_lc`: on a locally-closed
  redex, the lifting/decrementing reduction coincides with the plain
  locally-nameless `subst`, so consumers of locally-closed terms can reuse the
  existing `subst` lemmas.
- `getOps_subset_betaReduceRedexesPreservingArgs`: the top-level
  call-preservation statement — the non-erasing reducer never drops an operator
  occurrence (call head), at *every* fuel budget. Syntactic analyses that must
  see every call (e.g. recursive-call extraction) rely on this.
- `getOps_betaReduce_of_not_bvarUsed`: the counterpoint — a constant-lambda
  redex erases its argument's operator occurrences, which is why the analogous
  preservation statement for the *erasing* reducer is provably false.
- Supporting per-step lemmas: `getOps_body_subset_betaReduce`,
  `getOps_arg_subset_betaReduce`, and the fuel-induction workhorse
  `getOps_subset_betaReduceRedexesFuel`. (The K-level helpers
  `getOps_liftBVars`, `getOps_subset_betaReduceK`,
  `getOps_arg_subset_betaReduceK`, and `getOps_betaReduceK_of_not_bvarUsed`
  are `private` — file-internal stepping stones only.)
-/

public section

namespace LExpr

variable {T : LExprParams} [DecidableEq T.IDMeta]

omit [DecidableEq T.IDMeta] in
/-- On a locally-closed redex body (`lcAt (k+1)`) with closed replacements
    (`lcAt 0`), `betaReduceK` coincides with `substK`: there are no enclosing-binder
    indices to decrement and the replacement needs no lift. -/
private theorem betaReduceK_eq_substK_of_lc
    {s : T.mono.base.Metadata → LExpr T.mono} (hs : ∀ m, lcAt 0 (s m) = true) :
    ∀ (body : LExpr T.mono) (k : Nat), lcAt (k + 1) body = true →
      betaReduceK k s body = substK k s body := by
  intro body
  induction body with
  | const | op | fvar => intro k _; rfl
  | bvar m i =>
    intro k hbody
    simp only [lcAt, decide_eq_true_eq] at hbody
    by_cases hik : i = k
    · subst hik; simp [betaReduceK, substK, liftBVars_eq_of_lcAt (hs m)]
    · have hni : ¬ i > k := by omega
      have hbeq : ¬ (i == k) = true := by simp [hik]
      simp [betaReduceK, substK, hbeq, hni]
  | abs _ _ _ b ih =>
    intro k hbody
    simp only [lcAt] at hbody
    simp only [betaReduceK, substK]
    exact congrArg _ (ih (k + 1) hbody)
  | quant _ _ _ _ tr b ihtr ihb =>
    intro k hbody
    simp only [lcAt, Bool.and_eq_true] at hbody
    simp only [betaReduceK, substK]
    rw [ihtr (k + 1) hbody.1, ihb (k + 1) hbody.2]
  | app _ fn a ihf iha =>
    intro k hbody
    simp only [lcAt, Bool.and_eq_true] at hbody
    simp only [betaReduceK, substK]
    rw [ihf k hbody.1, iha k hbody.2]
  | ite _ c t e ihc iht ihe =>
    intro k hbody
    simp only [lcAt, Bool.and_eq_true] at hbody
    simp only [betaReduceK, substK]
    rw [ihc k hbody.1.1, iht k hbody.1.2, ihe k hbody.2]
  | eq _ l r ihl ihr =>
    intro k hbody
    simp only [lcAt, Bool.and_eq_true] at hbody
    simp only [betaReduceK, substK]
    rw [ihl k hbody.1, ihr k hbody.2]

omit [DecidableEq T.IDMeta] in
/-- Bridge, metadata-aware form: on a locally-closed redex body with locally-closed
    replacements, the lifting/decrementing `betaReduceWith` equals the plain
    `subst`. Lets soundness proofs stated for locally-closed, empty-context terms
    reuse the existing `subst` lemmas. -/
theorem betaReduceWith_eq_subst_of_lc
    {s : T.mono.base.Metadata → LExpr T.mono} (hs : ∀ m, lcAt 0 (s m) = true)
    {body : LExpr T.mono} (hbody : lcAt 1 body = true)
    : betaReduceWith s body = subst s body :=
  betaReduceK_eq_substK_of_lc hs body 0 hbody

omit [DecidableEq T.IDMeta] in
/-- Bridge, single-argument corollary: on a locally-closed redex, the
    lifting/decrementing `betaReduce` equals the plain `subst`. -/
theorem betaReduce_eq_subst_of_lc
    {arg body : LExpr T.mono}
    (hbody : lcAt 1 body = true) (harg : lcAt 0 arg = true)
    : betaReduce arg body = subst (fun _ => arg) body :=
  betaReduceWith_eq_subst_of_lc (fun _ => harg) hbody

/-- `liftBVars` only shifts de Bruijn indices, so operator occurrences are
unchanged. -/
private theorem getOps_liftBVars {T} {GenericTy} (d : Nat) :
    ∀ (e : LExpr ⟨T, GenericTy⟩) (c : Nat), getOps (liftBVars d e c) = getOps e := by
  intro e
  induction e with
  | const | op | fvar => intro c; rfl
  | bvar m i => intro c; simp only [liftBVars]; split <;> rfl
  | abs _ _ _ b ih => intro c; simp only [liftBVars, getOps]; rw [ih (c + 1)]
  | quant _ _ _ _ tr b ihtr ihb => intro c; simp only [liftBVars, getOps]; rw [ihtr (c + 1), ihb (c + 1)]
  | app _ a b iha ihb => intro c; simp only [liftBVars, getOps]; rw [iha c, ihb c]
  | ite _ p t f ihp iht ihf => intro c; simp only [liftBVars, getOps]; rw [ihp c, iht c, ihf c]
  | eq _ a b iha ihb => intro c; simp only [liftBVars, getOps]; rw [iha c, ihb c]

/-- `betaReduceK` never drops an operator occurrence of the body: bound-variable
leaves carry no operators, and every other node is preserved structurally. -/
private theorem getOps_subset_betaReduceK {T : LExprParamsT} (s : T.base.Metadata → LExpr T) :
    ∀ (e : LExpr T) (k : Nat), getOps e ⊆ getOps (betaReduceK k s e) := by
  intro e
  induction e with
  | const | bvar | fvar => intro k; simp only [getOps]; exact List.nil_subset _
  | op => intro k; simp only [getOps, betaReduceK]; exact List.Subset.refl _
  | abs _ _ _ b ih => intro k; simp only [getOps, betaReduceK]; exact ih (k + 1)
  | quant _ _ _ _ tr b ihtr ihb => intro k; simp only [getOps, betaReduceK]; exact List.append_subset_append (ihtr (k + 1)) (ihb (k + 1))
  | app _ a b iha ihb => intro k; simp only [getOps, betaReduceK]; exact List.append_subset_append (iha k) (ihb k)
  | ite _ p t f ihp iht ihf => intro k; simp only [getOps, betaReduceK]; exact List.append_subset_append (List.append_subset_append (ihp k) (iht k)) (ihf k)
  | eq _ a b iha ihb => intro k; simp only [getOps, betaReduceK]; exact List.append_subset_append (iha k) (ihb k)

/-- If the redex body uses its bound variable (an *alias* redex), `betaReduceK`
places the argument at that occurrence, so the argument's operator
occurrences — including any recursive call — survive. -/
private theorem getOps_arg_subset_betaReduceK {T : LExprParamsT} (arg : LExpr T) :
    ∀ (e : LExpr T) (k : Nat), bvarUsed k e = true →
      getOps arg ⊆ getOps (betaReduceK k (fun _ => arg) e) := by
  intro e
  induction e with
  | const | op | fvar => intro k h; simp [bvarUsed] at h
  | bvar m i =>
    intro k h
    simp only [bvarUsed, beq_iff_eq] at h
    subst h
    simp only [betaReduceK, beq_self_eq_true, if_true]
    rw [getOps_liftBVars]
    exact List.Subset.refl _
  | abs _ _ _ b ih =>
    intro k h
    simp only [bvarUsed] at h
    simp only [betaReduceK, getOps]
    exact ih (k + 1) h
  | quant _ _ _ _ tr b ihtr ihb =>
    intro k h
    simp only [bvarUsed, Bool.or_eq_true] at h
    simp only [betaReduceK, getOps]
    rcases h with h | h
    · exact List.Subset.trans (ihtr (k + 1) h) (List.subset_append_left _ _)
    · exact List.Subset.trans (ihb (k + 1) h) (List.subset_append_right _ _)
  | app _ a b iha ihb =>
    intro k h
    simp only [bvarUsed, Bool.or_eq_true] at h
    simp only [betaReduceK, getOps]
    rcases h with h | h
    · exact List.Subset.trans (iha k h) (List.subset_append_left _ _)
    · exact List.Subset.trans (ihb k h) (List.subset_append_right _ _)
  | ite _ p t f ihp iht ihf =>
    intro k h
    simp only [bvarUsed, Bool.or_eq_true] at h
    simp only [betaReduceK, getOps]
    rcases h with (h | h) | h
    · exact List.Subset.trans (List.Subset.trans (ihp k h) (List.subset_append_left _ _)) (List.subset_append_left _ _)
    · exact List.Subset.trans (List.Subset.trans (iht k h) (List.subset_append_right _ _)) (List.subset_append_left _ _)
    · exact List.Subset.trans (ihf k h) (List.subset_append_right _ _)
  | eq _ a b iha ihb =>
    intro k h
    simp only [bvarUsed, Bool.or_eq_true] at h
    simp only [betaReduceK, getOps]
    rcases h with h | h
    · exact List.Subset.trans (iha k h) (List.subset_append_left _ _)
    · exact List.Subset.trans (ihb k h) (List.subset_append_right _ _)

/-- Conversely, if the redex body does NOT use its bound variable (a *constant*
lambda), `betaReduceK` erases the argument entirely: the result has exactly the
body's operator occurrences and none of the argument's. -/
private theorem getOps_betaReduceK_of_not_bvarUsed {T : LExprParamsT}
    (s : T.base.Metadata → LExpr T) :
    ∀ (e : LExpr T) (k : Nat), bvarUsed k e = false →
      getOps (betaReduceK k s e) = getOps e := by
  intro e
  induction e with
  | const | op | fvar => intro k _; rfl
  | bvar m i =>
    intro k h
    simp only [bvarUsed] at h
    simp [betaReduceK, getOps, h]
    split <;> rfl
  | abs _ _ _ b ih =>
    intro k h
    simp only [bvarUsed] at h
    simp only [betaReduceK, getOps]
    exact ih (k + 1) h
  | quant _ _ _ _ tr b ihtr ihb =>
    intro k h
    simp only [bvarUsed, Bool.or_eq_false_iff] at h
    simp only [betaReduceK, getOps]
    rw [ihtr (k + 1) h.1, ihb (k + 1) h.2]
  | app _ a b iha ihb =>
    intro k h
    simp only [bvarUsed, Bool.or_eq_false_iff] at h
    simp only [betaReduceK, getOps]
    rw [iha k h.1, ihb k h.2]
  | ite _ p t f ihp iht ihf =>
    intro k h
    simp only [bvarUsed, Bool.or_eq_false_iff] at h
    simp only [betaReduceK, getOps]
    rw [ihp k h.1.1, iht k h.1.2, ihf k h.2]
  | eq _ a b iha ihb =>
    intro k h
    simp only [bvarUsed, Bool.or_eq_false_iff] at h
    simp only [betaReduceK, getOps]
    rw [iha k h.1, ihb k h.2]

/-- `betaReduce` never drops the redex body's operator occurrences. -/
theorem getOps_body_subset_betaReduce {T : LExprParamsT} (arg body : LExpr T) :
    getOps body ⊆ getOps (betaReduce arg body) := by
  unfold betaReduce betaReduceWith
  exact getOps_subset_betaReduceK (fun _ => arg) body 0

/-- If the redex uses its bound variable (an *alias* redex, not a constant
lambda), `betaReduce` preserves the argument's operator occurrences — so a
recursive call inside `arg` survives the reduction. -/
theorem getOps_arg_subset_betaReduce {T : LExprParamsT} (arg body : LExpr T)
    (h : bvarUsed 0 body = true) :
    getOps arg ⊆ getOps (betaReduce arg body) := by
  unfold betaReduce betaReduceWith
  exact getOps_arg_subset_betaReduceK arg body 0 h

/-- A CONSTANT-lambda redex erases its argument: `betaReduce` drops every operator
occurrence of `arg`. This is why the erasing `betaReduceRedexes` is unsound for
call-extraction purposes (a call hidden in `arg` disappears) and why
call-preserving consumers use `betaReduceRedexesPreservingArgs`. -/
theorem getOps_betaReduce_of_not_bvarUsed {T : LExprParamsT} (arg body : LExpr T)
    (h : bvarUsed 0 body = false) :
    getOps (betaReduce arg body) = getOps body := by
  unfold betaReduce betaReduceWith
  exact getOps_betaReduceK_of_not_bvarUsed (fun _ => arg) body 0 h

/-- Whole-function call-preservation for the *non-erasing* reducer: every
operator occurrence (call head, `.op`) of `e` survives `betaReduceRedexesFuel
true`. It holds at *every* fuel (even `0`), so consumers do not depend on the
reducer reaching a normal form. The `app`/reduce case reduces exactly the
`bvarUsed 0 body = true` (alias) redexes, so `getOps_arg_subset_betaReduce`
applies and the argument's calls survive. The analogous statement for the
*erasing* reducer (`betaReduceRedexesFuel false`) is provably FALSE: a
constant-lambda redex erases its argument's calls
(`getOps_betaReduce_of_not_bvarUsed`). -/
theorem getOps_subset_betaReduceRedexesFuel {T : LExprParamsT} (fuel : Nat) :
    ∀ e : LExpr T, getOps e ⊆ getOps (betaReduceRedexesFuel true fuel e) := by
  induction fuel with
  | zero => intro e; simp only [betaReduceRedexesFuel]; exact List.Subset.refl _
  | succ fuel ih =>
    intro e
    cases e with
    | const m c => simp only [betaReduceRedexesFuel]; exact List.Subset.refl _
    | op m o ty => simp only [betaReduceRedexesFuel]; exact List.Subset.refl _
    | bvar m i => simp only [betaReduceRedexesFuel]; exact List.Subset.refl _
    | fvar m x ty => simp only [betaReduceRedexesFuel]; exact List.Subset.refl _
    | abs m n t body =>
      simp only [betaReduceRedexesFuel, getOps]
      exact ih body
    | quant m qk n t tr body =>
      simp only [betaReduceRedexesFuel, getOps]
      exact List.append_subset_append (ih tr) (ih body)
    | ite m c t f =>
      simp only [betaReduceRedexesFuel, getOps]
      exact List.append_subset_append
        (List.append_subset_append (ih c) (ih t)) (ih f)
    | eq m a b =>
      simp only [betaReduceRedexesFuel, getOps]
      exact List.append_subset_append (ih a) (ih b)
    | app m fn arg =>
      simp only [betaReduceRedexesFuel]
      split
      · rename_i mAbs n t body hfn
        have hfnbody : getOps fn ⊆ getOps body := by
          have hf := ih fn; rw [hfn] at hf; simpa only [getOps] using hf
        split
        · simp only [getOps]
          exact List.append_subset_append hfnbody (ih arg)
        · rename_i hcond
          have hbv : bvarUsed 0 body = true := by
            cases hb : bvarUsed 0 body with
            | true => rfl
            | false => rw [hb] at hcond; simp at hcond
          simp only [getOps]
          refine List.Subset.trans ?_
            (ih (betaReduce (betaReduceRedexesFuel true fuel arg) body))
          intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact List.Subset.trans hfnbody
              (getOps_body_subset_betaReduce (betaReduceRedexesFuel true fuel arg) body) h
          · exact List.Subset.trans (ih arg)
              (getOps_arg_subset_betaReduce (betaReduceRedexesFuel true fuel arg) body hbv) h
      · simp only [getOps]
        exact List.append_subset_append (ih fn) (ih arg)

/-- Whole-function call-preservation for `betaReduceRedexesPreservingArgs`: it
never drops an operator occurrence (call head) of its input, so every call in
the original term is still present in the reduced term. -/
theorem getOps_subset_betaReduceRedexesPreservingArgs {T : LExprParamsT}
    (e : LExpr T) :
    getOps e ⊆ getOps (betaReduceRedexesPreservingArgs e) := by
  unfold betaReduceRedexesPreservingArgs
  exact getOps_subset_betaReduceRedexesFuel (sizeOf e * (maxBvarMultiplicity e + 1)) e

end LExpr

end


end Lambda
