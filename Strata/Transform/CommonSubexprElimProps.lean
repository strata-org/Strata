/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CommonSubexprElim
public import Strata.Util.PtrCacheProps
import all Strata.Transform.CommonSubexprElim
import all Strata.DL.Lambda.LExpr
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Stmt
import all Init.ShareCommon
import all Init.Data.List.Sort.Basic

/-! # Properties of common subexpression elimination

`stmtRunCSESinglePass` names the shared subexpressions of a body in one pass; `stmtRunCSE`,
which names them in rounds, is kept as its specification. A *class* is an expression with its
locations erased (`E`). For a body with `FreshCSENames` and `NoHashCollisions`:
`stmtRunCSESinglePass_equiv` (both passes agree up to locations), and
`stmtRunCSESinglePass_wellFormed`, `stmtRunCSE_wellFormed` (the output is `CSEWellFormed`).

Structure of the file:
1. Erasure, naming (`rwE`), unfolding (`unfold`), subterms (`IsSub`).
2. The walk of `collectSubexprs`, the DAG and levels of the single pass, which is well formed
   outside its fallback (`stmtRunCSESinglePass_wellFormed_or_fallback`).
3. The walk as a list of visits (`occ`, `visits`); one round of naming (`one_step`,
   `round_step`).
4. The rounds of `stmtRunCSE`, round by round: round `r` names the nodes of level `r`
   (`round_iter`), so the loop ends with the single pass's output (`stmtRunCSE_E`).
5. The rounds in general, where visits can only drop (`one_step_le`, `GInv`), giving
   `stmtRunCSE_wellFormed`. -/


namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## Expressions up to locations -/

/-- `e` with every location erased (`Core.eraseLocs`): two expressions are the
    same subexpression for CSE when their erasures are equal. -/
abbrev E (e : Expression.Expr) : Expression.Expr := Core.eraseLocs e

/-- Erasing a constant. -/
@[simp] theorem E_const (m : ExpressionMetadata) c :
    E (.const m c) = .const valueLoc c := rfl
/-- Erasing an operator. -/
@[simp] theorem E_op (m : ExpressionMetadata) o ty :
    E (.op m o ty) = .op valueLoc o ty := rfl
/-- Erasing a bound variable. -/
@[simp] theorem E_bvar (m : ExpressionMetadata) i :
    E (.bvar m i) = .bvar valueLoc i := rfl
/-- Erasing a free variable. -/
@[simp] theorem E_fvar (m : ExpressionMetadata) x ty :
    E (.fvar m x ty) = .fvar valueLoc x ty := rfl
/-- Erasing an application. -/
@[simp] theorem E_app (m : ExpressionMetadata) (f a : Expression.Expr) :
    E (.app m f a) = .app valueLoc (E f) (E a) := rfl
/-- Erasing an `ite`. -/
@[simp] theorem E_ite (m : ExpressionMetadata) (c t f : Expression.Expr) :
    E (.ite m c t f) = .ite valueLoc (E c) (E t) (E f) := rfl
/-- Erasing an equality. -/
@[simp] theorem E_eq (m : ExpressionMetadata) (a b : Expression.Expr) :
    E (.eq m a b) = .eq valueLoc (E a) (E b) := rfl
/-- Erasing an abstraction. -/
@[simp] theorem E_abs (m : ExpressionMetadata) n ty (b : Expression.Expr) :
    E (.abs m n ty b) = .abs valueLoc n ty (E b) := rfl
/-- Erasing a quantifier. -/
@[simp] theorem E_quant (m : ExpressionMetadata) k n ty (tr b : Expression.Expr) :
    E (.quant m k n ty tr b) = .quant valueLoc k n ty (E tr) (E b) := rfl

/-- Erasing is idempotent. -/
@[simp] theorem E_E (e : Expression.Expr) : E (E e) = E e := by
  induction e <;> simp_all

/-- Re-tagging the root does not change the erasure. -/
@[simp] theorem E_replaceMetadata1 (m : ExpressionMetadata) (e : Expression.Expr) :
    E (e.replaceMetadata1 m) = E e := by
  cases e <;> rfl

/-- `exprEq` decides equality of erasures. -/
theorem exprEq_iff (a b : Expression.Expr) : exprEq a b = true ↔ E a = E b := by
  unfold exprEq LExpr.beqIgnoringMetadataFast
  induction a generalizing b with
  | const m c => cases b <;> simp [LExpr.beqIgnoringMetadata]
  | op m o ty => cases b <;> simp [LExpr.beqIgnoringMetadata]
  | bvar m i => cases b <;> simp [LExpr.beqIgnoringMetadata]
  | fvar m x ty => cases b <;> simp [LExpr.beqIgnoringMetadata]
  | abs m n ty body ih =>
    cases b <;> simp [LExpr.beqIgnoringMetadata, ih, and_assoc]
  | quant m k n ty tr body ih1 ih2 =>
    cases b <;> simp [LExpr.beqIgnoringMetadata, ih1, ih2, and_assoc]
  | app m f a ih1 ih2 => cases b <;> simp [LExpr.beqIgnoringMetadata, ih1, ih2]
  | ite m c t f ih1 ih2 ih3 =>
    cases b <;> simp [LExpr.beqIgnoringMetadata, ih1, ih2, ih3, and_assoc]
  | eq m x y ih1 ih2 => cases b <;> simp [LExpr.beqIgnoringMetadata, ih1, ih2]

/-- The structural hash ignores locations. -/
@[simp] theorem hx_E (e : Expression.Expr) : hx (E e) = hx e := by
  induction e <;> simp_all [hx, LExpr.hashExpr]

/-- Expressions with equal erasures have equal hashes. -/
theorem hx_eq_of_E {a b : Expression.Expr} (h : E a = E b) : hx a = hx b := by
  rw [← hx_E a, h, hx_E]

/-- Type checking ignores locations. -/
@[simp] theorem typeCheck_E (ctx : List LMonoTy) (e : Expression.Expr) :
    LExpr.typeCheck ctx (E e) = LExpr.typeCheck ctx e := by
  induction e generalizing ctx with
  | op m o ty => cases ty <;> rfl
  | fvar m x ty => cases ty <;> rfl
  | abs m n ty b ih => cases ty <;> simp_all [LExpr.typeCheck]
  | quant m k n ty tr b ih1 ih2 => cases ty <;> simp_all [LExpr.typeCheck]
  | _ => simp_all [LExpr.typeCheck]

/-- Bound variables are not locations. -/
@[simp] theorem hasBVar_E (e : Expression.Expr) : LExpr.hasBVar (E e) = LExpr.hasBVar e := by
  induction e <;> simp_all [LExpr.hasBVar]

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## Rewriting -/

/-- Replace the outermost subexpressions `c` with `ρ c = some v` by `v`, at every
    depth (binder bodies included). -/
def rwE (ρ : Expression.Expr → Option Expression.Expr) : Expression.Expr → Expression.Expr
  | .const m c => (ρ (.const m c)).getD (.const m c)
  | .op m o ty => (ρ (.op m o ty)).getD (.op m o ty)
  | .bvar m i => (ρ (.bvar m i)).getD (.bvar m i)
  | .fvar m x ty => (ρ (.fvar m x ty)).getD (.fvar m x ty)
  | .app m f a => (ρ (.app m f a)).getD (.app m (rwE ρ f) (rwE ρ a))
  | .ite m c t f => (ρ (.ite m c t f)).getD (.ite m (rwE ρ c) (rwE ρ t) (rwE ρ f))
  | .eq m a b => (ρ (.eq m a b)).getD (.eq m (rwE ρ a) (rwE ρ b))
  | .abs m n ty b => (ρ (.abs m n ty b)).getD (.abs m n ty (rwE ρ b))
  | .quant m k n ty tr b =>
    (ρ (.quant m k n ty tr b)).getD (.quant m k n ty (rwE ρ tr) (rwE ρ b))

/-- The replacement `tryReplace replacements` makes, on erased expressions. -/
def ρOf (replacements : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (c : Expression.Expr) : Option Expression.Expr :=
  (tryReplace replacements (hx c) c).map E

/-- `tryReplace` finds the same replacement, up to locations, for expressions
    equal up to locations. -/
theorem tryReplace_E (replacements : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    {a b : Expression.Expr} (h : E a = E b) :
    (tryReplace replacements (hx a) a).map E = (tryReplace replacements (hx b) b).map E := by
  have hh := hx_eq_of_E h
  have hp : (fun p : Expression.Expr × Expression.Expr => exprEq a p.1) =
      (fun p => exprEq b p.1) := by
    funext p
    apply Bool.eq_iff_iff.mpr
    rw [exprEq_iff, exprEq_iff, h]
  unfold tryReplace
  rw [hh]
  split
  · simp only [Option.map_map]
    rw [show (fun (x : Expression.Expr × Expression.Expr) => exprEq a x.1) = _ from hp]
    congr 1
    funext p
    simp
  · rfl

/-- `ρOf` read at an erasure. -/
theorem ρOf_E (replacements : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (e : Expression.Expr) :
    ρOf replacements (E e) = (tryReplace replacements (hx e) e).map E := by
  unfold ρOf
  rw [tryReplace_E replacements (E_E e)]

/-- The rewrite memo of `replaceSubexprs` is correct for the rewrite `rwE ρ`. -/
def RwInv (ρ : Expression.Expr → Option Expression.Expr) (s : RwState) : Prop :=
  ∀ h r, r ∈ s.memo.getD h [] →
    (r.changed = true → E r.rewrittenErased = rwE ρ (E r.original)) ∧
    (r.changed = false → rwE ρ (E r.original) = E r.original)

/-- `hashCached` computes `hashExpr`. -/
@[simp] theorem hashCached_fst (c : PtrCache hx) (e : Expression.Expr) :
    (hashCached c e).1 = hx e :=
  ((evalPtrCache e (LExpr.hashExprPtrCache e)).run c).1.h

/-- `eraseCached` computes `Core.eraseLocs`. -/
@[simp] theorem eraseCached_fst (c : PtrCache Core.eraseLocs) (e : Expression.Expr) :
    (eraseCached c e).1 = E e :=
  ((evalPtrCache e (eraseLocsPtrCache e)).run c).1.h

/-- `bind` in the state monad over `Id`, as a function of the state. -/
@[simp] theorem stateT_bind_apply {σ α β : Type} (x : StateT σ Id α) (f : α → StateT σ Id β)
    (s : σ) : (StateT.bind x f) s = f (x s).1 (x s).2 := rfl

/-- `pure` in the state monad over `Id`, as a function of the state. -/
@[simp] theorem stateT_pure_apply {σ α : Type} (a : α) (s : σ) :
    (StateT.pure a : StateT σ Id α) s = (a, s) := rfl

/-- `pure` in `Id`. -/
@[simp] theorem id_pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- `<$>` in `Id`. -/
@[simp] theorem id_map_eq {α β : Type} (f : α → β) (x : Id α) : (f <$> x) = f x := rfl

/-- `RwState.hashM` computes `hashExpr`. -/
@[simp] theorem RwState.hashM_apply (e : Expression.Expr) (s : RwState) :
    (RwState.hashM e) s = (hx e, { s with cache := (hashCached s.cache e).2 }) := by
  simp only [RwState.hashM, bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
    pure, stateT_bind_apply, stateT_pure_apply]
  rw [hashCached_fst]

/-- `RwState.eraseM` computes `Core.eraseLocs` and keeps the memo. -/
theorem RwState.eraseM_apply (e : Expression.Expr) (s : RwState) :
    ((RwState.eraseM e) s).1 = E e ∧ ((RwState.eraseM e) s).2.memo = s.memo := by
  simp only [RwState.eraseM, bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
    pure, stateT_bind_apply, stateT_pure_apply]
  exact ⟨eraseCached_fst _ _, trivial⟩

/-- The children step of `replaceSubexprs` on a memo miss. -/
def rsKids (repl : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (e : Expression.Expr) : StateM RwState (Expression.Expr × Bool) :=
  match e with
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => pure (e, false)
  | .app m fn arg => do
    let (fn', c1) ← replaceSubexprs repl fn
    let (arg', c2) ← replaceSubexprs repl arg
    pure (if c1 || c2 then (.app m fn' arg', true) else (e, false))
  | .ite m c t f => do
    let (c', c1) ← replaceSubexprs repl c
    let (t', c2) ← replaceSubexprs repl t
    let (f', c3) ← replaceSubexprs repl f
    pure (if c1 || c2 || c3 then (.ite m c' t' f', true) else (e, false))
  | .eq m e1 e2 => do
    let (e1', c1) ← replaceSubexprs repl e1
    let (e2', c2) ← replaceSubexprs repl e2
    pure (if c1 || c2 then (.eq m e1' e2', true) else (e, false))
  | .abs m name ty body => do
    let (body', c1) ← replaceSubexprs repl body
    pure (if c1 then (.abs m name ty body', true) else (e, false))
  | .quant m k name ty tr body => do
    let (tr', c1) ← replaceSubexprs repl tr
    let (body', c2) ← replaceSubexprs repl body
    pure (if c1 || c2 then (.quant m k name ty tr' body', true) else (e, false))

/-- The last step of `replaceSubexprs` on a memo miss. -/
def rsFinish (repl : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (e : Expression.Expr) (ho : UInt64) (p : Expression.Expr × Bool) :
    StateM RwState (Expression.Expr × Bool) := do
  let (e', childChanged) := p
  let (result, changed) := match tryReplace repl ho e with
    | some replacement => (replacement, true)
    | none => (e', childChanged)
  let erased ← if changed then RwState.eraseM result else pure e
  modify fun s => { s with memo := s.memo.insert ho (⟨e, erased, changed⟩ :: s.memo.getD ho []) }
  return (result, changed)

/-- `replaceSubexprs` unfolded into its memo lookup, `rsKids` and `rsFinish`. -/
theorem replaceSubexprs_eq (repl : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (e : Expression.Expr) :
    replaceSubexprs repl e = (do
      let ho ← RwState.hashM e
      let s ← get
      match (s.memo.getD ho []).find? (fun r => exprEq r.original e) with
      | some r =>
        if r.changed then return (r.rewrittenErased.replaceMetadata1 e.metadata, true)
        else return (e, false)
      | none => rsKids repl e >>= rsFinish repl e ho) := by
  rw [replaceSubexprs]
  cases e <;> rfl

/-- What a run of `replaceSubexprs` on `e` delivers: a correct memo, the rewrite
    `rwE ρ` up to locations, and `e` itself when nothing changed. -/
def RsSpec (ρ : Expression.Expr → Option Expression.Expr) (e : Expression.Expr)
    (r : (Expression.Expr × Bool) × RwState) : Prop :=
  RwInv ρ r.2 ∧ E r.1.1 = rwE ρ (E e) ∧ (r.1.2 = false → r.1.1 = e)

/-- `rwE` on an erasure: the replacement of the node, or the node rebuilt from the
    rewritten children. -/
theorem rwE_E_eq (ρ : Expression.Expr → Option Expression.Expr) (e : Expression.Expr) :
    rwE ρ (E e) = (ρ (E e)).getD (match e with
      | .app _ f a => .app valueLoc (rwE ρ (E f)) (rwE ρ (E a))
      | .ite _ c t f => .ite valueLoc (rwE ρ (E c)) (rwE ρ (E t)) (rwE ρ (E f))
      | .eq _ a b => .eq valueLoc (rwE ρ (E a)) (rwE ρ (E b))
      | .abs _ n ty b => .abs valueLoc n ty (rwE ρ (E b))
      | .quant _ k n ty tr b => .quant valueLoc k n ty (rwE ρ (E tr)) (rwE ρ (E b))
      | e => E e) := by
  cases e <;> simp [rwE]

/-- `rsFinish` meets `RsSpec`, given a children step that rewrote the children
    (`E p.1 = K`, the rebuilt node) and left `e` alone when nothing changed. -/
theorem rsFinish_spec (repl : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (e : Expression.Expr) (p : Expression.Expr × Bool) (K : Expression.Expr) (s : RwState)
    (hs : RwInv (ρOf repl) s) (hp1 : E p.1 = K) (hp2 : p.2 = false → p.1 = e)
    (hK : rwE (ρOf repl) (E e) = (ρOf repl (E e)).getD K) :
    RsSpec (ρOf repl) e ((rsFinish repl e (hx e) p) s) := by
  obtain ⟨e', c⟩ := p
  simp only at hp1 hp2
  have hρ := ρOf_E repl e
  unfold rsFinish
  cases htr : tryReplace repl (hx e) e with
  | some v =>
    rw [htr] at hρ
    simp only [Option.map_some] at hρ
    rw [hρ] at hK
    simp only [Option.getD_some] at hK
    have he := RwState.eraseM_apply v s
    simp only [bind, pure, modify,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, stateT_bind_apply, stateT_pure_apply,
      ite_true, RsSpec]
    refine ⟨?_, hK.symm, by simp⟩
    intro h r hr
    simp only [he.2] at hr
    rw [Std.HashMap.getD_insert] at hr
    split at hr
    next heq =>
      rcases List.mem_cons.mp hr with rfl | hr
      · refine ⟨fun _ => ?_, by simp⟩
        simp only [he.1, E_E]; exact hK.symm
      · exact hs _ _ (by simpa using (beq_iff_eq.mp heq) ▸ hr)
    next => exact hs _ _ hr
  | none =>
    rw [htr] at hρ
    simp only [Option.map_none] at hρ
    rw [hρ] at hK
    simp only [Option.getD_none] at hK
    cases c with
    | true =>
      have he := RwState.eraseM_apply e' s
      simp only [bind, pure, modify,
        modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, stateT_bind_apply, stateT_pure_apply,
        ite_true, RsSpec]
      refine ⟨?_, hp1.trans hK.symm, by simp⟩
      intro h r hr
      simp only [he.2] at hr
      rw [Std.HashMap.getD_insert] at hr
      split at hr
      next heq =>
        rcases List.mem_cons.mp hr with rfl | hr
        · refine ⟨fun _ => ?_, by simp⟩
          simp only [he.1, E_E]; exact hp1.trans hK.symm
        · exact hs _ _ (by simpa using (beq_iff_eq.mp heq) ▸ hr)
      next => exact hs _ _ hr
    | false =>
      have he' := hp2 rfl
      subst he'
      simp only [bind, pure, modify,
        modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, stateT_bind_apply, stateT_pure_apply,
        Bool.false_eq_true, ↓reduceIte, RsSpec]
      refine ⟨?_, hp1.trans hK.symm, fun _ => trivial⟩
      intro h r hr
      rw [Std.HashMap.getD_insert] at hr
      split at hr
      next heq =>
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨by simp, fun _ => hK.trans hp1.symm⟩
        · exact hs _ _ (by simpa using (beq_iff_eq.mp heq) ▸ hr)
      next => exact hs _ _ hr

/-- `replaceSubexprs` meets `RsSpec` on `e` once its children step `rsKids` rebuilds `e`
    as `K` (with `rwE` of `e` determined by `K`). -/
theorem replaceSubexprs_spec_of_kids
    (repl : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (e K : Expression.Expr)
    (hk : ∀ s, RwInv (ρOf repl) s → RwInv (ρOf repl) ((rsKids repl e) s).2 ∧
      E ((rsKids repl e) s).1.1 = K ∧
      (((rsKids repl e) s).1.2 = false → ((rsKids repl e) s).1.1 = e))
    (hK : rwE (ρOf repl) (E e) = (ρOf repl (E e)).getD K) :
    ∀ s, RwInv (ρOf repl) s → RsSpec (ρOf repl) e ((replaceSubexprs repl e) s) := by
  intro s hs
  rw [replaceSubexprs_eq]
  simp only [bind, get, getThe, MonadStateOf.get, StateT.get, stateT_bind_apply,
    RwState.hashM_apply, pure]
  cases hfind : List.find? (fun r => exprEq r.original e) (s.memo.getD (hx e) []) with
  | some r =>
    have hr := hfind
    have hmem := List.mem_of_find?_eq_some hr
    have hp : exprEq r.original e = true := List.find?_some (p := fun (r : Rewrite) => exprEq r.original e) hr
    have heq := (exprEq_iff _ _).mp hp
    obtain ⟨h1, h2⟩ := hs _ _ hmem
    cases hc : r.changed with
    | true =>
      simp only [hc, ite_true, RsSpec, stateT_pure_apply]
      refine ⟨hs, ?_, by simp⟩
      simp only [E_replaceMetadata1]
      rw [h1 hc, heq]
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte, RsSpec, stateT_pure_apply]
      refine ⟨hs, ?_, fun _ => trivial⟩
      rw [← heq, h2 hc]
  | none =>
    have hs' : RwInv (ρOf repl) { s with cache := (hashCached s.cache e).2 } := hs
    obtain ⟨hk1, hk2, hk3⟩ := hk _ hs'
    exact rsFinish_spec repl e _ K _ hk1 hk2 hk3 hK

/-- **`replaceSubexprs` computes `rwE` up to locations.** From a correct memo, a run of
    `replaceSubexprs` on `e` returns a correct memo and an expression whose erasure is
    `rwE (ρOf replacements) (E e)`; when it reports no change it returns `e` itself. -/
theorem replaceSubexprs_spec
    (repl : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr))) :
    ∀ (e : Expression.Expr) (s : RwState), RwInv (ρOf repl) s →
      RsSpec (ρOf repl) e ((replaceSubexprs repl e) s) := by
  intro e
  induction e with
  | const m c =>
    refine replaceSubexprs_spec_of_kids repl _ (E (.const m c)) ?_ (by simp [rwE])
    intro s hs; exact ⟨hs, rfl, fun _ => rfl⟩
  | op m o ty =>
    refine replaceSubexprs_spec_of_kids repl _ (E (.op m o ty)) ?_ (by simp [rwE])
    intro s hs; exact ⟨hs, rfl, fun _ => rfl⟩
  | bvar m i =>
    refine replaceSubexprs_spec_of_kids repl _ (E (.bvar m i)) ?_ (by simp [rwE])
    intro s hs; exact ⟨hs, rfl, fun _ => rfl⟩
  | fvar m x ty =>
    refine replaceSubexprs_spec_of_kids repl _ (E (.fvar m x ty)) ?_ (by simp [rwE])
    intro s hs; exact ⟨hs, rfl, fun _ => rfl⟩
  | app m f a ihf iha =>
    refine replaceSubexprs_spec_of_kids repl _
      (.app valueLoc (rwE (ρOf repl) (E f)) (rwE (ρOf repl) (E a))) ?_ (by simp [rwE])
    intro s hs
    obtain ⟨h1, h2, h3⟩ := ihf s hs
    obtain ⟨h4, h5, h6⟩ := iha _ h1
    simp only [rsKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    refine ⟨h4, ?_, ?_⟩
    · split
      · simp [h2, h5]
      · rename_i hc
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
        rw [h3 hc.1] at h2; rw [h6 hc.2] at h5
        simp only [E_app]; rw [← h2, ← h5]
    · split
      · simp
      · intro _; rfl
  | ite m c t f ihc iht ihf =>
    refine replaceSubexprs_spec_of_kids repl _
      (.ite valueLoc (rwE (ρOf repl) (E c)) (rwE (ρOf repl) (E t)) (rwE (ρOf repl) (E f))) ?_
      (by simp [rwE])
    intro s hs
    obtain ⟨h1, h2, h3⟩ := ihc s hs
    obtain ⟨h4, h5, h6⟩ := iht _ h1
    obtain ⟨h7, h8, h9⟩ := ihf _ h4
    simp only [rsKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    refine ⟨h7, ?_, ?_⟩
    · split
      · simp [h2, h5, h8]
      · rename_i hc
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
        rw [h3 hc.1.1] at h2; rw [h6 hc.1.2] at h5; rw [h9 hc.2] at h8
        simp only; rw [E_ite, ← h2, ← h5, ← h8]
    · split
      · simp
      · intro _; rfl
  | eq m a b iha ihb =>
    refine replaceSubexprs_spec_of_kids repl _
      (.eq valueLoc (rwE (ρOf repl) (E a)) (rwE (ρOf repl) (E b))) ?_ (by simp [rwE])
    intro s hs
    obtain ⟨h1, h2, h3⟩ := iha s hs
    obtain ⟨h4, h5, h6⟩ := ihb _ h1
    simp only [rsKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    refine ⟨h4, ?_, ?_⟩
    · split
      · simp [h2, h5]
      · rename_i hc
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
        rw [h3 hc.1] at h2; rw [h6 hc.2] at h5
        simp only [E_eq]; rw [← h2, ← h5]
    · split
      · simp
      · intro _; rfl
  | abs m n ty b ih =>
    refine replaceSubexprs_spec_of_kids repl _
      (.abs valueLoc n ty (rwE (ρOf repl) (E b))) ?_ (by simp [rwE])
    intro s hs
    obtain ⟨h1, h2, h3⟩ := ih s hs
    simp only [rsKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    refine ⟨h1, ?_, ?_⟩
    · split
      · simp [h2]
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        rw [h3 hc] at h2
        simp only; rw [E_abs, ← h2]
    · split
      · simp
      · intro _; rfl
  | quant m k n ty tr b ihtr ihb =>
    refine replaceSubexprs_spec_of_kids repl _
      (.quant valueLoc k n ty (rwE (ρOf repl) (E tr)) (rwE (ρOf repl) (E b))) ?_ (by simp [rwE])
    intro s hs
    obtain ⟨h1, h2, h3⟩ := ihtr s hs
    obtain ⟨h4, h5, h6⟩ := ihb _ h1
    simp only [rsKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    refine ⟨h4, ?_, ?_⟩
    · split
      · simp [h2, h5]
      · rename_i hc
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
        rw [h3 hc.1] at h2; rw [h6 hc.2] at h5
        simp only [E_quant]; rw [← h2, ← h5]
    · split
      · simp
      · intro _; rfl

/-- The empty rewrite memo is correct. -/
theorem RwInv_empty (ρ : Expression.Expr → Option Expression.Expr) : RwInv ρ {} := by
  intro h r hr
  simp at hr

/-! ## Type checking -/

/-- The type memo of `typeCheckClosed` is correct. -/
def TcInv (s : TcState) : Prop :=
  ∀ h p, p ∈ s.memo.getD h [] → p.2 = LExpr.typeCheck [] p.1

/-- The empty type memo is correct. -/
theorem TcInv_empty : TcInv {} := by
  intro h p hp
  simp at hp

/-- What a run of a type-checking step on `e` delivers. -/
def TcSpec (e : Expression.Expr) (r : Option LMonoTy × TcState) : Prop :=
  r.1 = LExpr.typeCheck [] e ∧ TcInv r.2

/-- `tcMemo` meets `TcSpec` when its continuation does. -/
theorem tcMemo_spec (e : Expression.Expr) (k : Unit → StateM TcState (Option LMonoTy))
    (hk : ∀ s, TcInv s → TcSpec e ((k ()) s)) :
    ∀ s, TcInv s → TcSpec e ((tcMemo e k) s) := by
  intro s hs
  unfold tcMemo
  simp only [bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure,
    modify, modifyGet, MonadStateOf.modifyGet, stateT_bind_apply]
  have hs' : TcInv { s with cache := (hashCached s.cache e).2 } := hs
  cases hfind : List.find? (fun p => exprEq p.1 e) (s.memo.getD (hashCached s.cache e).1 []) with
  | some p =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hp : exprEq p.1 e = true :=
      List.find?_some (p := fun (p : Expression.Expr × Option LMonoTy) => exprEq p.1 e) hfind
    refine ⟨?_, hs'⟩
    simp only [stateT_pure_apply]
    rw [hs _ _ hmem, ← typeCheck_E, (exprEq_iff _ _).mp hp, typeCheck_E]
  | none =>
    obtain ⟨h1, h2⟩ := hk _ hs'
    refine ⟨h1, ?_⟩
    intro h q hq
    simp only [stateT_bind_apply, StateT.modifyGet, stateT_pure_apply, id_pure_eq] at hq
    rw [Std.HashMap.getD_insert] at hq
    split at hq
    next heq =>
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h1
      · exact h2 _ _ (by simpa using (beq_iff_eq.mp heq) ▸ hq)
    next => exact h2 _ _ hq

/-- **`typeCheckClosed` is `LExpr.typeCheck []`.** From a correct memo, a run returns the
    type `LExpr.typeCheck []` gives and a correct memo. -/
theorem typeCheckClosed_spec : ∀ (e : Expression.Expr) (s : TcState), TcInv s →
    TcSpec e ((typeCheckClosed e) s) := by
  intro e
  induction e with
  | app m f a ihf iha =>
    rw [typeCheckClosed]
    refine tcMemo_spec _ _ fun s hs => ?_
    obtain ⟨h1, h2⟩ := ihf s hs
    obtain ⟨h3, h4⟩ := iha _ h2
    simp only [bind, pure, stateT_bind_apply, stateT_pure_apply]
    exact ⟨by rw [h1, h3, LExpr.typeCheck_app]; rfl, h4⟩
  | ite m c t f ihc iht ihf =>
    rw [typeCheckClosed]
    refine tcMemo_spec _ _ fun s hs => ?_
    obtain ⟨h1, h2⟩ := ihc s hs
    obtain ⟨h3, h4⟩ := iht _ h2
    obtain ⟨h5, h6⟩ := ihf _ h4
    simp only [bind, pure, stateT_bind_apply, stateT_pure_apply]
    exact ⟨by rw [h1, h3, h5, LExpr.typeCheck_ite]; rfl, h6⟩
  | eq m a b iha ihb =>
    rw [typeCheckClosed]
    refine tcMemo_spec _ _ fun s hs => ?_
    obtain ⟨h1, h2⟩ := iha s hs
    obtain ⟨h3, h4⟩ := ihb _ h2
    simp only [bind, pure, stateT_bind_apply, stateT_pure_apply]
    exact ⟨by rw [h1, h3, LExpr.typeCheck_eq]; rfl, h4⟩
  | _ =>
    intro s hs
    exact ⟨rfl, hs⟩

/-! ## Generated names -/

/-- The name of the `k`-th generated variable. -/
def cseName (k : Nat) : CoreIdent := ⟨s!"{cseVarPrefix}{k}", ()⟩

/-- Generated names are distinct. -/
theorem cseName_inj {i j : Nat} (h : cseName i = cseName j) : i = j := by
  simp only [cseName, Identifier.mk.injEq, and_true] at h
  exact String.append_toString_inj (toString cseVarPrefix) i j h

/-- The `k`-th generated variable at type `ty`, as the passes build it. -/
def cseVar (k : Nat) (ty : LMonoTy) : Expression.Expr :=
  .fvar valueLoc (cseName k) (some ty)

/-! ## Subterms -/

public section

/-- `a` is a subterm of `b` (every child counts: binder bodies, triggers and the functions
    of applications included). -/
inductive IsSub : Expression.Expr → Expression.Expr → Prop
  | refl (e) : IsSub e e
  | app₁ {a} (m f x) : IsSub a f → IsSub a (.app m f x)
  | app₂ {a} (m f x) : IsSub a x → IsSub a (.app m f x)
  | ite₁ {a} (m c t f) : IsSub a c → IsSub a (.ite m c t f)
  | ite₂ {a} (m c t f) : IsSub a t → IsSub a (.ite m c t f)
  | ite₃ {a} (m c t f) : IsSub a f → IsSub a (.ite m c t f)
  | eq₁ {a} (m x y) : IsSub a x → IsSub a (.eq m x y)
  | eq₂ {a} (m x y) : IsSub a y → IsSub a (.eq m x y)
  | abs {a} (m n ty b) : IsSub a b → IsSub a (.abs m n ty b)
  | quant₁ {a} (m k n ty tr b) : IsSub a tr → IsSub a (.quant m k n ty tr b)
  | quant₂ {a} (m k n ty tr b) : IsSub a b → IsSub a (.quant m k n ty tr b)

end

/-- The tree size of an expression. -/
def esize : Expression.Expr → Nat
  | .app _ f x => esize f + esize x + 1
  | .ite _ c t f => esize c + esize t + esize f + 1
  | .eq _ x y => esize x + esize y + 1
  | .abs _ _ _ b => esize b + 1
  | .quant _ _ _ _ tr b => esize tr + esize b + 1
  | _ => 1

/-- A subterm is no larger. -/
theorem IsSub.size_le {a b : Expression.Expr} (h : IsSub a b) : esize a ≤ esize b := by
  induction h <;> (try simp only [esize] at *) <;> omega

/-- Subterms of subterms are subterms. -/
theorem IsSub.trans {a b c : Expression.Expr} (h₁ : IsSub a b) (h₂ : IsSub b c) : IsSub a c := by
  induction h₂ with
  | refl => exact h₁
  | app₁ m f x _ ih => exact .app₁ m f x ih
  | app₂ m f x _ ih => exact .app₂ m f x ih
  | ite₁ m c t f _ ih => exact .ite₁ m c t f ih
  | ite₂ m c t f _ ih => exact .ite₂ m c t f ih
  | ite₃ m c t f _ ih => exact .ite₃ m c t f ih
  | eq₁ m x y _ ih => exact .eq₁ m x y ih
  | eq₂ m x y _ ih => exact .eq₂ m x y ih
  | abs m n ty b _ ih => exact .abs m n ty b ih
  | quant₁ m k n ty tr b _ ih => exact .quant₁ m k n ty tr b ih
  | quant₂ m k n ty tr b _ ih => exact .quant₂ m k n ty tr b ih

/-- A subterm of the same size is the term itself. -/
theorem IsSub.eq_of_size {a b : Expression.Expr} (h : IsSub a b) (hs : esize b ≤ esize a) :
    a = b := by
  cases h with
  | refl => rfl
  | _ => rename_i h'; have := h'.size_le; simp only [esize] at hs; omega

/-- `a` is a proper subterm of `b`. -/
def IsPSub (a b : Expression.Expr) : Prop := IsSub a b ∧ a ≠ b

/-- A proper subterm is smaller. -/
theorem IsPSub.size_lt {a b : Expression.Expr} (h : IsPSub a b) : esize a < esize b := by
  rcases Nat.lt_or_ge (esize a) (esize b) with h' | h'
  · exact h'
  · exact absurd (h.1.eq_of_size h') h.2

/-- The subterm relation is antisymmetric. -/
theorem IsSub.antisymm {a b : Expression.Expr} (h₁ : IsSub a b) (h₂ : IsSub b a) : a = b :=
  h₁.eq_of_size h₂.size_le

/-! ## Naming a list of subexpressions -/

/-- A named subexpression: its erasure, its index and its type. -/
abbrev NTarget := Expression.Expr × Nat × LMonoTy

/-- The replacement that names the subexpressions of `L`: the first entry of `L` for a
    class gives its variable. -/
def ρL (L : List NTarget) (c : Expression.Expr) : Option Expression.Expr :=
  (L.find? (fun t => decide (t.1 = c))).map (fun t => cseVar t.2.1 t.2.2)

/-- `e` with its children rewritten (and `e` itself kept). -/
def rwKids (ρ : Expression.Expr → Option Expression.Expr) : Expression.Expr → Expression.Expr
  | .app m f a => .app m (rwE ρ f) (rwE ρ a)
  | .ite m c t f => .ite m (rwE ρ c) (rwE ρ t) (rwE ρ f)
  | .eq m a b => .eq m (rwE ρ a) (rwE ρ b)
  | .abs m n ty b => .abs m n ty (rwE ρ b)
  | .quant m k n ty tr b => .quant m k n ty (rwE ρ tr) (rwE ρ b)
  | e => e

/-- `rwE` only reads the replacement at subterms. -/
theorem rwE_congr {ρ₁ ρ₂ : Expression.Expr → Option Expression.Expr} :
    ∀ (e : Expression.Expr), (∀ c, IsSub c e → ρ₁ c = ρ₂ c) → rwE ρ₁ e = rwE ρ₂ e := by
  intro e
  induction e with
  | app m f a ihf iha =>
    intro h
    simp only [rwE]
    rw [h _ (.refl _), ihf (fun c hc => h c (.app₁ _ _ _ hc)),
      iha (fun c hc => h c (.app₂ _ _ _ hc))]
  | ite m c t f ihc iht ihf =>
    intro h
    simp only [rwE]
    rw [h _ (.refl _), ihc (fun c hc => h c (.ite₁ _ _ _ _ hc)),
      iht (fun c hc => h c (.ite₂ _ _ _ _ hc)), ihf (fun c hc => h c (.ite₃ _ _ _ _ hc))]
  | eq m a b iha ihb =>
    intro h
    simp only [rwE]
    rw [h _ (.refl _), iha (fun c hc => h c (.eq₁ _ _ _ hc)),
      ihb (fun c hc => h c (.eq₂ _ _ _ hc))]
  | abs m n ty b ih =>
    intro h
    simp only [rwE]
    rw [h _ (.refl _), ih (fun c hc => h c (.abs _ _ _ _ hc))]
  | quant m k n ty tr b ihtr ihb =>
    intro h
    simp only [rwE]
    rw [h _ (.refl _), ihtr (fun c hc => h c (.quant₁ _ _ _ _ _ _ hc)),
      ihb (fun c hc => h c (.quant₂ _ _ _ _ _ _ hc))]
  | _ => intro h; simp only [rwE]; rw [h _ (.refl _)]

/-- `rwKids` only reads the replacement at proper subterms. -/
theorem rwKids_congr {ρ₁ ρ₂ : Expression.Expr → Option Expression.Expr} (e : Expression.Expr)
    (h : ∀ c, IsPSub c e → ρ₁ c = ρ₂ c) : rwKids ρ₁ e = rwKids ρ₂ e := by
  have hk : ∀ c k, IsSub k e → k ≠ e → IsSub c k → ρ₁ c = ρ₂ c := fun c k hk hne hc =>
    h c ⟨hc.trans hk, fun he => hne (hk.antisymm (he ▸ hc))⟩
  cases e with
  | app m f a =>
    simp only [rwKids]
    rw [rwE_congr f (fun c hc => hk c f (.app₁ _ _ _ (.refl _)) (by
          intro he; have := congrArg esize he; simp only [esize] at this; omega) hc),
      rwE_congr a (fun c hc => hk c a (.app₂ _ _ _ (.refl _)) (by
          intro he; have := congrArg esize he; simp only [esize] at this; omega) hc)]
  | ite m c t f =>
    simp only [rwKids]
    rw [rwE_congr c (fun x hx => hk x c (.ite₁ _ _ _ _ (.refl _)) (by
          intro he; have := congrArg esize he; simp only [esize] at this; omega) hx),
      rwE_congr t (fun x hx => hk x t (.ite₂ _ _ _ _ (.refl _)) (by
          intro he; have := congrArg esize he; simp only [esize] at this; omega) hx),
      rwE_congr f (fun x hx => hk x f (.ite₃ _ _ _ _ (.refl _)) (by
          intro he; have := congrArg esize he; simp only [esize] at this; omega) hx)]
  | eq m a b =>
    simp only [rwKids]
    rw [rwE_congr a (fun c hc => hk c a (.eq₁ _ _ _ (.refl _)) (by
          intro he; have := congrArg esize he; simp only [esize] at this; omega) hc),
      rwE_congr b (fun c hc => hk c b (.eq₂ _ _ _ (.refl _)) (by
          intro he; have := congrArg esize he; simp only [esize] at this; omega) hc)]
  | abs m n ty b =>
    simp only [rwKids]
    rw [rwE_congr b (fun c hc => hk c b (.abs _ _ _ _ (.refl _)) (by
          intro he; have := congrArg esize he; simp only [esize] at this; omega) hc)]
  | quant m k n ty tr b =>
    simp only [rwKids]
    rw [rwE_congr tr (fun c hc => hk c tr (.quant₁ _ _ _ _ _ _ (.refl _)) (by
          intro he; have := congrArg esize he; simp only [esize] at this; omega) hc),
      rwE_congr b (fun c hc => hk c b (.quant₂ _ _ _ _ _ _ (.refl _)) (by
          intro he; have := congrArg esize he; simp only [esize] at this; omega) hc)]
  | _ => rfl

/-- `ρL` of a list `P ++ Q` at a class of `P` is `ρL P`. -/
theorem ρL_append_of_mem {P Q : List NTarget} {c : Expression.Expr} (h : c ∈ P.map (·.1)) :
    ρL (P ++ Q) c = ρL P c := by
  unfold ρL
  rw [List.find?_append]
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
  have : (P.find? (fun t' => decide (t'.1 = t.1))).isSome := by
    rw [List.find?_isSome]; exact ⟨t, ht, by simp⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp this
  rw [hx]; rfl

/-- `ρL` of a list `P ++ Q` away from the classes of `P` is `ρL Q`. -/
theorem ρL_append_of_not_mem {P Q : List NTarget} {c : Expression.Expr} (h : c ∉ P.map (·.1)) :
    ρL (P ++ Q) c = ρL Q c := by
  unfold ρL
  rw [List.find?_append]
  have : P.find? (fun t' => decide (t'.1 = c)) = none := by
    rw [List.find?_eq_none]
    intro t ht
    simp only [decide_eq_true_eq]
    intro he; exact h (List.mem_map.mpr ⟨t, ht, he⟩)
  rw [this]; rfl

/-- `ρL` is `none` away from the classes of the list. -/
theorem ρL_eq_none {L : List NTarget} {c : Expression.Expr} (h : c ∉ L.map (·.1)) :
    ρL L c = none := by
  have := ρL_append_of_not_mem (Q := []) h
  simpa [ρL] using this

/-- `rwE` at a node: the replacement, or the node with its children rewritten. -/
theorem rwE_eq (ρ : Expression.Expr → Option Expression.Expr) (e : Expression.Expr) :
    rwE ρ e = (ρ e).getD (rwKids ρ e) := by
  cases e <;> rfl

/-! ## Unfolding the declarations -/

/-- A declaration made by CSE: index, type and right-hand side. -/
abbrev Decl := Nat × LMonoTy × Expression.Expr

/-- The `init` statement of a declaration. -/
def initOf (d : Decl) : Statement :=
  Statement.init (cseName d.1) (LTy.forAll [] d.2.1) (.det d.2.2) .empty

/-- Inline the declarations `ds` into `e`, the last declared first. -/
def unfold (ds : List Decl) (e : Expression.Expr) : Expression.Expr :=
  ds.foldr (fun d e => LExpr.substFvar e (cseName d.1) d.2.2) e

/-- Re-tagging the root of an erasure with the erased location changes nothing. -/
theorem replaceMetadata1_valueLoc_E (e : Expression.Expr) :
    (E e).replaceMetadata1 valueLoc = E e := by
  cases e <;> rfl

/-- The erasure of a substitution depends only on the erasure of its subject. -/
theorem E_substFvar_E (a : Expression.Expr) (x : CoreIdent) (to : Expression.Expr) :
    E (LExpr.substFvar (E a) x to) = E (LExpr.substFvar a x to) := by
  induction a with
  | fvar m y ty =>
    simp only [E_fvar, LExpr.substFvar]
    split <;> simp
  | app m f b ihf ihb => simp only [E_app, LExpr.substFvar, ihf, ihb]
  | ite m c t f ihc iht ihf => simp only [E_ite, LExpr.substFvar, ihc, iht, ihf]
  | eq m f b ihf ihb => simp only [E_eq, LExpr.substFvar, ihf, ihb]
  | abs m n ty b ih => simp only [E_abs, LExpr.substFvar, ih]
  | quant m k n ty tr b ihtr ihb => simp only [E_quant, LExpr.substFvar, ihtr, ihb]
  | _ => simp [LExpr.substFvar]

/-- The erasure of an unfolding depends only on the erasure of its subject. -/
theorem E_unfold_E (ds : List Decl) (a : Expression.Expr) :
    E (unfold ds (E a)) = E (unfold ds a) := by
  induction ds generalizing a with
  | nil => simp [unfold]
  | cons d ds ih =>
    simp only [unfold, List.foldr_cons] at ih ⊢
    rw [← E_substFvar_E _ _ d.2.2, ih, E_substFvar_E]

/-- A node equal to its erasure has erased children and the erased location. -/
theorem E_eq_self_app {m : ExpressionMetadata} {f a : Expression.Expr}
    (h : E (.app m f a) = .app m f a) : m = valueLoc ∧ E f = f ∧ E a = a := by
  simp only [E_app, LExpr.app.injEq] at h; exact ⟨h.1.symm, h.2⟩

/-- The free variables of an expression. -/
abbrev vars (e : Expression.Expr) : List CoreIdent := LExpr.LExpr.getVars e

/-- Substituting a variable that does not occur changes nothing. -/
theorem substFvar_of_not_mem (x : CoreIdent) (r : Expression.Expr) :
    ∀ e : Expression.Expr, x ∉ vars e → LExpr.substFvar e x r = e := by
  intro e
  induction e with
  | fvar m y ty =>
    intro h
    have : y ≠ x := fun he => h (by simp [vars, LExpr.LExpr.getVars, he])
    simp [LExpr.substFvar, this]
  | app m f a ihf iha =>
    intro h
    simp only [vars, LExpr.LExpr.getVars, List.mem_append, not_or] at h
    simp only [LExpr.substFvar, ihf h.1, iha h.2]
  | ite m c t f ihc iht ihf =>
    intro h
    simp only [vars, LExpr.LExpr.getVars, List.mem_append, not_or] at h
    simp only [LExpr.substFvar, ihc h.1.1, iht h.1.2, ihf h.2]
  | eq m a b iha ihb =>
    intro h
    simp only [vars, LExpr.LExpr.getVars, List.mem_append, not_or] at h
    simp only [LExpr.substFvar, iha h.1, ihb h.2]
  | abs m n ty b ih =>
    intro h
    simp only [vars, LExpr.LExpr.getVars] at h
    simp only [LExpr.substFvar, ih h]
  | quant m k n ty tr b ihtr ihb =>
    intro h
    simp only [vars, LExpr.LExpr.getVars, List.mem_append, not_or] at h
    simp only [LExpr.substFvar, ihtr h.1, ihb h.2]
  | _ => intro _; rfl

/-- Unfolding declarations whose names do not occur changes nothing. -/
theorem unfold_of_fresh (ds : List Decl) (e : Expression.Expr)
    (h : ∀ d ∈ ds, cseName d.1 ∉ vars e) : unfold ds e = e := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [unfold, List.foldr_cons] at ih ⊢
    rw [ih (fun d' hd' => h d' (by simp [hd']))]
    exact substFvar_of_not_mem _ _ e (h d (by simp))

/-- Unfolding goes through an application. -/
theorem unfold_app (ds : List Decl) (m : ExpressionMetadata) (f a : Expression.Expr) :
    unfold ds (.app m f a) = .app m (unfold ds f) (unfold ds a) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [unfold, List.foldr_cons] at ih ⊢; rw [ih]; rfl

/-- Unfolding goes through an `ite`. -/
theorem unfold_ite (ds : List Decl) (m : ExpressionMetadata) (c t f : Expression.Expr) :
    unfold ds (.ite m c t f) = .ite m (unfold ds c) (unfold ds t) (unfold ds f) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [unfold, List.foldr_cons] at ih ⊢; rw [ih]; rfl

/-- Unfolding goes through an equality. -/
theorem unfold_eq (ds : List Decl) (m : ExpressionMetadata) (a b : Expression.Expr) :
    unfold ds (.eq m a b) = .eq m (unfold ds a) (unfold ds b) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [unfold, List.foldr_cons] at ih ⊢; rw [ih]; rfl

/-- Unfolding goes through an abstraction. -/
theorem unfold_abs (ds : List Decl) (m : ExpressionMetadata) n ty (b : Expression.Expr) :
    unfold ds (.abs m n ty b) = .abs m n ty (unfold ds b) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [unfold, List.foldr_cons] at ih ⊢; rw [ih]; rfl

/-- Unfolding goes through a quantifier. -/
theorem unfold_quant (ds : List Decl) (m : ExpressionMetadata) k n ty (tr b : Expression.Expr) :
    unfold ds (.quant m k n ty tr b) = .quant m k n ty (unfold ds tr) (unfold ds b) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [unfold, List.foldr_cons] at ih ⊢; rw [ih]; rfl

/-- Unfolding a node whose children's rewrites unfold back gives the node back, up to
    locations, when the node is erased and its own variable is not declared. -/
theorem E_unfold_rwKids (ds : List Decl) (ρ : Expression.Expr → Option Expression.Expr)
    (t : Expression.Expr) (ht : E t = t) (hf : ∀ d ∈ ds, cseName d.1 ∉ vars t)
    (hk : ∀ k, IsSub k t → k ≠ t → E k = k → E (unfold ds (rwE ρ k)) = k) :
    E (unfold ds (rwKids ρ t)) = t := by
  have hsub : ∀ k, IsSub k t → E k = k := by
    intro k hkt
    clear hf hk
    induction hkt with
    | refl => exact ht
    | _ => rename_i ih; apply ih; simp_all
  cases t with
  | app m f a =>
    have hne1 : f ≠ .app m f a := fun h => by have := congrArg esize h; simp [esize] at this; omega
    have hne2 : a ≠ .app m f a := fun h => by have := congrArg esize h; simp [esize] at this; omega
    have h1 := hk f (.app₁ _ _ _ (.refl _)) hne1 (hsub _ (.app₁ _ _ _ (.refl _)))
    have h2 := hk a (.app₂ _ _ _ (.refl _)) hne2 (hsub _ (.app₂ _ _ _ (.refl _)))
    obtain ⟨rfl, -, -⟩ := E_eq_self_app ht
    simp only [rwKids, unfold_app, E_app, h1, h2]
  | ite m c t' f =>
    simp only [E_ite, LExpr.ite.injEq] at ht
    obtain ⟨rfl, -, -, -⟩ := ht
    have hs : ∀ k, IsSub k (.ite valueLoc c t' f) → k ≠ .ite valueLoc c t' f → E k = k →
        E (unfold ds (rwE ρ k)) = k := hk
    have h1 := hs c (.ite₁ _ _ _ _ (.refl _)) (fun h => by
      have := congrArg esize h; simp [esize] at this; omega) (hsub _ (.ite₁ _ _ _ _ (.refl _)))
    have h2 := hs t' (.ite₂ _ _ _ _ (.refl _)) (fun h => by
      have := congrArg esize h; simp [esize] at this; omega) (hsub _ (.ite₂ _ _ _ _ (.refl _)))
    have h3 := hs f (.ite₃ _ _ _ _ (.refl _)) (fun h => by
      have := congrArg esize h; simp [esize] at this; omega) (hsub _ (.ite₃ _ _ _ _ (.refl _)))
    simp only [rwKids, unfold_ite, E_ite, h1, h2, h3]
  | eq m a b =>
    simp only [E_eq, LExpr.eq.injEq] at ht
    obtain ⟨rfl, -, -⟩ := ht
    have hs : ∀ k, IsSub k (.eq valueLoc a b) → k ≠ .eq valueLoc a b → E k = k →
        E (unfold ds (rwE ρ k)) = k := hk
    have h1 := hs a (.eq₁ _ _ _ (.refl _)) (fun h => by
      have := congrArg esize h; simp [esize] at this; omega) (hsub _ (.eq₁ _ _ _ (.refl _)))
    have h2 := hs b (.eq₂ _ _ _ (.refl _)) (fun h => by
      have := congrArg esize h; simp [esize] at this; omega) (hsub _ (.eq₂ _ _ _ (.refl _)))
    simp only [rwKids, unfold_eq, E_eq, h1, h2]
  | abs m n ty b =>
    simp only [E_abs, LExpr.abs.injEq] at ht
    obtain ⟨rfl, -, -, -⟩ := ht
    have hs : ∀ k, IsSub k (.abs valueLoc n ty b) → k ≠ .abs valueLoc n ty b → E k = k →
        E (unfold ds (rwE ρ k)) = k := hk
    have h1 := hs b (.abs _ _ _ _ (.refl _)) (fun h => by
      have := congrArg esize h; simp [esize] at this) (hsub _ (.abs _ _ _ _ (.refl _)))
    simp only [rwKids, unfold_abs, E_abs, h1]
  | quant m k n ty tr b =>
    simp only [E_quant, LExpr.quant.injEq] at ht
    obtain ⟨rfl, -, -, -, -, -⟩ := ht
    have hs : ∀ k', IsSub k' (.quant valueLoc k n ty tr b) → k' ≠ .quant valueLoc k n ty tr b →
        E k' = k' → E (unfold ds (rwE ρ k')) = k' := hk
    have h1 := hs tr (.quant₁ _ _ _ _ _ _ (.refl _)) (fun h => by
      have := congrArg esize h; simp [esize] at this; omega) (hsub _ (.quant₁ _ _ _ _ _ _ (.refl _)))
    have h2 := hs b (.quant₂ _ _ _ _ _ _ (.refl _)) (fun h => by
      have := congrArg esize h; simp [esize] at this; omega) (hsub _ (.quant₂ _ _ _ _ _ _ (.refl _)))
    simp only [rwKids, unfold_quant, E_quant, h1, h2]
  | _ => simp only [rwKids]; rw [unfold_of_fresh ds _ hf]; exact ht

/-- `ρL` at a class of the list is a variable of the list. -/
theorem ρL_of_mem {P : List NTarget} {c : Expression.Expr} (h : c ∈ P.map (·.1)) :
    ∃ t ∈ P, ρL P c = some (cseVar t.2.1 t.2.2) := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
  have : (P.find? (fun t' => decide (t'.1 = t.1))).isSome := by
    rw [List.find?_isSome]; exact ⟨t, ht, by simp⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp this
  exact ⟨x, List.mem_of_find?_eq_some hx, by simp [ρL, hx]⟩

/-- The node step of `subst_rwE_step`: it holds at `e` once it holds for `rwKids` at `e`. -/
theorem subst_rwE_node (P : List NTarget) (n : Expression.Expr) (k : Nat) (ty : LMonoTy)
    (rhs : Expression.Expr) (hn : n ∉ P.map (·.1)) (hk : k ∉ P.map (·.2.1))
    (hrhs : E rhs = rwKids (ρL P) n) (e : Expression.Expr)
    (hkids : e ∉ P.map (·.1) → e ≠ n →
      E (LExpr.substFvar (rwKids (ρL (P ++ [(n, k, ty)])) e) (cseName k) rhs) = rwKids (ρL P) e) :
    E (LExpr.substFvar (rwE (ρL (P ++ [(n, k, ty)])) e) (cseName k) rhs) = rwE (ρL P) e := by
  rw [rwE_eq, rwE_eq (ρL P)]
  by_cases hP : e ∈ P.map (·.1)
  · rw [ρL_append_of_mem hP]
    obtain ⟨t, ht, hρ⟩ := ρL_of_mem hP
    have hne : cseName t.2.1 ≠ cseName k := fun h =>
      hk (List.mem_map.mpr ⟨t, ht, cseName_inj h⟩)
    rw [hρ]
    simp only [Option.getD_some, cseVar, LExpr.substFvar]
    have : (cseName t.2.1 == cseName k) = false := by simpa using hne
    rw [this]; rfl
  · rw [ρL_append_of_not_mem hP, ρL_eq_none hP]
    by_cases hen : e = n
    · subst hen
      have : ρL [(e, k, ty)] e = some (cseVar k ty) := by simp [ρL]
      rw [this]
      simp only [Option.getD_some, Option.getD_none, cseVar, LExpr.substFvar, beq_self_eq_true,
        ite_true, E_replaceMetadata1]
      exact hrhs
    · have : ρL [(n, k, ty)] e = none := ρL_eq_none (by simpa using hen)
      rw [this]
      simp only [Option.getD_none]
      exact hkids hP hen

/-- Unfolding one declaration undoes its naming: substituting the right-hand side
    `rwKids (ρL P) n` for the variable of `n` in `rwE (ρL (P ++ [n]))` gives `rwE (ρL P)`. -/
theorem subst_rwE_step (P : List NTarget) (n : Expression.Expr) (k : Nat) (ty : LMonoTy)
    (rhs : Expression.Expr) (hn : n ∉ P.map (·.1)) (hk : k ∉ P.map (·.2.1))
    (hrhs : E rhs = rwKids (ρL P) n) :
    ∀ e, E e = e → cseName k ∉ vars e →
      E (LExpr.substFvar (rwE (ρL (P ++ [(n, k, ty)])) e) (cseName k) rhs) = rwE (ρL P) e := by
  intro e
  induction e with
  | app m f a ihf iha =>
    intro he hv
    refine subst_rwE_node P n k ty rhs hn hk hrhs _ fun _ _ => ?_
    obtain ⟨rfl, hf, ha⟩ := E_eq_self_app he
    simp only [vars, LExpr.LExpr.getVars, List.mem_append, not_or] at hv
    simp only [rwKids, LExpr.substFvar, E_app, ihf hf hv.1, iha ha hv.2]
  | ite m c t f ihc iht ihf =>
    intro he hv
    refine subst_rwE_node P n k ty rhs hn hk hrhs _ fun _ _ => ?_
    simp only [E_ite, LExpr.ite.injEq] at he
    obtain ⟨rfl, hc, ht, hf⟩ := he
    simp only [vars, LExpr.LExpr.getVars, List.mem_append, not_or] at hv
    simp only [rwKids, LExpr.substFvar, E_ite, ihc hc hv.1.1, iht ht hv.1.2, ihf hf hv.2]
  | eq m a b iha ihb =>
    intro he hv
    refine subst_rwE_node P n k ty rhs hn hk hrhs _ fun _ _ => ?_
    simp only [E_eq, LExpr.eq.injEq] at he
    obtain ⟨rfl, ha, hb⟩ := he
    simp only [vars, LExpr.LExpr.getVars, List.mem_append, not_or] at hv
    simp only [rwKids, LExpr.substFvar, E_eq, iha ha hv.1, ihb hb hv.2]
  | abs m nm ty' b ih =>
    intro he hv
    refine subst_rwE_node P n k ty rhs hn hk hrhs _ fun _ _ => ?_
    simp only [E_abs, LExpr.abs.injEq] at he
    obtain ⟨rfl, -, -, hb⟩ := he
    simp only [vars, LExpr.LExpr.getVars] at hv
    simp only [rwKids, LExpr.substFvar, E_abs, ih hb hv]
  | quant m qk nm ty' tr b ihtr ihb =>
    intro he hv
    refine subst_rwE_node P n k ty rhs hn hk hrhs _ fun _ _ => ?_
    simp only [E_quant, LExpr.quant.injEq] at he
    obtain ⟨rfl, -, -, -, htr, hb⟩ := he
    simp only [vars, LExpr.LExpr.getVars, List.mem_append, not_or] at hv
    simp only [rwKids, LExpr.substFvar, E_quant, ihtr htr hv.1, ihb hb hv.2]
  | fvar m x ty' =>
    intro he hv
    refine subst_rwE_node P n k ty rhs hn hk hrhs _ fun _ _ => ?_
    simp only [vars, LExpr.LExpr.getVars, List.mem_singleton] at hv
    have : (x == cseName k) = false := by simpa using fun h => hv h.symm
    simp only [rwKids, LExpr.substFvar, this]
    exact he
  | const m c =>
    intro he hv
    exact subst_rwE_node P n k ty rhs hn hk hrhs _ fun _ _ => he
  | op m o ty' =>
    intro he hv
    exact subst_rwE_node P n k ty rhs hn hk hrhs _ fun _ _ => he
  | bvar m i =>
    intro he hv
    exact subst_rwE_node P n k ty rhs hn hk hrhs _ fun _ _ => he

/-- Unfolding a last declaration first substitutes it. -/
theorem unfold_append_singleton (ds : List Decl) (d : Decl) (x : Expression.Expr) :
    unfold (ds ++ [d]) x = unfold ds (LExpr.substFvar x (cseName d.1) d.2.2) := by
  simp [unfold, List.foldr_append]

/-- Naming nothing changes nothing. -/
theorem rwE_none (e : Expression.Expr) : rwE (fun _ => none) e = e := by
  induction e <;> simp_all [rwE]

/-- `ρL` of the empty list names nothing. -/
theorem ρL_nil : ρL [] = fun _ => none := by
  funext c; rfl

/-- **Unfolding undoes naming.** Let `Z` list named subexpressions (distinct erased
    classes, distinct indices) in declaration order, each with a right-hand side equal, up to
    locations, to the subexpression with its children rewritten by the names declared before
    it. Then unfolding the declarations (the last declared first) in an erased expression
    whose named subexpressions were replaced (`rwE`) and that mentions none of the names gives
    the expression back, up to locations. -/
theorem unfold_rwE : ∀ (Z : List (NTarget × Expression.Expr)),
    (Z.map (·.1.1)).Nodup → (Z.map (·.1.2.1)).Nodup →
    (∀ i (h : i < Z.length), E Z[i].2 = rwKids (ρL ((Z.take i).map (·.1))) Z[i].1.1) →
    ∀ e, E e = e → (∀ z ∈ Z, cseName z.1.2.1 ∉ vars e) →
      E (unfold (Z.map fun z => (z.1.2.1, z.1.2.2, z.2)) (rwE (ρL (Z.map (·.1))) e)) = e := by
  intro Z
  suffices H : ∀ len (Z : List (NTarget × Expression.Expr)), Z.length = len →
      (Z.map (·.1.1)).Nodup → (Z.map (·.1.2.1)).Nodup →
      (∀ i (h : i < Z.length), E Z[i].2 = rwKids (ρL ((Z.take i).map (·.1))) Z[i].1.1) →
      ∀ e, E e = e → (∀ z ∈ Z, cseName z.1.2.1 ∉ vars e) →
        E (unfold (Z.map fun z => (z.1.2.1, z.1.2.2, z.2)) (rwE (ρL (Z.map (·.1))) e)) = e from
    H _ Z rfl
  intro len
  induction len with
  | zero =>
    intro Z hl _ _ _ e he _
    rw [List.length_eq_zero_iff] at hl; subst hl
    simp [unfold, ρL_nil, rwE_none, he]
  | succ len ih =>
    intro Z hl
    have hZ : Z ≠ [] := by intro h; subst h; simp at hl
    have hl' := hl
    rw [← List.dropLast_concat_getLast hZ] at hl' ⊢
    generalize Z.dropLast = Y at *
    generalize Z.getLast hZ = z at *
    intro hc hi hr e he hv
    have hlY : Y.length = len := by simp at hl'; omega
    have hcY : (Y.map (·.1.1)).Nodup := by
      rw [List.map_append] at hc; exact (List.nodup_append.mp hc).1
    have hiY : (Y.map (·.1.2.1)).Nodup := by
      rw [List.map_append] at hi; exact (List.nodup_append.mp hi).1
    have hn : z.1.1 ∉ (Y.map (·.1)).map (·.1) := by
      rw [List.map_map]
      rw [List.map_append] at hc
      intro h
      exact (List.nodup_append.mp hc).2.2 _ h _ (by simp) rfl
    have hk : z.1.2.1 ∉ (Y.map (·.1)).map (·.2.1) := by
      rw [List.map_map]
      rw [List.map_append] at hi
      intro h
      exact (List.nodup_append.mp hi).2.2 _ h _ (by simp) rfl
    have hrz := hr Y.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem_cons_zero, List.take_left'] at hrz
    have hrY : ∀ i (h : i < Y.length), E Y[i].2 = rwKids (ρL ((Y.take i).map (·.1))) Y[i].1.1 := by
      intro i h
      have := hr i (by simp; omega)
      rwa [List.getElem_append_left h, List.take_append_of_le_length (Nat.le_of_lt h)] at this
    have hvY : ∀ z ∈ Y, cseName z.1.2.1 ∉ vars e := fun z' hz => hv z' (by simp [hz])
    obtain ⟨⟨n, k, ty⟩, rhs⟩ := z
    simp only [List.map_append, List.map_cons, List.map_nil, unfold_append_singleton]
      at hn hk hrz ⊢
    have hstep := subst_rwE_step (Y.map (·.1)) n k ty rhs hn hk hrz e he
      (hv ((n, k, ty), rhs) (by simp))
    rw [← E_unfold_E, hstep]
    exact ih Y hlY hcY hiY hrY e he hvY

/-! ## The walk of `collectSubexprs`: invariants -/

/-- Whether CSE may name `e`: a bvar-free application, `ite` or `eq`. -/
def eligible (e : Expression.Expr) : Prop :=
  (match e with | .app .. | .ite .. | .eq .. => True | _ => False) ∧ LExpr.hasBVar e = false

/-- Eligibility ignores locations. -/
theorem eligible_of_E {a b : Expression.Expr} (h : E a = E b) (hb : eligible b) : eligible a := by
  refine ⟨?_, by rw [← hasBVar_E, h, hasBVar_E]; exact hb.2⟩
  have := hb.1
  cases a <;> cases b <;> simp_all

/-- A bucket map whose buckets hold entries hashing to their key, all eligible, pairwise
    distinct up to locations. -/
def GoodBuckets (m : Std.HashMap UInt64 (Array Expression.Expr)) : Prop :=
  ∀ h, (∀ e ∈ m.getD h #[], hx e = h ∧ eligible e) ∧
    (m.getD h #[]).toList.Pairwise (fun a b => E a ≠ E b)

/-- The invariant of the walk: good `seen` and `dups` maps, every duplicate seen. -/
def WInv (st : CollectedExprs) : Prop :=
  GoodBuckets st.seen ∧ GoodBuckets st.dups

/-- The empty state satisfies the invariant. -/
theorem WInv_empty : WInv {} := by
  constructor <;> intro h <;> simp

/-- Pushing a new eligible entry, distinct from the bucket's, keeps buckets good. -/
theorem GoodBuckets.push {m : Std.HashMap UInt64 (Array Expression.Expr)} (hm : GoodBuckets m)
    {h : UInt64} {e : Expression.Expr} (he : hx e = h) (hel : eligible e)
    (hnew : ∀ x ∈ m.getD h #[], E x ≠ E e) :
    GoodBuckets (m.insert h ((m.getD h #[]).push e)) := by
  intro h'
  rw [Std.HashMap.getD_insert]
  split
  · next heq =>
    have heq : h = h' := by simpa using heq
    subst heq
    obtain ⟨h1, h2⟩ := hm h
    refine ⟨fun x hmem => ?_, ?_⟩
    · rcases Array.mem_push.mp hmem with hmem | rfl
      · exact h1 x hmem
      · exact ⟨he, hel⟩
    · rw [Array.toList_push, List.pairwise_append]
      refine ⟨h2, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb
      exact hnew a (by simpa using ha)
  · exact hm h'

/-- `recordSeen` keeps the walk invariant, for an eligible node not yet seen. -/
theorem WInv.recordSeen {st : CollectedExprs} (hs : WInv st) {e : Expression.Expr}
    (hel : eligible e) (hnew : (st.seen.getD (hx e) #[]).any (exprEq e) = false) :
    WInv (st.recordSeen (hx e) e) := by
  refine ⟨hs.1.push rfl hel ?_, hs.2⟩
  intro x hmem hxe
  have : (st.seen.getD (hx e) #[]).any (exprEq e) = true :=
    Array.any_eq_true'.mpr ⟨x, hmem, (exprEq_iff _ _).mpr hxe.symm⟩
  rw [this] at hnew; exact Bool.noConfusion hnew

/-- `recordDup` keeps the walk invariant, for an eligible node. -/
theorem WInv.recordDup {st : CollectedExprs} (hs : WInv st) {e : Expression.Expr}
    (hel : eligible e) : WInv (st.recordDup (hx e) e) := by
  unfold CollectedExprs.recordDup
  dsimp only
  split
  · exact hs
  · next hany =>
    refine ⟨hs.1, hs.2.push rfl hel ?_⟩
    intro x hmem hxe
    exact hany (Array.any_eq_true'.mpr ⟨x, hmem, (exprEq_iff _ _).mpr hxe.symm⟩)

/-- `withHash` returns the structural hash and keeps `seen` and `dups`. -/
theorem CollectedExprs.withHash_eq (st : CollectedExprs) (e : Expression.Expr) :
    (st.withHash e).1 = hx e ∧ (st.withHash e).2.seen = st.seen ∧
      (st.withHash e).2.dups = st.dups :=
  ⟨((evalPtrCache e (LExpr.hashExprPtrCache e)).run st.memoHash).1.h, rfl, rfl⟩

/-- Membership in a bucket after pushing onto one. -/
theorem mem_getD_insert_push (m : Std.HashMap UInt64 (Array Expression.Expr)) (h h' : UInt64)
    (e x : Expression.Expr) :
    x ∈ (m.insert h ((m.getD h #[]).push e)).getD h' #[] ↔
      x ∈ m.getD h' #[] ∨ (h = h' ∧ x = e) := by
  rw [Std.HashMap.getD_insert]
  split
  · next heq =>
    have heq : h = h' := by simpa using heq
    subst heq; simp [Array.mem_push]
  · next hne =>
    simp only [beq_iff_eq] at hne
    simp [hne]

/-- How the walk changed the maps: old entries stay, and new ones are subterms of `e`. -/
def Grows (st st' : CollectedExprs) (e : Expression.Expr) : Prop :=
  ∀ h x,
    (x ∈ st.seen.getD h #[] → x ∈ st'.seen.getD h #[]) ∧
    (x ∈ st.dups.getD h #[] → x ∈ st'.dups.getD h #[]) ∧
    (x ∈ st'.seen.getD h #[] → x ∈ st.seen.getD h #[] ∨ ∃ c, IsSub c e ∧ E x = E c) ∧
    (x ∈ st'.dups.getD h #[] → x ∈ st.dups.getD h #[] ∨ ∃ c, IsSub c e ∧ E x = E c)

/-- Nothing changed. -/
theorem Grows.rfl' {st : CollectedExprs} (e : Expression.Expr) : Grows st st e :=
  fun _ _ => ⟨id, id, Or.inl, Or.inl⟩

/-- Growth composes, along subterms of `e`. -/
theorem Grows.trans' {st₁ st₂ st₃ : CollectedExprs} {a b e : Expression.Expr}
    (h₁ : Grows st₁ st₂ a) (h₂ : Grows st₂ st₃ b) (ha : IsSub a e) (hb : IsSub b e) :
    Grows st₁ st₃ e := by
  intro h x
  obtain ⟨a1, a2, a3, a4⟩ := h₁ h x
  obtain ⟨b1, b2, b3, b4⟩ := h₂ h x
  refine ⟨b1 ∘ a1, b2 ∘ a2, fun hx => ?_, fun hx => ?_⟩
  · rcases b3 hx with hx | ⟨c, hc, he⟩
    · rcases a3 hx with hx | ⟨c, hc, he⟩
      · exact Or.inl hx
      · exact Or.inr ⟨c, hc.trans ha, he⟩
    · exact Or.inr ⟨c, hc.trans hb, he⟩
  · rcases b4 hx with hx | ⟨c, hc, he⟩
    · rcases a4 hx with hx | ⟨c, hc, he⟩
      · exact Or.inl hx
      · exact Or.inr ⟨c, hc.trans ha, he⟩
    · exact Or.inr ⟨c, hc.trans hb, he⟩

/-- Growth along a subterm is growth along the term. -/
theorem Grows.mono {st st' : CollectedExprs} {a e : Expression.Expr} (h : Grows st st' a)
    (ha : IsSub a e) : Grows st st' e :=
  Grows.trans' h (Grows.rfl' e) ha (.refl e)

/-- Erasing keeps the size. -/
@[simp] theorem esize_E (e : Expression.Expr) : esize (E e) = esize e := by
  induction e <;> simp_all [esize]

/-- `recordSeen` grows the maps by `e` itself. -/
theorem Grows.recordSeen (st : CollectedExprs) (e : Expression.Expr) :
    Grows st (st.recordSeen (hx e) e) e := by
  intro h x
  simp only [CollectedExprs.recordSeen]
  refine ⟨fun hx => (mem_getD_insert_push _ _ _ _ _).mpr (Or.inl hx), id, fun hx => ?_, Or.inl⟩
  rcases (mem_getD_insert_push _ _ _ _ _).mp hx with hx | ⟨_, rfl⟩
  · exact Or.inl hx
  · exact Or.inr ⟨x, .refl _, rfl⟩

/-- `recordDup` grows the maps by `e` itself. -/
theorem Grows.recordDup (st : CollectedExprs) (e : Expression.Expr) :
    Grows st (st.recordDup (hx e) e) e := by
  unfold CollectedExprs.recordDup
  dsimp only
  split
  · exact Grows.rfl' e
  · intro h x
    refine ⟨id, fun hx => (mem_getD_insert_push _ _ _ _ _).mpr (Or.inl hx), Or.inl, fun hx => ?_⟩
    rcases (mem_getD_insert_push _ _ _ _ _).mp hx with hx | ⟨_, rfl⟩
    · exact Or.inl hx
    · exact Or.inr ⟨x, .refl _, rfl⟩

/-- The walk invariant only reads `seen` and `dups`. -/
theorem WInv.of_eq {st st' : CollectedExprs} (h : WInv st) (h1 : st'.seen = st.seen)
    (h2 : st'.dups = st.dups) : WInv st' := by
  unfold WInv; rw [h1, h2]; exact h

/-- Growth only reads `seen` and `dups`. -/
theorem Grows.of_eq_left {st st' st'' : CollectedExprs} {e : Expression.Expr}
    (h : Grows st' st'' e) (h1 : st'.seen = st.seen) (h2 : st'.dups = st.dups) :
    Grows st st'' e := by
  unfold Grows at *; rw [h1, h2] at h; exact h

/-- An expression reached again by the walk is eligible. -/
theorem eligible_of_seen {st : CollectedExprs} (hs : WInv st) {e : Expression.Expr}
    (hany : (st.seen.getD (hx e) #[]).any (exprEq e) = true) : eligible e := by
  obtain ⟨x, hxm, hxe⟩ := Array.any_eq_true'.mp hany
  exact eligible_of_E ((exprEq_iff _ _).mp hxe) ((hs.1 _).1 x hxm).2

/-- What a step of the walk on `e` delivers from a state satisfying the invariant. -/
def WalkSpec (st : CollectedExprs) (e : Expression.Expr) (r : Bool × CollectedExprs) : Prop :=
  WInv r.2 ∧ r.1 = !LExpr.hasBVar e ∧ Grows st r.2 e

/-- A child is a subterm. -/
theorem IsSub.app_fn (m : ExpressionMetadata) (f a : Expression.Expr) : IsSub f (.app m f a) :=
  .app₁ _ _ _ (.refl _)
/-- A child is a subterm. -/
theorem IsSub.app_arg (m : ExpressionMetadata) (f a : Expression.Expr) : IsSub a (.app m f a) :=
  .app₂ _ _ _ (.refl _)

/-- The class of a node is not among the classes added by walking its proper subterms. -/
theorem not_mem_of_grows {st st' : CollectedExprs} {c e : Expression.Expr}
    (hg : Grows st st' c) (hc : esize c < esize e)
    (hnew : (st.seen.getD (hx e) #[]).any (exprEq e) = false) :
    (st'.seen.getD (hx e) #[]).any (exprEq e) = false := by
  apply Bool.eq_false_iff.mpr
  intro hany
  obtain ⟨x, hxm, hxe⟩ := Array.any_eq_true'.mp hany
  rcases (hg _ x).2.2.1 hxm with hxo | ⟨c', hc', hce⟩
  · have : (st.seen.getD (hx e) #[]).any (exprEq e) = true := Array.any_eq_true'.mpr ⟨x, hxo, hxe⟩
    rw [this] at hnew; exact Bool.noConfusion hnew
  · have h1 := congrArg esize ((exprEq_iff _ _).mp hxe)
    have h2 := congrArg esize hce
    simp only [esize_E] at h1 h2
    have := hc'.size_le
    omega

/-- The finishing step of the walk at an `app`, `ite` or `eq` node: record it as seen when it
    is bvar-free. -/
theorem walk_finish {st st₁ : CollectedExprs} {e : Expression.Expr} (hs : WInv st₁)
    (hkind : match e with | .app .. | .ite .. | .eq .. => True | _ => False)
    (ok : Bool) (hok : ok = !LExpr.hasBVar e) (hg : Grows st st₁ e)
    (hnew : (st₁.seen.getD (hx e) #[]).any (exprEq e) = false) :
    WalkSpec st e (ok, if ok then st₁.recordSeen (hx e) e else st₁) := by
  refine ⟨?_, hok, ?_⟩
  · split
    · next hok' =>
      exact hs.recordSeen ⟨hkind, by simpa [hok] using hok'⟩ hnew
    · exact hs
  · split
    · exact Grows.trans' hg (Grows.recordSeen _ _) (.refl _) (.refl _)
    · exact hg

/-- The walk on a node already in `seen`: it records a duplicate. -/
theorem walk_hit {st st₁ : CollectedExprs} {e : Expression.Expr} (hs : WInv st)
    (h2 : st₁.seen = st.seen) (h3 : st₁.dups = st.dups)
    (hany : (st₁.seen.getD (hx e) #[]).any (exprEq e) = true) :
    WalkSpec st e (true, st₁.recordDup (hx e) e) := by
  have hs1 : WInv st₁ := hs.of_eq h2 h3
  have hel := eligible_of_seen hs1 hany
  exact ⟨hs1.recordDup hel, by simp [hel.2], (Grows.recordDup st₁ e).of_eq_left h2 h3⟩

set_option hygiene false in
/-- Unfold the hashing step of the walk at `e`, naming the state after it `st₁`. -/
scoped macro "hash_step" st:ident e:term : tactic => `(tactic| (
  rw [collectSubexprs]
  dsimp only
  obtain ⟨hh1, hh2, hh3⟩ := CollectedExprs.withHash_eq $st $e
  generalize CollectedExprs.withHash $st $e = p at *
  obtain ⟨_, st₁⟩ := p
  simp only at hh1 hh2 hh3 ⊢
  subst hh1))

set_option hygiene false in
/-- Unfold the hashing step of the walk at `e`, naming the state after it `st₁`, and handle a
    node reached before. -/
local macro "walk_prefix" st:ident e:term : tactic => `(tactic| (
  hash_step $st $e
  split
  · exact walk_hit (by assumption) hh2 hh3 (by assumption)
  rename_i hany
  simp only [Bool.not_eq_true] at hany
  have hs₁ : WInv st₁ := WInv.of_eq (by assumption) hh2 hh3))

/-- **The walk's invariants.** From a state satisfying `WInv`, `collectSubexprs` and its
    spine walk keep `WInv`, report whether the expression is bvar-free, and only add
    subterms of the expression to `seen` and `dups`. -/
theorem walk_spec : ∀ e : Expression.Expr,
    (∀ st, WInv st → WalkSpec st e (collectSubexprs st e)) ∧
    (∀ st, WInv st → WalkSpec st e (collectSubexprs.walkSpine st e)) := by
  intro e
  induction e with
  | app m f a ihf iha =>
    refine ⟨fun st hs => ?_, fun st hs => ?_⟩
    · walk_prefix st (LExpr.app m f a)
      obtain ⟨i1, o1, g1⟩ := ihf.2 st₁ hs₁
      generalize collectSubexprs.walkSpine st₁ f = w at *
      obtain ⟨fnOk, st2⟩ := w
      obtain ⟨i2, o2, g2⟩ := iha.1 st2 i1
      generalize collectSubexprs st2 a = w at *
      obtain ⟨argOk, st3⟩ := w
      simp only at o1 o2 i2 g2 g1 ⊢
      have hg : Grows st₁ st3 (.app m f a) :=
        Grows.trans' g1 g2 (IsSub.app_fn m f a) (IsSub.app_arg m f a)
      refine walk_finish i2 trivial _ (by simp [LExpr.hasBVar, o1, o2]) (hg.of_eq_left hh2 hh3) ?_
      exact not_mem_of_grows g2 (by simp [esize]; omega)
        (not_mem_of_grows g1 (by simp [esize]; omega) hany)
    · rw [collectSubexprs.walkSpine]; try dsimp only
      obtain ⟨i1, o1, g1⟩ := ihf.2 st hs
      generalize collectSubexprs.walkSpine st f = w at *
      obtain ⟨fnOk, st2⟩ := w
      obtain ⟨i2, o2, g2⟩ := iha.1 st2 i1
      generalize collectSubexprs st2 a = w at *
      obtain ⟨argOk, st3⟩ := w
      simp only at o1 o2 i2 g2 g1 ⊢
      exact ⟨i2, by simp [LExpr.hasBVar, o1, o2],
        Grows.trans' g1 g2 (IsSub.app_fn m f a) (IsSub.app_arg m f a)⟩
  | ite m c t f ihc iht ihf =>
    refine ⟨fun st hs => ?_, fun st hs => ?_⟩
    · walk_prefix st (LExpr.ite m c t f)
      obtain ⟨i1, o1, g1⟩ := ihc.1 st₁ hs₁
      generalize collectSubexprs st₁ c = w at *
      obtain ⟨cOk, st2⟩ := w
      obtain ⟨i2, o2, g2⟩ := iht.1 st2 i1
      generalize collectSubexprs st2 t = w at *
      obtain ⟨tOk, st3⟩ := w
      obtain ⟨i3, o3, g3⟩ := ihf.1 st3 i2
      generalize collectSubexprs st3 f = w at *
      obtain ⟨fOk, st4⟩ := w
      simp only at o1 o2 o3 i3 g3 g2 g1 ⊢
      have hg : Grows st₁ st4 (.ite m c t f) :=
        Grows.trans' (Grows.trans' g1 g2 (.ite₁ _ _ _ _ (.refl _)) (.ite₂ _ _ _ _ (.refl _))) g3
          (.refl _) (.ite₃ _ _ _ _ (.refl _))
      refine walk_finish i3 trivial _ (by simp [LExpr.hasBVar, o1, o2, o3])
        (hg.of_eq_left hh2 hh3) ?_
      exact not_mem_of_grows g3 (by simp [esize]; omega)
        (not_mem_of_grows g2 (by simp [esize]; omega)
          (not_mem_of_grows g1 (by simp [esize]; omega) hany))
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact ⟨hs, by simp [LExpr.hasBVarCached_eq], Grows.rfl' _⟩
  | eq m a b iha ihb =>
    refine ⟨fun st hs => ?_, fun st hs => ?_⟩
    · walk_prefix st (LExpr.eq m a b)
      obtain ⟨i1, o1, g1⟩ := iha.1 st₁ hs₁
      generalize collectSubexprs st₁ a = w at *
      obtain ⟨ok1, st2⟩ := w
      obtain ⟨i2, o2, g2⟩ := ihb.1 st2 i1
      generalize collectSubexprs st2 b = w at *
      obtain ⟨ok2, st3⟩ := w
      simp only at o1 o2 i2 g2 g1 ⊢
      have hg : Grows st₁ st3 (.eq m a b) :=
        Grows.trans' g1 g2 (.eq₁ _ _ _ (.refl _)) (.eq₂ _ _ _ (.refl _))
      refine walk_finish i2 trivial _ (by simp [LExpr.hasBVar, o1, o2]) (hg.of_eq_left hh2 hh3) ?_
      exact not_mem_of_grows g2 (by simp [esize]; omega)
        (not_mem_of_grows g1 (by simp [esize]; omega) hany)
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact ⟨hs, by simp [LExpr.hasBVarCached_eq], Grows.rfl' _⟩
  | abs m n ty b ih =>
    refine ⟨fun st hs => ?_, fun st hs => ?_⟩
    · walk_prefix st (LExpr.abs m n ty b)
      exact ⟨hs₁, by simp [LExpr.hasBVarCached_eq, LExpr.hasBVar],
        (Grows.rfl' _).of_eq_left hh2 hh3⟩
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact ⟨hs, by simp [LExpr.hasBVarCached_eq], Grows.rfl' _⟩
  | quant m k n ty tr b ihtr ihb =>
    refine ⟨fun st hs => ?_, fun st hs => ?_⟩
    · walk_prefix st (LExpr.quant m k n ty tr b)
      obtain ⟨i1, o1, g1⟩ := ihtr.1 st₁ hs₁
      generalize collectSubexprs st₁ tr = w at *
      obtain ⟨ok1, st2⟩ := w
      obtain ⟨i2, o2, g2⟩ := ihb.1 { st₁ with memoHash := st2.memoHash } hs₁
      generalize collectSubexprs { st₁ with memoHash := st2.memoHash } b = w at *
      obtain ⟨ok2, st3⟩ := w
      simp only at o1 o2 ⊢
      exact ⟨hs₁, by simp [LExpr.hasBVar, o1, o2], (Grows.rfl' _).of_eq_left hh2 hh3⟩
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact ⟨hs, by simp [LExpr.hasBVarCached_eq], Grows.rfl' _⟩
  | const m c =>
    refine ⟨fun st hs => ?_, fun st hs => ?_⟩
    · walk_prefix st (LExpr.const m c)
      exact ⟨hs₁, by simp [LExpr.hasBVar], (Grows.rfl' _).of_eq_left hh2 hh3⟩
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact ⟨hs, by simp [LExpr.hasBVar], Grows.rfl' _⟩
  | op m o ty =>
    refine ⟨fun st hs => ?_, fun st hs => ?_⟩
    · walk_prefix st (LExpr.op m o ty)
      exact ⟨hs₁, by simp [LExpr.hasBVar], (Grows.rfl' _).of_eq_left hh2 hh3⟩
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact ⟨hs, by simp [LExpr.hasBVar], Grows.rfl' _⟩
  | fvar m x ty =>
    refine ⟨fun st hs => ?_, fun st hs => ?_⟩
    · walk_prefix st (LExpr.fvar m x ty)
      exact ⟨hs₁, by simp [LExpr.hasBVar], (Grows.rfl' _).of_eq_left hh2 hh3⟩
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact ⟨hs, by simp [LExpr.hasBVar], Grows.rfl' _⟩
  | bvar m i =>
    refine ⟨fun st hs => ?_, fun st hs => ?_⟩
    · walk_prefix st (LExpr.bvar m i)
      exact ⟨hs₁, by simp [LExpr.hasBVar], (Grows.rfl' _).of_eq_left hh2 hh3⟩
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact ⟨hs, by simp [LExpr.hasBVar], Grows.rfl' _⟩

/-- Walking a list of expressions keeps the invariant and only adds subterms of the
    expressions to `dups`. -/
theorem walk_foldl_spec : ∀ (exprs : List Expression.Expr) (st : CollectedExprs), WInv st →
    WInv (exprs.foldl (fun st e => (collectSubexprs st e).2) st) ∧
    ∀ h x, x ∈ (exprs.foldl (fun st e => (collectSubexprs st e).2) st).dups.getD h #[] →
      x ∈ st.dups.getD h #[] ∨ ∃ r ∈ exprs, ∃ c, IsSub c r ∧ E x = E c := by
  intro exprs
  induction exprs with
  | nil => intro st hs; exact ⟨hs, fun _ _ hx => Or.inl hx⟩
  | cons r rs ih =>
    intro st hs
    obtain ⟨i1, -, g1⟩ := (walk_spec r).1 st hs
    obtain ⟨i2, g2⟩ := ih _ i1
    refine ⟨i2, fun h x hx => ?_⟩
    rcases g2 h x hx with hx | ⟨r', hr', c, hc, he⟩
    · rcases (g1 h x).2.2.2 hx with hx | ⟨c, hc, he⟩
      · exact Or.inl hx
      · exact Or.inr ⟨r, by simp, c, hc, he⟩
    · exact Or.inr ⟨r', by simp [hr'], c, hc, he⟩

/-- **The duplicates.** The list `collectDups` returns pairs each duplicate with its
    structural hash; the duplicates are eligible, distinct up to locations, and subterms of the
    input expressions (up to locations). -/
theorem collectDups_spec (exprs : List Expression.Expr) :
    (∀ p ∈ (collectExprsToAbbreviate.collectDups exprs).1,
      hx p.2 = p.1 ∧ eligible p.2 ∧ ∃ r ∈ exprs, ∃ c, IsSub c r ∧ E p.2 = E c) ∧
    (collectExprsToAbbreviate.collectDups exprs).1.Pairwise (fun p q => E p.2 ≠ E q.2) := by
  obtain ⟨hinv, hsub⟩ := walk_foldl_spec exprs {} WInv_empty
  simp only [collectExprsToAbbreviate.collectDups]
  generalize exprs.foldl (fun st e => (collectSubexprs st e).2) {} = final at *
  have hmem : ∀ p, p ∈ final.dups.toList → p.2 = final.dups.getD p.1 #[] := by
    intro p hp
    have := (Std.HashMap.mem_toList_iff_getElem?_eq_some).mp hp
    rw [Std.HashMap.getD_eq_getD_getElem?, this]; rfl
  have hperm := List.mergeSort_perm final.dups.toList (fun a b => decide (a.1 < b.1))
  refine ⟨fun p hp => ?_, ?_⟩
  · simp only [List.mem_flatMap, List.mem_map] at hp
    obtain ⟨⟨h, b⟩, hb, x, hx, rfl⟩ := hp
    have hb' := hmem _ (hperm.mem_iff.mp hb)
    simp only at hb'
    subst hb'
    have hx' : x ∈ final.dups.getD h #[] := by simpa using hx
    obtain ⟨h1, h2⟩ := (hinv.2 h).1 x hx'
    refine ⟨h1, h2, ?_⟩
    rcases hsub h x hx' with hx'' | h3
    · simp at hx''
    · exact h3
  · rw [List.pairwise_flatMap]
    have hkeys := (Std.HashMap.distinct_keys_toList (m := final.dups)).perm hperm.symm
      (fun {a b} h => by simp only [beq_eq_false_iff_ne] at h ⊢; exact Ne.symm h)
    refine ⟨fun ⟨h, b⟩ hb => ?_, ?_⟩
    · have hb' := hmem _ (hperm.mem_iff.mp hb)
      simp only at hb'
      subst hb'
      rw [List.pairwise_map]
      exact (hinv.2 h).2
    · refine hkeys.imp_of_mem fun {a b} ha hb hab => ?_
      intro x hx y hy hxy
      simp only [List.mem_map] at hx hy
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      have ha' := hmem _ (hperm.mem_iff.mp ha)
      have hb' := hmem _ (hperm.mem_iff.mp hb)
      have hx1 := ((hinv.2 a.1).1 x (by rw [← ha']; simpa using hx)).1
      have hy1 := ((hinv.2 b.1).1 y (by rw [← hb']; simpa using hy)).1
      have := hx_eq_of_E hxy
      simp only at this
      rw [hx1, hy1] at this
      simp [this] at hab

/-- Type checking a list of duplicates with a shared memo gives each one its
    `LExpr.typeCheck []` type. -/
theorem typed_eq (dups : List (UInt64 × Expression.Expr)) :
    (dups.mapM (m := StateM TcState)
      (fun (p : UInt64 × Expression.Expr) => do return (p.1, p.2, ← typeCheckClosed p.2))).run' {} =
    dups.map (fun p => (p.1, p.2, LExpr.typeCheck [] p.2)) := by
  suffices H : ∀ (s : TcState), TcInv s →
      ((dups.mapM (m := StateM TcState)
        (fun (p : UInt64 × Expression.Expr) => do return (p.1, p.2, ← typeCheckClosed p.2))) s).1 =
      dups.map (fun p => (p.1, p.2, LExpr.typeCheck [] p.2)) from H {} TcInv_empty
  induction dups with
  | nil => intro s _; rfl
  | cons p ps ih =>
    intro s hs
    obtain ⟨h1, h2⟩ := typeCheckClosed_spec p.2 s hs
    have := ih _ h2
    simp only [bind, pure] at this
    simp only [List.mapM_cons, bind, pure, stateT_bind_apply, stateT_pure_apply, List.map_cons]
    rw [h1, this]

/-! ## The DAG -/

/-- The children of a node, in order. -/
def childList : Expression.Expr → List Expression.Expr
  | .app _ f a => [f, a]
  | .ite _ c t f => [c, t, f]
  | .eq _ a b => [a, b]
  | .abs _ _ _ b => [b]
  | .quant _ _ _ _ tr b => [tr, b]
  | _ => []

/-- The invariant of the DAG: the index map is correct and complete, classes are distinct,
    and each node's children are the nodes listed in `kids`, all with smaller indices. -/
def DInv (g : Dag) : Prop :=
  g.kids.size = g.nodes.size ∧
  (∀ h p, p ∈ g.ids.getD h [] → hx p.1 = h ∧ p.2 < g.nodes.size ∧ g.nodes[p.2]! = p.1) ∧
  (∀ i < g.nodes.size, ∃ p ∈ g.ids.getD (hx g.nodes[i]!) [], p.2 = i) ∧
  (∀ i < g.nodes.size, ∀ j < g.nodes.size, E g.nodes[i]! = E g.nodes[j]! → i = j) ∧
  (∀ i < g.nodes.size, (g.kids[i]!).length = (childList g.nodes[i]!).length ∧
     ∀ j (hj : j < (g.kids[i]!).length),
       (g.kids[i]!)[j] < i ∧ E g.nodes[(g.kids[i]!)[j]]! = E (childList g.nodes[i]!)[j]!)

/-- The empty DAG satisfies the invariant. -/
theorem DInv_empty (c : PtrCache hx) : DInv { cache := c } := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

/-- `Dag.find?` is correct and complete. -/
theorem Dag.find?_spec {g : Dag} (hg : DInv g) (e : Expression.Expr) :
    (∀ i, g.find? (hx e) e = some i → i < g.nodes.size ∧ E g.nodes[i]! = E e) ∧
    (g.find? (hx e) e = none → ∀ i < g.nodes.size, E g.nodes[i]! ≠ E e) := by
  obtain ⟨_, hb, hc, -, -⟩ := hg
  unfold Dag.find?
  refine ⟨fun i hi => ?_, fun hi i hil hie => ?_⟩
  · simp only [Option.map_eq_some_iff] at hi
    obtain ⟨p, hp, rfl⟩ := hi
    have hmem := List.mem_of_find?_eq_some hp
    have heq : exprEq p.1 e = true :=
      List.find?_some (p := fun (p : Expression.Expr × Nat) => exprEq p.1 e) hp
    obtain ⟨-, h2, h3⟩ := hb _ _ hmem
    exact ⟨h2, by rw [h3]; exact (exprEq_iff _ _).mp heq⟩
  · simp only [Option.map_eq_none_iff, List.find?_eq_none] at hi
    obtain ⟨p, hp, hpi⟩ := hc i hil
    rw [hx_eq_of_E hie] at hp
    have := hi p hp
    obtain ⟨-, -, h3⟩ := hb _ _ hp
    rw [hpi] at h3
    rw [h3] at hie
    exact this ((exprEq_iff _ _).mpr hie)

/-- The children step of `dagNode` on a miss. -/
def dagKids (e : Expression.Expr) : StateM Dag (List Nat) :=
  match e with
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => pure []
  | .app _ fn arg => do
    let i₁ ← dagNode fn
    let i₂ ← dagNode arg
    pure [i₁, i₂]
  | .ite _ c t f => do
    let i₁ ← dagNode c
    let i₂ ← dagNode t
    let i₃ ← dagNode f
    pure [i₁, i₂, i₃]
  | .eq _ e1 e2 => do
    let i₁ ← dagNode e1
    let i₂ ← dagNode e2
    pure [i₁, i₂]
  | .abs _ _ _ body => do
    let i₁ ← dagNode body
    pure [i₁]
  | .quant _ _ _ _ tr body => do
    let i₁ ← dagNode tr
    let i₂ ← dagNode body
    pure [i₁, i₂]

/-- The last step of `dagNode` on a miss: add the node. -/
def dagFinish (e : Expression.Expr) (h : UInt64) (ks : List Nat) : StateM Dag Nat := do
  let g ← get
  let i := g.nodes.size
  set { g with ids := g.ids.insert h ((e, i) :: g.ids.getD h []),
               nodes := g.nodes.push e, kids := g.kids.push ks }
  return i

/-- `dagNode` unfolded into its lookup, `dagKids` and `dagFinish`. -/
theorem dagNode_eq (e : Expression.Expr) :
    dagNode e = (do
      let g ← get
      let (h, cache) := hashCached g.cache e
      set { g with cache }
      match (← get).find? h e with
      | some i => return i
      | none => dagKids e >>= dagFinish e h) := by
  rw [dagNode]
  cases e <;> rfl

/-- An old entry of a pushed array. -/
theorem push_getElem!_lt {α : Type} [Inhabited α] (xs : Array α) (x : α) {i : Nat}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by simp; omega), getElem!_pos xs i h, Array.getElem_push_lt h]

/-- The new entry of a pushed array. -/
theorem push_getElem!_size {α : Type} [Inhabited α] (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos (xs.push x) xs.size (by simp), Array.getElem_push_eq]

/-- Adding a new node whose children are already in the DAG keeps the invariant. -/
theorem dagFinish_spec (g : Dag) (hg : DInv g) (e : Expression.Expr) (ks : List Nat)
    (habs : ∀ i < g.nodes.size, E g.nodes[i]! ≠ E e)
    (hkl : ks.length = (childList e).length)
    (hks : ∀ j (hj : j < ks.length),
      ks[j] < g.nodes.size ∧ E g.nodes[ks[j]]! = E (childList e)[j]!) :
    ((dagFinish e (hx e) ks) g).1 = g.nodes.size ∧ DInv ((dagFinish e (hx e) ks) g).2 ∧
      ((dagFinish e (hx e) ks) g).2.nodes = g.nodes.push e ∧
      ((dagFinish e (hx e) ks) g).2.kids = g.kids.push ks := by
  obtain ⟨ha, hb, hc, hd, he⟩ := hg
  simp only [dagFinish, bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure,
    stateT_bind_apply, stateT_pure_apply]
  refine ⟨trivial, ⟨by simp [ha], ?_, ?_, ?_, ?_⟩, trivial, trivial⟩
  · intro h p hp
    rw [Std.HashMap.getD_insert] at hp
    split at hp
    · next heq =>
      rcases List.mem_cons.mp hp with rfl | hp
      · refine ⟨by simpa using heq, by simp, push_getElem!_size _ _⟩
      · have heq : hx e = h := by simpa using heq
        subst heq
        obtain ⟨h1, h2, h3⟩ := hb _ _ hp
        exact ⟨h1, by simp; omega, by rw [push_getElem!_lt _ _ h2, h3]⟩
    · obtain ⟨h1, h2, h3⟩ := hb _ _ hp
      exact ⟨h1, by simp; omega, by rw [push_getElem!_lt _ _ h2, h3]⟩
  · intro i hi
    simp only [Array.size_push] at hi
    rcases Nat.lt_or_ge i g.nodes.size with hi' | hi'
    · rw [push_getElem!_lt _ _ hi']
      obtain ⟨p, hp, rfl⟩ := hc _ hi'
      refine ⟨p, ?_, rfl⟩
      rw [Std.HashMap.getD_insert]
      split
      · next heq =>
        have heq : hx e = hx g.nodes[p.2]! := by simpa using heq
        rw [← heq] at hp
        exact List.mem_cons_of_mem _ hp
      · exact hp
    · have : i = g.nodes.size := by omega
      subst this
      rw [push_getElem!_size]
      exact ⟨(e, g.nodes.size), by simp, rfl⟩
  · intro i hi j hj hij
    simp only [Array.size_push] at hi hj
    rcases Nat.lt_or_ge i g.nodes.size with hi' | hi' <;>
      rcases Nat.lt_or_ge j g.nodes.size with hj' | hj'
    · rw [push_getElem!_lt _ _ hi', push_getElem!_lt _ _ hj'] at hij
      exact hd i hi' j hj' hij
    · have : j = g.nodes.size := by omega
      subst this
      rw [push_getElem!_lt _ _ hi', push_getElem!_size] at hij
      exact absurd hij (habs i hi')
    · have : i = g.nodes.size := by omega
      subst this
      rw [push_getElem!_lt _ _ hj', push_getElem!_size] at hij
      exact absurd hij.symm (habs j hj')
    · omega
  · intro i hi
    simp only [Array.size_push] at hi
    rcases Nat.lt_or_ge i g.nodes.size with hi' | hi'
    · have hik : i < g.kids.size := by omega
      rw [push_getElem!_lt _ _ hi', push_getElem!_lt _ _ hik]
      obtain ⟨h1, h2⟩ := he i hi'
      refine ⟨h1, fun j hj => ?_⟩
      obtain ⟨h3, h4⟩ := h2 j hj
      exact ⟨h3, by rw [push_getElem!_lt _ _ (by omega)]; exact h4⟩
    · have : i = g.nodes.size := by omega
      subst this
      rw [push_getElem!_size, ← ha, push_getElem!_size]
      refine ⟨hkl, fun j hj => ?_⟩
      obtain ⟨h1, h2⟩ := hks j hj
      exact ⟨by rw [ha]; exact h1, by rw [push_getElem!_lt _ _ h1]; exact h2⟩

/-- A subterm of `e` has a counterpart in any `e'` equal to `e` up to locations. -/
theorem IsSub.transport {c e : Expression.Expr} (h : IsSub c e) :
    ∀ {e'}, E e = E e' → ∃ c', IsSub c' e' ∧ E c = E c' := by
  induction h with
  | refl => intro e' he; exact ⟨e', .refl _, he⟩
  | app₁ m f x _ ih =>
    intro e' he
    cases e' with
    | app _ _ _ =>
      simp only [E_app, LExpr.app.injEq, true_and] at he
      obtain ⟨c', h1, h2⟩ := ih he.1; exact ⟨c', .app₁ _ _ _ h1, h2⟩
    | _ => simp at he
  | app₂ m f x _ ih =>
    intro e' he
    cases e' with
    | app _ _ _ =>
      simp only [E_app, LExpr.app.injEq, true_and] at he
      obtain ⟨c', h1, h2⟩ := ih he.2; exact ⟨c', .app₂ _ _ _ h1, h2⟩
    | _ => simp at he
  | ite₁ m c t f _ ih =>
    intro e' he
    cases e' with
    | ite _ _ _ _ =>
      simp only [E_ite, LExpr.ite.injEq, true_and] at he
      obtain ⟨c', h1, h2⟩ := ih he.1; exact ⟨c', .ite₁ _ _ _ _ h1, h2⟩
    | _ => simp at he
  | ite₂ m c t f _ ih =>
    intro e' he
    cases e' with
    | ite _ _ _ _ =>
      simp only [E_ite, LExpr.ite.injEq, true_and] at he
      obtain ⟨c', h1, h2⟩ := ih he.2.1; exact ⟨c', .ite₂ _ _ _ _ h1, h2⟩
    | _ => simp at he
  | ite₃ m c t f _ ih =>
    intro e' he
    cases e' with
    | ite _ _ _ _ =>
      simp only [E_ite, LExpr.ite.injEq, true_and] at he
      obtain ⟨c', h1, h2⟩ := ih he.2.2; exact ⟨c', .ite₃ _ _ _ _ h1, h2⟩
    | _ => simp at he
  | eq₁ m x y _ ih =>
    intro e' he
    cases e' with
    | eq _ _ _ =>
      simp only [E_eq, LExpr.eq.injEq, true_and] at he
      obtain ⟨c', h1, h2⟩ := ih he.1; exact ⟨c', .eq₁ _ _ _ h1, h2⟩
    | _ => simp at he
  | eq₂ m x y _ ih =>
    intro e' he
    cases e' with
    | eq _ _ _ =>
      simp only [E_eq, LExpr.eq.injEq, true_and] at he
      obtain ⟨c', h1, h2⟩ := ih he.2; exact ⟨c', .eq₂ _ _ _ h1, h2⟩
    | _ => simp at he
  | abs m n ty b _ ih =>
    intro e' he
    cases e' with
    | abs _ _ _ _ =>
      simp only [E_abs, LExpr.abs.injEq, true_and] at he
      obtain ⟨c', h1, h2⟩ := ih he.2.2; exact ⟨c', .abs _ _ _ _ h1, h2⟩
    | _ => simp at he
  | quant₁ m k n ty tr b _ ih =>
    intro e' he
    cases e' with
    | quant _ _ _ _ _ _ =>
      simp only [E_quant, LExpr.quant.injEq, true_and] at he
      obtain ⟨c', h1, h2⟩ := ih he.2.2.2.1; exact ⟨c', .quant₁ _ _ _ _ _ _ h1, h2⟩
    | _ => simp at he
  | quant₂ m k n ty tr b _ ih =>
    intro e' he
    cases e' with
    | quant _ _ _ _ _ _ =>
      simp only [E_quant, LExpr.quant.injEq, true_and] at he
      obtain ⟨c', h1, h2⟩ := ih he.2.2.2.2; exact ⟨c', .quant₂ _ _ _ _ _ _ h1, h2⟩
    | _ => simp at he

/-- A proper subterm lies within a child. -/
theorem IsSub.child_of_ne {c e : Expression.Expr} (h : IsSub c e) (hne : c ≠ e) :
    ∃ j < (childList e).length, IsSub c (childList e)[j]! := by
  cases h with
  | refl => exact absurd rfl hne
  | app₁ _ _ _ h => exact ⟨0, by simp [childList], by simpa [childList] using h⟩
  | app₂ _ _ _ h => exact ⟨1, by simp [childList], by simpa [childList] using h⟩
  | ite₁ _ _ _ _ h => exact ⟨0, by simp [childList], by simpa [childList] using h⟩
  | ite₂ _ _ _ _ h => exact ⟨1, by simp [childList], by simpa [childList] using h⟩
  | ite₃ _ _ _ _ h => exact ⟨2, by simp [childList], by simpa [childList] using h⟩
  | eq₁ _ _ _ h => exact ⟨0, by simp [childList], by simpa [childList] using h⟩
  | eq₂ _ _ _ h => exact ⟨1, by simp [childList], by simpa [childList] using h⟩
  | abs _ _ _ _ h => exact ⟨0, by simp [childList], by simpa [childList] using h⟩
  | quant₁ _ _ _ _ _ _ h => exact ⟨0, by simp [childList], by simpa [childList] using h⟩
  | quant₂ _ _ _ _ _ _ h => exact ⟨1, by simp [childList], by simpa [childList] using h⟩

/-- A DAG satisfying the invariant contains every subterm of each of its nodes. -/
theorem DInv.closed {g : Dag} (hg : DInv g) :
    ∀ i < g.nodes.size, ∀ c, IsSub c g.nodes[i]! → ∃ j < g.nodes.size, E g.nodes[j]! = E c := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi c hc
    by_cases hce : c = g.nodes[i]!
    · exact ⟨i, hi, by rw [hce]⟩
    · obtain ⟨j, hj, hcj⟩ := hc.child_of_ne hce
      obtain ⟨h1, h2⟩ := hg.2.2.2.2 i hi
      have hjk : j < (g.kids[i]!).length := by omega
      obtain ⟨h3, h4⟩ := h2 j hjk
      obtain ⟨c', hc', hcc'⟩ := hcj.transport h4.symm
      obtain ⟨k, hk, hke⟩ := ih _ h3 (by omega) c' hc'
      exact ⟨k, hk, hke.trans hcc'.symm⟩

/-- A child is a smaller subterm. -/
theorem childList_spec (e : Expression.Expr) (j : Nat) (hj : j < (childList e).length) :
    IsSub (childList e)[j] e ∧ esize (childList e)[j] < esize e := by
  cases e <;> simp only [childList, List.length_cons, List.length_nil] at hj
  case app m f a =>
    match j, hj with
    | 0, _ => exact ⟨.app₁ _ _ _ (.refl _), by simp only [childList, esize, List.getElem_cons_zero]; omega⟩
    | 1, _ => exact ⟨.app₂ _ _ _ (.refl _), by simp only [childList, esize, List.getElem_cons_succ, List.getElem_cons_zero]; omega⟩
  case ite m c t f =>
    match j, hj with
    | 0, _ => exact ⟨.ite₁ _ _ _ _ (.refl _), by simp only [childList, esize, List.getElem_cons_zero]; omega⟩
    | 1, _ => exact ⟨.ite₂ _ _ _ _ (.refl _), by simp only [childList, esize, List.getElem_cons_succ, List.getElem_cons_zero]; omega⟩
    | 2, _ => exact ⟨.ite₃ _ _ _ _ (.refl _), by simp only [childList, esize, List.getElem_cons_succ, List.getElem_cons_zero]; omega⟩
  case eq m a b =>
    match j, hj with
    | 0, _ => exact ⟨.eq₁ _ _ _ (.refl _), by simp only [childList, esize, List.getElem_cons_zero]; omega⟩
    | 1, _ => exact ⟨.eq₂ _ _ _ (.refl _), by simp only [childList, esize, List.getElem_cons_succ, List.getElem_cons_zero]; omega⟩
  case abs m n ty b =>
    match j, hj with
    | 0, _ => exact ⟨.abs _ _ _ _ (.refl _), by simp only [childList, esize, List.getElem_cons_zero]; omega⟩
  case quant m k n ty tr b =>
    match j, hj with
    | 0, _ => exact ⟨.quant₁ _ _ _ _ _ _ (.refl _), by simp only [childList, esize, List.getElem_cons_zero]; omega⟩
    | 1, _ => exact ⟨.quant₂ _ _ _ _ _ _ (.refl _), by simp only [childList, esize, List.getElem_cons_succ, List.getElem_cons_zero]; omega⟩
  all_goals omega

/-- How a DAG grew: old nodes stay, and new ones are subterms of one of `cs`. -/
def DExt (g g' : Dag) (cs : List Expression.Expr) : Prop :=
  g.nodes.size ≤ g'.nodes.size ∧
  (∀ i < g.nodes.size, g'.nodes[i]! = g.nodes[i]! ∧ g'.kids[i]! = g.kids[i]!) ∧
  (∀ i, g.nodes.size ≤ i → i < g'.nodes.size → ∃ c ∈ cs, ∃ c', IsSub c' c ∧ E g'.nodes[i]! = E c')

/-- Growth composes. -/
theorem DExt.trans {g₁ g₂ g₃ : Dag} {cs : List Expression.Expr} (h₁ : DExt g₁ g₂ cs)
    (h₂ : DExt g₂ g₃ cs) : DExt g₁ g₃ cs := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun i hi => ?_, fun i hi hi' => ?_⟩
  · obtain ⟨a, b⟩ := h₁.2.1 i hi
    obtain ⟨c, d⟩ := h₂.2.1 i (by have := h₁.1; omega)
    exact ⟨c.trans a, d.trans b⟩
  · rcases Nat.lt_or_ge i g₂.nodes.size with h | h
    · obtain ⟨c, hc, c', h1, h2⟩ := h₁.2.2 i hi h
      exact ⟨c, hc, c', h1, by rw [(h₂.2.1 i h).1]; exact h2⟩
    · exact h₂.2.2 i h hi'

/-- Growth along fewer roots is growth along more. -/
theorem DExt.mono {g g' : Dag} {cs cs' : List Expression.Expr} (h : DExt g g' cs)
    (hsub : ∀ c ∈ cs, c ∈ cs') : DExt g g' cs' := by
  refine ⟨h.1, h.2.1, fun i hi hi' => ?_⟩
  obtain ⟨c, hc, rest⟩ := h.2.2 i hi hi'
  exact ⟨c, hsub c hc, rest⟩

/-- Growth composes, along both root lists. -/
theorem DExt.trans' {g₁ g₂ g₃ : Dag} {cs cs' : List Expression.Expr} (h₁ : DExt g₁ g₂ cs)
    (h₂ : DExt g₂ g₃ cs') : DExt g₁ g₃ (cs ++ cs') :=
  (h₁.mono (fun _ hc => List.mem_append_left _ hc)).trans
    (h₂.mono (fun _ hc => List.mem_append_right _ hc))

/-- Nothing changed. -/
theorem DExt.refl' (g : Dag) (cs : List Expression.Expr) : DExt g g cs :=
  ⟨Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩, fun _ h h' => absurd h' (by omega)⟩

/-- What `dagNode` on `e` delivers. -/
def DagSpec (g : Dag) (e : Expression.Expr) (r : Nat × Dag) : Prop :=
  DInv r.2 ∧ r.1 < r.2.nodes.size ∧ E r.2.nodes[r.1]! = E e ∧ DExt g r.2 [e] ∧
  (∀ c, IsSub c e → ∃ i < r.2.nodes.size, E r.2.nodes[i]! = E c)

/-- What `dagKids` on `e` delivers. -/
def KidsSpec (g : Dag) (e : Expression.Expr) (r : List Nat × Dag) : Prop :=
  DInv r.2 ∧ DExt g r.2 (childList e) ∧ r.1.length = (childList e).length ∧
  ∀ j (hj : j < r.1.length), r.1[j] < r.2.nodes.size ∧ E r.2.nodes[r.1[j]]! = E (childList e)[j]!

/-- `dagNode` meets `DagSpec` on `e` once `dagKids` meets `KidsSpec` on `e`. -/
theorem dagNode_spec_of_kids (e : Expression.Expr)
    (hk : ∀ g, DInv g → KidsSpec g e ((dagKids e) g)) :
    ∀ g, DInv g → DagSpec g e ((dagNode e) g) := by
  intro g hg
  rw [dagNode_eq]
  simp only [bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure,
    stateT_bind_apply, hashCached_fst]
  have hg1 : DInv { g with cache := (hashCached g.cache e).2 } := hg
  have e1 : ({ g with cache := (hashCached g.cache e).2 } : Dag).nodes = g.nodes := rfl
  have e2 : ({ g with cache := (hashCached g.cache e).2 } : Dag).kids = g.kids := rfl
  generalize ({ g with cache := (hashCached g.cache e).2 } : Dag) = g1 at hg1 e1 e2 ⊢
  have hext1 : DExt g g1 [e] := by
    unfold DExt; rw [e1, e2]; exact DExt.refl' g [e]
  cases hf : g1.find? (hx e) e with
  | some i =>
    obtain ⟨hi, hie⟩ := (Dag.find?_spec hg1 e).1 i hf
    refine ⟨hg1, hi, hie, hext1, fun c hc => ?_⟩
    obtain ⟨c', hc', hcc⟩ := hc.transport hie.symm
    obtain ⟨j, hj, hje⟩ := hg1.closed i hi c' hc'
    exact ⟨j, hj, hje.trans hcc.symm⟩
  | none =>
    have hnone := (Dag.find?_spec hg1 e).2 hf
    simp only [stateT_bind_apply]
    obtain ⟨k1, k2, k3, k4⟩ := hk g1 hg1
    generalize dagKids e g1 = r at *
    obtain ⟨ks, g2⟩ := r
    simp only at k1 k2 k3 k4 ⊢
    have habs : ∀ i < g2.nodes.size, E g2.nodes[i]! ≠ E e := by
      intro i hi hie
      rcases Nat.lt_or_ge i g1.nodes.size with h | h
      · rw [(k2.2.1 i h).1] at hie; exact hnone i h hie
      · obtain ⟨c, hc, c', h1, h2⟩ := k2.2.2 i h hi
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
        have hsz := congrArg esize (hie.symm.trans h2)
        simp only [esize_E] at hsz
        have := h1.size_le
        have hlt := (childList_spec e j hj).2
        omega
    obtain ⟨f1, f2, f3, f4⟩ := dagFinish_spec g2 k1 e ks habs k3 k4
    generalize dagFinish e (hx e) ks g2 = r at *
    obtain ⟨i, g3⟩ := r
    simp only at f1 f2 f3 f4 ⊢
    subst f1
    refine ⟨f2, by rw [f3]; simp, by rw [f3, push_getElem!_size], ?_, ?_⟩
    · have hext3 : DExt g2 g3 [e] := by
        refine ⟨by rw [f3]; simp, fun i hi => ⟨by rw [f3, push_getElem!_lt _ _ hi],
          by rw [f4, push_getElem!_lt _ _ (by rw [k1.1]; exact hi)]⟩, fun i hi hi' => ?_⟩
        rw [f3] at hi' ⊢
        simp only [Array.size_push] at hi'
        have : i = g2.nodes.size := by omega
        subst this
        exact ⟨e, by simp, e, .refl _, by rw [push_getElem!_size]⟩
      have hext2 : DExt g1 g2 [e] := by
        refine ⟨k2.1, k2.2.1, fun i hi hi' => ?_⟩
        obtain ⟨c, hc, c', h1, h2⟩ := k2.2.2 i hi hi'
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
        exact ⟨e, by simp, c', h1.trans (childList_spec e j hj).1, h2⟩
      exact hext1.trans (hext2.trans hext3)
    · intro c hc
      by_cases hce : c = e
      · subst hce; exact ⟨g2.nodes.size, by rw [f3]; simp, by rw [f3, push_getElem!_size]⟩
      · obtain ⟨j, hj, hcj⟩ := hc.child_of_ne hce
        obtain ⟨h1, h2⟩ := k4 j (by omega)
        obtain ⟨c', hc', hcc⟩ := hcj.transport h2.symm
        have hlt : ks[j] < g3.nodes.size := by rw [f3]; simp; omega
        have hnode : g3.nodes[ks[j]]! = g2.nodes[ks[j]]! := by rw [f3, push_getElem!_lt _ _ h1]
        obtain ⟨k, hk, hke⟩ := f2.closed (ks[j]) hlt c' (by rw [hnode]; exact hc')
        exact ⟨k, hk, hke.trans hcc.symm⟩

/-- A node added by an earlier `dagNode` keeps its class through later growth. -/
theorem DagSpec.keep {g g' g'' : Dag} {e : Expression.Expr} {i : Nat} {cs : List Expression.Expr}
    (h : DagSpec g e (i, g')) (h' : DExt g' g'' cs) :
    i < g''.nodes.size ∧ E g''.nodes[i]! = E e :=
  ⟨Nat.lt_of_lt_of_le h.2.1 h'.1, by rw [(h'.2.1 i h.2.1).1]; exact h.2.2.1⟩

/-- **`dagNode` builds the DAG.** From a DAG satisfying the invariant, `dagNode e` returns a DAG
    satisfying it that contains every subterm of `e`, and the index of `e`'s node. -/
theorem dagNode_spec : ∀ (e : Expression.Expr) (g : Dag), DInv g → DagSpec g e ((dagNode e) g) := by
  intro e
  induction e with
  | app m f a ihf iha =>
    refine dagNode_spec_of_kids _ fun g hg => ?_
    simp only [dagKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    have s1 := ihf g hg
    generalize dagNode f g = r1 at *
    obtain ⟨i1, g2⟩ := r1
    have s2 := iha g2 s1.1
    generalize dagNode a g2 = r2 at *
    obtain ⟨i2, g3⟩ := r2
    have k1 := s1.keep s2.2.2.2.1
    refine ⟨s2.1, (s1.2.2.2.1.mono (by simp [childList])).trans
      (s2.2.2.2.1.mono (by simp [childList])), by simp [childList], fun j hj => ?_⟩
    match j, hj with
    | 0, _ => exact k1
    | 1, _ => exact ⟨s2.2.1, s2.2.2.1⟩
  | ite m c t f ihc iht ihf =>
    refine dagNode_spec_of_kids _ fun g hg => ?_
    simp only [dagKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    have s1 := ihc g hg
    generalize dagNode c g = r1 at *
    obtain ⟨i1, g2⟩ := r1
    have s2 := iht g2 s1.1
    generalize dagNode t g2 = r2 at *
    obtain ⟨i2, g3⟩ := r2
    have s3 := ihf g3 s2.1
    generalize dagNode f g3 = r3 at *
    obtain ⟨i3, g4⟩ := r3
    have k1 := s1.keep (s2.2.2.2.1.trans' s3.2.2.2.1)
    have k2 := s2.keep s3.2.2.2.1
    refine ⟨s3.1, ((s1.2.2.2.1.mono (by simp [childList])).trans
      (s2.2.2.2.1.mono (by simp [childList]))).trans (s3.2.2.2.1.mono (by simp [childList])),
      by simp [childList], fun j hj => ?_⟩
    match j, hj with
    | 0, _ => exact k1
    | 1, _ => exact k2
    | 2, _ => exact ⟨s3.2.1, s3.2.2.1⟩
  | eq m a b iha ihb =>
    refine dagNode_spec_of_kids _ fun g hg => ?_
    simp only [dagKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    have s1 := iha g hg
    generalize dagNode a g = r1 at *
    obtain ⟨i1, g2⟩ := r1
    have s2 := ihb g2 s1.1
    generalize dagNode b g2 = r2 at *
    obtain ⟨i2, g3⟩ := r2
    have k1 := s1.keep s2.2.2.2.1
    refine ⟨s2.1, (s1.2.2.2.1.mono (by simp [childList])).trans
      (s2.2.2.2.1.mono (by simp [childList])), by simp [childList], fun j hj => ?_⟩
    match j, hj with
    | 0, _ => exact k1
    | 1, _ => exact ⟨s2.2.1, s2.2.2.1⟩
  | abs m n ty b ih =>
    refine dagNode_spec_of_kids _ fun g hg => ?_
    simp only [dagKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    have s1 := ih g hg
    generalize dagNode b g = r1 at *
    obtain ⟨i1, g2⟩ := r1
    refine ⟨s1.1, s1.2.2.2.1.mono (by simp [childList]), by simp [childList], fun j hj => ?_⟩
    match j, hj with
    | 0, _ => exact ⟨s1.2.1, s1.2.2.1⟩
  | quant m k n ty tr b ihtr ihb =>
    refine dagNode_spec_of_kids _ fun g hg => ?_
    simp only [dagKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    have s1 := ihtr g hg
    generalize dagNode tr g = r1 at *
    obtain ⟨i1, g2⟩ := r1
    have s2 := ihb g2 s1.1
    generalize dagNode b g2 = r2 at *
    obtain ⟨i2, g3⟩ := r2
    have k1 := s1.keep s2.2.2.2.1
    refine ⟨s2.1, (s1.2.2.2.1.mono (by simp [childList])).trans
      (s2.2.2.2.1.mono (by simp [childList])), by simp [childList], fun j hj => ?_⟩
    match j, hj with
    | 0, _ => exact k1
    | 1, _ => exact ⟨s2.2.1, s2.2.2.1⟩
  | _ =>
    refine dagNode_spec_of_kids _ fun g hg => ?_
    simp only [dagKids, pure, stateT_pure_apply]
    exact ⟨hg, DExt.refl' _ _, rfl, fun j hj => absurd hj (by simp)⟩

/-! ## Levels -/

/-- An entry of a modified array. -/
theorem modify_getElem! (xs : Array Nat) (k : Nat) (f : Nat → Nat) {j : Nat} (hj : j < xs.size) :
    (xs.modify k f)[j]! = if k = j then f xs[j]! else xs[j]! := by
  rw [getElem!_pos (xs.modify k f) j (by simpa using hj), getElem!_pos xs j hj,
    Array.getElem_modify]

/-- Pushing the value `v` to the entries `ks` (each to at least `v`). -/
theorem foldl_modify_spec (v : Nat) : ∀ (ks : List Nat) (up : Array Nat),
    let up' := ks.foldl (fun up k => up.modify k (max · v)) up
    up'.size = up.size ∧ (∀ j < up.size, j ∉ ks → up'[j]! = up[j]!) ∧
    (∀ j < up.size, up[j]! ≤ up'[j]!) ∧ (∀ k ∈ ks, k < up.size → v ≤ up'[k]!) := by
  intro ks
  induction ks with
  | nil => intro up; simp
  | cons k ks ih =>
    intro up
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := ih (up.modify k (max · v))
    simp only [Array.size_modify] at h1 h2 h3 h4
    refine ⟨h1, fun j hj hjk => ?_, fun j hj => ?_, fun k' hk' hlt => ?_⟩
    · simp only [List.mem_cons, not_or] at hjk
      rw [h2 j hj hjk.2, modify_getElem! _ _ _ hj, ite_eq_right (Ne.symm hjk.1)]
    · have := h3 j hj
      rw [modify_getElem! _ _ _ hj] at this
      split at this <;> omega
    · rcases List.mem_cons.mp hk' with rfl | hk'
      · have := h3 k' hlt
        rw [modify_getElem! _ _ _ hlt, ite_eq_left rfl] at this
        omega
      · exact h4 k' hk' hlt

/-- The marking bonus of node `i`. -/
abbrev bonus (marked : Array Bool) (i : Nat) : Nat := if marked[i]! then 1 else 0

/-- `propagateUp.go` processes nodes below `i`: it leaves the entries at `i` and above alone,
    only raises entries, and makes every edge out of a processed node satisfy
    `up[j] + bonus j ≤ up[k]`. -/
theorem propagateUp_go_spec (kids : Array (List Nat)) (marked : Array Bool)
    (hk : ∀ i < kids.size, ∀ k ∈ kids[i]!, k < i) :
    ∀ i (up : Array Nat), up.size = kids.size → i ≤ kids.size →
      let up' := propagateUp.go kids marked i up
      up'.size = kids.size ∧ (∀ j, i ≤ j → j < kids.size → up'[j]! = up[j]!) ∧
      (∀ j < kids.size, up[j]! ≤ up'[j]!) ∧
      (∀ j < i, ∀ k ∈ kids[j]!, up'[j]! + bonus marked j ≤ up'[k]!) := by
  intro i
  induction i with
  | zero => intro up hs _; simp [propagateUp.go, hs]
  | succ i ih =>
    intro up hs hi
    simp only [propagateUp.go]
    obtain ⟨f1, f2, f3, f4⟩ := foldl_modify_spec (up[i]! + bonus marked i) (kids[i]!) up
    obtain ⟨g1, g2, g3, g4⟩ := ih _ (by rw [f1, hs]) (by omega)
    refine ⟨g1, fun j hj hjn => ?_, fun j hj => ?_, fun j hj k hkm => ?_⟩
    · rw [g2 j (by omega) hjn, f2 j (by omega) (fun hm => by have := hk i (by omega) j hm; omega)]
    · exact Nat.le_trans (f3 j (by omega)) (g3 j hj)
    · rcases Nat.lt_or_ge j i with hj' | hj'
      · exact g4 j hj' k hkm
      · have hji : j = i := by omega
        subst hji
        have hkl := hk j (by omega) k hkm
        rw [g2 j (Nat.le_refl _) (by omega),
          f2 j (by omega) (fun hm => by have := hk j (by omega) j hm; omega)]
        exact Nat.le_trans (f4 k hkm (by omega)) (g3 k (by omega))

/-- **Levels respect edges.** If every child index is below its parent, `propagateUp` gives
    each node's children at least the node's value plus its bonus. -/
theorem propagateUp_edge (kids : Array (List Nat)) (marked : Array Bool)
    (hk : ∀ i < kids.size, ∀ k ∈ kids[i]!, k < i) :
    (propagateUp kids marked).size = kids.size ∧
    ∀ i < kids.size, ∀ k ∈ kids[i]!,
      (propagateUp kids marked)[i]! + bonus marked i ≤ (propagateUp kids marked)[k]! := by
  obtain ⟨h1, -, -, h4⟩ := propagateUp_go_spec kids marked hk kids.size
    (Array.replicate kids.size 0) (by simp) (Nat.le_refl _)
  exact ⟨h1, h4⟩

/-- **Levels respect proper subterms.** In a DAG satisfying the invariant, with values that
    respect its edges, a node's proper subterm has at least the node's value plus its bonus. -/
theorem up_psub {g : Dag} (hg : DInv g) (marked : Array Bool) (up : Array Nat)
    (hup : ∀ i < g.kids.size, ∀ k ∈ g.kids[i]!, up[i]! + bonus marked i ≤ up[k]!) :
    ∀ i < g.nodes.size, ∀ j < g.nodes.size, ∀ c, IsSub c g.nodes[i]! → c ≠ g.nodes[i]! →
      E c = E g.nodes[j]! → up[i]! + bonus marked i ≤ up[j]! := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi j hj c hc hne hcj
    obtain ⟨jj, hjj, hcjj⟩ := hc.child_of_ne hne
    obtain ⟨h1, h2⟩ := hg.2.2.2.2 i hi
    have hjk : jj < (g.kids[i]!).length := by omega
    obtain ⟨h3, h4⟩ := h2 jj hjk
    have hedge := hup i (by rw [hg.1]; exact hi) _ (List.getElem_mem hjk)
    obtain ⟨c', hc', hcc'⟩ := hcjj.transport h4.symm
    by_cases hce : c' = g.nodes[(g.kids[i]!)[jj]]!
    · have : (g.kids[i]!)[jj] = j :=
        hg.2.2.2.1 _ (by omega) j hj (by rw [← hce, ← hcc', hcj])
      rw [← this]; exact hedge
    · have := ih _ h3 (by omega) j hj c' hc' hce (by rw [← hcc', hcj])
      omega

/-! ## Statements -/

/-- The expression of an `ExprOrNondet`, if any. -/
def eonExprs : ExprOrNondet Expression → List Expression.Expr
  | .det e => [e]
  | .nondet => []

mutual
/-- The user-facing expressions of a statement, in program order (`collectExprs` as a list). -/
def sExprs : Statement → List Expression.Expr
  | .cmd (.cmd (.assert _ e _)) => [e]
  | .cmd (.cmd (.assume _ e _)) => [e]
  | .cmd (.cmd (.cover _ e _)) => [e]
  | .cmd (.cmd (.init _ _ e _)) => eonExprs e
  | .cmd (.cmd (.set _ e _)) => eonExprs e
  | .cmd (.call _ _ args _) => args.filterMap fun | .inArg e => some e | _ => none
  | .block _ ss _ => bExprs ss
  | .ite c tss ess _ => eonExprs c ++ bExprs tss ++ bExprs ess
  | .loop g m inv body _ => eonExprs g ++ m.toList ++ inv.map (·.2) ++ bExprs body
  | .exit _ _ => []
  | .typeDecl _ _ => []
/-- The user-facing expressions of a list of statements, in order. -/
def bExprs : List Statement → List Expression.Expr
  | [] => []
  | s :: ss => sExprs s ++ bExprs ss
end

/-- Pushing the call arguments. -/
theorem foldl_push_args (args : List (CallArg Expression)) (acc : Array Expression.Expr) :
    (args.foldl (fun acc a => match a with | .inArg e => acc.push e | _ => acc) acc).toList =
      acc.toList ++ args.filterMap (fun | .inArg e => some e | _ => none) := by
  induction args generalizing acc with
  | nil => simp
  | cons a as ih =>
    cases a <;> simp [ih]

/-- Pushing the invariants. -/
theorem foldl_push_inv (inv : List (String × Expression.Expr)) (acc : Array Expression.Expr) :
    (inv.foldl (fun acc p => acc.push p.2) acc).toList = acc.toList ++ inv.map (·.2) := by
  induction inv generalizing acc with
  | nil => simp
  | cons a as ih => simp []

mutual
/-- `collectExprsInto` appends `sExprs`. -/
theorem collectExprsInto_stmt (acc : Array Expression.Expr) (s : Statement) :
    (Statement.collectExprsInto acc s).toList = acc.toList ++ sExprs s := by
  match s with
  | .cmd (.cmd (.assert _ e _)) => simp [Statement.collectExprsInto, sExprs]
  | .cmd (.cmd (.assume _ e _)) => simp [Statement.collectExprsInto, sExprs]
  | .cmd (.cmd (.cover _ e _)) => simp [Statement.collectExprsInto, sExprs]
  | .cmd (.cmd (.init _ _ e _)) =>
    cases e <;> simp [Statement.collectExprsInto, sExprs, pushExprOrNondet, eonExprs]
  | .cmd (.cmd (.set _ e _)) =>
    cases e <;> simp [Statement.collectExprsInto, sExprs, pushExprOrNondet, eonExprs]
  | .cmd (.call _ _ args _) =>
    simp only [Statement.collectExprsInto, sExprs]; exact foldl_push_args args acc
  | .block _ ss _ =>
    simp only [Statement.collectExprsInto, sExprs]; exact collectExprsInto_block acc ss
  | .ite c tss ess _ =>
    simp only [Statement.collectExprsInto, sExprs]
    rw [collectExprsInto_block, collectExprsInto_block]
    cases c <;> simp [pushExprOrNondet, eonExprs]
  | .loop g m inv body _ =>
    simp only [Statement.collectExprsInto, sExprs]
    rw [collectExprsInto_block, foldl_push_inv]
    cases g <;> cases m <;> simp [pushExprOrNondet, eonExprs]
  | .exit _ _ => simp [Statement.collectExprsInto, sExprs]
  | .typeDecl _ _ => simp [Statement.collectExprsInto, sExprs]
  termination_by sizeOf s
/-- `collectExprsInto` appends `bExprs`. -/
theorem collectExprsInto_block (acc : Array Expression.Expr) (ss : List Statement) :
    (Statements.collectExprsInto acc ss).toList = acc.toList ++ bExprs ss := by
  match ss with
  | [] => simp [Statements.collectExprsInto, bExprs]
  | s :: rest =>
    simp only [Statements.collectExprsInto, bExprs]
    rw [collectExprsInto_block, collectExprsInto_stmt, List.append_assoc]
  termination_by sizeOf ss
end

/-- `collectExprs` is `bExprs`. -/
theorem collectExprs_eq (ss : Statements) : Statements.collectExprs ss = bExprs ss := by
  simp [Statements.collectExprs, collectExprsInto_block]

/-- The expressions of a mapped `ExprOrNondet`. -/
theorem eonExprs_map (f : Expression.Expr → Expression.Expr) (c : ExprOrNondet Expression) :
    eonExprs (match c with | .det e => .det (f e) | .nondet => .nondet) = (eonExprs c).map f := by
  cases c <;> rfl

mutual
/-- Mapping a statement's expressions maps its expression list. -/
theorem sExprs_mapExpr (f : Expression.Expr → Expression.Expr) (s : Statement) :
    sExprs (Stmt.mapExpr f (Command.mapExpr f) s) = (sExprs s).map f := by
  match s with
  | .cmd (.cmd (.assert _ e _)) => simp [Stmt.mapExpr, Command.mapExpr, sExprs]
  | .cmd (.cmd (.assume _ e _)) => simp [Stmt.mapExpr, Command.mapExpr, sExprs]
  | .cmd (.cmd (.cover _ e _)) => simp [Stmt.mapExpr, Command.mapExpr, sExprs]
  | .cmd (.cmd (.init _ _ e _)) => cases e <;> simp [Stmt.mapExpr, Command.mapExpr, sExprs, eonExprs]
  | .cmd (.cmd (.set _ e _)) => cases e <;> simp [Stmt.mapExpr, Command.mapExpr, sExprs, eonExprs]
  | .cmd (.call _ _ args _) =>
    simp only [Stmt.mapExpr, Command.mapExpr, sExprs]
    induction args with
    | nil => rfl
    | cons a as ih => cases a <;> simp [CallArg.mapInput, ih]
  | .block _ ss _ =>
    simp only [Stmt.mapExpr, sExprs]; exact bExprs_mapExpr f ss
  | .ite c tss ess _ =>
    have h1 := bExprs_mapExpr f tss
    have h2 := bExprs_mapExpr f ess
    cases c <;> simp [Stmt.mapExpr, sExprs, h1, h2, List.map_append, eonExprs]
  | .loop g m inv body _ =>
    have h1 := bExprs_mapExpr f body
    cases g <;> cases m <;>
      simp [Stmt.mapExpr, sExprs, h1, List.map_append, eonExprs]
  | .exit _ _ => simp [Stmt.mapExpr, sExprs]
  | .typeDecl _ _ => simp [Stmt.mapExpr, sExprs]
  termination_by sizeOf s
/-- Mapping a block's expressions maps its expression list. -/
theorem bExprs_mapExpr (f : Expression.Expr → Expression.Expr) (ss : List Statement) :
    bExprs (Block.mapExpr f (Command.mapExpr f) ss) = (bExprs ss).map f := by
  match ss with
  | [] => simp [Block.mapExpr, bExprs]
  | s :: rest =>
    simp only [Block.mapExpr, bExprs, List.map_append]
    rw [sExprs_mapExpr, bExprs_mapExpr]
  termination_by sizeOf ss
end

mutual
/-- Mapping depends only on the function at the statement's expressions. -/
theorem stmt_mapExpr_congr {f g : Expression.Expr → Expression.Expr} (s : Statement)
    (h : ∀ e ∈ sExprs s, f e = g e) :
    Stmt.mapExpr f (Command.mapExpr f) s = Stmt.mapExpr g (Command.mapExpr g) s := by
  match s with
  | .cmd (.cmd (.assert _ e _)) => simp_all [Stmt.mapExpr, Command.mapExpr, sExprs]
  | .cmd (.cmd (.assume _ e _)) => simp_all [Stmt.mapExpr, Command.mapExpr, sExprs]
  | .cmd (.cmd (.cover _ e _)) => simp_all [Stmt.mapExpr, Command.mapExpr, sExprs]
  | .cmd (.cmd (.init _ _ e _)) =>
    cases e <;> simp_all [Stmt.mapExpr, Command.mapExpr, sExprs, eonExprs]
  | .cmd (.cmd (.set _ e _)) =>
    cases e <;> simp_all [Stmt.mapExpr, Command.mapExpr, sExprs, eonExprs]
  | .cmd (.call _ _ args _) =>
    simp only [Stmt.mapExpr, Command.mapExpr, sExprs] at h ⊢
    congr 2
    induction args with
    | nil => rfl
    | cons a as ih =>
      cases a <;> simp_all [CallArg.mapInput]
  | .block _ ss _ =>
    simp only [Stmt.mapExpr, sExprs] at h ⊢
    rw [block_mapExpr_congr ss h]
  | .ite c tss ess _ =>
    simp only [sExprs, List.mem_append] at h
    have h1 := block_mapExpr_congr tss (fun e he => h e (Or.inl (Or.inr he)))
    have h2 := block_mapExpr_congr ess (fun e he => h e (Or.inr he))
    cases c <;> simp_all [Stmt.mapExpr, eonExprs]
  | .loop gd m inv body _ =>
    simp only [sExprs, List.mem_append] at h
    have h1 := block_mapExpr_congr body (fun e he => h e (Or.inr he))
    have h2 : (inv.map fun (l, e) => (l, f e)) = inv.map fun (l, e) => (l, g e) := by
      apply List.map_congr_left
      rintro ⟨l, e⟩ hp
      simp only
      rw [h e (Or.inl (Or.inr (List.mem_map.mpr ⟨(l, e), hp, rfl⟩)))]
    have hm : m.map f = m.map g := by
      cases m with
      | none => rfl
      | some x => simp only [Option.map_some]; rw [h x (Or.inl (Or.inl (Or.inr (by simp))))]
    cases gd with
    | det e =>
      simp only [Stmt.mapExpr, h1, h2, hm, h e (Or.inl (Or.inl (Or.inl (by simp [eonExprs]))))]
    | nondet => simp only [Stmt.mapExpr, h1, h2, hm]
  | .exit _ _ => simp [Stmt.mapExpr]
  | .typeDecl _ _ => simp [Stmt.mapExpr]
  termination_by sizeOf s
/-- Mapping depends only on the function at the block's expressions. -/
theorem block_mapExpr_congr {f g : Expression.Expr → Expression.Expr} (ss : List Statement)
    (h : ∀ e ∈ bExprs ss, f e = g e) :
    Block.mapExpr f (Command.mapExpr f) ss = Block.mapExpr g (Command.mapExpr g) ss := by
  match ss with
  | [] => simp [Block.mapExpr]
  | s :: rest =>
    simp only [bExprs, List.mem_append] at h
    simp only [Block.mapExpr]
    rw [stmt_mapExpr_congr s (fun e he => h e (Or.inl he)),
      block_mapExpr_congr rest (fun e he => h e (Or.inr he))]
  termination_by sizeOf ss
end

mutual
/-- Mapping twice is mapping the composition. -/
theorem stmt_mapExpr_comp (f g : Expression.Expr → Expression.Expr) (s : Statement) :
    Stmt.mapExpr f (Command.mapExpr f) (Stmt.mapExpr g (Command.mapExpr g) s) =
      Stmt.mapExpr (f ∘ g) (Command.mapExpr (f ∘ g)) s := by
  match s with
  | .cmd (.cmd (.assert _ e _)) => simp [Stmt.mapExpr, Command.mapExpr]
  | .cmd (.cmd (.assume _ e _)) => simp [Stmt.mapExpr, Command.mapExpr]
  | .cmd (.cmd (.cover _ e _)) => simp [Stmt.mapExpr, Command.mapExpr]
  | .cmd (.cmd (.init _ _ e _)) => cases e <;> simp [Stmt.mapExpr, Command.mapExpr]
  | .cmd (.cmd (.set _ e _)) => cases e <;> simp [Stmt.mapExpr, Command.mapExpr]
  | .cmd (.call _ _ args _) =>
    simp only [Stmt.mapExpr, Command.mapExpr, List.map_map]
    congr 2
    apply List.map_congr_left
    intro a _
    cases a <;> rfl
  | .block _ ss _ =>
    simp only [Stmt.mapExpr]
    rw [block_mapExpr_comp f g ss]
  | .ite c tss ess _ =>
    have h1 := block_mapExpr_comp f g tss
    have h2 := block_mapExpr_comp f g ess
    cases c <;> simp_all [Stmt.mapExpr]
  | .loop gd m inv body _ =>
    have h1 := block_mapExpr_comp f g body
    cases gd <;> cases m <;> simp_all [Stmt.mapExpr]
  | .exit _ _ => simp [Stmt.mapExpr]
  | .typeDecl _ _ => simp [Stmt.mapExpr]
  termination_by sizeOf s
/-- Mapping twice is mapping the composition. -/
theorem block_mapExpr_comp (f g : Expression.Expr → Expression.Expr) (ss : List Statement) :
    Block.mapExpr f (Command.mapExpr f) (Block.mapExpr g (Command.mapExpr g) ss) =
      Block.mapExpr (f ∘ g) (Command.mapExpr (f ∘ g)) ss := by
  match ss with
  | [] => simp [Block.mapExpr]
  | s :: rest =>
    simp only [Block.mapExpr]
    rw [stmt_mapExpr_comp f g s, block_mapExpr_comp f g rest]
  termination_by sizeOf ss
end

/-- `Statements.mapExprs` is `Block.mapExpr`. -/
theorem mapExprs_eq_block (f : Expression.Expr → Expression.Expr) (ss : Statements) :
    Statements.mapExprs f ss = Block.mapExpr f (Command.mapExpr f) ss := by
  induction ss with
  | nil => simp [Statements.mapExprs, Block.mapExpr]
  | cons s ss ih =>
    simp only [Statements.mapExprs, List.map_cons, Block.mapExpr] at ih ⊢
    rw [← ih]; rfl

section MapM
set_option linter.unusedSectionVars false
variable {σ : Type} (I : σ → Prop)

/-- `List.mapM` with a step that keeps `I` and whose result, read by `P`, is `Q` of its input. -/
theorem list_mapM_spec {α β γ : Type} (k : α → StateM σ β) (P : β → γ) (Q : α → γ)
    (hk : ∀ a s, I s → I ((k a) s).2 ∧ P ((k a) s).1 = Q a) :
    ∀ (l : List α) (s : σ), I s → I ((l.mapM k) s).2 ∧ ((l.mapM k) s).1.map P = l.map Q := by
  intro l
  induction l with
  | nil => intro s hs; exact ⟨hs, rfl⟩
  | cons a as ih =>
    intro s hs
    obtain ⟨h1, h2⟩ := hk a s hs
    obtain ⟨h3, h4⟩ := ih _ h1
    simp only [List.mapM_cons, bind, pure, stateT_bind_apply, stateT_pure_apply, List.map_cons]
      at h3 h4 ⊢
    exact ⟨h3, by rw [h2, h4]⟩

/-- `Option.mapM` with a step that keeps `I` and whose result, read by `P`, is `Q` of its
    input. -/
theorem option_mapM_spec {α β γ : Type} (k : α → StateM σ β) (P : β → γ) (Q : α → γ)
    (hk : ∀ a s, I s → I ((k a) s).2 ∧ P ((k a) s).1 = Q a) :
    ∀ (o : Option α) (s : σ), I s → I ((o.mapM k) s).2 ∧ ((o.mapM k) s).1.map P = o.map Q := by
  intro o s hs
  cases o with
  | none => exact ⟨hs, rfl⟩
  | some x =>
    obtain ⟨h1, h2⟩ := hk x s hs
    refine ⟨h1, ?_⟩
    show Option.map P (some ((k x) s).1) = _
    rw [Option.map_some, h2]; rfl

variable (f : Expression.Expr → StateM σ Expression.Expr) (g : Expression.Expr → Expression.Expr)
  (hf : ∀ e s, I s → I ((f e) s).2 ∧ E ((f e) s).1 = g e)
include hf

/-- A command: mapping its expressions. -/
theorem command_mapExprM_spec (c : Command) (s : σ) (hs : I s) :
    I ((Command.mapExprM f c) s).2 ∧
      Command.mapExpr E ((Command.mapExprM f c) s).1 = Command.mapExpr g c := by
  cases c with
  | cmd c =>
    cases c with
    | assert l e md =>
      obtain ⟨h1, h2⟩ := hf e s hs
      simp only [Command.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply, Command.mapExpr]
      exact ⟨h1, by rw [h2]⟩
    | assume l e md =>
      obtain ⟨h1, h2⟩ := hf e s hs
      simp only [Command.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply, Command.mapExpr]
      exact ⟨h1, by rw [h2]⟩
    | cover l e md =>
      obtain ⟨h1, h2⟩ := hf e s hs
      simp only [Command.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply, Command.mapExpr]
      exact ⟨h1, by rw [h2]⟩
    | init n ty e md =>
      cases e with
      | det e =>
        obtain ⟨h1, h2⟩ := hf e s hs
        simp only [Command.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply,
          Command.mapExpr]
        exact ⟨h1, by rw [h2]⟩
      | nondet => exact ⟨hs, rfl⟩
    | set n e md =>
      cases e with
      | det e =>
        obtain ⟨h1, h2⟩ := hf e s hs
        simp only [Command.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply,
          Command.mapExpr]
        exact ⟨h1, by rw [h2]⟩
      | nondet => exact ⟨hs, rfl⟩
  | call pn tys args md =>
    simp only [Command.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply, Command.mapExpr]
    obtain ⟨h1, h2⟩ := list_mapM_spec I (fun (a : CallArg Expression) => match a with
        | .inArg e => do return CallArg.inArg (← f e)
        | a => pure a) (CallArg.mapInput E) (CallArg.mapInput g)
      (fun a s hs => by
        cases a with
        | inArg e =>
          obtain ⟨h1, h2⟩ := hf e s hs
          simp only [bind, pure, stateT_bind_apply, stateT_pure_apply, CallArg.mapInput]
          exact ⟨h1, by rw [h2]⟩
        | inoutArg x => exact ⟨hs, rfl⟩
        | outArg x => exact ⟨hs, rfl⟩) args s hs
    simp only [bind, pure] at h1 h2
    exact ⟨h1, congrArg (CmdExt.call pn tys · md) h2⟩

mutual
/-- A statement: mapping its expressions monadically computes `g` up to locations. -/
theorem stmt_mapExprM_spec (s : Statement) (st : σ) (hs : I st) :
    I ((Stmt.mapExprM f (Command.mapExprM f) s) st).2 ∧
      Stmt.mapExpr E (Command.mapExpr E) ((Stmt.mapExprM f (Command.mapExprM f) s) st).1 =
        Stmt.mapExpr g (Command.mapExpr g) s := by
  match s with
  | .cmd c =>
    obtain ⟨h1, h2⟩ := command_mapExprM_spec I f g hf c st hs
    simp only [Stmt.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply, Stmt.mapExpr]
    exact ⟨h1, by rw [h2]⟩
  | .block l ss md =>
    obtain ⟨h1, h2⟩ := block_mapExprM_spec ss st hs
    simp only [Stmt.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply, Stmt.mapExpr]
    exact ⟨h1, by rw [h2]⟩
  | .ite (.det c) tss ess md =>
    obtain ⟨h1, h2⟩ := hf c st hs
    obtain ⟨h3, h4⟩ := block_mapExprM_spec tss _ h1
    obtain ⟨h5, h6⟩ := block_mapExprM_spec ess _ h3
    simp only [Stmt.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply, Stmt.mapExpr]
    exact ⟨h5, by rw [h2, h4, h6]⟩
  | .ite .nondet tss ess md =>
    obtain ⟨h3, h4⟩ := block_mapExprM_spec tss st hs
    obtain ⟨h5, h6⟩ := block_mapExprM_spec ess _ h3
    simp only [Stmt.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply, Stmt.mapExpr]
    exact ⟨h5, by rw [h4, h6]⟩
  | .loop (.det gd) m inv body md =>
    obtain ⟨h1, h2⟩ := hf gd st hs
    obtain ⟨h3, h4⟩ := option_mapM_spec I f E g hf m _ h1
    obtain ⟨h5, h6⟩ := list_mapM_spec I
      (fun (p : String × Expression.Expr) => match p with | (l, e) => do return (l, ← f e))
      (fun (p : String × Expression.Expr) => match p with | (l, e) => (l, E e))
      (fun (p : String × Expression.Expr) => match p with | (l, e) => (l, g e))
      (fun ⟨l, e⟩ s hs => by
        obtain ⟨h1, h2⟩ := hf e s hs
        simp only [bind, pure, stateT_bind_apply, stateT_pure_apply]
        exact ⟨h1, by rw [h2]⟩) inv _ h3
    obtain ⟨h7, h8⟩ := block_mapExprM_spec body _ h5
    simp only [bind, pure] at h5 h6 h7 h8
    simp only [Stmt.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply, Stmt.mapExpr]
    exact ⟨h7, by rw [h2, h4, h8]; congr 1⟩
  | .loop .nondet m inv body md =>
    obtain ⟨h3, h4⟩ := option_mapM_spec I f E g hf m st hs
    obtain ⟨h5, h6⟩ := list_mapM_spec I
      (fun (p : String × Expression.Expr) => match p with | (l, e) => do return (l, ← f e))
      (fun (p : String × Expression.Expr) => match p with | (l, e) => (l, E e))
      (fun (p : String × Expression.Expr) => match p with | (l, e) => (l, g e))
      (fun ⟨l, e⟩ s hs => by
        obtain ⟨h1, h2⟩ := hf e s hs
        simp only [bind, pure, stateT_bind_apply, stateT_pure_apply]
        exact ⟨h1, by rw [h2]⟩) inv _ h3
    obtain ⟨h7, h8⟩ := block_mapExprM_spec body _ h5
    simp only [bind, pure] at h5 h6 h7 h8
    simp only [Stmt.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply, Stmt.mapExpr]
    exact ⟨h7, by rw [h4, h8]; congr 1⟩
  | .exit l md =>
    simp only [Stmt.mapExprM, pure, stateT_pure_apply, Stmt.mapExpr]; exact ⟨hs, trivial⟩
  | .typeDecl tc md =>
    simp only [Stmt.mapExprM, pure, stateT_pure_apply, Stmt.mapExpr]; exact ⟨hs, trivial⟩
  termination_by sizeOf s
/-- A block: mapping its expressions monadically computes `g` up to locations. -/
theorem block_mapExprM_spec (ss : List Statement) (st : σ) (hs : I st) :
    I ((Block.mapExprM f (Command.mapExprM f) ss) st).2 ∧
      Block.mapExpr E (Command.mapExpr E) ((Block.mapExprM f (Command.mapExprM f) ss) st).1 =
        Block.mapExpr g (Command.mapExpr g) ss := by
  match ss with
  | [] => simp only [Block.mapExprM, pure, stateT_pure_apply, Block.mapExpr]; exact ⟨hs, trivial⟩
  | s :: rest =>
    obtain ⟨h1, h2⟩ := stmt_mapExprM_spec s st hs
    obtain ⟨h3, h4⟩ := block_mapExprM_spec rest _ h1
    simp only [Block.mapExprM, bind, pure, stateT_bind_apply, stateT_pure_apply, Block.mapExpr]
    exact ⟨h3, by rw [h2, h4]⟩
  termination_by sizeOf ss
end

/-- **Rewriting a body monadically.** With a step `f` that keeps `I` and computes `g` up to
    locations, `Statements.mapExprsM f` keeps `I` and computes `Statements.mapExprs g` up to
    locations. -/
theorem mapExprsM_spec (ss : Statements) (st : σ) (hs : I st) :
    I ((Statements.mapExprsM f ss) st).2 ∧
      Statements.mapExprs E ((Statements.mapExprsM f ss) st).1 = Statements.mapExprs g ss := by
  induction ss generalizing st with
  | nil => exact ⟨hs, rfl⟩
  | cons s ss ih =>
    obtain ⟨h1, h2⟩ := stmt_mapExprM_spec I f g hf s st hs
    obtain ⟨h3, h4⟩ := ih _ h1
    simp only [Statements.mapExprsM, List.mapM_cons, bind, pure, stateT_bind_apply,
      stateT_pure_apply, Statements.mapExprs, List.map_cons] at h3 h4 ⊢
    exact ⟨h3, by rw [← h4]; exact congrArg (· :: _) h2⟩

end MapM

/-! ## Facts about naming a list of subexpressions -/

/-- A bvar-free expression types the same in every context. -/
theorem typeCheck_ctx_of_noBVar : ∀ (e : Expression.Expr) (ctx : List LMonoTy),
    LExpr.hasBVar e = false → LExpr.typeCheck ctx e = LExpr.typeCheck [] e := by
  intro e
  induction e with
  | bvar m i => intro ctx h; simp [LExpr.hasBVar] at h
  | app m f a ihf iha =>
    intro ctx h; simp only [LExpr.hasBVar, Bool.or_eq_false_iff] at h
    simp only [LExpr.typeCheck, ihf ctx h.1, iha ctx h.2]
  | ite m c t f ihc iht ihf =>
    intro ctx h; simp only [LExpr.hasBVar, Bool.or_eq_false_iff] at h
    simp only [LExpr.typeCheck, ihc ctx h.1.1, iht ctx h.1.2, ihf ctx h.2]
  | eq m a b iha ihb =>
    intro ctx h; simp only [LExpr.hasBVar, Bool.or_eq_false_iff] at h
    simp only [LExpr.typeCheck, iha ctx h.1, ihb ctx h.2]
  | abs m n ty b ih =>
    intro ctx h; simp only [LExpr.hasBVar] at h
    cases ty with
    | none => rfl
    | some ty => simp only [LExpr.typeCheck, ih _ h]
  | quant m k n ty tr b ihtr ihb =>
    intro ctx h; simp only [LExpr.hasBVar, Bool.or_eq_false_iff] at h
    cases ty with
    | none => rfl
    | some ty => simp only [LExpr.typeCheck, ihtr _ h.1, ihb _ h.2]
  | op m o ty => intro ctx _; cases ty <;> rfl
  | fvar m x ty => intro ctx _; cases ty <;> rfl
  | const m c => intro ctx _; rfl

/-- `ρL` names a class with the variable of its entry in the list. -/
theorem ρL_eq_some {L : List NTarget} {c v : Expression.Expr} (h : ρL L c = some v) :
    ∃ t ∈ L, t.1 = c ∧ v = cseVar t.2.1 t.2.2 := by
  unfold ρL at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  have := List.find?_some ht
  exact ⟨t, List.mem_of_find?_eq_some ht, by simpa using this, rfl⟩

/-- Naming typed, bvar-free subexpressions with variables of their types keeps the type. -/
theorem typeCheck_rwE (L : List NTarget)
    (hL : ∀ t ∈ L, LExpr.typeCheck [] t.1 = some t.2.2 ∧ LExpr.hasBVar t.1 = false) :
    ∀ (e : Expression.Expr) (ctx : List LMonoTy),
      LExpr.typeCheck ctx (rwE (ρL L) e) = LExpr.typeCheck ctx e := by
  have hnode : ∀ (e : Expression.Expr) ctx,
      LExpr.typeCheck ctx (rwKids (ρL L) e) = LExpr.typeCheck ctx e →
      LExpr.typeCheck ctx (rwE (ρL L) e) = LExpr.typeCheck ctx e := by
    intro e ctx hk
    rw [rwE_eq]
    cases hρ : ρL L e with
    | none => exact hk
    | some v =>
      obtain ⟨t, ht, rfl, rfl⟩ := ρL_eq_some hρ
      obtain ⟨h1, h2⟩ := hL t ht
      simp only [Option.getD_some, cseVar, LExpr.typeCheck]
      rw [typeCheck_ctx_of_noBVar _ _ h2, h1]
  intro e
  induction e with
  | app m f a ihf iha => intro ctx; exact hnode _ ctx (by simp only [rwKids, LExpr.typeCheck, ihf, iha])
  | ite m c t f ihc iht ihf =>
    intro ctx; exact hnode _ ctx (by simp only [rwKids, LExpr.typeCheck, ihc, iht, ihf])
  | eq m a b iha ihb => intro ctx; exact hnode _ ctx (by simp only [rwKids, LExpr.typeCheck, iha, ihb])
  | abs m n ty b ih =>
    intro ctx; exact hnode _ ctx (by cases ty <;> simp only [rwKids, LExpr.typeCheck, ih])
  | quant m k n ty tr b ihtr ihb =>
    intro ctx; exact hnode _ ctx (by cases ty <;> simp only [rwKids, LExpr.typeCheck, ihtr, ihb])
  | _ => intro ctx; exact hnode _ ctx rfl

/-- `rwKids` keeps the type too. -/
theorem typeCheck_rwKids (L : List NTarget)
    (hL : ∀ t ∈ L, LExpr.typeCheck [] t.1 = some t.2.2 ∧ LExpr.hasBVar t.1 = false)
    (e : Expression.Expr) (ctx : List LMonoTy) :
    LExpr.typeCheck ctx (rwKids (ρL L) e) = LExpr.typeCheck ctx e := by
  cases e with
  | app m f a => simp only [rwKids, LExpr.typeCheck, typeCheck_rwE L hL]
  | ite m c t f => simp only [rwKids, LExpr.typeCheck, typeCheck_rwE L hL]
  | eq m a b => simp only [rwKids, LExpr.typeCheck, typeCheck_rwE L hL]
  | abs m n ty b => cases ty <;> simp only [rwKids, LExpr.typeCheck, typeCheck_rwE L hL]
  | quant m k n ty tr b => cases ty <;> simp only [rwKids, LExpr.typeCheck, typeCheck_rwE L hL]
  | _ => rfl

/-- The variables of a rewritten expression: its own, or the names of the subterms it
    replaced. -/
theorem vars_rwE (L : List NTarget) : ∀ (e : Expression.Expr), ∀ x ∈ vars (rwE (ρL L) e),
    x ∈ vars e ∨ ∃ t ∈ L, x = cseName t.2.1 ∧ IsSub t.1 e := by
  have hnode : ∀ (e : Expression.Expr),
      (∀ x ∈ vars (rwKids (ρL L) e), x ∈ vars e ∨ ∃ t ∈ L, x = cseName t.2.1 ∧ IsSub t.1 e) →
      ∀ x ∈ vars (rwE (ρL L) e), x ∈ vars e ∨ ∃ t ∈ L, x = cseName t.2.1 ∧ IsSub t.1 e := by
    intro e hk x hx
    rw [rwE_eq] at hx
    cases hρ : ρL L e with
    | none => rw [hρ] at hx; exact hk x hx
    | some v =>
      rw [hρ] at hx
      obtain ⟨t, ht, rfl, rfl⟩ := ρL_eq_some hρ
      simp only [vars, cseVar, Option.getD_some, LExpr.LExpr.getVars, List.mem_cons, List.not_mem_nil, or_false] at hx
      exact Or.inr ⟨t, ht, hx, .refl _⟩
  intro e
  induction e with
  | app m f a ihf iha =>
    refine hnode _ fun x hx => ?_
    simp only [rwKids, vars, LExpr.LExpr.getVars, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · rcases ihf x hx with h | ⟨t, ht, h1, h2⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨t, ht, h1, .app₁ _ _ _ h2⟩
    · rcases iha x hx with h | ⟨t, ht, h1, h2⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨t, ht, h1, .app₂ _ _ _ h2⟩
  | ite m c t f ihc iht ihf =>
    refine hnode _ fun x hx => ?_
    simp only [rwKids, vars, LExpr.LExpr.getVars, List.mem_append] at hx ⊢
    rcases hx with (hx | hx) | hx
    · rcases ihc x hx with h | ⟨t, ht, h1, h2⟩
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr ⟨t, ht, h1, .ite₁ _ _ _ _ h2⟩
    · rcases iht x hx with h | ⟨t, ht, h1, h2⟩
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr ⟨t, ht, h1, .ite₂ _ _ _ _ h2⟩
    · rcases ihf x hx with h | ⟨t, ht, h1, h2⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨t, ht, h1, .ite₃ _ _ _ _ h2⟩
  | eq m a b iha ihb =>
    refine hnode _ fun x hx => ?_
    simp only [rwKids, vars, LExpr.LExpr.getVars, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · rcases iha x hx with h | ⟨t, ht, h1, h2⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨t, ht, h1, .eq₁ _ _ _ h2⟩
    · rcases ihb x hx with h | ⟨t, ht, h1, h2⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨t, ht, h1, .eq₂ _ _ _ h2⟩
  | abs m n ty b ih =>
    refine hnode _ fun x hx => ?_
    simp only [rwKids, vars, LExpr.LExpr.getVars] at hx ⊢
    rcases ih x hx with h | ⟨t, ht, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, h1, .abs _ _ _ _ h2⟩
  | quant m k n ty tr b ihtr ihb =>
    refine hnode _ fun x hx => ?_
    simp only [rwKids, vars, LExpr.LExpr.getVars, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · rcases ihtr x hx with h | ⟨t, ht, h1, h2⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨t, ht, h1, .quant₁ _ _ _ _ _ _ h2⟩
    · rcases ihb x hx with h | ⟨t, ht, h1, h2⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨t, ht, h1, .quant₂ _ _ _ _ _ _ h2⟩
  | _ => exact hnode _ fun x hx => Or.inl hx

/-- Erasing keeps the variables. -/
@[simp] theorem vars_E (e : Expression.Expr) : vars (E e) = vars e := by
  induction e <;> simp_all [vars, LExpr.LExpr.getVars]

/-- A subterm's variables are variables of the term. -/
theorem IsSub.vars_subset {c e : Expression.Expr} (h : IsSub c e) : ∀ x ∈ vars c, x ∈ vars e := by
  induction h <;> intro x hx <;> simp_all [vars, LExpr.LExpr.getVars]

/-- The variables of a node with rewritten children: its own, or the names of proper subterms. -/
theorem vars_rwKids (L : List NTarget) (e : Expression.Expr) : ∀ x ∈ vars (rwKids (ρL L) e),
    x ∈ vars e ∨ ∃ t ∈ L, x = cseName t.2.1 ∧ IsPSub t.1 e := by
  have hp : ∀ (c : Expression.Expr) (j : Nat) (hj : j < (childList e).length),
      IsSub c (childList e)[j] → IsPSub c e := fun c j hj hc => by
    have h1 := childList_spec e j hj
    refine ⟨hc.trans h1.1, fun he => ?_⟩
    subst he
    have := hc.size_le; omega
  have hv : ∀ (j : Nat) (hj : j < (childList e).length), ∀ x ∈ vars (childList e)[j], x ∈ vars e :=
    fun j hj => (childList_spec e j hj).1.vars_subset
  have hk : ∀ (j : Nat) (hj : j < (childList e).length), ∀ x ∈ vars (rwE (ρL L) (childList e)[j]),
      x ∈ vars e ∨ ∃ t ∈ L, x = cseName t.2.1 ∧ IsPSub t.1 e := by
    intro j hj x hx
    rcases vars_rwE L _ x hx with h | ⟨t, ht, h1, h2⟩
    · exact Or.inl (hv j hj x h)
    · exact Or.inr ⟨t, ht, h1, hp _ j hj h2⟩
  intro x hx
  cases e with
  | app m f a =>
    simp only [rwKids, vars, LExpr.LExpr.getVars, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hk 0 (by simp [childList]) x hx
    · exact hk 1 (by simp [childList]) x hx
  | ite m c t f =>
    simp only [rwKids, vars, LExpr.LExpr.getVars, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact hk 0 (by simp [childList]) x hx
    · exact hk 1 (by simp [childList]) x hx
    · exact hk 2 (by simp [childList]) x hx
  | eq m a b =>
    simp only [rwKids, vars, LExpr.LExpr.getVars, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hk 0 (by simp [childList]) x hx
    · exact hk 1 (by simp [childList]) x hx
  | abs m n ty b =>
    simp only [rwKids, vars, LExpr.LExpr.getVars] at hx
    exact hk 0 (by simp [childList]) x hx
  | quant m k n ty tr b =>
    simp only [rwKids, vars, LExpr.LExpr.getVars, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hk 0 (by simp [childList]) x hx
    · exact hk 1 (by simp [childList]) x hx
  | _ => exact Or.inl hx

/-- Entries of a list with distinct keys are determined by their keys. -/
theorem eq_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b := by
  intro l
  induction l with
  | nil => intro _ a b ha; simp at ha
  | cons x xs ih =>
    intro hn a b ha hb hab
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · rw [h1, h2]
    · subst h1; exact absurd hab.symm (hn.1 b h2)
    · subst h2; exact absurd hab (hn.1 a h1)
    · exact ih hn.2 h1 h2 hab

/-- With distinct classes, `ρL` names an entry's class with that entry's variable. -/
theorem ρL_of_mem_nodup {L : List NTarget} (hn : (L.map (·.1)).Nodup) {t : NTarget} (ht : t ∈ L) :
    ρL L t.1 = some (cseVar t.2.1 t.2.2) := by
  obtain ⟨t', ht', hρ⟩ := ρL_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩)
  rw [hρ]
  obtain ⟨t'', ht'', h1, h2⟩ := ρL_eq_some hρ
  have := eq_of_nodup_map hn ht'' ht h1
  subst this
  rw [h2]

/-- Two lists with distinct classes, one inside the other, name a class of the smaller one
    alike. -/
theorem ρL_eq_of_sub {L₁ L₂ : List NTarget} (hn₁ : (L₁.map (·.1)).Nodup)
    (hn₂ : (L₂.map (·.1)).Nodup) (hsub : ∀ t ∈ L₂, t ∈ L₁) (c : Expression.Expr)
    (hc : c ∈ L₁.map (·.1) → c ∈ L₂.map (·.1)) : ρL L₁ c = ρL L₂ c := by
  by_cases h : c ∈ L₂.map (·.1)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
    rw [ρL_of_mem_nodup hn₂ ht, ρL_of_mem_nodup hn₁ (hsub t ht)]
  · rw [ρL_eq_none h, ρL_eq_none (fun h' => h (hc h'))]

/-! ## Well-formed results -/

/-- The variables of a body's expressions. -/
def bodyVars (body : Statements) : List CoreIdent :=
  (Statements.collectExprs body).flatMap vars

end Core.CSE

namespace Core.CSE

open Lambda Imperative

public section

/-- No expression of `body` mentions a generated name with index `idx` or more. Nothing
    reserves the `$__cse.` prefix in source programs; in the default pipelines the symbolic
    evaluators rename every program variable before this phase runs, which makes the
    generated names fresh. -/
def FreshCSENames (body : Statements) (idx : Nat) : Prop :=
  ∀ k, idx ≤ k → ⟨s!"{cseVarPrefix}{k}", ()⟩ ∉
    (Statements.collectExprs body).flatMap (fun e => LExpr.LExpr.getVars e)

/-- What a CSE pass delivers on `body` from index `idx`: declarations `ds`
    (index, type, right-hand side) followed by a body `rest` such that
    * the indices are `idx, …, idx' - 1`, each declared once;
    * each right-hand side has its declared type, and, once the declarations are inlined into
      it, is a subterm of `body` of that type without bound variables, up to locations;
    * a right-hand side mentions only names declared before it and variables of `body`, and
      `rest` mentions only declared names and variables of `body`;
    * inlining the declarations into `rest` (the last declared first) gives `body` back, up to
      locations. -/
def CSEWellFormed (body : Statements) (idx : Nat) (out : Statements) (idx' : Nat) : Prop :=
  ∃ (ds : List (Nat × LMonoTy × Expression.Expr)) (rest : Statements),
    out = ds.map (fun d => Statement.init ⟨s!"{cseVarPrefix}{d.1}", ()⟩ (LTy.forAll [] d.2.1)
      (.det d.2.2) .empty) ++ rest ∧
    idx ≤ idx' ∧ (ds.map (·.1)).Perm (List.range' idx (idx' - idx)) ∧
    (∀ d ∈ ds, LExpr.typeCheck [] d.2.2 = some d.2.1) ∧
    (∀ d ∈ ds, ∃ r ∈ Statements.collectExprs body, ∃ c, IsSub c r ∧
      LExpr.typeCheck [] c = some d.2.1 ∧ LExpr.hasBVar c = false ∧
      Core.eraseLocs (ds.foldr (fun d e =>
        LExpr.substFvar e ⟨s!"{cseVarPrefix}{d.1}", ()⟩ d.2.2) d.2.2) = Core.eraseLocs c) ∧
    (∀ i (h : i < ds.length), ∀ x ∈ LExpr.LExpr.getVars ds[i].2.2,
      (∃ j, ∃ (hj : j < i), x = ⟨s!"{cseVarPrefix}{(ds[j]'(by omega)).1}", ()⟩) ∨
      x ∈ (Statements.collectExprs body).flatMap (fun e => LExpr.LExpr.getVars e)) ∧
    (∀ e ∈ Statements.collectExprs rest, ∀ x ∈ LExpr.LExpr.getVars e,
      (∃ d ∈ ds, x = ⟨s!"{cseVarPrefix}{d.1}", ()⟩) ∨
      x ∈ (Statements.collectExprs body).flatMap (fun e => LExpr.LExpr.getVars e)) ∧
    Statements.mapExprs (fun e => Core.eraseLocs (ds.foldr (fun d e =>
        LExpr.substFvar e ⟨s!"{cseVarPrefix}{d.1}", ()⟩ d.2.2) e)) rest =
      Statements.mapExprs Core.eraseLocs body

end

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- In a list sorted by non-increasing key, an entry with a larger key comes first. -/
theorem idx_lt_of_pairwise {α : Type} {key : α → Nat} {Z : List α}
    (hs : Z.Pairwise (fun a b => key b ≤ key a)) {i j : Nat} (hi : i < Z.length)
    (hj : j < Z.length) (hk : key Z[i] < key Z[j]) : j < i := by
  rcases Nat.lt_or_ge j i with h | h
  · exact h
  · rcases Nat.lt_or_eq_of_le h with h | h
    · have := List.pairwise_iff_getElem.mp hs i j hi hj h
      omega
    · subst h; omega

/-- **The single-pass shape is well formed.** Named subexpressions `named` (index, node, type,
    level) with distinct classes, typed and bvar-free, below the body's expressions, whose
    levels grow towards proper subterms; declarations `Z` listing them by non-increasing level,
    each with a right-hand side equal (up to locations) to its node with the children
    rewritten; and a body `body'` equal (up to locations) to `body` rewritten. Then the
    declarations followed by `body'` are well formed. -/
theorem wf_of_named (body body' : Statements) (idx : Nat)
    (named : List (Nat × Expression.Expr × LMonoTy × Nat))
    (Z : List ((Nat × Expression.Expr × LMonoTy × Nat) × Expression.Expr))
    (hidx : named.map (·.1) = List.range' idx named.length)
    (hcls : (named.map (fun t => E t.2.1)).Nodup)
    (hty : ∀ t ∈ named, LExpr.typeCheck [] t.2.1 = some t.2.2.1 ∧ LExpr.hasBVar t.2.1 = false)
    (hsub : ∀ t ∈ named, ∃ r ∈ Statements.collectExprs body, ∃ c, IsSub c r ∧ E t.2.1 = E c)
    (hlvl : ∀ t ∈ named, ∀ t' ∈ named, IsPSub (E t'.2.1) (E t.2.1) → t.2.2.2 < t'.2.2.2)
    (hperm : (Z.map (·.1)).Perm named)
    (hsort : Z.Pairwise (fun a b => b.1.2.2.2 ≤ a.1.2.2.2))
    (hrhs : ∀ z ∈ Z, E z.2 = rwKids (ρL (named.map fun t => (E t.2.1, t.1, t.2.2.1))) (E z.1.2.1))
    (hbody : Statements.mapExprs E body' =
      Statements.mapExprs (fun e => rwE (ρL (named.map fun t => (E t.2.1, t.1, t.2.2.1))) (E e)) body)
    (hfresh : FreshCSENames body idx) :
    CSEWellFormed body idx ((Z.map fun z => (z.1.1, z.1.2.2.1, z.2)).map (fun d =>
      Statement.init ⟨s!"{cseVarPrefix}{d.1}", ()⟩ (LTy.forAll [] d.2.1) (.det d.2.2) .empty)
        ++ body') (idx + named.length) := by
  -- The replacement, in naming order and in declaration order.
  generalize hLc : (named.map fun t => (E t.2.1, t.1, t.2.2.1)) = Lc at hrhs hbody
  have hLc1 : Lc.map (·.1) = named.map (fun t => E t.2.1) := by rw [← hLc, List.map_map]; rfl
  have hLcn : (Lc.map (·.1)).Nodup := by rw [hLc1]; exact hcls
  let Zt := Z.map fun z => ((E z.1.2.1, z.1.1, z.1.2.2.1), z.2)
  have hZt1 : (Zt.map (·.1)).Perm Lc := by
    have : Zt.map (·.1) = (Z.map (·.1)).map (fun t => (E t.2.1, t.1, t.2.2.1)) := by
      simp [Zt, List.map_map]
    rw [this, ← hLc]; exact hperm.map _
  have hZtn : ((Zt.map (·.1)).map (·.1)).Nodup := (hZt1.map _).nodup_iff.mpr hLcn
  have hZti : (Zt.map (·.1.2.1)).Nodup := by
    have : Zt.map (·.1.2.1) = (Z.map (·.1)).map (·.1) := by simp [Zt, List.map_map]
    rw [this, (hperm.map _).nodup_iff, hidx]; exact List.nodup_range'
  have hρ : ∀ c, ρL Lc c = ρL (Zt.map (·.1)) c := fun c =>
    ρL_eq_of_sub hLcn hZtn (fun t ht => hZt1.mem_iff.mp ht) c
      (fun h => (hZt1.map (·.1)).mem_iff.mpr h)
  have hρ' : ρL Lc = ρL (Zt.map (·.1)) := funext hρ
  -- Named entries and their declarations.
  have hmemZ : ∀ t ∈ named, ∃ j, ∃ hj : j < Z.length, Z[j].1 = t := fun t ht => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (hperm.mem_iff.mpr ht)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hz
    exact ⟨j, hj, rfl⟩
  have hZnamed : ∀ z ∈ Z, z.1 ∈ named := fun z hz => hperm.mem_iff.mp (List.mem_map.mpr ⟨z, hz, rfl⟩)
  have hLcnamed : ∀ t ∈ Lc, ∃ t' ∈ named, t = (E t'.2.1, t'.1, t'.2.2.1) := fun t ht => by
    rw [← hLc] at ht; obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht; exact ⟨t', ht', rfl⟩
  have hLty : ∀ t ∈ Lc, LExpr.typeCheck [] t.1 = some t.2.2 ∧ LExpr.hasBVar t.1 = false := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := hLcnamed t ht
    simpa using hty t' ht'
  have hbv : ∀ r ∈ Statements.collectExprs body, ∀ x ∈ vars r,
      x ∈ (Statements.collectExprs body).flatMap (fun e => LExpr.LExpr.getVars e) :=
    fun r hr x hx => List.mem_flatMap.mpr ⟨r, hr, hx⟩
  -- The rewritten body's expressions.
  have hexprs : (Statements.collectExprs body').map E =
      (Statements.collectExprs body).map (fun e => rwE (ρL Lc) (E e)) := by
    have := congrArg Statements.collectExprs hbody
    rw [mapExprs_eq_block, mapExprs_eq_block, collectExprs_eq, collectExprs_eq,
      bExprs_mapExpr, bExprs_mapExpr] at this
    rw [collectExprs_eq, collectExprs_eq]; exact this
  -- Unfolding undoes the naming.
  have hds : Zt.map (fun z => (z.1.2.1, z.1.2.2, z.2)) = Z.map fun z => (z.1.1, z.1.2.2.1, z.2) := by
    simp [Zt, List.map_map]
  have hunf : ∀ e, E e = e → (∀ z ∈ Z.map (fun z => (z.1.1, z.1.2.2.1, z.2)), cseName z.1 ∉ vars e) →
      E (unfold (Z.map fun z => (z.1.1, z.1.2.2.1, z.2)) (rwE (ρL Lc) e)) = e := by
    intro e he hef
    rw [← hds, hρ']
    refine unfold_rwE Zt (by rw [List.map_map] at hZtn; exact hZtn) hZti ?_ e he ?_
    · intro i hi
      have hiZ : i < Z.length := by simpa [Zt] using hi
      have hZti' : Zt[i] = ((E Z[i].1.2.1, Z[i].1.1, Z[i].1.2.2.1), Z[i].2) := by simp [Zt]
      rw [hZti']
      simp only
      rw [hrhs _ (List.getElem_mem hiZ)]
      apply rwKids_congr
      intro c hc
      have hpre : (((Zt.take i).map (·.1)).map (·.1)).Nodup :=
        (((List.take_sublist i Zt).map (·.1)).map (·.1)).nodup hZtn
      refine ρL_eq_of_sub hLcn hpre (fun t ht => ?_) c (fun hcm => ?_)
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ht
        exact hZt1.mem_iff.mp (List.mem_map.mpr ⟨z, List.mem_of_mem_take hz, rfl⟩)
      · rw [hLc1] at hcm
        obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hcm
        obtain ⟨j, hj, hZj⟩ := hmemZ t' ht'
        have hl := hlvl _ (hZnamed _ (List.getElem_mem hiZ)) t' ht' hc
        have hji : j < i := idx_lt_of_pairwise (key := fun z => z.1.2.2.2) hsort hiZ hj
          (by simp only [hZj]; exact hl)
        refine List.mem_map.mpr ⟨Zt[j].1, List.mem_map.mpr ⟨Zt[j], ?_, rfl⟩, by simp [Zt, hZj]⟩
        exact List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩
    · intro z hz hzv
      exact hef (z.1.2.1, z.1.2.2, z.2) (by rw [← hds]; exact List.mem_map.mpr ⟨z, hz, rfl⟩) hzv
  refine ⟨Z.map fun z => (z.1.1, z.1.2.2.1, z.2), body', rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- indices
    rw [show idx + named.length - idx = named.length by omega, ← hidx,
      show (Z.map fun z => (z.1.1, z.1.2.2.1, z.2)).map (·.1) = (Z.map (·.1)).map (·.1) by
        simp [List.map_map]]
    exact hperm.map (·.1)
  · -- types
    intro d hd
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hd
    have ht := hty z.1 (hZnamed z hz)
    rw [← typeCheck_E, hrhs z hz, typeCheck_rwKids Lc hLty, typeCheck_E, ht.1]
  · -- declarations unfold to subterms of the body
    intro d hd
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hd
    have ht := hty z.1 (hZnamed z hz)
    obtain ⟨r, hr, c, hc, hce⟩ := hsub z.1 (hZnamed z hz)
    refine ⟨r, hr, c, hc, by rw [← typeCheck_E, ← hce, typeCheck_E, ht.1],
      by rw [← hasBVar_E, ← hce, hasBVar_E, ht.2], ?_⟩
    show E (unfold (Z.map fun z => (z.1.1, z.1.2.2.1, z.2)) z.2) = E c
    rw [← E_unfold_E, hrhs z hz, ← hce]
    have hfr : ∀ x ∈ vars (E z.1.2.1), x ∈ (Statements.collectExprs body).flatMap
        (fun e => LExpr.LExpr.getVars e) := by
      intro x hx
      rw [hce, vars_E] at hx
      exact hbv r hr x (hc.vars_subset x hx)
    have hnot : ∀ d ∈ Z.map (fun z => (z.1.1, z.1.2.2.1, z.2)), ∀ e,
        (∀ x ∈ vars e, x ∈ (Statements.collectExprs body).flatMap (fun e => LExpr.LExpr.getVars e)) →
        cseName d.1 ∉ vars e := by
      intro d hd e he hv
      obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hd
      have hk : z'.1.1 ∈ List.range' idx named.length := by
        rw [← hidx]; exact List.mem_map.mpr ⟨z'.1, hZnamed z' hz', rfl⟩
      rw [List.mem_range'_1] at hk
      exact hfresh _ hk.1 (he _ hv)
    refine E_unfold_rwKids _ _ _ (E_E _) (fun d hd => hnot d hd _ hfr) ?_
    intro k hk hne hkE
    exact hunf k hkE (fun d hd => hnot d hd k (fun x hx => hfr x (hk.vars_subset x hx)))
  · -- right-hand sides
    intro i hi x hx
    simp only [List.length_map] at hi
    simp only [List.getElem_map] at hx ⊢
    have hx' : x ∈ vars (rwKids (ρL Lc) (E Z[i].1.2.1)) := by
      rw [← hrhs _ (List.getElem_mem hi), vars_E]; exact hx
    rcases vars_rwKids Lc _ x hx' with h | ⟨t, ht, rfl, hps⟩
    · right
      obtain ⟨r, hr, c, hc, hce⟩ := hsub _ (hZnamed _ (List.getElem_mem hi))
      rw [vars_E] at h
      have : x ∈ vars (E c) := by rw [← hce, vars_E]; exact h
      rw [vars_E] at this
      exact hbv r hr x (hc.vars_subset x this)
    · left
      obtain ⟨t', ht', rfl⟩ := hLcnamed t ht
      obtain ⟨j, hj, hZj⟩ := hmemZ t' ht'
      have hl := hlvl _ (hZnamed _ (List.getElem_mem hi)) t' ht' hps
      have hji : j < i := idx_lt_of_pairwise (key := fun z => z.1.2.2.2) hsort hi hj
        (by simp only [hZj]; exact hl)
      exact ⟨j, hji, by simp [hZj]; rfl⟩
  · -- the body
    intro e he x hx
    have hEe : E e ∈ (Statements.collectExprs body').map E := List.mem_map.mpr ⟨e, he, rfl⟩
    rw [hexprs] at hEe
    obtain ⟨r, hr, hre⟩ := List.mem_map.mp hEe
    have hx' : x ∈ vars (rwE (ρL Lc) (E r)) := by rw [hre, vars_E]; exact hx
    rcases vars_rwE Lc _ x hx' with h | ⟨t, ht, rfl, -⟩
    · right; rw [vars_E] at h; exact hbv r hr x h
    · left
      obtain ⟨t', ht', rfl⟩ := hLcnamed t ht
      obtain ⟨j, hj, hZj⟩ := hmemZ t' ht'
      exact ⟨(Z[j].1.1, Z[j].1.2.2.1, Z[j].2), List.mem_map.mpr ⟨Z[j], List.getElem_mem hj, rfl⟩,
        by simp [hZj]; rfl⟩
  · -- unfolding
    have hpt : ∀ r ∈ Statements.collectExprs body,
        E (unfold (Z.map fun z => (z.1.1, z.1.2.2.1, z.2)) (rwE (ρL Lc) (E r))) = E r := by
      intro r hr
      refine hunf (E r) (E_E r) ?_
      intro z hz hzv
      obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
      have hk : z'.1.1 ∈ List.range' idx named.length := by
        rw [← hidx]; exact List.mem_map.mpr ⟨z'.1, hZnamed z' hz', rfl⟩
      rw [List.mem_range'_1] at hk
      rw [vars_E] at hzv
      exact hfresh _ hk.1 (hbv r hr _ hzv)
    generalize hds' : (Z.map fun z => (z.1.1, z.1.2.2.1, z.2)) = ds at hpt
    show Statements.mapExprs (fun e => E (unfold ds e)) body' = Statements.mapExprs E body
    calc Statements.mapExprs (fun e => E (unfold ds e)) body'
        = Statements.mapExprs (fun e => E (unfold ds e)) (Statements.mapExprs E body') := by
          rw [mapExprs_eq_block, mapExprs_eq_block, mapExprs_eq_block, block_mapExpr_comp]
          apply block_mapExpr_congr
          intro e _
          exact (E_unfold_E _ _).symm
      _ = Statements.mapExprs (fun e => E (unfold ds e))
            (Statements.mapExprs (fun e => rwE (ρL Lc) (E e)) body) := by rw [hbody]
      _ = Statements.mapExprs E body := by
          rw [mapExprs_eq_block, mapExprs_eq_block, mapExprs_eq_block, block_mapExpr_comp]
          apply block_mapExpr_congr
          intro r hr
          exact hpt r (by rw [collectExprs_eq]; exact hr)

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## The single pass, piece by piece -/

/-- `replaceKids` rewrites the children of an `app`, `ite` or `eq` node. -/
theorem replaceKids_spec (repl : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (e : Expression.Expr) (he : match e with | .app .. | .ite .. | .eq .. => True | _ => False)
    (s : RwState) (hs : RwInv (ρOf repl) s) :
    RwInv (ρOf repl) ((replaceKids repl e) s).2 ∧
      E ((replaceKids repl e) s).1 = rwKids (ρOf repl) (E e) := by
  cases e with
  | app m f a =>
    obtain ⟨h1, h2, -⟩ := replaceSubexprs_spec repl f s hs
    obtain ⟨h3, h4, -⟩ := replaceSubexprs_spec repl a _ h1
    simp only [replaceKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    exact ⟨h3, by simp only [E_app, rwKids, h2, h4]⟩
  | ite m c t f =>
    obtain ⟨h1, h2, -⟩ := replaceSubexprs_spec repl c s hs
    obtain ⟨h3, h4, -⟩ := replaceSubexprs_spec repl t _ h1
    obtain ⟨h5, h6, -⟩ := replaceSubexprs_spec repl f _ h3
    simp only [replaceKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    exact ⟨h5, by simp only [E_ite, rwKids, h2, h4, h6]⟩
  | eq m a b =>
    obtain ⟨h1, h2, -⟩ := replaceSubexprs_spec repl a s hs
    obtain ⟨h3, h4, -⟩ := replaceSubexprs_spec repl b _ h1
    simp only [replaceKids, bind, pure, stateT_bind_apply, stateT_pure_apply]
    exact ⟨h3, by simp only [E_eq, rwKids, h2, h4]⟩
  | _ => simp at he

/-- The replacement map the single pass builds: each entry of a target list, keyed by its
    hash, mapped to its variable. -/
theorem repl_foldl_spec (L : List (UInt64 × Expression.Expr × LMonoTy × Nat)) :
    ∀ (m : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr))) (idx : Nat),
      let r := L.foldl (fun (acc : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)) × Nat)
          (t : UInt64 × Expression.Expr × LMonoTy × Nat) =>
          (acc.1.insert t.1 ((t.2.1, cseVar acc.2 t.2.2.1) :: acc.1.getD t.1 []), acc.2 + 1))
        (m, idx)
      r.2 = idx + L.length ∧
      ∀ h p, p ∈ r.1.getD h [] ↔ p ∈ m.getD h [] ∨
        ∃ j, ∃ hj : j < L.length, L[j].1 = h ∧ p = (L[j].2.1, cseVar (idx + j) L[j].2.2.1) := by
  induction L with
  | nil => intro m idx; simp
  | cons t ts ih =>
    intro m idx
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (m.insert t.1 ((t.2.1, cseVar idx t.2.2.1) :: m.getD t.1 [])) (idx + 1)
    refine ⟨by rw [h1]; simp; omega, fun h p => ?_⟩
    rw [h2, Std.HashMap.getD_insert]
    constructor
    · rintro (hp | ⟨j, hj, hjh, rfl⟩)
      · split at hp
        · next heq =>
          have heq : t.1 = h := by simpa using heq
          rcases List.mem_cons.mp hp with rfl | hp
          · exact Or.inr ⟨0, by simp, heq, rfl⟩
          · exact Or.inl (heq ▸ hp)
        · exact Or.inl hp
      · exact Or.inr ⟨j + 1, by simp; omega, by simpa using hjh, by
          simp only [List.getElem_cons_succ]; rw [show idx + 1 + j = idx + (j + 1) by omega]⟩
    · rintro (hp | ⟨j, hj, hjh, rfl⟩)
      · left
        split
        · next heq =>
          have heq : t.1 = h := by simpa using heq
          subst heq; exact List.mem_cons_of_mem _ hp
        · exact hp
      · cases j with
        | zero =>
          left
          simp only [List.getElem_cons_zero] at hjh ⊢
          rw [ite_eq_left (by simpa using hjh)]
          exact List.mem_cons.mpr (Or.inl (by simp))
        | succ j =>
          right
          exact ⟨j, by simp at hj; omega, by simpa using hjh, by
            simp only [List.getElem_cons_succ]; rw [show idx + 1 + j = idx + (j + 1) by omega]⟩

/-- A generated variable is its own erasure. -/
@[simp] theorem E_cseVar (k : Nat) (ty : LMonoTy) : E (cseVar k ty) = cseVar k ty := rfl

/-- The replacement of a map holding, under its hash, each entry of `P` (index, hash, node,
    type, level) with its variable: `ρL` of the entries' classes. -/
theorem ρOf_eq_ρL (repl : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (P : List (Nat × UInt64 × Expression.Expr × LMonoTy × Nat))
    (hmem : ∀ h p, p ∈ repl.getD h [] ↔
      ∃ q ∈ P, q.2.1 = h ∧ p = (q.2.2.1, cseVar q.1 q.2.2.2.1))
    (hh : ∀ q ∈ P, hx q.2.2.1 = q.2.1)
    (hn : ((P.map fun q => (E q.2.2.1, q.1, q.2.2.2.1)).map (·.1)).Nodup)
    (c : Expression.Expr) (hc : E c = c) :
    ρOf repl c = ρL (P.map fun q => (E q.2.2.1, q.1, q.2.2.2.1)) c := by
  have hget : ∀ pairs, repl[hx c]? = some pairs → pairs = repl.getD (hx c) [] := by
    intro pairs h; rw [Std.HashMap.getD_eq_getD_getElem?, h]; rfl
  unfold ρOf tryReplace
  by_cases hq : ∃ q ∈ P, E q.2.2.1 = c
  · obtain ⟨q, hqP, hqc⟩ := hq
    have hqL : (E q.2.2.1, q.1, q.2.2.2.1) ∈ P.map fun q => (E q.2.2.1, q.1, q.2.2.2.1) :=
      List.mem_map.mpr ⟨q, hqP, rfl⟩
    rw [← hqc, ρL_of_mem_nodup hn hqL, hqc]
    have hin : (q.2.2.1, cseVar q.1 q.2.2.2.1) ∈ repl.getD (hx c) [] := by
      rw [hmem]; exact ⟨q, hqP, by rw [← hqc, hx_E, hh q hqP], rfl⟩
    cases hr : repl[hx c]? with
    | none =>
      rw [Std.HashMap.getD_eq_getD_getElem?, hr] at hin; simp at hin
    | some pairs =>
      simp only
      rw [← hget pairs hr] at hin
      have hsome : (pairs.find? fun p => exprEq c p.1).isSome := by
        rw [List.find?_isSome]
        exact ⟨_, hin, (exprEq_iff _ _).mpr (by rw [hc, ← hqc])⟩
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
      rw [hp]
      have hpm : p ∈ repl.getD (hx c) [] := by
        rw [← hget pairs hr]; exact List.mem_of_find?_eq_some hp
      have hpe : exprEq c p.1 = true :=
        List.find?_some (p := fun (p : Expression.Expr × Expression.Expr) => exprEq c p.1) hp
      obtain ⟨q', hq'P, -, rfl⟩ := (hmem _ _).mp hpm
      have hcls : E q'.2.2.1 = E q.2.2.1 := by
        rw [← (exprEq_iff _ _).mp hpe, hc, hqc]
      have := eq_of_nodup_map hn (List.mem_map.mpr ⟨q', hq'P, rfl⟩) hqL hcls
      simp only [Prod.mk.injEq] at this
      simp [this.2.1, this.2.2]
  · rw [ρL_eq_none (by
      intro h; obtain ⟨t, ht, htc⟩ := List.mem_map.mp h
      obtain ⟨q, hqP, rfl⟩ := List.mem_map.mp ht
      exact hq ⟨q, hqP, htc⟩)]
    cases hr : repl[hx c]? with
    | none => rfl
    | some pairs =>
      simp only
      have : (pairs.find? fun p => exprEq c p.1) = none := by
        rw [List.find?_eq_none]
        intro p hp hpe
        have hpm : p ∈ repl.getD (hx c) [] := by rw [← hget pairs hr]; exact hp
        obtain ⟨q', hq'P, -, rfl⟩ := (hmem _ _).mp hpm
        exact hq ⟨q', hq'P, by rw [← (exprEq_iff _ _).mp hpe, hc]⟩
      rw [this]; rfl

/-- A subterm of an erased expression is erased. -/
theorem IsSub.E_eq {c e : Expression.Expr} (h : IsSub c e) (he : E e = e) : E c = c := by
  induction h with
  | refl => exact he
  | _ => rename_i ih; apply ih; simp_all

/-- `rwE` on an erased expression only reads the replacement at erased expressions. -/
theorem rwE_congr_E {ρ₁ ρ₂ : Expression.Expr → Option Expression.Expr}
    (h : ∀ c, E c = c → ρ₁ c = ρ₂ c) (e : Expression.Expr) (he : E e = e) :
    rwE ρ₁ e = rwE ρ₂ e :=
  rwE_congr e fun c hc => h c (hc.E_eq he)

/-- `rwKids` on an erased expression only reads the replacement at erased expressions. -/
theorem rwKids_congr_E {ρ₁ ρ₂ : Expression.Expr → Option Expression.Expr}
    (h : ∀ c, E c = c → ρ₁ c = ρ₂ c) (e : Expression.Expr) (he : E e = e) :
    rwKids ρ₁ e = rwKids ρ₂ e :=
  rwKids_congr e fun c hc => h c (hc.1.E_eq he)

/-- `List.mapM` with a step that builds `mk (p, rhs)` for some `rhs` related to `p`. -/
theorem list_mapM_exists {σ α β γ : Type} (I : σ → Prop) (k : α → StateM σ γ) (mk : α × β → γ)
    (R : α → β → Prop) :
    ∀ (D : List α), (∀ p ∈ D, ∀ s, I s → ∃ b, ((k p) s).1 = mk (p, b) ∧ R p b ∧ I ((k p) s).2) →
    ∀ (s : σ), I s → ∃ bs : List β, ∃ hlen : bs.length = D.length,
      ((D.mapM k) s).1 = (D.zip bs).map mk ∧
      (∀ i (hi : i < D.length), R D[i] (bs[i]'(hlen ▸ hi))) ∧ I ((D.mapM k) s).2 := by
  intro D
  induction D with
  | nil => intro _ s hs; exact ⟨[], rfl, rfl, fun i hi => absurd hi (by simp), hs⟩
  | cons p ps ih =>
    intro hk s hs
    obtain ⟨b, h1, h2, h3⟩ := hk p (by simp) s hs
    obtain ⟨bs, h4, h5, h6, h7⟩ := ih (fun q hq => hk q (by simp [hq])) _ h3
    refine ⟨b :: bs, by simp [h4], ?_, fun i hi => ?_, ?_⟩
    · simp only [List.mapM_cons, bind, pure, stateT_bind_apply, stateT_pure_apply, List.zip_cons_cons,
        List.map_cons] at h5 ⊢
      rw [h1, h5]
    · cases i with
      | zero => exact h2
      | succ i => exact h6 i (by simp at hi; omega)
    · simp only [List.mapM_cons, bind, pure, stateT_bind_apply, stateT_pure_apply] at h7 ⊢
      exact h7

/-- Marking entries of a Boolean array with `set!`. -/
theorem foldl_set_spec {α : Type} (ix : α → Nat) : ∀ (L : List α) (a : Array Bool),
    (L.foldl (fun a x => a.set! (ix x) true) a).size = a.size ∧
    ∀ x ∈ L, ix x < a.size → (L.foldl (fun a x => a.set! (ix x) true) a)[ix x]! = true := by
  have hkeep : ∀ (L : List α) (a : Array Bool) (j : Nat), j < a.size → a[j]! = true →
      (L.foldl (fun a x => a.set! (ix x) true) a)[j]! = true := by
    intro L
    induction L with
    | nil => intro a j _ h; exact h
    | cons y ys ih =>
      intro a j hj h
      simp only [List.foldl_cons]
      apply ih _ j (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hj)
      rw [getElem!_pos _ j (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hj)]
      rw [getElem!_pos a j hj] at h
      simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds hj]
      split <;> simp_all
  intro L
  induction L with
  | nil => intro a; simp
  | cons y ys ih =>
    intro a
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (a.set! (ix y) true)
    refine ⟨by rw [h1]; simp, fun x hx hlt => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · apply hkeep ys _ _ (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hlt)
      rw [getElem!_pos _ _ (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hlt)]
      simp
    · exact h2 x hx (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hlt)

/-- Building the DAG of a list of expressions keeps the invariant and contains every subterm
    of every expression. -/
theorem dag_mapM_spec : ∀ (exprs : List Expression.Expr) (g : Dag), DInv g →
    DInv ((exprs.mapM dagNode) g).2 ∧
    (∀ i < g.nodes.size, i < ((exprs.mapM dagNode) g).2.nodes.size ∧
      ((exprs.mapM dagNode) g).2.nodes[i]! = g.nodes[i]!) ∧
    ∀ r ∈ exprs, ∀ c, IsSub c r → ∃ i < ((exprs.mapM dagNode) g).2.nodes.size,
      E ((exprs.mapM dagNode) g).2.nodes[i]! = E c := by
  intro exprs
  induction exprs with
  | nil => intro g hg; exact ⟨hg, fun i hi => ⟨hi, rfl⟩, fun r hr => absurd hr (by simp)⟩
  | cons r rs ih =>
    intro g hg
    have s1 := dagNode_spec r g hg
    simp only [List.mapM_cons, bind, pure, stateT_bind_apply, stateT_pure_apply]
    generalize dagNode r g = p at *
    obtain ⟨i, g2⟩ := p
    try simp only at s1
    obtain ⟨h1, h2, h3⟩ := ih g2 s1.1
    refine ⟨h1, fun j hj => ?_, fun r' hr' c hc => ?_⟩
    · obtain ⟨a, b⟩ := s1.2.2.2.1.2.1 j hj
      have := h2 j (Nat.lt_of_lt_of_le hj s1.2.2.2.1.1)
      exact ⟨this.1, this.2.trans a⟩
    · rcases List.mem_cons.mp hr' with rfl | hr'
      · obtain ⟨k, hk, hke⟩ := s1.2.2.2.2 c hc
        obtain ⟨a, b⟩ := h2 k hk
        exact ⟨k, a, by rw [b]; exact hke⟩
      · exact h3 r' hr' c hc

/-! ## The single pass, as named steps -/

/-- The duplicates and the hash cache. -/
def spDups (body : Statements) : List (UInt64 × Expression.Expr) × PtrCache hx :=
  collectExprsToAbbreviate.collectDups (Statements.collectExprs body)

/-- The duplicates with their types. -/
def spTyped (body : Statements) : List (UInt64 × Expression.Expr × Option LMonoTy) :=
  ((spDups body).1.mapM (m := StateM TcState)
      (fun (h, d) => do return (h, d, ← typeCheckClosed d))).run' {}

/-- The hashes of the proper subterms of the untyped duplicates. -/
def spBlocked (body : Statements) : Std.HashSet UInt64 :=
  ((spTyped body).foldlM (fun acc (p : UInt64 × Expression.Expr × Option LMonoTy) =>
        let (_, d, ty) := p
        if ty.isNone then collectSubexprHashes acc true d else pure acc)
      ({} : Std.HashSet UInt64)).run' (spDups body).2

/-- The named nodes, with their types. -/
def spNamed (body : Statements) : List (UInt64 × Expression.Expr × LMonoTy) :=
  (spTyped body).filterMap
    fun (h, d, ty) => if (spBlocked body).contains h then none else ty.map ((h, d, ·))

/-- The DAG of the body's expressions. -/
def spDag (body : Statements) : Dag :=
  (((Statements.collectExprs body).mapM dagNode).run { cache := (spDups body).2 }).2

/-- The DAG index of a node. -/
def spIndex (body : Statements) (h : UInt64) (d : Expression.Expr) : Nat :=
  ((spDag body).find? h d).getD 0

/-- The marks of the named nodes. -/
def spMarked (body : Statements) : Array Bool :=
  (spNamed body).foldl (fun a (h, d, _) => a.set! (spIndex body h d) true)
    (Array.replicate (spDag body).nodes.size false)

/-- The named nodes with their levels plus one, in hash order. -/
def spTargets (body : Statements) : List Target :=
  (spNamed body).map fun (h, d, ty) =>
    (h, d, ty, (propagateUp (spDag body).kids (spMarked body))[spIndex body h d]! + 1)

/-- The named nodes in naming order. -/
def spByRound (body : Statements) : List Target :=
  (spTargets body).mergeSort (fun a b => a.2.2.2 ≤ b.2.2.2)

/-- The replacement map and the next index. -/
def spRepl (body : Statements) (startIdx : Nat) :
    Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)) × Nat :=
  (spByRound body).foldl
      (fun (repMap, idx) (h, dup, ty, _) =>
        let freshVar : Expression.Expr :=
          .fvar valueLoc ⟨s!"{cseVarPrefix}{idx}", ()⟩ (some ty)
        (repMap.insert h ((dup, freshVar) :: repMap.getD h []), idx + 1))
      (({} : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr))), startIdx)

/-- The named nodes with their indices, in declaration order. -/
def spDeclOrder (body : Statements) (startIdx : Nat) : List (Nat × Target) :=
  ((List.range' startIdx (spByRound body).length).zip (spByRound body)).mergeSort
    (fun a b => a.2.2.2.2 ≥ b.2.2.2.2)

/-- The declarations and the rewritten body. -/
def spOut (body : Statements) (startIdx : Nat) : Statements × Statements :=
  (do
      let decls ← (spDeclOrder body startIdx).mapM fun (p : Nat × Target) => do
        let (idx, _, dup, ty, _) := p
        let rhs ← replaceKids (spRepl body startIdx).1 dup
        pure (Statement.init ⟨s!"{cseVarPrefix}{idx}", ()⟩ (LTy.forAll [] ty) (.det rhs)
          .empty)
      let body' ← Statements.mapExprsM
        (fun e => Prod.fst <$> replaceSubexprs (spRepl body startIdx).1 e) body
      pure (decls, body')).run' ({} : RwState)

/-- `stmtRunCSESinglePass` through its named steps. -/
theorem stmtRunCSESinglePass_eq (body : Statements) (idx : Nat) :
    stmtRunCSESinglePass body idx =
      if (spNamed body).isEmpty then (body, idx)
      else if markedFunction (spDag body) (spMarked body) then stmtRunCSE body idx
      else ((spOut body idx).1 ++ (spOut body idx).2, (spRepl body idx).2) := by
  unfold stmtRunCSESinglePass
  simp only [ShareCommon.shareCommon']
  rfl

/-- The types of the duplicates. -/
theorem spTyped_eq (body : Statements) :
    spTyped body = (spDups body).1.map (fun p => (p.1, p.2, LExpr.typeCheck [] p.2)) :=
  typed_eq _

/-- The named nodes: duplicates with their types, distinct up to locations. -/
theorem spNamed_spec (body : Statements) :
    (∀ x ∈ spNamed body, (x.1, x.2.1) ∈ (spDups body).1 ∧
      LExpr.typeCheck [] x.2.1 = some x.2.2) ∧
    (spNamed body).Pairwise (fun x y => E x.2.1 ≠ E y.2.1) := by
  have hdup := (collectDups_spec (Statements.collectExprs body)).2
  unfold spNamed
  rw [spTyped_eq]
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [List.mem_filterMap, List.mem_map] at hx
    obtain ⟨_, ⟨p, hp, rfl⟩, hx⟩ := hx
    split at hx
    · simp at hx
    · simp only [Option.map_eq_some_iff] at hx
      obtain ⟨ty, hty, rfl⟩ := hx
      exact ⟨hp, hty⟩
  · rw [List.pairwise_filterMap, List.pairwise_map]
    refine (hdup : (spDups body).1.Pairwise _).imp fun {a b} hab => ?_
    have key : ∀ (p : UInt64 × Expression.Expr) (y : UInt64 × Expression.Expr × LMonoTy),
        (match (p.1, p.2, LExpr.typeCheck [] p.2) with
          | (h, d, ty) => if (spBlocked body).contains h = true then none
            else Option.map (fun x => (h, d, x)) ty) = some y → y.2.1 = p.2 := by
      intro p y hy
      obtain ⟨h, d⟩ := p
      simp only at hy
      split at hy
      · simp at hy
      · simp only [Option.map_eq_some_iff] at hy
        obtain ⟨_, _, rfl⟩ := hy
        rfl
    intro x hxm y hym
    rw [key a x hxm, key b y hym]
    exact hab

/-- The named nodes are eligible duplicates hashed by their hash, below the body's
    expressions. -/
theorem spNamed_mem (body : Statements) {x : UInt64 × Expression.Expr × LMonoTy}
    (hxm : x ∈ spNamed body) :
    hx x.2.1 = x.1 ∧ eligible x.2.1 ∧ LExpr.typeCheck [] x.2.1 = some x.2.2 ∧
      ∃ r ∈ Statements.collectExprs body, ∃ c, IsSub c r ∧ E x.2.1 = E c := by
  obtain ⟨h1, h2⟩ := (spNamed_spec body).1 x hxm
  obtain ⟨h3, h4, h5⟩ := (collectDups_spec (Statements.collectExprs body)).1 _ h1
  exact ⟨h3, h4, h2, h5⟩

/-- The DAG of the body: the invariant, and every subterm of the body's expressions. -/
theorem spDag_spec (body : Statements) :
    DInv (spDag body) ∧ ∀ r ∈ Statements.collectExprs body, ∀ c, IsSub c r →
      ∃ i < (spDag body).nodes.size, E (spDag body).nodes[i]! = E c := by
  obtain ⟨h1, -, h3⟩ := dag_mapM_spec (Statements.collectExprs body) _ (DInv_empty _)
  exact ⟨h1, h3⟩

/-- A named node's index is the index of its class. -/
theorem spIndex_spec (body : Statements) {x : UInt64 × Expression.Expr × LMonoTy}
    (hxm : x ∈ spNamed body) :
    spIndex body x.1 x.2.1 < (spDag body).nodes.size ∧
      E (spDag body).nodes[spIndex body x.1 x.2.1]! = E x.2.1 := by
  obtain ⟨hh, -, -, r, hr, c, hc, hce⟩ := spNamed_mem body hxm
  obtain ⟨hg, hsub⟩ := spDag_spec body
  obtain ⟨i, hi, hie⟩ := hsub r hr c hc
  unfold spIndex
  rw [← hh]
  cases hf : (spDag body).find? (hx x.2.1) x.2.1 with
  | none => exact absurd (hie.trans hce.symm) ((Dag.find?_spec hg x.2.1).2 hf i hi)
  | some j => exact (Dag.find?_spec hg x.2.1).1 j hf

/-- Every named node is marked. -/
theorem spMarked_spec (body : Statements) :
    (spMarked body).size = (spDag body).nodes.size ∧
    ∀ x ∈ spNamed body, (spMarked body)[spIndex body x.1 x.2.1]! = true := by
  obtain ⟨h1, h2⟩ := foldl_set_spec (fun (x : UInt64 × Expression.Expr × LMonoTy) =>
    spIndex body x.1 x.2.1) (spNamed body) (Array.replicate (spDag body).nodes.size false)
  refine ⟨by unfold spMarked; rw [h1]; simp, fun x hxm => ?_⟩
  exact h2 x hxm (by simpa using (spIndex_spec body hxm).1)

/-- In a DAG satisfying the invariant, children have smaller indices. -/
theorem DInv.kids_lt {g : Dag} (hg : DInv g) : ∀ i < g.kids.size, ∀ k ∈ g.kids[i]!, k < i := by
  intro i hi k hk
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hk
  exact ((hg.2.2.2.2 i (by rw [← hg.1]; exact hi)).2 j hj).1

/-- **Levels grow towards proper subterms.** Of two named nodes, the one that is a proper
    subterm of the other (up to locations) has the larger level. -/
theorem spLevel_lt (body : Statements) {x x' : UInt64 × Expression.Expr × LMonoTy}
    (hx : x ∈ spNamed body) (hx' : x' ∈ spNamed body) (hps : IsPSub (E x'.2.1) (E x.2.1)) :
    (propagateUp (spDag body).kids (spMarked body))[spIndex body x.1 x.2.1]! + 1 ≤
      (propagateUp (spDag body).kids (spMarked body))[spIndex body x'.1 x'.2.1]! := by
  obtain ⟨hg, -⟩ := spDag_spec body
  obtain ⟨-, hedge⟩ := propagateUp_edge (spDag body).kids (spMarked body) hg.kids_lt
  obtain ⟨hi1, hi2⟩ := spIndex_spec body hx
  obtain ⟨hj1, hj2⟩ := spIndex_spec body hx'
  have hb : bonus (spMarked body) (spIndex body x.1 x.2.1) = 1 := by
    simp [bonus, (spMarked_spec body).2 x hx]
  obtain ⟨c, hc, hce⟩ := hps.1.transport (e' := (spDag body).nodes[spIndex body x.1 x.2.1]!)
    (by rw [hi2]; exact E_E _)
  have := up_psub hg (spMarked body) _ hedge _ hi1 _ hj1 c hc (by
    intro h; subst h; apply hps.2; rw [← E_E x'.2.1, hce, hi2]) (by rw [← hce, E_E, hj2])
  rw [hb] at this
  exact this

/-- The replacement map holds each named node under its hash with its variable, and the next
    index follows the last one given. -/
theorem spRepl_spec (body : Statements) (idx : Nat) :
    (spRepl body idx).2 = idx + (spByRound body).length ∧
    ∀ h p, p ∈ (spRepl body idx).1.getD h [] ↔
      ∃ j, ∃ hj : j < (spByRound body).length, (spByRound body)[j].1 = h ∧
        p = ((spByRound body)[j].2.1, cseVar (idx + j) (spByRound body)[j].2.2.1) := by
  have := repl_foldl_spec (spByRound body) ∅ idx
  simp only [Std.HashMap.getD_empty, List.not_mem_nil, false_or] at this
  exact this

/-- The declaration order: the named nodes with their indices, by non-increasing level. -/
theorem spDeclOrder_spec (body : Statements) (idx : Nat) :
    (spDeclOrder body idx).Perm ((List.range' idx (spByRound body).length).zip (spByRound body)) ∧
    (spDeclOrder body idx).Pairwise (fun a b => b.2.2.2.2 ≤ a.2.2.2.2) := by
  refine ⟨List.mergeSort_perm _ _, ?_⟩
  have := List.pairwise_mergeSort (le := fun (a b : Nat × Target) => decide (a.2.2.2.2 ≥ b.2.2.2.2))
    (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega)
    ((List.range' idx (spByRound body).length).zip (spByRound body))
  exact this.imp fun h => by simpa using h

/-- `Prod.fst <$>` in the state monad over `Id`, as a function of the state. -/
@[simp] theorem stateT_map_fst_apply {σ α β : Type} (x : StateT σ Id (α × β)) (s : σ) :
    (Prod.fst <$> x) s = ((x s).1.1, (x s).2) := rfl

/-- The named nodes are in `spNamed` with their levels. -/
theorem spByRound_mem (body : Statements) {t : Target} (ht : t ∈ spByRound body) :
    (t.1, t.2.1, t.2.2.1) ∈ spNamed body ∧
      t.2.2.2 = (propagateUp (spDag body).kids (spMarked body))[spIndex body t.1 t.2.1]! + 1 := by
  have ht' := (List.mergeSort_perm _ _).mem_iff.mp ht
  unfold spTargets at ht'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht'
  exact ⟨hx, rfl⟩

/-- The single pass outside its fallback, without names: the body unchanged. -/
theorem wf_refl (body : Statements) (idx : Nat) : CSEWellFormed body idx body idx := by
  refine ⟨[], body, rfl, Nat.le_refl _, by simp, by simp, by simp, by simp, ?_, ?_⟩
  · intro e he x hx; exact Or.inr (List.mem_flatMap.mpr ⟨e, he, hx⟩)
  · rfl

/-- **The single pass is well formed outside its fallback**, without the hash assumption: either
    its output is well formed or it is the output of `stmtRunCSE`. -/
public theorem stmtRunCSESinglePass_wellFormed_or_fallback (body : Statements) (idx : Nat)
    (hf : FreshCSENames body idx) :
    CSEWellFormed body idx (stmtRunCSESinglePass body idx).1 (stmtRunCSESinglePass body idx).2 ∨
      stmtRunCSESinglePass body idx = stmtRunCSE body idx := by
  rw [stmtRunCSESinglePass_eq]
  split
  · exact Or.inl (wf_refl body idx)
  split
  · exact Or.inr rfl
  left
  simp only
  -- The named nodes with their indices.
  generalize hBR : spByRound body = BR at *
  have hBRmem : ∀ t ∈ BR, (t.1, t.2.1, t.2.2.1) ∈ spNamed body ∧
      t.2.2.2 = (propagateUp (spDag body).kids (spMarked body))[spIndex body t.1 t.2.1]! + 1 :=
    fun t ht => spByRound_mem body (hBR ▸ ht)
  let P : List (Nat × Target) := (List.range' idx BR.length).zip BR
  have hPlen : P.length = BR.length := by simp [P]
  have hPfst : P.map (·.1) = List.range' idx BR.length := by
    simp only [P]; rw [List.map_fst_zip]; simp
  have hPsnd : P.map (·.2) = BR := by
    simp only [P]; rw [List.map_snd_zip]; simp
  have hPmem : ∀ q ∈ P, q.2 ∈ BR := fun q hq => hPsnd ▸ List.mem_map.mpr ⟨q, hq, rfl⟩
  have hPget : ∀ j (hj : j < P.length), P[j] = (idx + j, BR[j]'(by omega)) := by
    intro j hj; simp [P, List.getElem_zip, List.getElem_range']
  -- Distinct classes.
  have hBRn : (BR.map fun t => E t.2.1).Nodup := by
    have hperm : BR.Perm (spTargets body) := hBR ▸ List.mergeSort_perm _ _
    rw [(hperm.map _).nodup_iff]
    unfold spTargets
    rw [List.map_map]
    have := (spNamed_spec body).2
    rw [List.Nodup, List.pairwise_map]
    exact this
  -- The replacement.
  obtain ⟨hR2, hRmem⟩ := spRepl_spec body idx
  rw [hBR] at hR2 hRmem
  have hLcn : ((P.map fun q => (E q.2.2.1, q.1, q.2.2.2.1)).map (·.1)).Nodup := by
    rw [List.map_map]
    have : P.map ((·.1) ∘ fun q : Nat × Target => (E q.2.2.1, q.1, q.2.2.2.1)) =
        (P.map (·.2)).map (fun t => E t.2.1) := by simp [List.map_map]
    rw [this, hPsnd]; exact hBRn
  have hρ : ∀ c, E c = c → ρOf (spRepl body idx).1 c =
      ρL (P.map fun q => (E q.2.2.1, q.1, q.2.2.2.1)) c := by
    refine ρOf_eq_ρL _ P (fun h p => ?_) (fun q hq => ?_) hLcn
    · rw [hRmem]
      constructor
      · rintro ⟨j, hj, h1, rfl⟩
        refine ⟨P[j]'(by omega), List.getElem_mem _, ?_, ?_⟩ <;> rw [hPget j (by omega)]
        · exact h1
      · rintro ⟨q, hq, h1, rfl⟩
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
        rw [hPget j hj] at h1 ⊢
        exact ⟨j, by omega, h1, rfl⟩
    · exact (spNamed_mem body (hBRmem q.2 (hPmem q hq)).1).1
  -- The declaration order.
  obtain ⟨hDperm, hDsort⟩ := spDeclOrder_spec body idx
  rw [hBR] at hDperm
  have hDmem : ∀ p ∈ spDeclOrder body idx, p ∈ P := fun p hp => hDperm.mem_iff.mp hp
  -- The declarations and the body.
  unfold spOut
  simp only [StateT.run', bind, pure, stateT_bind_apply, stateT_pure_apply, id_map_eq]
  obtain ⟨rhss, hlen, hdecls, hrhss, hinv⟩ := list_mapM_exists (RwInv (ρOf (spRepl body idx).1))
    (fun (p : Nat × Target) => do
        let (k, _, dup, ty, _) := p
        let rhs ← replaceKids (spRepl body idx).1 dup
        pure (Statement.init ⟨s!"{cseVarPrefix}{k}", ()⟩ (LTy.forAll [] ty) (.det rhs) .empty))
    (fun (pr : (Nat × Target) × Expression.Expr) =>
      Statement.init ⟨s!"{cseVarPrefix}{pr.1.1}", ()⟩ (LTy.forAll [] pr.1.2.2.2.1) (.det pr.2) .empty)
    (fun p rhs => E rhs = rwKids (ρOf (spRepl body idx).1) (E p.2.2.1))
    (spDeclOrder body idx) (fun p hp s hs => by
      obtain ⟨k, h, d, ty, r⟩ := p
      have hel := (spNamed_mem body (hBRmem _ (hPmem _ (hDmem _ hp))).1).2.1
      obtain ⟨h1, h2⟩ := replaceKids_spec (spRepl body idx).1 d hel.1 s hs
      simp only [bind, pure, stateT_bind_apply, stateT_pure_apply]
      exact ⟨_, rfl, h2, h1⟩) {} (RwInv_empty _)
  obtain ⟨hbinv, hbody⟩ := mapExprsM_spec (RwInv (ρOf (spRepl body idx).1))
    (fun e => Prod.fst <$> replaceSubexprs (spRepl body idx).1 e)
    (fun e => rwE (ρOf (spRepl body idx).1) (E e))
    (fun e s hs => by
      obtain ⟨h1, h2, -⟩ := replaceSubexprs_spec (spRepl body idx).1 e s hs
      simp only [stateT_map_fst_apply]
      exact ⟨h1, h2⟩) body _ hinv
  simp only [bind, pure] at hdecls hbody hinv hbinv ⊢
  rw [hdecls, hR2]
  -- The shape of `wf_of_named`.
  let named := P.map (fun q => (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2))
  let Z := ((spDeclOrder body idx).zip rhss).map
    (fun pr => ((pr.1.1, pr.1.2.2.1, pr.1.2.2.2.1, pr.1.2.2.2.2), pr.2))
  have hLc : (named.map fun t => (E t.2.1, t.1, t.2.2.1)) =
      P.map fun q => (E q.2.2.1, q.1, q.2.2.2.1) := by simp [named, List.map_map]
  have hρ' : ∀ c, E c = c → ρOf (spRepl body idx).1 c = ρL (named.map fun t => (E t.2.1, t.1, t.2.2.1)) c :=
    fun c hc => by rw [hLc]; exact hρ c hc
  have hnamedmem : ∀ t ∈ named, ∃ q ∈ P, t = (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2) := fun t ht => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht; exact ⟨q, hq, rfl⟩
  have hbody2 : Statements.mapExprs (fun e => rwE (ρOf (spRepl body idx).1) (E e)) body =
      Statements.mapExprs (fun e => rwE (ρL (named.map fun t => (E t.2.1, t.1, t.2.2.1))) (E e))
        body := by
    rw [mapExprs_eq_block, mapExprs_eq_block]
    apply block_mapExpr_congr
    intro e _
    exact rwE_congr_E hρ' (E e) (E_E e)
  have key := wf_of_named body _ idx named Z ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hbody.trans hbody2) hf
  · have hlen' : named.length = BR.length := by simp [named, hPlen]
    rw [hlen'] at key
    have hds : ((Z.map fun z => (z.1.1, z.1.2.2.1, z.2)).map (fun d =>
        Statement.init ⟨s!"{cseVarPrefix}{d.1}", ()⟩ (LTy.forAll [] d.2.1) (.det d.2.2) .empty)) =
        ((spDeclOrder body idx).zip rhss).map (fun (pr : (Nat × Target) × Expression.Expr) =>
          Statement.init ⟨s!"{cseVarPrefix}{pr.1.1}", ()⟩ (LTy.forAll [] pr.1.2.2.2.1) (.det pr.2)
            .empty) := by
      simp [Z, List.map_map]
    rw [hds] at key
    exact key
  · -- indices
    have : named.map (·.1) = P.map (·.1) := by simp [named, List.map_map]
    rw [this, hPfst]; simp [named, hPlen]
  · -- classes
    have : named.map (fun t => E t.2.1) = BR.map (fun t => E t.2.1) := by
      rw [← hPsnd]; simp [named, List.map_map]
    rw [this]; exact hBRn
  · -- types
    intro t ht
    obtain ⟨q, hq, rfl⟩ := hnamedmem t ht
    obtain ⟨-, hel, hty, -⟩ := spNamed_mem body (hBRmem q.2 (hPmem q hq)).1
    exact ⟨hty, hel.2⟩
  · -- below the body
    intro t ht
    obtain ⟨q, hq, rfl⟩ := hnamedmem t ht
    exact (spNamed_mem body (hBRmem q.2 (hPmem q hq)).1).2.2.2
  · -- levels
    intro t ht t' ht' hps
    obtain ⟨q, hq, rfl⟩ := hnamedmem t ht
    obtain ⟨q', hq', rfl⟩ := hnamedmem t' ht'
    obtain ⟨hm, hr⟩ := hBRmem q.2 (hPmem q hq)
    obtain ⟨hm', hr'⟩ := hBRmem q'.2 (hPmem q' hq')
    have := spLevel_lt body hm hm' hps
    simp only at hr hr' this ⊢
    omega
  · -- declaration order is a permutation
    have : Z.map (·.1) = (spDeclOrder body idx).map
        (fun q => (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) := by
      simp only [Z, List.map_map]
      rw [show ((fun z => z.1) ∘ fun (pr : (Nat × Target) × Expression.Expr) =>
          ((pr.1.1, pr.1.2.2.1, pr.1.2.2.2.1, pr.1.2.2.2.2), pr.2)) =
          (fun q => (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) ∘ Prod.fst from rfl, ← List.map_map,
        List.map_fst_zip (by omega)]
    rw [this]
    exact hDperm.map _
  · -- sorted
    simp only [Z, List.pairwise_map]
    have h1 : ((spDeclOrder body idx).zip rhss).map Prod.fst = spDeclOrder body idx :=
      List.map_fst_zip (by omega)
    have h2 := hDsort
    rw [← h1, List.pairwise_map] at h2
    exact h2
  · -- right-hand sides
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    have hiD : i < (spDeclOrder body idx).length := by simp [Z] at hi; omega
    simp only [Z, List.getElem_map, List.getElem_zip]
    rw [hrhss i hiD]
    exact rwKids_congr_E hρ' _ (E_E _)

/-! ## The walk counts duplicates

The walk of `collectSubexprs` reaches a node once per *visit*: a visit of an eligible node
(a bvar-free `app`, `ite` or `eq`) that has been reached before only counts; the first visit
also *expands* the node, visiting the eligible nodes visible from its children (through the
spine of an application and through nodes that are not bvar-free, which are expanded at every
visit, and never into a binder). `occ e` lists the eligible nodes a visit of `e` reaches
directly and `occK d` those the expansion of `d` reaches. -/

/-- Whether `e` is a bvar-free `app`, `ite` or `eq`. -/
def elig (e : Expression.Expr) : Bool :=
  match e with
  | .app .. | .ite .. | .eq .. => !LExpr.hasBVar e
  | _ => false

mutual
/-- The eligible nodes a visit of `e` reaches directly (as erasures). -/
def occ : Expression.Expr → List Expression.Expr
  | .app m f a => if elig (.app m f a) then [E (.app m f a)] else spOcc f ++ occ a
  | .ite m c t f => if elig (.ite m c t f) then [E (.ite m c t f)] else occ c ++ occ t ++ occ f
  | .eq m a b => if elig (.eq m a b) then [E (.eq m a b)] else occ a ++ occ b
  | _ => []
/-- The eligible nodes the walk of an application spine reaches. -/
def spOcc : Expression.Expr → List Expression.Expr
  | .app _ f a => spOcc f ++ occ a
  | _ => []
end

/-- The eligible nodes the expansion of a node reaches. -/
def occK : Expression.Expr → List Expression.Expr
  | .app _ f a => spOcc f ++ occ a
  | .ite _ c t f => occ c ++ occ t ++ occ f
  | .eq _ a b => occ a ++ occ b
  | _ => []

/-- `elig` ignores locations. -/
@[simp] theorem elig_E (e : Expression.Expr) : elig (E e) = elig e := by
  have := hasBVar_E e
  cases e <;> simp_all [elig]

/-- `eligible` is `elig`. -/
theorem eligible_iff_elig (e : Expression.Expr) : eligible e ↔ elig e = true := by
  cases e <;> simp [eligible, elig]

mutual
/-- `occ` ignores locations. -/
theorem occ_E : ∀ e : Expression.Expr, occ (E e) = occ e
  | .app m f a => by
    have h : elig (.app valueLoc (E f) (E a)) = elig (.app m f a) := elig_E (.app m f a)
    simp only [E_app, occ, h, spOcc_E f, occ_E a, E_E]
  | .ite m c t f => by
    have h : elig (.ite valueLoc (E c) (E t) (E f)) = elig (.ite m c t f) := elig_E (.ite m c t f)
    simp only [E_ite, occ, h, occ_E c, occ_E t, occ_E f, E_E]
  | .eq m a b => by
    have h : elig (.eq valueLoc (E a) (E b)) = elig (.eq m a b) := elig_E (.eq m a b)
    simp only [E_eq, occ, h, occ_E a, occ_E b, E_E]
  | .const _ _ | .op _ _ _ | .bvar _ _ | .fvar _ _ _ | .abs _ _ _ _ | .quant _ _ _ _ _ _ => rfl
/-- `spOcc` ignores locations. -/
theorem spOcc_E : ∀ e : Expression.Expr, spOcc (E e) = spOcc e
  | .app m f a => by simp only [E_app, spOcc, spOcc_E f, occ_E a]
  | .const _ _ | .op _ _ _ | .bvar _ _ | .fvar _ _ _ | .abs _ _ _ _ | .quant _ _ _ _ _ _
  | .ite _ _ _ _ | .eq _ _ _ => rfl
end

/-- `occK` ignores locations. -/
theorem occK_E (e : Expression.Expr) : occK (E e) = occK e := by
  cases e <;> simp [occK, spOcc_E, occ_E]

/-- `occ` of an eligible node is its class; otherwise its expansion. -/
theorem occ_eq (e : Expression.Expr) :
    occ e = if elig e then [E e] else occK e := by
  cases e <;> simp [occ, occK, elig]

/-- The classes in `seen`. -/
def seenC (st : CollectedExprs) (c : Expression.Expr) : Prop :=
  ∃ h, ∃ x ∈ st.seen.getD h #[], E x = c

/-- The classes in `dups`. -/
def dupC (st : CollectedExprs) (c : Expression.Expr) : Prop :=
  ∃ h, ∃ x ∈ st.dups.getD h #[], E x = c

/-- The number of occurrences of `c` in `l`. -/
def cnt (c : Expression.Expr) (l : List Expression.Expr) : Nat :=
  l.countP (fun x => decide (x = c))

/-- No occurrence in the empty list. -/
@[simp] theorem cnt_nil (c : LExpr ⟨⟨ExpressionMetadata, Unit⟩, LMonoTy⟩) : cnt c [] = 0 := rfl
/-- Occurrences in a concatenation add up. -/
@[simp] theorem cnt_append (c : LExpr ⟨⟨ExpressionMetadata, Unit⟩, LMonoTy⟩)
    (l₁ l₂ : List (LExpr ⟨⟨ExpressionMetadata, Unit⟩, LMonoTy⟩)) :
    cnt c (l₁ ++ l₂) = cnt c l₁ + cnt c l₂ := List.countP_append ..
/-- Occurrences in a list with a head. -/
@[simp] theorem cnt_cons (c x : LExpr ⟨⟨ExpressionMetadata, Unit⟩, LMonoTy⟩)
    (l : List (LExpr ⟨⟨ExpressionMetadata, Unit⟩, LMonoTy⟩)) :
    cnt c (x :: l) = cnt c l + (if x = c then 1 else 0) := by
  simp [cnt, List.countP_cons]
/-- `c` occurs in `l` exactly when it is a member. -/
theorem cnt_pos {c : Expression.Expr} {l : List Expression.Expr} : 0 < cnt c l ↔ c ∈ l := by
  simp [cnt, List.countP_pos_iff]
/-- `c` does not occur in `l` exactly when it is not a member. -/
theorem cnt_eq_zero {c : Expression.Expr} {l : List Expression.Expr} : cnt c l = 0 ↔ c ∉ l := by
  simp only [cnt, List.countP_eq_zero, decide_eq_true_eq]
  exact ⟨fun h hc => h c hc rfl, fun h a ha hac => h (hac ▸ ha)⟩
/-- Permuted lists have the same occurrences. -/
theorem perm_cnt_eq {l₁ l₂ : List Expression.Expr} (h : l₁.Perm l₂) (c : Expression.Expr) :
    cnt c l₁ = cnt c l₂ := h.countP_eq _

/-- The duplicate counting of two walks in a row. -/
theorem dup_arith (D : Prop) (a₀ x y : Nat) (ha : a₀ ≤ 1) :
    ((D ∨ 2 ≤ a₀ + x) ∨ 2 ≤ (if 1 ≤ a₀ + x then 1 else 0) + y) ↔ (D ∨ 2 ≤ a₀ + (x + y)) := by
  constructor
  · rintro ((hD | h) | h)
    · exact Or.inl hD
    · exact Or.inr (by omega)
    · right; split at h <;> omega
  · rintro (hD | h)
    · exact Or.inl (Or.inl hD)
    · by_cases hx : 2 ≤ a₀ + x
      · exact Or.inl (Or.inr hx)
      · right; split <;> omega

open Classical in
/-- What walking from `st` to `st'` did, for direct visits `V`: the classes newly seen `new`
    (each visited and not seen before), the visits `V ++ new.flatMap occK`, `seen` grown by
    the visited classes, a class a duplicate once visited twice in all (counting an earlier
    first visit), and every new class reached from `V` or from the expansion of a new class. -/
def WC (st : CollectedExprs) (V : List Expression.Expr) (st' : CollectedExprs) : Prop :=
  ∃ new : List Expression.Expr, new.Nodup ∧
    (∀ c, c ∈ new ↔ ¬ seenC st c ∧ c ∈ V ++ new.flatMap occK) ∧
    (∀ c, seenC st' c ↔ seenC st c ∨ c ∈ V ++ new.flatMap occK) ∧
    (∀ c, dupC st' c ↔ dupC st c ∨
      2 ≤ (if seenC st c then 1 else 0) + cnt c (V ++ new.flatMap occK)) ∧
    (∀ d ∈ new, d ∈ V ∨ ∃ d' ∈ new, d ∈ occK d')

/-- Walking nothing. -/
theorem WC.nil (st : CollectedExprs) : WC st [] st := by
  refine ⟨[], List.nodup_nil, fun c => by simp, fun c => by simp, fun c => ?_, fun d hd => by simp at hd⟩
  have h0 : cnt c ([] ++ List.flatMap occK []) = 0 := rfl
  rw [h0, Nat.add_zero]
  constructor
  · exact Or.inl
  · rintro (h | h)
    · exact h
    · split at h <;> omega

/-- Two walks in a row. -/
theorem WC.append {st₀ st₁ st₂ : CollectedExprs} {V₁ V₂ : List Expression.Expr}
    (h₁ : WC st₀ V₁ st₁) (h₂ : WC st₁ V₂ st₂) : WC st₀ (V₁ ++ V₂) st₂ := by
  classical
  obtain ⟨n₁, hn₁, hm₁, hs₁, hd₁, hr₁⟩ := h₁
  obtain ⟨n₂, hn₂, hm₂, hs₂, hd₂, hr₂⟩ := h₂
  have hdisj : ∀ c ∈ n₁, c ∉ n₂ := fun c hc hc2 =>
    ((hm₂ c).mp hc2).1 ((hs₁ c).mpr (Or.inr ((hm₁ c).mp hc).2))
  have hmemL : ∀ c, c ∈ (V₁ ++ V₂) ++ (n₁ ++ n₂).flatMap occK ↔
      c ∈ V₁ ++ n₁.flatMap occK ∨ c ∈ V₂ ++ n₂.flatMap occK := by
    intro c; simp only [List.mem_append, List.flatMap_append]
    constructor
    · rintro ((h | h) | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
    · rintro ((h | h) | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
  have hcnt : ∀ c, cnt c ((V₁ ++ V₂) ++ (n₁ ++ n₂).flatMap occK) =
      cnt c (V₁ ++ n₁.flatMap occK) + cnt c (V₂ ++ n₂.flatMap occK) := by
    intro c; simp only [List.flatMap_append, cnt_append]; omega
  refine ⟨n₁ ++ n₂, List.nodup_append.mpr ⟨hn₁, hn₂, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩,
    fun c => ?_, fun c => ?_, fun c => ?_, fun d hd => ?_⟩
  · rw [hmemL, List.mem_append, hm₁, hm₂, hs₁]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨fun h => h1 (Or.inl h), Or.inr h2⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · by_cases h3 : c ∈ V₁ ++ n₁.flatMap occK
        · exact Or.inl ⟨h1, h3⟩
        · exact Or.inr ⟨fun h => by rcases h with h | h <;> contradiction, h2⟩
  · rw [hs₂, hs₁, hmemL]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  · rw [hd₂, hd₁, hcnt]
    have hs1 : (if seenC st₁ c then 1 else 0) =
        (if 1 ≤ (if seenC st₀ c then 1 else 0) + cnt c (V₁ ++ n₁.flatMap occK) then 1 else 0) := by
      by_cases h0 : seenC st₀ c
      · simp [h0, (hs₁ c).mpr (Or.inl h0)]
      · by_cases hc1 : c ∈ V₁ ++ n₁.flatMap occK
        · have := cnt_pos.mpr hc1
          simp only [h0, (hs₁ c).mpr (Or.inr hc1), ite_true, ite_false]; split <;> omega
        · have h1 : ¬ seenC st₁ c := fun h => by rcases (hs₁ c).mp h with h | h <;> contradiction
          have := cnt_eq_zero.mpr hc1
          simp only [h0, h1, ite_false]; split <;> omega
    rw [hs1]
    exact dup_arith _ _ _ _ (by split <;> omega)
  · rcases List.mem_append.mp hd with hd | hd
    · rcases hr₁ d hd with h | ⟨d', hd', h⟩
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr ⟨d', List.mem_append_left _ hd', h⟩
    · rcases hr₂ d hd with h | ⟨d', hd', h⟩
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr ⟨d', List.mem_append_right _ hd', h⟩

/-- Changing only the walk's direct visits up to a permutation. -/
theorem WC.perm {st st' : CollectedExprs} {V V' : List Expression.Expr} (h : WC st V st')
    (hp : V.Perm V') : WC st V' st' := by
  obtain ⟨n, hn, hm, hs, hd, hr⟩ := h
  have hp' : (V ++ n.flatMap occK).Perm (V' ++ n.flatMap occK) := hp.append_right _
  refine ⟨n, hn, fun c => by rw [hm, hp'.mem_iff], fun c => by rw [hs, hp'.mem_iff],
    fun c => by rw [hd, perm_cnt_eq hp'], fun d hd' => ?_⟩
  rcases hr d hd' with h | h
  · exact Or.inl (hp.mem_iff.mp h)
  · exact Or.inr h

/-- `recordSeen` adds the class of `e` to `seen`. -/
theorem seenC_recordSeen (st : CollectedExprs) (e c : Expression.Expr) :
    seenC (st.recordSeen (hx e) e) c ↔ seenC st c ∨ c = E e := by
  simp only [seenC, CollectedExprs.recordSeen]
  constructor
  · rintro ⟨h, x, hxm, rfl⟩
    rcases (mem_getD_insert_push _ _ _ _ _).mp hxm with hxm | ⟨_, rfl⟩
    · exact Or.inl ⟨h, x, hxm, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨h, x, hxm, rfl⟩ | rfl)
    · exact ⟨h, x, (mem_getD_insert_push _ _ _ _ _).mpr (Or.inl hxm), rfl⟩
    · exact ⟨hx e, e, (mem_getD_insert_push _ _ _ _ _).mpr (Or.inr ⟨rfl, rfl⟩), rfl⟩

/-- `recordSeen` keeps `dups`. -/
theorem dupC_recordSeen (st : CollectedExprs) (e c : Expression.Expr) :
    dupC (st.recordSeen (hx e) e) c ↔ dupC st c := Iff.rfl

/-- `recordDup` keeps `seen`. -/
theorem seenC_recordDup (st : CollectedExprs) (e c : Expression.Expr) :
    seenC (st.recordDup (hx e) e) c ↔ seenC st c := by
  unfold CollectedExprs.recordDup; dsimp only; split <;> exact Iff.rfl

/-- `recordDup` adds the class of `e` to `dups`. -/
theorem dupC_recordDup (st : CollectedExprs) (e c : Expression.Expr) :
    dupC (st.recordDup (hx e) e) c ↔ dupC st c ∨ c = E e := by
  unfold CollectedExprs.recordDup; dsimp only
  split
  · next hany =>
    obtain ⟨x, hxm, hxe⟩ := Array.any_eq_true'.mp hany
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact ⟨hx e, x, hxm, ((exprEq_iff _ _).mp hxe).symm⟩
  · simp only [dupC]
    constructor
    · rintro ⟨h, x, hxm, rfl⟩
      rcases (mem_getD_insert_push _ _ _ _ _).mp hxm with hxm | ⟨_, rfl⟩
      · exact Or.inl ⟨h, x, hxm, rfl⟩
      · exact Or.inr rfl
    · rintro (⟨h, x, hxm, rfl⟩ | h)
      · exact ⟨h, x, (mem_getD_insert_push _ _ _ _ _).mpr (Or.inl hxm), rfl⟩
      · subst h
        exact ⟨hx e, e, (mem_getD_insert_push _ _ _ _ _).mpr (Or.inr ⟨rfl, rfl⟩), rfl⟩

/-- A class whose bucket check fails is not seen. -/
theorem not_seenC_of_any {st : CollectedExprs} (hs : WInv st) {e : Expression.Expr}
    (h : (st.seen.getD (hx e) #[]).any (exprEq e) = false) : ¬ seenC st (E e) := by
  rintro ⟨h', x, hxm, hxe⟩
  have hk := ((hs.1 h').1 x hxm).1
  rw [← hk, hx_eq_of_E hxe] at hxm
  have : (st.seen.getD (hx e) #[]).any (exprEq e) = true :=
    Array.any_eq_true'.mpr ⟨x, hxm, (exprEq_iff _ _).mpr hxe.symm⟩
  rw [this] at h; exact Bool.noConfusion h

/-- A class whose bucket check succeeds is seen. -/
theorem seenC_of_any {st : CollectedExprs} {e : Expression.Expr}
    (h : (st.seen.getD (hx e) #[]).any (exprEq e) = true) : seenC st (E e) := by
  obtain ⟨x, hxm, hxe⟩ := Array.any_eq_true'.mp h
  exact ⟨hx e, x, hxm, ((exprEq_iff _ _).mp hxe).symm⟩

open Classical in
/-- Walks are judged by `seen` and `dups` alone. -/
theorem WC.congr {st₁ st₂ st₁' st₂' : CollectedExprs} {V : List Expression.Expr}
    (h : WC st₁ V st₂) (h1 : ∀ c, seenC st₁' c ↔ seenC st₁ c) (h2 : ∀ c, dupC st₁' c ↔ dupC st₁ c)
    (h3 : ∀ c, seenC st₂' c ↔ seenC st₂ c) (h4 : ∀ c, dupC st₂' c ↔ dupC st₂ c) :
    WC st₁' V st₂' := by
  obtain ⟨n, hn, hm, hs, hd, hr⟩ := h
  refine ⟨n, hn, fun c => by rw [hm, h1], fun c => by rw [h3, hs, h1], fun c => ?_, hr⟩
  rw [h4, hd, h2]
  have : (if seenC st₁' c then 1 else 0) = (if seenC st₁ c then 1 else 0) := by
    by_cases hc : seenC st₁ c
    · rw [ite_eq_left hc, ite_eq_left ((h1 c).mpr hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((h1 c).mp h'))]
  rw [this]

open Classical in
/-- Duplicates stay seen. -/
theorem WC.dupSub {st st' : CollectedExprs} {V : List Expression.Expr} (h : WC st V st')
    (hds : ∀ c, dupC st c → seenC st c) : ∀ c, dupC st' c → seenC st' c := by
  obtain ⟨n, -, -, hs, hd, -⟩ := h
  intro c hc
  rcases (hd c).mp hc with h | h
  · exact (hs c).mpr (Or.inl (hds c h))
  · by_cases h0 : seenC st c
    · exact (hs c).mpr (Or.inl h0)
    · simp only [h0, ite_false, Nat.zero_add] at h
      exact (hs c).mpr (Or.inr (cnt_pos.mp (by omega)))

open Classical in
/-- A visit of an eligible node already seen: a duplicate. -/
theorem WC.hit {st : CollectedExprs} {e : Expression.Expr} (hseen : seenC st (E e)) :
    WC st [E e] (st.recordDup (hx e) e) := by
  refine ⟨[], List.nodup_nil, fun c => ?_, fun c => ?_, fun c => ?_, fun d hd => by simp at hd⟩
  · simp only [List.not_mem_nil, false_iff, List.flatMap_nil, List.append_nil, List.mem_singleton]
    rintro ⟨h1, rfl⟩; exact h1 hseen
  · simp only [seenC_recordDup, List.flatMap_nil, List.append_nil, List.mem_singleton]
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact hseen
  · rw [dupC_recordDup]
    simp only [List.flatMap_nil, List.append_nil]
    by_cases hc : c = E e
    · subst hc
      have : cnt (E e) [E e] = 1 := by simp [cnt]
      rw [this, ite_eq_left hseen]
      exact ⟨fun _ => Or.inr (by omega), fun _ => Or.inr rfl⟩
    · have : cnt c [E e] = 0 := cnt_eq_zero.mpr (by simpa [eq_comm] using hc)
      rw [this]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact absurd h hc
      · rintro (h | h)
        · exact Or.inl h
        · split at h <;> omega

open Classical in
/-- Recording an eligible node as seen after walking its children. -/
theorem WC.record {st₁ st₃ : CollectedExprs} {e : Expression.Expr}
    (h : WC st₁ (occK e) st₃) (h1 : ¬ seenC st₁ (E e)) (h3 : ¬ seenC st₃ (E e))
    (hds : ∀ c, dupC st₁ c → seenC st₁ c) :
    WC st₁ [E e] (st₃.recordSeen (hx e) e) := by
  obtain ⟨n, hn, hm, hs, hd, hr⟩ := h
  have hnotL : E e ∉ occK e ++ n.flatMap occK := fun h => h3 ((hs _).mpr (Or.inr h))
  have hperm : ([E e] ++ (n ++ [E e]).flatMap occK).Perm ([E e] ++ (occK e ++ n.flatMap occK)) := by
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, occK_E]
    exact List.Perm.append_left _ List.perm_append_comm
  have hmem : ∀ c, c ∈ [E e] ++ (n ++ [E e]).flatMap occK ↔ c = E e ∨ c ∈ occK e ++ n.flatMap occK :=
    fun c => by rw [hperm.mem_iff]; simp
  refine ⟨n ++ [E e], ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun d hd => ?_⟩
  · exact List.nodup_append.mpr ⟨hn, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun a ha b hb hab => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; subst hab; exact hnotL (((hm _).mp ha).2)⟩
  · rw [hmem, List.mem_append, List.mem_singleton, hm]
    constructor
    · rintro (⟨h1', h2'⟩ | rfl)
      · exact ⟨h1', Or.inr h2'⟩
      · exact ⟨h1, Or.inl rfl⟩
    · rintro ⟨h1', rfl | h2'⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨h1', h2'⟩
  · rw [seenC_recordSeen, hs, hmem]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
  · rw [dupC_recordSeen, hd, perm_cnt_eq hperm, cnt_append c [E e]]
    by_cases hc : c = E e
    · subst hc
      have hz : cnt (E e) (occK e ++ n.flatMap occK) = 0 := cnt_eq_zero.mpr hnotL
      have h11 : cnt (E e) [E e] = 1 := by simp [cnt]
      rw [hz, h11, ite_eq_right h1]
      constructor
      · rintro (h | h)
        · exact absurd (hds _ h) h1
        · omega
      · rintro (h | h)
        · exact absurd (hds _ h) h1
        · omega
    · have h10 : cnt c [E e] = 0 := cnt_eq_zero.mpr (by simpa [eq_comm] using hc)
      rw [h10, Nat.zero_add]
  · rcases List.mem_append.mp hd with hd | hd
    · rcases hr d hd with h | ⟨d', hd', h⟩
      · exact Or.inr ⟨E e, by simp, by rw [occK_E]; exact h⟩
      · exact Or.inr ⟨d', List.mem_append_left _ hd', h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; subst hd; exact Or.inl (by simp)

/-- The walk's counting, with the hypotheses it needs of the starting state. -/
def WCSpec (st : CollectedExprs) (V : List Expression.Expr) (st' : CollectedExprs) : Prop :=
  WInv st → (∀ c, dupC st c → seenC st c) → WC st V st'

set_option hygiene false in
/-- Unfold the hashing step of the walk at `e` for `walk_count`, naming the state after it
    `st₁`. -/
local macro "count_prefix" st:ident e:term : tactic => `(tactic| (
  hash_step $st $e
  have hs₁ : WInv st₁ := WInv.of_eq (by assumption) hh2 hh3
  have hsC : ∀ c, seenC $st c ↔ seenC st₁ c := fun c => by unfold seenC; rw [hh2]
  have hdC : ∀ c, dupC $st c ↔ dupC st₁ c := fun c => by unfold dupC; rw [hh3]
  have hds₁ : ∀ c, dupC st₁ c → seenC st₁ c := fun c h => (hsC c).mp (hds c ((hdC c).mpr h))
  split
  · rename_i hany
    have hel := eligible_of_seen hs₁ hany
    rw [occ_eq, ite_eq_left ((eligible_iff_elig _).mp hel)]
    exact (WC.hit (seenC_of_any hany)).congr hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  rename_i hany
  simp only [Bool.not_eq_true] at hany))

/-- Two walks in a row, keeping the hypotheses. -/
theorem wc_step {st st' : CollectedExprs} {e : Expression.Expr} {V : List Expression.Expr}
    (hw : WalkSpec st e (true, st') ∨ WInv st')
    (h : WC st V st') (hds : ∀ c, dupC st c → seenC st c) :
    WInv st' ∧ (∀ c, dupC st' c → seenC st' c) := by
  refine ⟨?_, h.dupSub hds⟩
  rcases hw with hw | hw
  · exact hw.1
  · exact hw

/-- **The walk counts.** From a state satisfying the invariant, with every duplicate seen, the
    walk of `e` visits `occ e` (and its spine walk `spOcc e`) and the expansions of the newly
    seen classes, in the sense of `WC`. -/
theorem walk_count : ∀ e : Expression.Expr,
    (∀ st, WCSpec st (occ e) (collectSubexprs st e).2) ∧
    (∀ st, WCSpec st (spOcc e) (collectSubexprs.walkSpine st e).2) := by
  intro e
  induction e with
  | app m f a ihf iha =>
    refine ⟨fun st hs hds => ?_, fun st hs hds => ?_⟩
    · count_prefix st (LExpr.app m f a)
      obtain ⟨i1, o1, g1⟩ := (walk_spec f).2 st₁ hs₁
      have w1 := ihf.2 st₁ hs₁ hds₁
      generalize collectSubexprs.walkSpine st₁ f = w at *
      obtain ⟨fnOk, st2⟩ := w
      simp only at i1 o1 g1 w1
      have d2 := w1.dupSub hds₁
      obtain ⟨i2, o2, g2⟩ := (walk_spec a).1 st2 i1
      have w2 := iha.1 st2 i1 d2
      generalize collectSubexprs st2 a = w at *
      obtain ⟨argOk, st3⟩ := w
      simp only at i2 o2 g2 w2 ⊢
      have w12 := w1.append w2
      subst o1 o2
      by_cases hel : elig (LExpr.app m f a) = true
      · have hbf : (!f.hasBVar && !a.hasBVar) = true := by simpa [elig, LExpr.hasBVar] using hel
        rw [ite_eq_left hbf, occ_eq, ite_eq_left hel]
        have h3 := not_seenC_of_any i2 (not_mem_of_grows g2 (by simp [esize]; omega)
          (not_mem_of_grows g1 (by simp [esize]; omega) hany))
        exact (WC.record (e := LExpr.app m f a) w12 (not_seenC_of_any hs₁ hany) h3 hds₁).congr
          hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
      · have hbf : (!f.hasBVar && !a.hasBVar) = false := by simpa [elig, LExpr.hasBVar] using hel
        rw [ite_eq_right (by simp [hbf]), occ_eq, ite_eq_right hel]
        exact w12.congr hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    · rw [collectSubexprs.walkSpine]; dsimp only
      obtain ⟨i1, -, -⟩ := (walk_spec f).2 st hs
      have w1 := ihf.2 st hs hds
      generalize collectSubexprs.walkSpine st f = w at *
      obtain ⟨fnOk, st2⟩ := w
      simp only at i1 w1
      have w2 := iha.1 st2 i1 (w1.dupSub hds)
      generalize collectSubexprs st2 a = w at *
      obtain ⟨argOk, st3⟩ := w
      simp only at w2 ⊢
      exact w1.append w2
  | ite m c t f ihc iht ihf =>
    refine ⟨fun st hs hds => ?_, fun st hs hds => ?_⟩
    · count_prefix st (LExpr.ite m c t f)
      obtain ⟨i1, o1, g1⟩ := (walk_spec c).1 st₁ hs₁
      have w1 := ihc.1 st₁ hs₁ hds₁
      generalize collectSubexprs st₁ c = w at *
      obtain ⟨cOk, st2⟩ := w
      simp only at i1 o1 g1 w1
      obtain ⟨i2, o2, g2⟩ := (walk_spec t).1 st2 i1
      have w2 := iht.1 st2 i1 (w1.dupSub hds₁)
      generalize collectSubexprs st2 t = w at *
      obtain ⟨tOk, st3⟩ := w
      simp only at i2 o2 g2 w2
      obtain ⟨i3, o3, g3⟩ := (walk_spec f).1 st3 i2
      have w3 := ihf.1 st3 i2 ((w1.append w2).dupSub hds₁)
      generalize collectSubexprs st3 f = w at *
      obtain ⟨fOk, st4⟩ := w
      simp only at i3 o3 g3 w3 ⊢
      have w123 := (w1.append w2).append w3
      subst o1 o2 o3
      by_cases hel : elig (LExpr.ite m c t f) = true
      · have hbf : (!c.hasBVar && !t.hasBVar && !f.hasBVar) = true := by
          simpa [elig, LExpr.hasBVar] using hel
        rw [ite_eq_left hbf, occ_eq, ite_eq_left hel]
        have h3 := not_seenC_of_any i3 (not_mem_of_grows g3 (by simp [esize]; omega)
          (not_mem_of_grows g2 (by simp [esize]; omega)
            (not_mem_of_grows g1 (by simp [esize]; omega) hany)))
        exact (WC.record (e := LExpr.ite m c t f) w123 (not_seenC_of_any hs₁ hany) h3 hds₁).congr
          hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
      · have hbf : (!c.hasBVar && !t.hasBVar && !f.hasBVar) = false := by
          simpa [elig, LExpr.hasBVar] using hel
        rw [ite_eq_right (by simp [hbf]), occ_eq, ite_eq_right hel]
        exact w123.congr hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact WC.nil st
  | eq m a b iha ihb =>
    refine ⟨fun st hs hds => ?_, fun st hs hds => ?_⟩
    · count_prefix st (LExpr.eq m a b)
      obtain ⟨i1, o1, g1⟩ := (walk_spec a).1 st₁ hs₁
      have w1 := iha.1 st₁ hs₁ hds₁
      generalize collectSubexprs st₁ a = w at *
      obtain ⟨ok1, st2⟩ := w
      simp only at i1 o1 g1 w1
      obtain ⟨i2, o2, g2⟩ := (walk_spec b).1 st2 i1
      have w2 := ihb.1 st2 i1 (w1.dupSub hds₁)
      generalize collectSubexprs st2 b = w at *
      obtain ⟨ok2, st3⟩ := w
      simp only at i2 o2 g2 w2 ⊢
      have w12 := w1.append w2
      subst o1 o2
      by_cases hel : elig (LExpr.eq m a b) = true
      · have hbf : (!a.hasBVar && !b.hasBVar) = true := by simpa [elig, LExpr.hasBVar] using hel
        rw [ite_eq_left hbf, occ_eq, ite_eq_left hel]
        have h3 := not_seenC_of_any i2 (not_mem_of_grows g2 (by simp [esize]; omega)
          (not_mem_of_grows g1 (by simp [esize]; omega) hany))
        exact (WC.record (e := LExpr.eq m a b) w12 (not_seenC_of_any hs₁ hany) h3 hds₁).congr
          hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
      · have hbf : (!a.hasBVar && !b.hasBVar) = false := by simpa [elig, LExpr.hasBVar] using hel
        rw [ite_eq_right (by simp [hbf]), occ_eq, ite_eq_right hel]
        exact w12.congr hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact WC.nil st
  | abs m n ty b ih =>
    refine ⟨fun st hs hds => ?_, fun st hs hds => ?_⟩
    · count_prefix st (LExpr.abs m n ty b)
      exact (WC.nil st₁).congr hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact WC.nil st
  | quant m k n ty tr b ihtr ihb =>
    refine ⟨fun st hs hds => ?_, fun st hs hds => ?_⟩
    · count_prefix st (LExpr.quant m k n ty tr b)
      exact (WC.nil st₁).congr hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    · rw [collectSubexprs.walkSpine]
      rotate_left
      all_goals (try (intros; simp_all; done))
      exact WC.nil st
  | const m c =>
    refine ⟨fun st hs hds => ?_, fun st hs hds => ?_⟩
    · count_prefix st (LExpr.const m c)
      exact (WC.nil st₁).congr hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    · rw [collectSubexprs.walkSpine]; exact WC.nil st
  | op m o ty =>
    refine ⟨fun st hs hds => ?_, fun st hs hds => ?_⟩
    · count_prefix st (LExpr.op m o ty)
      exact (WC.nil st₁).congr hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    · rw [collectSubexprs.walkSpine]; exact WC.nil st
  | fvar m x ty =>
    refine ⟨fun st hs hds => ?_, fun st hs hds => ?_⟩
    · count_prefix st (LExpr.fvar m x ty)
      exact (WC.nil st₁).congr hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    · rw [collectSubexprs.walkSpine]; exact WC.nil st
  | bvar m i =>
    refine ⟨fun st hs hds => ?_, fun st hs hds => ?_⟩
    · count_prefix st (LExpr.bvar m i)
      exact (WC.nil st₁).congr hsC hdC (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    · rw [collectSubexprs.walkSpine]; exact WC.nil st

/-! ## Visits of rewritten expressions -/

/-- Visits reach subterms. -/
theorem occ_sub : ∀ (e : Expression.Expr), (∀ c ∈ occ e, ∃ s, IsSub s e ∧ c = E s) ∧
    (∀ c ∈ spOcc e, ∃ s, IsSub s e ∧ s ≠ e ∧ c = E s) := by
  intro e
  induction e with
  | app m f a ihf iha =>
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · simp only [occ] at hc
      split at hc
      · simp only [E_app, List.mem_cons, List.not_mem_nil, or_false] at hc; exact ⟨_, .refl _, hc⟩
      · rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨s, h1, -, h3⟩ := ihf.2 c hc; exact ⟨s, .app₁ _ _ _ h1, h3⟩
        · obtain ⟨s, h1, h3⟩ := iha.1 c hc; exact ⟨s, .app₂ _ _ _ h1, h3⟩
    · simp only [spOcc] at hc
      have hlt : ∀ s, IsSub s f ∨ IsSub s a → s ≠ .app m f a := fun s hs he => by
        subst he; rcases hs with hs | hs <;> (have := hs.size_le; simp [esize] at this; omega)
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨s, h1, -, h3⟩ := ihf.2 c hc; exact ⟨s, .app₁ _ _ _ h1, hlt s (Or.inl h1), h3⟩
      · obtain ⟨s, h1, h3⟩ := iha.1 c hc; exact ⟨s, .app₂ _ _ _ h1, hlt s (Or.inr h1), h3⟩
  | ite m c t f ihc iht ihf =>
    refine ⟨fun x hx => ?_, fun x hx => by simp [spOcc] at hx⟩
    simp only [occ] at hx
    split at hx
    · simp only [E_ite, List.mem_cons, List.not_mem_nil, or_false] at hx; exact ⟨_, .refl _, hx⟩
    · simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · obtain ⟨s, h1, h3⟩ := ihc.1 x hx; exact ⟨s, .ite₁ _ _ _ _ h1, h3⟩
      · obtain ⟨s, h1, h3⟩ := iht.1 x hx; exact ⟨s, .ite₂ _ _ _ _ h1, h3⟩
      · obtain ⟨s, h1, h3⟩ := ihf.1 x hx; exact ⟨s, .ite₃ _ _ _ _ h1, h3⟩
  | eq m a b iha ihb =>
    refine ⟨fun x hx => ?_, fun x hx => by simp [spOcc] at hx⟩
    simp only [occ] at hx
    split at hx
    · simp only [E_eq, List.mem_cons, List.not_mem_nil, or_false] at hx; exact ⟨_, .refl _, hx⟩
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨s, h1, h3⟩ := iha.1 x hx; exact ⟨s, .eq₁ _ _ _ h1, h3⟩
      · obtain ⟨s, h1, h3⟩ := ihb.1 x hx; exact ⟨s, .eq₂ _ _ _ h1, h3⟩
  | _ => exact ⟨fun c hc => by simp [occ] at hc, fun c hc => by simp [spOcc] at hc⟩

/-- The expansion of a node reaches its proper subterms. -/
theorem occK_sub (d : Expression.Expr) : ∀ c ∈ occK d, ∃ s, IsSub s d ∧ s ≠ d ∧ c = E s := by
  intro c hc
  have hne : ∀ s, IsSub s d → esize s < esize d → s ≠ d := fun s _ h he => by subst he; omega
  cases d with
  | app m f a =>
    simp only [occK] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨s, h1, -, h3⟩ := (occ_sub f).2 c hc
      exact ⟨s, .app₁ _ _ _ h1, hne s (.app₁ _ _ _ h1) (by have := h1.size_le; simp [esize]; omega), h3⟩
    · obtain ⟨s, h1, h3⟩ := (occ_sub a).1 c hc
      exact ⟨s, .app₂ _ _ _ h1, hne s (.app₂ _ _ _ h1) (by have := h1.size_le; simp [esize]; omega), h3⟩
  | ite m x t f =>
    simp only [occK, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · obtain ⟨s, h1, h3⟩ := (occ_sub x).1 c hc
      exact ⟨s, .ite₁ _ _ _ _ h1, hne s (.ite₁ _ _ _ _ h1) (by have := h1.size_le; simp [esize]; omega), h3⟩
    · obtain ⟨s, h1, h3⟩ := (occ_sub t).1 c hc
      exact ⟨s, .ite₂ _ _ _ _ h1, hne s (.ite₂ _ _ _ _ h1) (by have := h1.size_le; simp [esize]; omega), h3⟩
    · obtain ⟨s, h1, h3⟩ := (occ_sub f).1 c hc
      exact ⟨s, .ite₃ _ _ _ _ h1, hne s (.ite₃ _ _ _ _ h1) (by have := h1.size_le; simp [esize]; omega), h3⟩
  | eq m a b =>
    simp only [occK] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨s, h1, h3⟩ := (occ_sub a).1 c hc
      exact ⟨s, .eq₁ _ _ _ h1, hne s (.eq₁ _ _ _ h1) (by have := h1.size_le; simp [esize]; omega), h3⟩
    · obtain ⟨s, h1, h3⟩ := (occ_sub b).1 c hc
      exact ⟨s, .eq₂ _ _ _ h1, hne s (.eq₂ _ _ _ h1) (by have := h1.size_le; simp [esize]; omega), h3⟩
  | _ => simp [occK] at hc

/-- A visited class is erased and eligible. -/
theorem occ_elig : ∀ (e : Expression.Expr), (∀ c ∈ occ e, E c = c ∧ elig c = true) ∧
    (∀ c ∈ spOcc e, E c = c ∧ elig c = true) := by
  intro e
  induction e with
  | app m f a ihf iha =>
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · simp only [occ] at hc
      split at hc
      · rename_i h; simp only [E_app, List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc
        exact ⟨E_E (LExpr.app m f a), (elig_E (LExpr.app m f a)).trans h⟩
      · rcases List.mem_append.mp hc with hc | hc
        · exact ihf.2 c hc
        · exact iha.1 c hc
    · simp only [spOcc] at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ihf.2 c hc
      · exact iha.1 c hc
  | ite m c t f ihc iht ihf =>
    refine ⟨fun x hx => ?_, fun x hx => by simp [spOcc] at hx⟩
    simp only [occ] at hx
    split at hx
    · rename_i h; simp only [E_ite, List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx
      exact ⟨E_E (LExpr.ite m c t f), (elig_E (LExpr.ite m c t f)).trans h⟩
    · simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact ihc.1 x hx
      · exact iht.1 x hx
      · exact ihf.1 x hx
  | eq m a b iha ihb =>
    refine ⟨fun x hx => ?_, fun x hx => by simp [spOcc] at hx⟩
    simp only [occ] at hx
    split at hx
    · rename_i h; simp only [E_eq, List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx
      exact ⟨E_E (LExpr.eq m a b), (elig_E (LExpr.eq m a b)).trans h⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact iha.1 x hx
      · exact ihb.1 x hx
  | _ => exact ⟨fun c hc => by simp [occ] at hc, fun c hc => by simp [spOcc] at hc⟩

/-- An expanded class is erased and eligible. -/
theorem occK_elig (d : Expression.Expr) : ∀ c ∈ occK d, E c = c ∧ elig c = true := by
  intro c hc
  cases d with
  | app m f a =>
    simp only [occK] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (occ_elig f).2 c hc
    · exact (occ_elig a).1 c hc
  | ite m x t f =>
    simp only [occK, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact (occ_elig x).1 c hc
    · exact (occ_elig t).1 c hc
    · exact (occ_elig f).1 c hc
  | eq m a b =>
    simp only [occK] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (occ_elig a).1 c hc
    · exact (occ_elig b).1 c hc
  | _ => simp [occK] at hc

/-! ## Duplicates of a list of expressions -/

/-- `R` lists, once each, the classes the visits `Rt` reach: each is visited by `Rt` or by the
    expansion of a class of `R`, and each reached class is in `R`. -/
def IsReachList (Rt R : List Expression.Expr) : Prop :=
  R.Nodup ∧ (∀ c, c ∈ R ↔ c ∈ Rt ++ R.flatMap occK) ∧ (∀ d ∈ R, d ∈ Rt ∨ ∃ d' ∈ R, d ∈ occK d')

/-- The classes reached from the visits `Rt`. -/
inductive Reach (Rt : List Expression.Expr) : Expression.Expr → Prop
  | root {c} : c ∈ Rt → Reach Rt c
  | step {d c} : Reach Rt d → c ∈ occK d → Reach Rt c

/-- An expanded class is smaller. -/
theorem esize_lt_of_occK {d c : Expression.Expr} (h : c ∈ occK d) : esize c < esize d := by
  obtain ⟨s, h1, h2, rfl⟩ := occK_sub d c h
  rw [esize_E]
  exact IsPSub.size_lt ⟨h1, h2⟩

/-- Every entry's size is at most the largest. -/
theorem foldr_max_le : ∀ (R : List Expression.Expr), ∀ d ∈ R,
    esize d ≤ R.foldr (fun d m => max (esize d) m) 0 := by
  intro R
  induction R with
  | nil => intro d hd; simp at hd
  | cons x xs ih =>
    intro d hd
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih d hd) (Nat.le_max_right _ _)

/-- A reach list holds exactly the reached classes. -/
theorem IsReachList.mem_iff {Rt R : List Expression.Expr} (h : IsReachList Rt R) :
    ∀ c, c ∈ R ↔ Reach Rt c := by
  obtain ⟨_, hcl, hwf⟩ := h
  intro c
  constructor
  · intro hc
    let B := R.foldr (fun d m => max (esize d) m) 0
    have hB : ∀ d ∈ R, esize d ≤ B := foldr_max_le R
    suffices H : ∀ k, ∀ d ∈ R, B - esize d = k → Reach Rt d from H _ c hc rfl
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro d hd hk
      rcases hwf d hd with h | ⟨d', hd', h⟩
      · exact .root h
      · have h1 := esize_lt_of_occK h
        have h2 := hB d' hd'
        exact .step (ih (B - esize d') (by omega) d' hd' rfl) h
  · intro hc
    induction hc with
    | root h => exact (hcl _).mpr (List.mem_append_left _ h)
    | step _ h ih => exact (hcl _).mpr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ih, h⟩))

/-- Two reach lists of the same visits are permutations of each other. -/
theorem IsReachList.perm {Rt R R' : List Expression.Expr} (h : IsReachList Rt R)
    (h' : IsReachList Rt R') : R.Perm R' :=
  (List.perm_ext_iff_of_nodup h.1 h'.1).mpr fun c => by rw [h.mem_iff, h'.mem_iff]

/-- Walking a list of expressions from a state satisfying the hypotheses. -/
theorem walk_foldl_count : ∀ (exprs : List Expression.Expr) (st : CollectedExprs), WInv st →
    (∀ c, dupC st c → seenC st c) →
    WC st (exprs.flatMap occ) (exprs.foldl (fun st e => (collectSubexprs st e).2) st) := by
  intro exprs
  induction exprs with
  | nil => intro st _ _; exact WC.nil st
  | cons r rs ih =>
    intro st hs hds
    have w1 := (walk_count r).1 st hs hds
    have i1 := ((walk_spec r).1 st hs).1
    have w2 := ih _ i1 (w1.dupSub hds)
    simp only [List.foldl_cons, List.flatMap_cons]
    exact w1.append w2

/-- **What the walk records.** Walking a list of expressions from the empty state gives the
    classes reached from their visits as `seen`, and as `dups` the classes visited at least
    twice, counting the visits of the expressions and of the expansions of the reached
    classes. -/
theorem walk_forest (exprs : List Expression.Expr) :
    ∃ R, IsReachList (exprs.flatMap occ) R ∧
      (∀ c, seenC (exprs.foldl (fun st e => (collectSubexprs st e).2) {}) c ↔ c ∈ R) ∧
      (∀ c, dupC (exprs.foldl (fun st e => (collectSubexprs st e).2) {}) c ↔
        2 ≤ cnt c (exprs.flatMap occ ++ R.flatMap occK)) := by
  have h0s : ∀ c, ¬ seenC ({} : CollectedExprs) c := fun c ⟨h, x, hx, _⟩ => by simp at hx
  have h0d : ∀ c, ¬ dupC ({} : CollectedExprs) c := fun c ⟨h, x, hx, _⟩ => by simp at hx
  obtain ⟨R, hn, hm, hs, hd, hr⟩ := walk_foldl_count exprs {} WInv_empty (fun c h => absurd h (h0d c))
  refine ⟨R, ⟨hn, fun c => by rw [hm]; simp [h0s c], hr⟩, fun c => ?_, fun c => ?_⟩
  · rw [hs, hm]; simp [h0s c]
  · rw [hd]; simp [h0d c, h0s c]

/-! ## Naming a set of nodes, seen by the walk -/

section NamingT
variable (TL : List NTarget)

/-- `TL` names none of `e`'s subterms (it may name `e`'s variables). -/
def NoneIn (e : Expression.Expr) : Prop := ∀ t ∈ TL, ¬ IsSub t.1 e

/-- No generated name of `TL` is a variable of `e`. -/
def FreshIn (e : Expression.Expr) : Prop := ∀ t ∈ TL, cseName t.2.1 ∉ vars e

/-- No node of `TL` is the function of an application inside `e`. -/
def NoFnT (e : Expression.Expr) : Prop :=
  ∀ m f a, IsSub (.app m f a) e → f ∉ TL.map (·.1)

/-- A subterm of a fresh expression is fresh. -/
theorem FreshIn.sub {c e : Expression.Expr} (h : FreshIn TL e) (hc : IsSub c e) : FreshIn TL c :=
  fun t ht hv => h t ht (hc.vars_subset _ hv)

/-- `NoFnT` holds for subterms. -/
theorem NoFnT.sub {c e : Expression.Expr} (h : NoFnT TL e) (hc : IsSub c e) : NoFnT TL c :=
  fun m f a hs => h m f a (hs.trans hc)

/-- `NoneIn` holds for subterms. -/
theorem NoneIn.sub {c e : Expression.Expr} (h : NoneIn TL e) (hc : IsSub c e) : NoneIn TL c :=
  fun t ht hs => h t ht (hs.trans hc)

/-- Naming nothing inside `e` changes nothing. -/
theorem rwE_self : ∀ (e : Expression.Expr), NoneIn TL e → rwE (ρL TL) e = e := by
  have hnone : ∀ e, NoneIn TL e → ρL TL e = none := fun e h =>
    ρL_eq_none (fun hm => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm; exact h t ht (.refl _))
  intro e
  induction e with
  | app m f a ihf iha =>
    intro h; rw [rwE_eq, hnone _ h]
    simp only [Option.getD_none, rwKids, ihf (h.sub TL (.app₁ _ _ _ (.refl _))),
      iha (h.sub TL (.app₂ _ _ _ (.refl _)))]
  | ite m c t f ihc iht ihf =>
    intro h; rw [rwE_eq, hnone _ h]
    simp only [Option.getD_none, rwKids, ihc (h.sub TL (.ite₁ _ _ _ _ (.refl _))),
      iht (h.sub TL (.ite₂ _ _ _ _ (.refl _))), ihf (h.sub TL (.ite₃ _ _ _ _ (.refl _)))]
  | eq m a b iha ihb =>
    intro h; rw [rwE_eq, hnone _ h]
    simp only [Option.getD_none, rwKids, iha (h.sub TL (.eq₁ _ _ _ (.refl _))),
      ihb (h.sub TL (.eq₂ _ _ _ (.refl _)))]
  | abs m n ty b ih =>
    intro h; rw [rwE_eq, hnone _ h]
    simp only [Option.getD_none, rwKids, ih (h.sub TL (.abs _ _ _ _ (.refl _)))]
  | quant m k n ty tr b ihtr ihb =>
    intro h; rw [rwE_eq, hnone _ h]
    simp only [Option.getD_none, rwKids, ihtr (h.sub TL (.quant₁ _ _ _ _ _ _ (.refl _))),
      ihb (h.sub TL (.quant₂ _ _ _ _ _ _ (.refl _)))]
  | _ => intro h; rw [rwE_eq, hnone _ h]; rfl

/-- Rewriting an erased expression gives an erased expression. -/
theorem E_rwE : ∀ (e : Expression.Expr), E e = e → E (rwE (ρL TL) e) = rwE (ρL TL) e := by
  intro e
  induction e with
  | app m f a ihf iha =>
    intro h; rw [rwE_eq]
    cases hρ : ρL TL (.app m f a) with
    | some v => obtain ⟨t, -, -, rfl⟩ := ρL_eq_some hρ; rfl
    | none =>
      obtain ⟨rfl, hf, ha⟩ := E_eq_self_app h
      simp only [Option.getD_none, rwKids, E_app, ihf hf, iha ha]
  | ite m c t f ihc iht ihf =>
    intro h; rw [rwE_eq]
    cases hρ : ρL TL (.ite m c t f) with
    | some v => obtain ⟨t, -, -, rfl⟩ := ρL_eq_some hρ; rfl
    | none =>
      simp only [E_ite, LExpr.ite.injEq] at h
      obtain ⟨rfl, hc, ht, hf⟩ := h
      simp only [Option.getD_none, rwKids, E_ite, ihc hc, iht ht, ihf hf]
  | eq m a b iha ihb =>
    intro h; rw [rwE_eq]
    cases hρ : ρL TL (.eq m a b) with
    | some v => obtain ⟨t, -, -, rfl⟩ := ρL_eq_some hρ; rfl
    | none =>
      simp only [E_eq, LExpr.eq.injEq] at h
      obtain ⟨rfl, ha, hb⟩ := h
      simp only [Option.getD_none, rwKids, E_eq, iha ha, ihb hb]
  | abs m n ty b ih =>
    intro h; rw [rwE_eq]
    cases hρ : ρL TL (.abs m n ty b) with
    | some v => obtain ⟨t, -, -, rfl⟩ := ρL_eq_some hρ; rfl
    | none =>
      simp only [E_abs, LExpr.abs.injEq] at h
      obtain ⟨rfl, -, -, hb⟩ := h
      simp only [Option.getD_none, rwKids, E_abs, ih hb]
  | quant m k n ty tr b ihtr ihb =>
    intro h; rw [rwE_eq]
    cases hρ : ρL TL (.quant m k n ty tr b) with
    | some v => obtain ⟨t, -, -, rfl⟩ := ρL_eq_some hρ; rfl
    | none =>
      simp only [E_quant, LExpr.quant.injEq] at h
      obtain ⟨rfl, -, -, -, htr, hb⟩ := h
      simp only [Option.getD_none, rwKids, E_quant, ihtr htr, ihb hb]
  | _ =>
    intro h; rw [rwE_eq]
    revert h
    generalize hρ : ρL TL _ = o
    intro h
    cases o with
    | some v => obtain ⟨t, -, -, rfl⟩ := ρL_eq_some hρ; rfl
    | none => exact h

/-- A rewrite node by node: `rwE` at `e`, by the replacement or the node with its children
    rewritten. -/
theorem rwE_cases (e : Expression.Expr) :
    (∃ t ∈ TL, t.1 = e ∧ rwE (ρL TL) e = cseVar t.2.1 t.2.2) ∨
      (e ∉ TL.map (·.1) ∧ rwE (ρL TL) e = rwKids (ρL TL) e) := by
  rw [rwE_eq]
  cases hρ : ρL TL e with
  | some v =>
    obtain ⟨t, ht, h1, rfl⟩ := ρL_eq_some hρ
    exact Or.inl ⟨t, ht, h1, rfl⟩
  | none =>
    refine Or.inr ⟨fun hm => ?_, rfl⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    obtain ⟨t', -, ht'⟩ := ρL_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩)
    rw [hρ] at ht'; cases ht'

/-- Naming bvar-free nodes keeps bound variables. -/
theorem hasBVar_rwE (hb : ∀ t ∈ TL, LExpr.hasBVar t.1 = false) :
    ∀ (e : Expression.Expr), LExpr.hasBVar (rwE (ρL TL) e) = LExpr.hasBVar e := by
  intro e
  induction e with
  | app m f a ihf iha =>
    rcases rwE_cases TL (.app m f a) with ⟨t, ht, h1, h2⟩ | ⟨-, h2⟩
    · rw [h2, ← h1, hb t ht]; rfl
    · rw [h2]; simp only [rwKids, LExpr.hasBVar, ihf, iha]
  | ite m c t f ihc iht ihf =>
    rcases rwE_cases TL (.ite m c t f) with ⟨t', ht, h1, h2⟩ | ⟨-, h2⟩
    · rw [h2, ← h1, hb t' ht]; rfl
    · rw [h2]; simp only [rwKids, LExpr.hasBVar, ihc, iht, ihf]
  | eq m a b iha ihb =>
    rcases rwE_cases TL (.eq m a b) with ⟨t, ht, h1, h2⟩ | ⟨-, h2⟩
    · rw [h2, ← h1, hb t ht]; rfl
    · rw [h2]; simp only [rwKids, LExpr.hasBVar, iha, ihb]
  | abs m n ty b ih =>
    rcases rwE_cases TL (.abs m n ty b) with ⟨t, ht, h1, h2⟩ | ⟨-, h2⟩
    · rw [h2, ← h1, hb t ht]; rfl
    · rw [h2]; simp only [rwKids, LExpr.hasBVar, ih]
  | quant m k n ty tr b ihtr ihb =>
    rcases rwE_cases TL (.quant m k n ty tr b) with ⟨t, ht, h1, h2⟩ | ⟨-, h2⟩
    · rw [h2, ← h1, hb t ht]; rfl
    · rw [h2]; simp only [rwKids, LExpr.hasBVar, ihtr, ihb]
  | _ =>
    rename_i e0
    rcases rwE_cases TL _ with ⟨t, ht, h1, h2⟩ | ⟨-, h2⟩
    · rw [h2, ← h1, hb t ht]; rfl
    · rw [h2]; rfl

/-- A named node inside `e` leaves a generated name in the rewrite of `e`. -/
theorem vars_rwE_of_sub : ∀ (e : Expression.Expr) (t : NTarget), t ∈ TL → IsSub t.1 e →
    ∃ t' ∈ TL, cseName t'.2.1 ∈ vars (rwE (ρL TL) e) := by
  intro e t ht hs
  induction hs with
  | refl =>
    rcases rwE_cases TL t.1 with ⟨t', ht', -, h2⟩ | ⟨h1, -⟩
    · exact ⟨t', ht', by rw [h2]; simp [cseVar, vars, LExpr.LExpr.getVars]⟩
    · exact absurd (List.mem_map.mpr ⟨t, ht, rfl⟩) h1
  | app₁ m f x _ ih =>
    rcases rwE_cases TL (.app m f x) with ⟨t', ht', -, h2⟩ | ⟨-, h2⟩
    · exact ⟨t', ht', by rw [h2]; simp [cseVar, vars, LExpr.LExpr.getVars]⟩
    · obtain ⟨t', ht', hv⟩ := ih
      exact ⟨t', ht', by rw [h2]; simp only [vars, rwKids, LExpr.LExpr.getVars, List.mem_append] at hv ⊢; exact Or.inl hv⟩
  | app₂ m f x _ ih =>
    rcases rwE_cases TL (.app m f x) with ⟨t', ht', -, h2⟩ | ⟨-, h2⟩
    · exact ⟨t', ht', by rw [h2]; simp [cseVar, vars, LExpr.LExpr.getVars]⟩
    · obtain ⟨t', ht', hv⟩ := ih
      exact ⟨t', ht', by rw [h2]; simp only [vars, rwKids, LExpr.LExpr.getVars, List.mem_append] at hv ⊢; exact Or.inr hv⟩
  | ite₁ m c u f _ ih =>
    rcases rwE_cases TL (.ite m c u f) with ⟨t', ht', -, h2⟩ | ⟨-, h2⟩
    · exact ⟨t', ht', by rw [h2]; simp [cseVar, vars, LExpr.LExpr.getVars]⟩
    · obtain ⟨t', ht', hv⟩ := ih
      exact ⟨t', ht', by rw [h2]; simp only [vars, rwKids, LExpr.LExpr.getVars, List.append_assoc, List.mem_append] at hv ⊢; exact Or.inl hv⟩
  | ite₂ m c u f _ ih =>
    rcases rwE_cases TL (.ite m c u f) with ⟨t', ht', -, h2⟩ | ⟨-, h2⟩
    · exact ⟨t', ht', by rw [h2]; simp [cseVar, vars, LExpr.LExpr.getVars]⟩
    · obtain ⟨t', ht', hv⟩ := ih
      exact ⟨t', ht', by rw [h2]; simp only [vars, rwKids, LExpr.LExpr.getVars, List.append_assoc, List.mem_append] at hv ⊢
                         exact Or.inr (Or.inl hv)⟩
  | ite₃ m c u f _ ih =>
    rcases rwE_cases TL (.ite m c u f) with ⟨t', ht', -, h2⟩ | ⟨-, h2⟩
    · exact ⟨t', ht', by rw [h2]; simp [cseVar, vars, LExpr.LExpr.getVars]⟩
    · obtain ⟨t', ht', hv⟩ := ih
      exact ⟨t', ht', by rw [h2]; simp only [vars, rwKids, LExpr.LExpr.getVars, List.append_assoc, List.mem_append] at hv ⊢
                         exact Or.inr (Or.inr hv)⟩
  | eq₁ m x y _ ih =>
    rcases rwE_cases TL (.eq m x y) with ⟨t', ht', -, h2⟩ | ⟨-, h2⟩
    · exact ⟨t', ht', by rw [h2]; simp [cseVar, vars, LExpr.LExpr.getVars]⟩
    · obtain ⟨t', ht', hv⟩ := ih
      exact ⟨t', ht', by rw [h2]; simp only [vars, rwKids, LExpr.LExpr.getVars, List.mem_append] at hv ⊢; exact Or.inl hv⟩
  | eq₂ m x y _ ih =>
    rcases rwE_cases TL (.eq m x y) with ⟨t', ht', -, h2⟩ | ⟨-, h2⟩
    · exact ⟨t', ht', by rw [h2]; simp [cseVar, vars, LExpr.LExpr.getVars]⟩
    · obtain ⟨t', ht', hv⟩ := ih
      exact ⟨t', ht', by rw [h2]; simp only [vars, rwKids, LExpr.LExpr.getVars, List.mem_append] at hv ⊢; exact Or.inr hv⟩
  | abs m n ty b _ ih =>
    rcases rwE_cases TL (.abs m n ty b) with ⟨t', ht', -, h2⟩ | ⟨-, h2⟩
    · exact ⟨t', ht', by rw [h2]; simp [cseVar, vars, LExpr.LExpr.getVars]⟩
    · obtain ⟨t', ht', hv⟩ := ih
      exact ⟨t', ht', by rw [h2]; simp only [vars, rwKids, LExpr.LExpr.getVars] at hv ⊢; exact hv⟩
  | quant₁ m k n ty tr b _ ih =>
    rcases rwE_cases TL (.quant m k n ty tr b) with ⟨t', ht', -, h2⟩ | ⟨-, h2⟩
    · exact ⟨t', ht', by rw [h2]; simp [cseVar, vars, LExpr.LExpr.getVars]⟩
    · obtain ⟨t', ht', hv⟩ := ih
      exact ⟨t', ht', by rw [h2]; simp only [vars, rwKids, LExpr.LExpr.getVars, List.mem_append] at hv ⊢; exact Or.inl hv⟩
  | quant₂ m k n ty tr b _ ih =>
    rcases rwE_cases TL (.quant m k n ty tr b) with ⟨t', ht', -, h2⟩ | ⟨-, h2⟩
    · exact ⟨t', ht', by rw [h2]; simp [cseVar, vars, LExpr.LExpr.getVars]⟩
    · obtain ⟨t', ht', hv⟩ := ih
      exact ⟨t', ht', by rw [h2]; simp only [vars, rwKids, LExpr.LExpr.getVars, List.mem_append] at hv ⊢; exact Or.inr hv⟩

/-- A generated variable is not a rewritten node with its children rewritten, unless that node
    is a variable with the generated name. -/
theorem cseVar_ne_rwKids {e : Expression.Expr} (hf : FreshIn TL e) {t : NTarget} (ht : t ∈ TL)
    (h : cseVar t.2.1 t.2.2 = rwKids (ρL TL) e) : False := by
  cases e with
  | fvar m y ty =>
    simp only [rwKids, cseVar, LExpr.fvar.injEq] at h
    exact hf t ht (by rw [← h.2.1]; simp [vars, LExpr.LExpr.getVars])
  | _ => simp [rwKids, cseVar] at h

/-- Rewriting the children with no replacement changes nothing. -/
theorem rwKids_none (e : Expression.Expr) : rwKids (fun _ => none) e = e := by
  cases e <;> simp [rwKids, rwE_none]

/-- **Naming is injective** on erased expressions that mention no generated name, when the
    named classes are erased, distinct and none is a proper subterm of another, and their
    indices are distinct: unfolding the names inverts it. -/
theorem rwE_inj (hcls : (TL.map (·.1)).Nodup) (hidx : (TL.map (·.2.1)).Nodup)
    (hE : ∀ t ∈ TL, E t.1 = t.1)
    (hinc : ∀ t ∈ TL, ∀ t' ∈ TL, ¬ IsPSub t'.1 t.1)
    {e₁ e₂ : Expression.Expr} (h₁ : E e₁ = e₁) (h₂ : E e₂ = e₂) (f₁ : FreshIn TL e₁)
    (f₂ : FreshIn TL e₂) (h : rwE (ρL TL) e₁ = rwE (ρL TL) e₂) : e₁ = e₂ := by
  let Z : List (NTarget × Expression.Expr) := TL.map fun t => (t, t.1)
  have hZ1 : Z.map (·.1) = TL := by
    simp only [Z, List.map_map]; exact List.map_id' _
  have hu : ∀ e, E e = e → FreshIn TL e →
      E (unfold (Z.map fun z => (z.1.2.1, z.1.2.2, z.2)) (rwE (ρL TL) e)) = e := by
    intro e he hf
    have := unfold_rwE Z (by
        have : Z.map (·.1.1) = (Z.map (·.1)).map (·.1) := by simp [List.map_map]
        rw [this, hZ1]; exact hcls)
      (by simp only [Z, List.map_map]; exact hidx)
      (fun i hi => ?_) e he (fun z hz => ?_)
    · rw [hZ1] at this; exact this
    · simp only [Z, List.getElem_map]
      have ht : TL[i]'(by simpa [Z] using hi) ∈ TL := List.getElem_mem _
      rw [hE _ ht]
      rw [rwKids_congr (ρ₂ := fun _ => none) _ (fun c hc => ?_), rwKids_none]
      apply ρL_eq_none
      intro hm
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hm
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ht'
      obtain ⟨t3, ht3, rfl⟩ := List.mem_map.mp ((List.take_sublist i _).subset hz)
      exact hinc _ ht _ ht3 hc
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
      exact hf t ht
  rw [← hu e₁ h₁ f₁, ← hu e₂ h₂ f₂, h]

/-- A rewritten expression that mentions no generated name is not a named class, when no named
    class mentions a generated name. -/
theorem rwE_not_mem (hT : ∀ t ∈ TL, FreshIn TL t.1) (e : Expression.Expr) :
    rwE (ρL TL) e ∉ TL.map (·.1) := by
  intro hm
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp hm
  by_cases hn : NoneIn TL e
  · rw [rwE_self TL e hn] at hte
    exact hn t ht (by rw [hte]; exact .refl _)
  · obtain ⟨t', ht', hs⟩ : ∃ t' ∈ TL, IsSub t'.1 e := by
      apply Classical.byContradiction
      intro hc
      exact hn (fun t ht hs => hc ⟨t, ht, hs⟩)
    obtain ⟨t'', ht'', hv⟩ := vars_rwE_of_sub TL e t' ht' hs
    rw [← hte] at hv
    exact hT t ht t'' ht'' hv

open Classical in
/-- The rewrite of a visited class: dropped if named, rewritten otherwise. -/
noncomputable def gT (c : Expression.Expr) : Option Expression.Expr :=
  if c ∈ TL.map (fun t : NTarget => t.1) then none else some (rwE (ρL TL) c)

/-- Rewriting keeps eligibility away from the named classes. -/
theorem elig_rwKids (hb : ∀ t ∈ TL, LExpr.hasBVar t.1 = false) (e : Expression.Expr) :
    elig (rwKids (ρL TL) e) = elig e := by
  cases e <;> simp [rwKids, elig, LExpr.hasBVar, hasBVar_rwE TL hb]

set_option hygiene false in
/-- The visits of a rewritten node other than an `app`, `ite` or `eq`: none. -/
scoped macro "leaf_rw" e:term : tactic => `(tactic| (
  intro he
  try intro _
  rcases rwE_cases TL $e with ⟨t, ht, h1, -⟩ | ⟨-, h2⟩
  · have := hel t ht; rw [h1] at this; simp [elig] at this
  · rw [h2]; exact ⟨by simp [rwKids, occ], by simp [rwKids, spOcc]⟩))

/-- **Visits of a rewritten expression.** If no named class is the function of an
    application, the visits of the rewrite of an erased expression are the rewrites of its
    visits, with the named classes dropped (and so for the spine walk of an unnamed node). -/
theorem occ_rwE (hel : ∀ t ∈ TL, elig t.1 = true) (hb : ∀ t ∈ TL, LExpr.hasBVar t.1 = false) :
    ∀ (e : Expression.Expr), E e = e → NoFnT TL e →
      occ (rwE (ρL TL) e) = (occ e).filterMap (gT TL) ∧
      (e ∉ TL.map (·.1) → spOcc (rwE (ρL TL) e) = (spOcc e).filterMap (gT TL)) := by
  have hnamed : ∀ e, E e = e → (∃ t ∈ TL, t.1 = e ∧ rwE (ρL TL) e = cseVar t.2.1 t.2.2) →
      occ (rwE (ρL TL) e) = (occ e).filterMap (gT TL) := by
    rintro e he ⟨t, ht, rfl, h2⟩
    rw [h2, occ_eq t.1, ite_eq_left (hel t ht), he]
    simp [cseVar, occ, gT, List.mem_map.mpr ⟨t, ht, rfl⟩]
  have helig : ∀ e, E e = e → e ∉ TL.map (·.1) → elig e = true →
      rwE (ρL TL) e = rwKids (ρL TL) e →
      occ (rwE (ρL TL) e) = (occ e).filterMap (gT TL) := by
    intro e he hm hel' h2
    have hel2 : elig (rwE (ρL TL) e) = true := by rw [h2, elig_rwKids TL hb]; exact hel'
    rw [occ_eq, ite_eq_left hel2, occ_eq e, ite_eq_left hel', he, E_rwE TL e he]
    simp [gT, hm]
  intro e
  induction e with
  | app m f a ihf iha =>
    intro he hfn
    obtain ⟨rfl, hf, ha⟩ := E_eq_self_app he
    have hfm : f ∉ TL.map (·.1) := hfn _ _ _ (.refl _)
    have ihf' := (ihf hf (hfn.sub TL (.app₁ _ _ _ (.refl _)))).2 hfm
    have iha' := (iha ha (hfn.sub TL (.app₂ _ _ _ (.refl _)))).1
    rcases rwE_cases TL (.app valueLoc f a) with hn | ⟨hm, h2⟩
    · exact ⟨hnamed _ he hn, fun hm => by
        obtain ⟨t, ht, h1, -⟩ := hn; exact absurd (List.mem_map.mpr ⟨t, ht, h1⟩) hm⟩
    · refine ⟨?_, fun _ => ?_⟩
      · by_cases hel' : elig (.app valueLoc f a) = true
        · exact helig _ he hm hel' h2
        · have hel2 : elig (rwE (ρL TL) (.app valueLoc f a)) = false := by
            rw [h2, elig_rwKids TL hb]; simpa using hel'
          rw [occ_eq, ite_eq_right (by simp [hel2]), occ_eq (.app valueLoc f a),
            ite_eq_right hel', h2]
          simp only [rwKids, occK, List.filterMap_append, ihf', iha']
      · rw [h2]; simp only [rwKids, spOcc, List.filterMap_append, ihf', iha']
  | ite m c t f ihc iht ihf =>
    intro he hfn
    simp only [E_ite, LExpr.ite.injEq] at he
    obtain ⟨rfl, hc, ht, hf⟩ := he
    have he : E (.ite valueLoc c t f) = .ite valueLoc c t f := by simp [hc, ht, hf]
    have ihc' := (ihc hc (hfn.sub TL (.ite₁ _ _ _ _ (.refl _)))).1
    have iht' := (iht ht (hfn.sub TL (.ite₂ _ _ _ _ (.refl _)))).1
    have ihf' := (ihf hf (hfn.sub TL (.ite₃ _ _ _ _ (.refl _)))).1
    rcases rwE_cases TL (.ite valueLoc c t f) with hn | ⟨hm, h2⟩
    · exact ⟨hnamed _ he hn, fun hm => by
        obtain ⟨t, ht, h1, -⟩ := hn; exact absurd (List.mem_map.mpr ⟨t, ht, h1⟩) hm⟩
    · refine ⟨?_, fun _ => by rw [h2]; rfl⟩
      by_cases hel' : elig (.ite valueLoc c t f) = true
      · exact helig _ he hm hel' h2
      · have hel2 : elig (rwE (ρL TL) (.ite valueLoc c t f)) = false := by
          rw [h2, elig_rwKids TL hb]; simpa using hel'
        rw [occ_eq, ite_eq_right (by simp [hel2]), occ_eq (.ite valueLoc c t f),
          ite_eq_right hel', h2]
        simp only [rwKids, occK, List.filterMap_append, ihc', iht', ihf']
  | eq m a b iha ihb =>
    intro he hfn
    simp only [E_eq, LExpr.eq.injEq] at he
    obtain ⟨rfl, ha, hb'⟩ := he
    have he : E (.eq valueLoc a b) = .eq valueLoc a b := by simp [ha, hb']
    have iha' := (iha ha (hfn.sub TL (.eq₁ _ _ _ (.refl _)))).1
    have ihb' := (ihb hb' (hfn.sub TL (.eq₂ _ _ _ (.refl _)))).1
    rcases rwE_cases TL (.eq valueLoc a b) with hn | ⟨hm, h2⟩
    · exact ⟨hnamed _ he hn, fun hm => by
        obtain ⟨t, ht, h1, -⟩ := hn; exact absurd (List.mem_map.mpr ⟨t, ht, h1⟩) hm⟩
    · refine ⟨?_, fun _ => by rw [h2]; rfl⟩
      by_cases hel' : elig (.eq valueLoc a b) = true
      · exact helig _ he hm hel' h2
      · have hel2 : elig (rwE (ρL TL) (.eq valueLoc a b)) = false := by
          rw [h2, elig_rwKids TL hb]; simpa using hel'
        rw [occ_eq, ite_eq_right (by simp [hel2]), occ_eq (.eq valueLoc a b),
          ite_eq_right hel', h2]
        simp only [rwKids, occK, List.filterMap_append, iha', ihb']
  | const m c => leaf_rw (LExpr.const m c)
  | op m o ty => leaf_rw (LExpr.op m o ty)
  | bvar m i => leaf_rw (LExpr.bvar m i)
  | fvar m x ty => leaf_rw (LExpr.fvar m x ty)
  | abs m n ty b _ => leaf_rw (LExpr.abs m n ty b)
  | quant m k n ty tr b _ _ => leaf_rw (LExpr.quant m k n ty tr b)

/-- The expansion of a rewritten unnamed node: the rewrites of its expansion, named classes
    dropped, if no named class is the function of an application. -/
theorem occK_rwE (hel : ∀ t ∈ TL, elig t.1 = true) (hb : ∀ t ∈ TL, LExpr.hasBVar t.1 = false)
    (d : Expression.Expr) (hd : E d = d) (hfn : NoFnT TL d) (hm : d ∉ TL.map (·.1)) :
    occK (rwE (ρL TL) d) = (occK d).filterMap (gT TL) := by
  rcases rwE_cases TL d with ⟨t, ht, h1, -⟩ | ⟨-, h2⟩
  · exact absurd (List.mem_map.mpr ⟨t, ht, h1⟩) hm
  rw [h2]
  cases d with
  | app m f a =>
    obtain ⟨rfl, hf, ha⟩ := E_eq_self_app hd
    simp only [rwKids, occK, List.filterMap_append,
      (occ_rwE TL hel hb f hf (hfn.sub TL (.app₁ _ _ _ (.refl _)))).2 (hfn _ _ _ (.refl _)),
      (occ_rwE TL hel hb a ha (hfn.sub TL (.app₂ _ _ _ (.refl _)))).1]
  | ite m c t f =>
    simp only [E_ite, LExpr.ite.injEq] at hd
    obtain ⟨rfl, hc, ht, hf⟩ := hd
    simp only [rwKids, occK, List.filterMap_append,
      (occ_rwE TL hel hb c hc (hfn.sub TL (.ite₁ _ _ _ _ (.refl _)))).1,
      (occ_rwE TL hel hb t ht (hfn.sub TL (.ite₂ _ _ _ _ (.refl _)))).1,
      (occ_rwE TL hel hb f hf (hfn.sub TL (.ite₃ _ _ _ _ (.refl _)))).1]
  | eq m a b =>
    simp only [E_eq, LExpr.eq.injEq] at hd
    obtain ⟨rfl, ha, hb'⟩ := hd
    simp only [rwKids, occK, List.filterMap_append,
      (occ_rwE TL hel hb a ha (hfn.sub TL (.eq₁ _ _ _ (.refl _)))).1,
      (occ_rwE TL hel hb b hb' (hfn.sub TL (.eq₂ _ _ _ (.refl _)))).1]
  | _ => simp [rwKids, occK]

end NamingT

/-- A reached class is (the erasure of) a subterm of one of the expressions. -/
theorem reach_sub {F : List Expression.Expr} {c : Expression.Expr} (h : Reach (F.flatMap occ) c) :
    ∃ r ∈ F, ∃ s, IsSub s r ∧ c = E s := by
  induction h with
  | root hc =>
    obtain ⟨r, hr, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨s, h1, h2⟩ := (occ_sub r).1 _ hc
    exact ⟨r, hr, s, h1, h2⟩
  | step _ hc ih =>
    obtain ⟨r, hr, s, h1, rfl⟩ := ih
    obtain ⟨s', h2, -, h3⟩ := occK_sub _ _ hc
    obtain ⟨s'', h4, h5⟩ := h2.transport (E_E s)
    exact ⟨r, hr, s'', h4.trans h1, h3.trans h5⟩

/-- Mapping a list without duplicates by a function injective on it. -/
theorem nodup_map_of_inj_on {α β : Type} {f : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; exact List.nodup_nil
  | cons x xs ih =>
    intro hn hinj
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih hn.2 (fun a ha b hb h => hinj a (by simp [ha]) b (by simp [hb]) h)⟩
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hm
    exact hn.1 (hinj y (by simp [hy]) x (by simp) hyx ▸ hy)

/-- `flatMap` depends only on the function at the list's entries. -/
theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- Dropping nothing and keeping every entry. -/
theorem filterMap_eq_self {g : Expression.Expr → Option Expression.Expr} :
    ∀ (l : List Expression.Expr), (∀ x ∈ l, g x = some x) → l.filterMap g = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    rw [List.filterMap_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- Counting after rewriting: a rewritten class occurs in the rewritten list as often as the
    class in the list. -/
theorem cnt_filterMap_gT (TL : List NTarget) (hcls : (TL.map (·.1)).Nodup)
    (hidx : (TL.map (·.2.1)).Nodup) (hTE : ∀ t ∈ TL, E t.1 = t.1)
    (hinc : ∀ t ∈ TL, ∀ t' ∈ TL, ¬ IsPSub t'.1 t.1) {c : Expression.Expr} (hc : E c = c)
    (hcf : FreshIn TL c) (hcT : c ∉ TL.map (·.1)) :
    ∀ (l : List Expression.Expr), (∀ y ∈ l, E y = y ∧ FreshIn TL y) →
      cnt (rwE (ρL TL) c) (l.filterMap (gT TL)) = cnt c l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y ys ih =>
    intro hl
    obtain ⟨hy1, hy2⟩ := hl y (by simp)
    have ih' := ih (fun z hz => hl z (by simp [hz]))
    rw [List.filterMap_cons]
    by_cases hyT : y ∈ TL.map (·.1)
    · have : gT TL y = none := by unfold gT; rw [ite_eq_left hyT]
      rw [this]; simp only
      rw [ih', cnt_cons, ite_eq_right (fun (h : y = c) => hcT (h ▸ hyT)), Nat.add_zero]
    · have : gT TL y = some (rwE (ρL TL) y) := by unfold gT; rw [ite_eq_right hyT]
      rw [this]; simp only
      rw [cnt_cons, cnt_cons, ih']
      congr 1
      by_cases hyc : y = c
      · subst hyc; simp
      · rw [ite_eq_right hyc,
          ite_eq_right (fun h => hyc (rwE_inj TL hcls hidx hTE hinc hy1 hc hy2 hcf h))]

/-- Named classes do not occur among rewritten ones. -/
theorem cnt_T_filterMap_gT (TL : List NTarget) (hTf : ∀ t ∈ TL, FreshIn TL t.1)
    {t : NTarget} (ht : t ∈ TL) :
    ∀ (l : List Expression.Expr), cnt t.1 (l.filterMap (gT TL)) = 0 := by
  intro l
  apply cnt_eq_zero.mpr
  intro h
  obtain ⟨y, -, hy⟩ := List.mem_filterMap.mp h
  by_cases hyT : y ∈ TL.map (·.1)
  · have : gT TL y = none := by unfold gT; rw [ite_eq_left hyT]
    rw [this] at hy; cases hy
  · have : gT TL y = some (rwE (ρL TL) y) := by unfold gT; rw [ite_eq_right hyT]
    rw [this] at hy
    simp only [Option.some.injEq] at hy
    exact rwE_not_mem TL hTf y (hy ▸ List.mem_map.mpr ⟨t, ht, rfl⟩)

/-- The classes reached by the walk of a list of erased expressions are erased subterms of
    them. -/
theorem reachList_sub {F R : List Expression.Expr} (hR : IsReachList (F.flatMap occ) R)
    (hFE : ∀ r ∈ F, E r = r) {c : Expression.Expr} (hc : c ∈ R) :
    E c = c ∧ ∃ r ∈ F, IsSub c r := by
  obtain ⟨r, hr, s, hs, rfl⟩ := reach_sub ((hR.mem_iff c).mp hc)
  have := hs.E_eq (hFE r hr)
  rw [this]
  exact ⟨this, r, hr, hs⟩

open Classical in
/-- **Naming does not change the other duplicates.** Name the classes `TL` of a list of
    erased expressions `F` that the walk reaches: distinct, eligible, none a proper subterm of
    another, none the function of an application, with fresh distinct indices. The walk of the
    declarations followed by the rewritten `F` reaches the named classes and the rewrites of the
    other reached classes; a named class it visits once, and the rewrite of any other class as
    often as the walk of `F` visits that class. -/
theorem one_step (TL : List NTarget) (F R : List Expression.Expr)
    (hR : IsReachList (F.flatMap occ) R)
    (hFE : ∀ r ∈ F, E r = r) (hFfn : ∀ r ∈ F, NoFnT TL r) (hFfr : ∀ r ∈ F, FreshIn TL r)
    (hTR : ∀ t ∈ TL, t.1 ∈ R) (hcls : (TL.map (·.1)).Nodup) (hidx : (TL.map (·.2.1)).Nodup)
    (hel : ∀ t ∈ TL, elig t.1 = true) (hinc : ∀ t ∈ TL, ∀ t' ∈ TL, ¬ IsPSub t'.1 t.1) :
    IsReachList ((TL.map (·.1) ++ F.map (rwE (ρL TL))).flatMap occ)
        (TL.map (·.1) ++ (R.filter (fun c => decide (c ∉ TL.map (·.1)))).map (rwE (ρL TL))) ∧
      ((TL.map (·.1) ++ F.map (rwE (ρL TL))).flatMap occ ++
        (TL.map (·.1) ++ (R.filter (fun c => decide (c ∉ TL.map (·.1)))).map (rwE (ρL TL))).flatMap occK).Perm
      (TL.map (·.1) ++ (F.flatMap occ ++ R.flatMap occK).filterMap (gT TL)) := by
  classical
  have hb : ∀ t ∈ TL, LExpr.hasBVar t.1 = false := fun t ht => by
    have := hel t ht; revert this; cases t.1 <;> simp [elig]
  have hRsub : ∀ c ∈ R, E c = c ∧ ∃ r ∈ F, IsSub c r := fun c hc => reachList_sub hR hFE hc
  have hRfn : ∀ c ∈ R, NoFnT TL c := fun c hc => by
    obtain ⟨-, r, hr, hs⟩ := hRsub c hc; exact (hFfn r hr).sub TL hs
  have hRfr : ∀ c ∈ R, FreshIn TL c := fun c hc => by
    obtain ⟨-, r, hr, hs⟩ := hRsub c hc; exact (hFfr r hr).sub TL hs
  have hTE : ∀ t ∈ TL, E t.1 = t.1 := fun t ht => (hRsub _ (hTR t ht)).1
  have hTf : ∀ t ∈ TL, FreshIn TL t.1 := fun t ht => hRfr _ (hTR t ht)
  -- The visits of the declarations and of the rewritten expressions.
  have hT1 : (TL.map (·.1)).flatMap occ = TL.map (·.1) := by
    have : ∀ (l : List NTarget), (∀ t ∈ l, elig t.1 = true ∧ E t.1 = t.1) →
        (l.map (·.1)).flatMap occ = l.map (·.1) := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons t ts ih =>
        intro h
        simp only [List.map_cons, List.flatMap_cons]
        rw [ih (fun t' ht' => h t' (by simp [ht'])), occ_eq, ite_eq_left (h t (by simp)).1,
          (h t (by simp)).2]; rfl
    exact this TL (fun t ht => ⟨hel t ht, hTE t ht⟩)
  have hF1 : (F.map (rwE (ρL TL))).flatMap occ = (F.flatMap occ).filterMap (gT TL) := by
    rw [List.flatMap_map, List.filterMap_flatMap]
    apply flatMap_congr'
    intro r hr
    exact (occ_rwE TL hel hb r (hFE r hr) (hFfn r hr)).1
  have hK1 : (TL.map (·.1)).flatMap occK = ((TL.map (·.1)).flatMap occK).filterMap (gT TL) := by
    symm
    apply filterMap_eq_self
    intro c hc
    obtain ⟨t', htm, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp htm
    obtain ⟨s, hs1, hs2, rfl⟩ := occK_sub _ _ hc
    have hsE : E s = s := hs1.E_eq (hTE t ht)
    rw [hsE]
    have hnT : s ∉ TL.map (·.1) := fun hm => by
      obtain ⟨t', ht', hts⟩ := List.mem_map.mp hm
      exact hinc t ht t' ht' (hts ▸ ⟨hs1, hs2⟩)
    unfold gT
    rw [ite_eq_right hnT, rwE_self TL s (fun t' ht' hsub => hinc t ht t' ht'
      ⟨hsub.trans hs1, fun he => hs2 (hs1.antisymm (he ▸ hsub))⟩)]
  have hK2 : ((R.filter (fun c => decide (c ∉ TL.map (·.1)))).map (rwE (ρL TL))).flatMap occK =
      (R.filter (fun c => decide (c ∉ TL.map (·.1)))).flatMap (fun d => (occK d).filterMap (gT TL)) := by
    rw [List.flatMap_map]
    apply flatMap_congr'
    intro d hd
    obtain ⟨hdR, hdT⟩ := List.mem_filter.mp hd
    exact occK_rwE TL hel hb d (hRsub d hdR).1 (hRfn d hdR) (by simpa using hdT)
  -- `R` splits into the named classes and the others.
  have hRsplit : R.Perm (TL.map (·.1) ++ R.filter (fun c => decide (c ∉ TL.map (·.1)))) := by
    have h1 := (List.filter_append_perm (fun c => decide (c ∈ TL.map (·.1))) R).symm
    simp only [decide_not] at h1 ⊢
    refine h1.trans (List.Perm.append_right _ ?_)
    · refine (List.perm_ext_iff_of_nodup (hR.1.filter _) hcls).mpr fun c => ?_
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro h; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h; exact ⟨hTR t ht, h⟩
  have hL : ((TL.map (·.1) ++ F.map (rwE (ρL TL))).flatMap occ ++
        (TL.map (·.1) ++ (R.filter (fun c => decide (c ∉ TL.map (·.1)))).map (rwE (ρL TL))).flatMap occK).Perm
      (TL.map (·.1) ++ (F.flatMap occ ++ R.flatMap occK).filterMap (gT TL)) := by
    rw [List.flatMap_append, List.flatMap_append, hT1, hF1, hK2, List.append_assoc]
    apply List.Perm.append_left
    rw [List.filterMap_append, hK1]
    apply List.Perm.append_left
    rw [List.filterMap_flatMap]
    have := (hRsplit.flatMap_right (fun d => (occK d).filterMap (gT TL)))
    rw [List.flatMap_append] at this
    have h2 : (R.flatMap occK).filterMap (gT TL) = R.flatMap (fun d => (occK d).filterMap (gT TL)) :=
      List.filterMap_flatMap ..
    rw [h2]
    exact this.symm
  refine ⟨⟨?_, fun c => ?_, fun d hd => ?_⟩, hL⟩
  · -- distinct
    refine List.nodup_append.mpr ⟨hcls, ?_, ?_⟩
    · refine nodup_map_of_inj_on (hR.1.filter _) ?_
      intro x hx y hy hxy
      have hx' := (List.mem_filter.mp hx).1
      have hy' := (List.mem_filter.mp hy).1
      exact rwE_inj TL hcls hidx hTE hinc (hRsub x hx').1 (hRsub y hy').1 (hRfr x hx')
        (hRfr y hy') hxy
    · intro a ha b hb hab
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hb
      exact rwE_not_mem TL hTf y (hab ▸ ha)
  · -- closed
    rw [hL.mem_iff]
    simp only [List.mem_append, List.mem_filterMap]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
        obtain ⟨hyR, hyT⟩ := List.mem_filter.mp hy
        refine ⟨y, List.mem_append.mp ((hR.2.1 y).mp hyR), ?_⟩
        unfold gT; rw [ite_eq_right (by simpa using hyT)]
    · rintro (h | ⟨y, hy, hg⟩)
      · exact Or.inl h
      · right
        unfold gT at hg
        by_cases hyT : y ∈ TL.map (·.1)
        · rw [ite_eq_left hyT] at hg; cases hg
        · rw [ite_eq_right hyT] at hg
          simp only [Option.some.injEq] at hg
          exact List.mem_map.mpr ⟨y, List.mem_filter.mpr ⟨(hR.2.1 y).mpr (List.mem_append.mpr hy),
            by simpa using hyT⟩, hg⟩
  · -- reached
    rcases List.mem_append.mp hd with hd | hd
    · exact Or.inl (List.mem_flatMap.mpr ⟨d, List.mem_append_left _ hd, by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
        rw [occ_eq, ite_eq_left (hel t ht), hTE t ht]; simp⟩)
    · obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
      obtain ⟨hd0R, hd0T⟩ := List.mem_filter.mp hd0
      have hd0T' : d0 ∉ TL.map (·.1) := by simpa using hd0T
      have hgd0 : gT TL d0 = some (rwE (ρL TL) d0) := by unfold gT; rw [ite_eq_right hd0T']
      rcases hR.2.2 d0 hd0R with h | ⟨d', hd', h⟩
      · left
        rw [List.flatMap_append, hF1]
        exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨d0, h, hgd0⟩)
      · right
        by_cases hd'T : d' ∈ TL.map (·.1)
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd'T
          obtain ⟨s, hs1, hs2, hs3⟩ := occK_sub _ _ h
          have hsE : E s = s := hs1.E_eq (hTE t ht)
          rw [hsE] at hs3
          rw [hs3, rwE_self TL s (fun t' ht' hsub => hinc t ht t' ht'
            ⟨hsub.trans hs1, fun he => hs2 (hs1.antisymm (he ▸ hsub))⟩)]
          rw [hs3] at h
          exact ⟨t.1, List.mem_append_left _ hd'T, h⟩
        · refine ⟨rwE (ρL TL) d', List.mem_append_right _ (List.mem_map.mpr
            ⟨d', List.mem_filter.mpr ⟨hd', by simpa using hd'T⟩, rfl⟩), ?_⟩
          rw [occK_rwE TL hel hb d' (hRsub d' hd').1 (hRfn d' hd') hd'T]
          exact List.mem_filterMap.mpr ⟨d0, h, hgd0⟩

/-! ## Subsumption by hashes -/

section Subsumption
variable (U : Expression.Expr → Prop)

/-- The set `acc` of hashes is closed under subterms for the classes of `U` up to size `n`. -/
def ClosedBelow (acc : Std.HashSet UInt64) (n : Nat) : Prop :=
  ∀ c, U c → esize c ≤ n → acc.contains (hx c) = true →
    ∀ c', IsSub c' c → acc.contains (hx c') = true

/-- What `collectSubexprHashes` delivers on `e`: a closed set, grown by the hashes of the
    subterms of `e` (proper ones when `top`). -/
def CshSpec (acc : Std.HashSet UInt64) (top : Bool) (e : Expression.Expr) (n : Nat)
    (acc' : Std.HashSet UInt64) : Prop :=
  ClosedBelow U acc' n ∧ ∀ h, acc'.contains h = true ↔
    acc.contains h = true ∨ ∃ c, IsSub c e ∧ (top = true → E c ≠ E e) ∧ hx c = h

/-- `hashM` computes the structural hash. -/
theorem hashM_fst (e : Expression.Expr) (s : PtrCache hx) : ((hashM e) s).1 = hx e := by
  simp only [hashM, bind, pure, stateT_bind_apply, stateT_pure_apply]
  exact ((evalPtrCache e (LExpr.hashExprPtrCache e)) s).1.h

end Subsumption

section Subsumption2
variable (U : Expression.Expr → Prop)
  (hU : ∀ a b, U a → U b → hx a = hx b → E a = E b)
  (hUsub : ∀ a b, U b → IsSub a b → U a)

/-- The children step of `collectSubexprHashes`. -/
def cshKids (acc : Std.HashSet UInt64) (e : Expression.Expr) :
    StateM (PtrCache hx) (Std.HashSet UInt64) :=
  match e with
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => pure acc
  | .app _ fn arg => do
    let acc ← collectSubexprHashes acc false fn
    collectSubexprHashes acc false arg
  | .ite _ c t f => do
    let acc ← collectSubexprHashes acc false c
    let acc ← collectSubexprHashes acc false t
    collectSubexprHashes acc false f
  | .eq _ e1 e2 => do
    let acc ← collectSubexprHashes acc false e1
    collectSubexprHashes acc false e2
  | .abs _ _ _ body => collectSubexprHashes acc false body
  | .quant _ _ _ _ tr body => do
    let acc ← collectSubexprHashes acc false tr
    collectSubexprHashes acc false body

/-- `collectSubexprHashes` unfolded into its early exit and `cshKids`. -/
theorem collectSubexprHashes_eq (acc : Std.HashSet UInt64) (top : Bool) (e : Expression.Expr) :
    collectSubexprHashes acc top e = (do
      let he ← hashM e
      if !top && acc.contains he then return acc
      else cshKids (if top then acc else acc.insert he) e) := by
  rw [collectSubexprHashes]
  cases e <;> rfl

/-- The spec of walking one child: from a set closed below `n`, the walk of `c` (no larger
    than `n`) leaves a set closed below `n` grown by the hashes of the subterms of `c`. -/
def ChildSpec (c : Expression.Expr) : Prop :=
  ∀ acc n s, U c → esize c ≤ n → ClosedBelow U acc n →
    CshSpec U acc false c n ((collectSubexprHashes acc false c) s).1

/-- Walking two children in a row. -/
theorem childSpec_two {c₁ c₂ : Expression.Expr} (h₁ : ChildSpec U c₁) (h₂ : ChildSpec U c₂)
    (acc : Std.HashSet UInt64) (n : Nat) (s : PtrCache hx) (hu₁ : U c₁) (hu₂ : U c₂)
    (hs₁ : esize c₁ ≤ n) (hs₂ : esize c₂ ≤ n) (hc : ClosedBelow U acc n) :
    let r := (do let acc ← collectSubexprHashes acc false c₁; collectSubexprHashes acc false c₂) s
    ClosedBelow U r.1 n ∧ ∀ h, r.1.contains h = true ↔ acc.contains h = true ∨
      (∃ c, IsSub c c₁ ∧ hx c = h) ∨ (∃ c, IsSub c c₂ ∧ hx c = h) := by
  simp only [bind, stateT_bind_apply]
  obtain ⟨a1, a2⟩ := h₁ acc n s hu₁ hs₁ hc
  obtain ⟨b1, b2⟩ := h₂ _ n ((collectSubexprHashes acc false c₁) s).2 hu₂ hs₂ a1
  refine ⟨b1, fun h => ?_⟩
  rw [b2, a2]
  simp only [Bool.false_eq_true, false_implies, true_and]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- The spec of the children step of `collectSubexprHashes` on `e`. -/
def KidsSpecH (e : Expression.Expr) : Prop :=
  ∀ acc m s, esize e ≤ m + 1 → ClosedBelow U acc m →
    ClosedBelow U ((cshKids acc e) s).1 m ∧ ∀ h, ((cshKids acc e) s).1.contains h = true ↔
      acc.contains h = true ∨ ∃ c, IsSub c e ∧ E c ≠ E e ∧ hx c = h

include hU hUsub in
/-- `collectSubexprHashes` meets its spec on `e` once its children step does. -/
theorem csh_node (e : Expression.Expr) (hk : KidsSpecH U e) (hue : U e) :
    ∀ acc top n s, esize e ≤ n → ClosedBelow U acc n →
      CshSpec U acc top e n ((collectSubexprHashes acc top e) s).1 := by
  intro acc top n s hn hc
  rw [collectSubexprHashes_eq]
  simp only [bind, stateT_bind_apply, hashM_fst]
  split
  · next hif =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hif
    obtain ⟨rfl, hin⟩ := hif
    simp only [pure, stateT_pure_apply]
    refine ⟨hc, fun h => ⟨Or.inl, ?_⟩⟩
    rintro (h' | ⟨c, hcs, -, rfl⟩)
    · exact h'
    · exact hc e hue hn hin c hcs
  · next hif =>
    have hpos : 1 ≤ esize e := by cases e <;> simp [esize]
    cases top with
    | true =>
      simp only [ite_true]
      obtain ⟨k1, k2⟩ := hk acc n (hashM e s).2 (by omega) hc
      refine ⟨k1, fun h => ?_⟩
      rw [k2]
      simp only [true_implies]
    | false =>
      simp only [Bool.not_false, Bool.true_and, Bool.not_eq_true] at hif
      simp only [Bool.false_eq_true, ite_false]
      have hc1 : ClosedBelow U (acc.insert (hx e)) (esize e - 1) := by
        intro c hu hsz hin c' hc'
        rw [Std.HashSet.contains_insert] at hin ⊢
        simp only [Bool.or_eq_true, beq_iff_eq] at hin ⊢
        rcases hin with hin | hin
        · have := congrArg esize (hU _ _ hue hu hin); simp at this; omega
        · exact Or.inr (hc c hu (by omega) hin c' hc')
      obtain ⟨k1, k2⟩ := hk _ (esize e - 1) (hashM e s).2 (by omega) hc1
      refine ⟨fun c hu hsz hin c' hc' => ?_, fun h => ?_⟩
      · by_cases hsz' : esize c ≤ esize e - 1
        · exact k1 c hu hsz' hin c' hc'
        rw [k2] at hin
        rw [k2]
        rw [Std.HashSet.contains_insert] at hin ⊢
        simp only [Bool.or_eq_true, beq_iff_eq] at hin ⊢
        by_cases hce : E c = E e
        · obtain ⟨c'', hc'', hcc⟩ := hc'.transport hce
          rw [hx_eq_of_E hcc]
          by_cases hc''e : E c'' = E e
          · exact Or.inl (Or.inl (hx_eq_of_E hc''e).symm)
          · exact Or.inr ⟨c'', hc'', hc''e, rfl⟩
        · rcases hin with (hin | hin) | ⟨c0, hc0, hc0e, hc0h⟩
          · exact absurd (hU _ _ hue hu hin) (Ne.symm hce)
          · exact Or.inl (Or.inr (hc c hu hsz hin c' hc'))
          · have := hU _ _ (hUsub _ _ hue hc0) hu hc0h
            have h1 := congrArg esize this; simp only [esize_E] at h1
            have h2 := IsPSub.size_lt ⟨hc0, fun he => hc0e (he ▸ rfl)⟩
            omega
      · rw [k2, Std.HashSet.contains_insert]
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, false_implies, true_and]
        constructor
        · rintro ((h' | h') | ⟨c, hc, -, hch⟩)
          · exact Or.inr ⟨e, .refl _, h'⟩
          · exact Or.inl h'
          · exact Or.inr ⟨c, hc, hch⟩
        · rintro (h' | ⟨c, hcs, hch⟩)
          · exact Or.inl (Or.inr h')
          · by_cases hce : E c = E e
            · exact Or.inl (Or.inl (by rw [← hch]; exact (hx_eq_of_E hce).symm))
            · exact Or.inr ⟨c, hcs, hce, hch⟩

/-- The children step walks the children in order. -/
theorem cshKids_eq (acc : Std.HashSet UInt64) (e : Expression.Expr) (s : PtrCache hx) :
    ((cshKids acc e) s).1 =
      (((childList e).foldlM (fun acc c => collectSubexprHashes acc false c) acc) s).1 := by
  cases e <;> simp [cshKids, childList, List.foldlM_cons, bind, pure, stateT_bind_apply,
    stateT_pure_apply]

/-- Walking a list of children, each meeting `ChildSpec`. -/
theorem foldlM_childSpec (m : Nat) : ∀ (cs : List Expression.Expr), (∀ c ∈ cs, ChildSpec U c) →
    (∀ c ∈ cs, U c ∧ esize c ≤ m) → ∀ acc s, ClosedBelow U acc m →
      let r := ((cs.foldlM (fun acc c => collectSubexprHashes acc false c) acc) s).1
      ClosedBelow U r m ∧ ∀ h, r.contains h = true ↔
        acc.contains h = true ∨ ∃ c ∈ cs, ∃ c', IsSub c' c ∧ hx c' = h := by
  intro cs
  induction cs with
  | nil => intro _ _ acc s hc; simp only [List.foldlM_nil, pure, stateT_pure_apply]; simp [hc]
  | cons c cs ih =>
    intro hsp hsz acc s hc
    simp only [List.foldlM_cons, bind, stateT_bind_apply]
    obtain ⟨hu, hs⟩ := hsz c (by simp)
    obtain ⟨a1, a2⟩ := hsp c (by simp) acc m s hu hs hc
    obtain ⟨b1, b2⟩ := ih (fun c' hc' => hsp c' (by simp [hc'])) (fun c' hc' => hsz c' (by simp [hc']))
      _ ((collectSubexprHashes acc false c) s).2 a1
    refine ⟨b1, fun h => ?_⟩
    rw [b2, a2]
    simp only [Bool.false_eq_true, false_implies, true_and, List.mem_cons]
    constructor
    · rintro ((h' | ⟨c', hc', hch⟩) | ⟨c0, hc0, c', hc', hch⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨c, Or.inl rfl, c', hc', hch⟩
      · exact Or.inr ⟨c0, Or.inr hc0, c', hc', hch⟩
    · rintro (h' | ⟨c0, hc0 | hc0, c', hc', hch⟩)
      · exact Or.inl (Or.inl h')
      · subst hc0; exact Or.inl (Or.inr ⟨c', hc', hch⟩)
      · exact Or.inr ⟨c0, hc0, c', hc', hch⟩

include hU hUsub in
/-- **`collectSubexprHashes` collects subterm hashes.** With `U` closed under subterms and the
    hash injective on it up to locations, walking `e` (in `U`) from a set closed below `n ≥
    esize e` leaves a set closed below `n`, grown by the hashes of the subterms of `e` (the
    proper ones when `top`). -/
theorem csh_spec : ∀ (e : Expression.Expr), U e → ∀ acc top n s, esize e ≤ n →
    ClosedBelow U acc n → CshSpec U acc top e n ((collectSubexprHashes acc top e) s).1 := by
  suffices H : ∀ k e, esize e = k → U e → ∀ acc top n s, esize e ≤ n →
      ClosedBelow U acc n → CshSpec U acc top e n ((collectSubexprHashes acc top e) s).1 from
    fun e => H _ e rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro e hk hue
    apply csh_node U hU hUsub e ?_ hue
    intro acc m s hm hc
    have hch : ∀ c ∈ childList e, IsSub c e ∧ esize c < esize e := fun c hc => by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
      exact childList_spec e j hj
    obtain ⟨r1, r2⟩ := foldlM_childSpec U m (childList e)
      (fun c hc acc' n' s' hu hs hc' => ih (esize c) (by rw [← hk]; exact (hch c hc).2) c rfl hu
        acc' false n' s' hs hc')
      (fun c hc => ⟨hUsub _ _ hue (hch c hc).1, by have := (hch c hc).2; omega⟩) acc s hc
    rw [cshKids_eq]
    refine ⟨r1, fun h => (r2 h).trans ?_⟩
    constructor
    · rintro (h' | ⟨c, hc, c', hc', hch'⟩)
      · exact Or.inl h'
      · refine Or.inr ⟨c', hc'.trans (hch c hc).1, fun he => ?_, hch'⟩
        have h1 := congrArg esize he; simp only [esize_E] at h1
        have h2 := hc'.size_le; have h3 := (hch c hc).2; omega
    · rintro (h' | ⟨c, hcs, hce, hch'⟩)
      · exact Or.inl h'
      · obtain ⟨j, hj, hcj⟩ := hcs.child_of_ne (fun he => hce (he ▸ rfl))
        have hget : (childList e)[j]! = (childList e)[j] := getElem!_pos (childList e) j hj
        rw [hget] at hcj
        exact Or.inr ⟨_, List.getElem_mem hj, c, hcj, hch'⟩

end Subsumption2

section Subsumption3
variable (U : Expression.Expr → Prop)
  (hU : ∀ a b, U a → U b → hx a = hx b → E a = E b)
  (hUsub : ∀ a b, U b → IsSub a b → U a)

include hU hUsub in
/-- Collecting the proper-subterm hashes of a list of nodes. -/
theorem foldlM_csh_spec (n : Nat) : ∀ (ps : List (UInt64 × Expression.Expr)),
    (∀ p ∈ ps, U p.2 ∧ esize p.2 ≤ n) → ∀ acc s, ClosedBelow U acc n →
      let r := ((ps.foldlM (fun acc p => collectSubexprHashes acc true p.2) acc) s).1
      ClosedBelow U r n ∧ ∀ h, r.contains h = true ↔ acc.contains h = true ∨
        ∃ q ∈ ps, ∃ c, IsSub c q.2 ∧ E c ≠ E q.2 ∧ hx c = h := by
  intro ps
  induction ps with
  | nil => intro _ acc s hc; simp only [List.foldlM_nil, pure, stateT_pure_apply]; simp [hc]
  | cons p ps ih =>
    intro hps acc s hc
    simp only [List.foldlM_cons, bind, stateT_bind_apply]
    obtain ⟨hu, hsz⟩ := hps p (by simp)
    obtain ⟨a1, a2⟩ := csh_spec U hU hUsub p.2 hu acc true n s hsz hc
    obtain ⟨b1, b2⟩ := ih (fun q hq => hps q (by simp [hq])) _
      ((collectSubexprHashes acc true p.2) s).2 a1
    refine ⟨b1, fun h => ?_⟩
    rw [b2, a2]
    simp only [true_implies, List.mem_cons]
    constructor
    · rintro ((h' | ⟨c, hc', hce, hch⟩) | ⟨q, hq, c, hc', hce, hch⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨p, Or.inl rfl, c, hc', hce, hch⟩
      · exact Or.inr ⟨q, Or.inr hq, c, hc', hce, hch⟩
    · rintro (h' | ⟨q, rfl | hq, c, hc', hce, hch⟩)
      · exact Or.inl (Or.inl h')
      · exact Or.inl (Or.inr ⟨c, hc', hce, hch⟩)
      · exact Or.inr ⟨q, hq, c, hc', hce, hch⟩

open Classical in
include hU hUsub in
/-- **`removeSubsumed` keeps the maximal nodes.** With `U` closed under subterms, the hash
    injective on it up to locations, and each entry hashed by its own hash, `removeSubsumed`
    keeps exactly the entries that are not (up to locations) a proper subterm of an entry. -/
theorem removeSubsumed_eq (memo : PtrCache hx) (ps : List (UInt64 × Expression.Expr))
    (hps : ∀ p ∈ ps, U p.2 ∧ hx p.2 = p.1) :
    removeSubsumed memo ps = ps.filter (fun p => decide (¬ ∃ q ∈ ps, ∃ c, IsSub c q.2 ∧
      E c ≠ E q.2 ∧ E c = E p.2)) := by
  unfold removeSubsumed
  simp only [StateT.run]
  let n := ps.foldr (fun p m => max (esize p.2) m) 0
  have hn : ∀ p ∈ ps, esize p.2 ≤ n := by
    have := foldr_max_le (ps.map (·.2))
    intro p hp
    have h' := this p.2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
    simp only [n]
    rw [List.foldr_map] at h'
    exact h'
  obtain ⟨-, hmem⟩ := foldlM_csh_spec U hU hUsub n ps (fun p hp => ⟨(hps p hp).1, hn p hp⟩) {} memo
    (fun c _ _ h => by simp at h)
  generalize ((ps.foldlM (fun acc p => collectSubexprHashes acc true p.2) {}) memo) = pr at hmem ⊢
  obtain ⟨sub, _⟩ := pr
  simp only at hmem ⊢
  apply List.filter_congr
  intro p hp
  obtain ⟨hu, hh⟩ := hps p hp
  have key : sub.contains p.1 = true ↔ ∃ q ∈ ps, ∃ c, IsSub c q.2 ∧ E c ≠ E q.2 ∧ E c = E p.2 := by
    rw [hmem]
    simp only [Std.HashSet.contains_empty, Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨q, hq, c, hc, hce, hch⟩
      exact ⟨q, hq, c, hc, hce, hU _ _ (hUsub _ _ (hps q hq).1 hc) hu (hch.trans hh.symm)⟩
    · rintro ⟨q, hq, c, hc, hce, hcp⟩
      exact ⟨q, hq, c, hc, hce, (hx_eq_of_E hcp).trans hh⟩
  by_cases hk : ∃ q ∈ ps, ∃ c, IsSub c q.2 ∧ E c ≠ E q.2 ∧ E c = E p.2
  · rw [key.mpr hk]; simp [hk]
  · have : sub.contains p.1 = false := Bool.eq_false_iff.mpr (fun h => hk (key.mp h))
    rw [this]; simp [hk]

end Subsumption3

/-! ## One round of `stmtRunCSE` -/

/-- The targets of a round: the maximal duplicates with their types. -/
def itTargets (body : Statements) : List (UInt64 × Expression.Expr × LMonoTy) :=
  ((collectExprsToAbbreviate (Statements.collectExprs body)).filterMapM (m := StateM TcState)
      (fun (h, dup) => do return (← typeCheckClosed dup).map (fun ty => (h, dup, ty)))).run' {}

/-- The declarations, replacement map and next index of a round. -/
def itFold (body : Statements) (startIdx : Nat) :
    List Statement × Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)) × Nat :=
  (itTargets body).foldl
      (fun (decls, repMap, idx) (h, dup, freshTy) =>
    let freshName : CoreIdent := ⟨s!"{cseVarPrefix}{idx}", ()⟩
    let freshVar : Expression.Expr := .fvar valueLoc freshName (some freshTy)
    let ty : Expression.Ty := LTy.forAll [] freshTy
    let varDecl := Statement.init freshName ty (.det dup) .empty
    let pairs := repMap.getD h []
    (varDecl :: decls, repMap.insert h ((dup, freshVar) :: pairs), idx + 1)
  ) ([], ({} : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr))), startIdx)

/-- The rewritten body of a round. -/
def itBody (body : Statements) (startIdx : Nat) : Statements :=
  (Statements.mapExprsM
    (fun e => Prod.fst <$> replaceSubexprs (itFold body startIdx).2.1 e) body).run' {}

/-- `stmtRunCSEIter` through its named steps. -/
theorem stmtRunCSEIter_eq (body : Statements) (idx : Nat) :
    stmtRunCSEIter body idx =
      if (itTargets body).isEmpty then none
      else some ((itFold body idx).1.reverseAux (itBody body idx), (itFold body idx).2.2) := by
  unfold stmtRunCSEIter
  rfl

/-- `collectExprsToAbbreviate` is `removeSubsumed` of the duplicates. -/
theorem collectExprsToAbbreviate_eq (exprs : List Expression.Expr) :
    collectExprsToAbbreviate exprs = removeSubsumed (collectExprsToAbbreviate.collectDups exprs).2
      (collectExprsToAbbreviate.collectDups exprs).1 := by
  unfold collectExprsToAbbreviate; rfl

/-- The targets: the maximal duplicates that type check, with their types. -/
theorem itTargets_eq (body : Statements) :
    itTargets body = (collectExprsToAbbreviate (Statements.collectExprs body)).filterMap
      (fun p => (LExpr.typeCheck [] p.2).map (fun ty => (p.1, p.2, ty))) := by
  unfold itTargets
  generalize collectExprsToAbbreviate (Statements.collectExprs body) = L
  suffices H : ∀ (s : TcState), TcInv s →
      ((L.filterMapM (m := StateM TcState)
        (fun (h, dup) => do return (← typeCheckClosed dup).map (fun ty => (h, dup, ty)))) s).1 =
      L.filterMap (fun p => (LExpr.typeCheck [] p.2).map (fun ty => (p.1, p.2, ty))) from
    H {} TcInv_empty
  induction L with
  | nil => intro s _; rfl
  | cons p ps ih =>
    intro s hs
    obtain ⟨h1, h2⟩ := typeCheckClosed_spec p.2 s hs
    have := ih _ h2
    simp only [bind, pure] at this
    simp only [List.filterMapM_cons, bind, pure, stateT_bind_apply, stateT_pure_apply,
      List.filterMap_cons]
    rw [h1]
    cases hty : LExpr.typeCheck [] p.2 with
    | none => simp only [Option.map_none]; exact this
    | some ty => simp only [Option.map_some, stateT_bind_apply, stateT_pure_apply]; rw [this]

/-- The declarations, map and next index the fold of a round builds. -/
theorem itFold_spec (L : List (UInt64 × Expression.Expr × LMonoTy)) :
    ∀ (ds : List Statement) (m : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
      (idx : Nat),
      let r := L.foldl
        (fun (acc : List Statement × Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)) × Nat)
            (t : UInt64 × Expression.Expr × LMonoTy) =>
          (Statement.init ⟨s!"{cseVarPrefix}{acc.2.2}", ()⟩ (LTy.forAll [] t.2.2) (.det t.2.1) .empty
              :: acc.1,
            acc.2.1.insert t.1 ((t.2.1, cseVar acc.2.2 t.2.2) :: acc.2.1.getD t.1 []), acc.2.2 + 1))
        (ds, m, idx)
      r.1.reverse = ds.reverse ++ ((List.range' idx L.length).zip L).map (fun q =>
          Statement.init ⟨s!"{cseVarPrefix}{q.1}", ()⟩ (LTy.forAll [] q.2.2.2) (.det q.2.2.1)
            .empty) ∧
      r.2.2 = idx + L.length ∧
      ∀ h p, p ∈ r.2.1.getD h [] ↔ p ∈ m.getD h [] ∨
        ∃ j, ∃ hj : j < L.length, L[j].1 = h ∧ p = (L[j].2.1, cseVar (idx + j) L[j].2.2) := by
  induction L with
  | nil => intro ds m idx; simp
  | cons t ts ih =>
    intro ds m idx
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (Statement.init ⟨s!"{cseVarPrefix}{idx}", ()⟩ (LTy.forAll [] t.2.2)
      (.det t.2.1) .empty :: ds) (m.insert t.1 ((t.2.1, cseVar idx t.2.2) :: m.getD t.1 []))
      (idx + 1)
    refine ⟨?_, by rw [h2]; simp; omega, fun h p => ?_⟩
    · rw [h1]
      simp only [List.reverse_cons, List.append_assoc, List.length_cons, List.range'_succ,
        List.zip_cons_cons, List.map_cons, List.singleton_append]
    · rw [h3, Std.HashMap.getD_insert]
      constructor
      · rintro (hp | ⟨j, hj, hjh, rfl⟩)
        · split at hp
          · next heq =>
            have heq : t.1 = h := by simpa using heq
            rcases List.mem_cons.mp hp with rfl | hp
            · exact Or.inr ⟨0, by simp, heq, rfl⟩
            · exact Or.inl (heq ▸ hp)
          · exact Or.inl hp
        · exact Or.inr ⟨j + 1, by simp; omega, by simpa using hjh, by
            simp only [List.getElem_cons_succ]; rw [show idx + 1 + j = idx + (j + 1) by omega]⟩
      · rintro (hp | ⟨j, hj, hjh, rfl⟩)
        · left
          split
          · next heq =>
            have heq : t.1 = h := by simpa using heq
            subst heq; exact List.mem_cons_of_mem _ hp
          · exact hp
        · cases j with
          | zero =>
            left
            simp only [List.getElem_cons_zero] at hjh ⊢
            rw [ite_eq_left (by simpa using hjh)]
            exact List.mem_cons.mpr (Or.inl (by simp))
          | succ j =>
            right
            exact ⟨j, by simp at hj; omega, by simpa using hjh, by
              simp only [List.getElem_cons_succ]; rw [show idx + 1 + j = idx + (j + 1) by omega]⟩

/-- The fold of a round, through `itFold_spec`. -/
theorem itFold_eq (body : Statements) (idx : Nat) :
    (itFold body idx).1.reverse = ((List.range' idx (itTargets body).length).zip (itTargets body)).map
        (fun q => Statement.init ⟨s!"{cseVarPrefix}{q.1}", ()⟩ (LTy.forAll [] q.2.2.2)
          (.det q.2.2.1) .empty) ∧
      (itFold body idx).2.2 = idx + (itTargets body).length ∧
      ∀ h p, p ∈ (itFold body idx).2.1.getD h [] ↔
        ∃ j, ∃ hj : j < (itTargets body).length, (itTargets body)[j].1 = h ∧
          p = ((itTargets body)[j].2.1, cseVar (idx + j) (itTargets body)[j].2.2) := by
  have := itFold_spec (itTargets body) [] ∅ idx
  simp only [List.reverse_nil, List.nil_append, Std.HashMap.getD_empty, List.not_mem_nil,
    false_or] at this
  exact this

/-! ## Naming in two steps -/

section Compose
variable (M T : List NTarget)

/-- A generated variable is not a named class when the named classes are `app`, `ite` or `eq`
    nodes. -/
theorem cseVar_not_mem (hT : ∀ t ∈ T, elig t.1 = true) (k : Nat) (ty : LMonoTy) :
    cseVar k ty ∉ T.map (·.1) := by
  intro hm
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp hm
  have := hT t ht; rw [hte] at this; simp [cseVar, elig] at this

/-- Rewriting a generated variable changes nothing, when the named classes are `app`, `ite` or
    `eq` nodes. -/
theorem rwE_cseVar (hT : ∀ t ∈ T, elig t.1 = true) (k : Nat) (ty : LMonoTy) :
    rwE (ρL T) (cseVar k ty) = cseVar k ty := by
  rw [rwE_eq, ρL_eq_none (cseVar_not_mem T hT k ty)]; rfl

/-- The node step of `rwE_comp`. -/
theorem rwE_comp_node (hTel : ∀ t ∈ T, elig t.1 = true) (hTM : ∀ t ∈ T, NoneIn M t.1)
    (hTf : ∀ t ∈ T, FreshIn M t.1) (e : Expression.Expr)
    (hk : rwKids (ρL T) (rwKids (ρL M) e) = rwKids (ρL (M ++ T)) e) :
    rwE (ρL T) (rwE (ρL M) e) = rwE (ρL (M ++ T)) e := by
  by_cases hM : e ∈ M.map (·.1)
  · obtain ⟨m, -, hρ⟩ := ρL_of_mem hM
    rw [rwE_eq (ρL M), hρ, Option.getD_some, rwE_cseVar T hTel, rwE_eq (ρL (M ++ T)),
      ρL_append_of_mem hM, hρ, Option.getD_some]
  · rcases rwE_cases M e with ⟨m', hm', h1, -⟩ | ⟨-, h2⟩
    · exact absurd (List.mem_map.mpr ⟨m', hm', h1⟩) hM
    rw [h2, rwE_eq (ρL (M ++ T)), ρL_append_of_not_mem hM]
    by_cases hT : e ∈ T.map (·.1)
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hT
      have hself : rwKids (ρL M) t.1 = t.1 := by rw [← h2]; exact rwE_self M t.1 (hTM t ht)
      obtain ⟨t', -, hρ⟩ := ρL_of_mem hT
      rw [hself, rwE_eq, hρ, Option.getD_some, Option.getD_some]
    · have hnT : rwKids (ρL M) e ∉ T.map (·.1) := by
        intro hm
        obtain ⟨t, ht, hte⟩ := List.mem_map.mp hm
        by_cases hn : NoneIn M e
        · rw [← h2, rwE_self M e hn] at hte; exact hT (hte ▸ List.mem_map.mpr ⟨t, ht, rfl⟩)
        · obtain ⟨m, hm, hs⟩ : ∃ m ∈ M, IsSub m.1 e := by
            apply Classical.byContradiction; intro hc; exact hn (fun t ht hs => hc ⟨t, ht, hs⟩)
          obtain ⟨m', hm', hv⟩ := vars_rwE_of_sub M e m hm hs
          rw [h2, ← hte] at hv
          exact hTf t ht m' hm' hv
      rw [rwE_eq, ρL_eq_none hnT, ρL_eq_none hT]
      exact hk

/-- **Naming in two steps.** Naming `M` and then `T` is naming `M ++ T`, when the nodes of `T`
    contain no node of `M`, are eligible and mention no generated name of `M`. -/
theorem rwE_comp (hTel : ∀ t ∈ T, elig t.1 = true) (hTM : ∀ t ∈ T, NoneIn M t.1)
    (hTf : ∀ t ∈ T, FreshIn M t.1) :
    ∀ (e : Expression.Expr), rwE (ρL T) (rwE (ρL M) e) = rwE (ρL (M ++ T)) e := by
  intro e
  induction e with
  | app m f a ihf iha =>
    exact rwE_comp_node M T hTel hTM hTf _ (by simp only [rwKids, ihf, iha])
  | ite m c t f ihc iht ihf =>
    exact rwE_comp_node M T hTel hTM hTf _ (by simp only [rwKids, ihc, iht, ihf])
  | eq m a b iha ihb =>
    exact rwE_comp_node M T hTel hTM hTf _ (by simp only [rwKids, iha, ihb])
  | abs m n ty b ih =>
    exact rwE_comp_node M T hTel hTM hTf _ (by simp only [rwKids, ih])
  | quant m k n ty tr b ihtr ihb =>
    exact rwE_comp_node M T hTel hTM hTf _ (by simp only [rwKids, ihtr, ihb])
  | _ => exact rwE_comp_node M T hTel hTM hTf _ rfl

/-- A child's rewritten variables are variables of the node with its children rewritten. -/
theorem vars_rwKids_child (ρ : Expression.Expr → Option Expression.Expr) (e : Expression.Expr)
    (j : Nat) (hj : j < (childList e).length) :
    ∀ x ∈ vars (rwE ρ (childList e)[j]), x ∈ vars (rwKids ρ e) := by
  intro x hx
  cases e with
  | app m f a =>
    match j, hj with
    | 0, _ => simp only [childList, List.getElem_cons_zero, vars] at hx; simp [rwKids, vars, LExpr.LExpr.getVars, hx]
    | 1, _ => simp only [childList, List.getElem_cons_zero, List.getElem_cons_succ, vars] at hx; simp [rwKids, vars, LExpr.LExpr.getVars, hx]
  | ite m c t f =>
    match j, hj with
    | 0, _ => simp only [childList, List.getElem_cons_zero, vars] at hx; simp [rwKids, vars, LExpr.LExpr.getVars, hx]
    | 1, _ => simp only [childList, List.getElem_cons_zero, List.getElem_cons_succ, vars] at hx; simp [rwKids, vars, LExpr.LExpr.getVars, hx]
    | 2, _ => simp only [childList, List.getElem_cons_zero, List.getElem_cons_succ, vars] at hx; simp [rwKids, vars, LExpr.LExpr.getVars, hx]
  | eq m a b =>
    match j, hj with
    | 0, _ => simp only [childList, List.getElem_cons_zero, vars] at hx; simp [rwKids, vars, LExpr.LExpr.getVars, hx]
    | 1, _ => simp only [childList, List.getElem_cons_zero, List.getElem_cons_succ, vars] at hx; simp [rwKids, vars, LExpr.LExpr.getVars, hx]
  | abs m n ty b =>
    match j, hj with
    | 0, _ => simp only [childList, List.getElem_cons_zero, vars] at hx; simp [rwKids, vars, LExpr.LExpr.getVars, hx]
  | quant m k n ty tr b =>
    match j, hj with
    | 0, _ => simp only [childList, List.getElem_cons_zero, vars] at hx; simp [rwKids, vars, LExpr.LExpr.getVars, hx]
    | 1, _ => simp only [childList, List.getElem_cons_zero, List.getElem_cons_succ, vars] at hx; simp [rwKids, vars, LExpr.LExpr.getVars, hx]
  | _ => simp [childList] at hj

/-- A node whose children are rewritten by `M` is not a node of `T`, when it is not one
    itself and the nodes of `T` mention no generated name of `M`. -/
theorem rwKids_not_mem (hTf : ∀ t ∈ T, FreshIn M t.1) {e : Expression.Expr}
    (he : e ∉ T.map (·.1)) : rwKids (ρL M) e ∉ T.map (·.1) := by
  intro hm
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp hm
  by_cases hn : ∀ c, IsPSub c e → ρL M c = none
  · rw [rwKids_congr (ρ₂ := fun _ => none) e hn, rwKids_none] at hte
    exact he (hte ▸ List.mem_map.mpr ⟨t, ht, rfl⟩)
  · obtain ⟨c, hc, hρ⟩ : ∃ c, IsPSub c e ∧ ρL M c ≠ none := by
      apply Classical.byContradiction; intro h
      exact hn (fun c hc => by
        apply Classical.byContradiction; intro h'; exact h ⟨c, hc, h'⟩)
    obtain ⟨m, hm, hmc, -⟩ := ρL_eq_some (Option.ne_none_iff_exists'.mp hρ).choose_spec
    obtain ⟨j, hj, hcj⟩ := hc.1.child_of_ne hc.2
    have hget : (childList e)[j]! = (childList e)[j] := getElem!_pos (childList e) j hj
    rw [hget] at hcj
    obtain ⟨m', hm', hv⟩ := vars_rwE_of_sub M _ m hm (hmc ▸ hcj)
    have hv' : cseName m'.2.1 ∈ vars (rwKids (ρL M) e) := vars_rwKids_child (ρL M) e j hj _ hv
    rw [← hte] at hv'
    exact hTf t ht m' hm' hv'

/-- Naming in two steps, for the children of a node that is not a node of `T`. -/
theorem rwKids_comp (hTel : ∀ t ∈ T, elig t.1 = true) (hTM : ∀ t ∈ T, NoneIn M t.1)
    (hTf : ∀ t ∈ T, FreshIn M t.1) (e : Expression.Expr) (he : e ∉ T.map (·.1)) :
    rwE (ρL T) (rwKids (ρL M) e) = rwKids (ρL (M ++ T)) e := by
  rw [rwE_eq, ρL_eq_none (rwKids_not_mem M T hTf he), Option.getD_none]
  cases e <;> simp [rwKids, rwE_comp M T hTel hTM hTf]

end Compose

/-! ## Rounds of `stmtRunCSE`, abstractly -/

/-- The visits of the walk of `F` with reach list `R`. -/
def visits (F R : List Expression.Expr) : List Expression.Expr := F.flatMap occ ++ R.flatMap occK

/-- The counting relation between a round's forest and the input's: after naming `M`
    (declared in the order `DL`), the walk of `F` with reach list `R` visits a declaration once,
    the rewrite of an unnamed class as often as the input's walk visits the class, and
    nothing else. -/
def CR (L0 : List Expression.Expr) (M DL : List NTarget) (F R : List Expression.Expr) : Prop :=
  IsReachList (F.flatMap occ) R ∧
  (∀ c, E c = c → FreshIn M c → c ∉ M.map (·.1) →
    cnt (rwE (ρL M) c) (visits F R) = cnt c L0) ∧
  (∀ t ∈ DL, cnt (rwKids (ρL M) t.1) (visits F R) = 1) ∧
  (∀ x ∈ visits F R, (∃ t ∈ DL, x = rwKids (ρL M) t.1) ∨
    ∃ c ∈ L0, c ∉ M.map (·.1) ∧ x = rwE (ρL M) c)

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- The variables of a rewrite of `c` are `c`'s or names of `M`; so the rewrite mentions no
    name of `T` when `c` mentions none and `M`, `T` have distinct indices. -/
theorem FreshIn_rwE {M T : List NTarget} (hidx : ((M ++ T).map (·.2.1)).Nodup) {c : Expression.Expr}
    (hc : FreshIn T c) : FreshIn T (rwE (ρL M) c) := by
  intro t ht hv
  rcases vars_rwE M c _ hv with h | ⟨m, hm, hmn, -⟩
  · exact hc t ht h
  · have := cseName_inj hmn.symm
    rw [List.map_append] at hidx
    exact (List.nodup_append.mp hidx).2.2 _ (List.mem_map.mpr ⟨m, hm, rfl⟩) _
      (List.mem_map.mpr ⟨t, ht, rfl⟩) this

/-- `FreshIn` of a list split in two. -/
theorem FreshIn_append {M T : List NTarget} {c : Expression.Expr} :
    FreshIn (M ++ T) c ↔ FreshIn M c ∧ FreshIn T c := by
  simp only [FreshIn, List.mem_append]
  exact ⟨fun h => ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩,
    fun h t ht => ht.elim (h.1 t) (h.2 t)⟩

/-- The variables of a node with rewritten children. -/
theorem FreshIn_rwKids {M T : List NTarget} (hidx : ((M ++ T).map (·.2.1)).Nodup)
    {c : Expression.Expr} (hc : FreshIn T c) : FreshIn T (rwKids (ρL M) c) := by
  intro t ht hv
  rcases vars_rwKids M c _ hv with h | ⟨m, hm, hmn, -⟩
  · exact hc t ht h
  · have := cseName_inj hmn.symm
    rw [List.map_append] at hidx
    exact (List.nodup_append.mp hidx).2.2 _ (List.mem_map.mpr ⟨m, hm, rfl⟩) _
      (List.mem_map.mpr ⟨t, ht, rfl⟩) this

/-- A rewritten class with a generated name of `M` inside is not a named class mentioning none. -/
theorem rwE_ne_of_fresh {M : List NTarget} {c d : Expression.Expr} (hd : FreshIn M d)
    (hc : ¬ NoneIn M c) : rwE (ρL M) c ≠ d := by
  intro h
  obtain ⟨m, hm, hs⟩ : ∃ m ∈ M, IsSub m.1 c := by
    apply Classical.byContradiction; intro h'; exact hc (fun t ht hs => h' ⟨t, ht, hs⟩)
  obtain ⟨m', hm', hv⟩ := vars_rwE_of_sub M c m hm hs
  rw [h] at hv
  exact hd m' hm' hv

/-- Rewriting a class that is not named and is not inside `T` by `M` gives no class of `T`. -/
theorem rwE_not_mem_T {M T : List NTarget} (hTf : ∀ t ∈ T, FreshIn M t.1) {c : Expression.Expr}
    (hcT : c ∉ T.map (·.1)) : rwE (ρL M) c ∉ T.map (·.1) := by
  intro hm
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp hm
  by_cases hn : NoneIn M c
  · rw [rwE_self M c hn] at hte; exact hcT (hte ▸ List.mem_map.mpr ⟨t, ht, rfl⟩)
  · exact rwE_ne_of_fresh (hTf t ht) hn hte.symm

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- Rewriting the children of an erased node gives an erased node. -/
theorem E_rwKids (M : List NTarget) (e : Expression.Expr) (he : E e = e) :
    E (rwKids (ρL M) e) = rwKids (ρL M) e := by
  cases e with
  | app m f a =>
    obtain ⟨rfl, hf, ha⟩ := E_eq_self_app he
    simp only [rwKids, E_app, E_rwE M f hf, E_rwE M a ha]
  | ite m c t f =>
    simp only [E_ite, LExpr.ite.injEq] at he
    obtain ⟨rfl, hc, ht, hf⟩ := he
    simp only [rwKids, E_ite, E_rwE M c hc, E_rwE M t ht, E_rwE M f hf]
  | eq m a b =>
    simp only [E_eq, LExpr.eq.injEq] at he
    obtain ⟨rfl, ha, hb⟩ := he
    simp only [rwKids, E_eq, E_rwE M a ha, E_rwE M b hb]
  | abs m n ty b =>
    simp only [E_abs, LExpr.abs.injEq] at he
    obtain ⟨rfl, -, -, hb⟩ := he
    simp only [rwKids, E_abs, E_rwE M b hb]
  | quant m k n ty tr b =>
    simp only [E_quant, LExpr.quant.injEq] at he
    obtain ⟨rfl, -, -, -, htr, hb⟩ := he
    simp only [rwKids, E_quant, E_rwE M tr htr, E_rwE M b hb]
  | _ => exact he

/-- A member of a list without duplicates occurs once. -/
theorem cnt_nodup_mem : ∀ {l : List Expression.Expr} {c : Expression.Expr}, l.Nodup → c ∈ l →
    cnt c l = 1 := by
  intro l
  induction l with
  | nil => intro c _ h; simp at h
  | cons x xs ih =>
    intro c hn hc
    rw [List.nodup_cons] at hn
    rw [cnt_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [cnt_eq_zero.mpr hn.1, ite_eq_left rfl]
    · rw [ih hn.2 hc, ite_eq_right (fun (h : x = c) => hn.1 (h ▸ hc))]

/-- **One round, abstractly.** If a round's forest (declarations of `M` in the order `DL`,
    then the input rewritten by `M`) is in the counting relation with the input's walk, and the
    round names `T` (reached, distinct, none a proper subterm of another, none the function of
    an application, containing no node of `M`), the next round's forest (declarations of `T`
    first) is in the counting relation too. -/
theorem round_step (L0 F0 R : List Expression.Expr) (M DL T : List NTarget)
    (hcr : CR L0 M DL (DL.map (fun t => rwKids (ρL M) t.1) ++ F0.map (rwE (ρL M))) R)
    (hidx : ((M ++ T).map (·.2.1)).Nodup) (hcls : ((M ++ T).map (·.1)).Nodup)
    (hel : ∀ t ∈ M ++ T, elig t.1 = true) (hE : ∀ t ∈ M ++ T, E t.1 = t.1)
    (hfr : ∀ t ∈ M ++ T, FreshIn (M ++ T) t.1) (hDL : ∀ t ∈ DL, t ∈ M)
    (hF0 : ∀ r ∈ F0, E r = r ∧ FreshIn (M ++ T) r)
    (hfn : ∀ x ∈ DL.map (fun t => rwKids (ρL M) t.1) ++ F0.map (rwE (ρL M)), NoFnT T x)
    (hTR : ∀ t ∈ T, t.1 ∈ R) (hinc : ∀ t ∈ T, ∀ t' ∈ T, ¬ IsPSub t'.1 t.1)
    (hTM : ∀ t ∈ T, NoneIn M t.1) :
    ((T ++ DL).map (fun t => rwKids (ρL (M ++ T)) t.1) ++ F0.map (rwE (ρL (M ++ T))) =
      T.map (·.1) ++ (DL.map (fun t => rwKids (ρL M) t.1) ++ F0.map (rwE (ρL M))).map
        (rwE (ρL T))) ∧
    ∃ R', CR L0 (M ++ T) (T ++ DL)
      ((T ++ DL).map (fun t => rwKids (ρL (M ++ T)) t.1) ++ F0.map (rwE (ρL (M ++ T)))) R' := by
  classical
  have hMcls : (M.map (·.1)).Nodup := by rw [List.map_append] at hcls; exact (List.nodup_append.mp hcls).1
  have hTcls : (T.map (·.1)).Nodup := by rw [List.map_append] at hcls; exact (List.nodup_append.mp hcls).2.1
  have hTidx : (T.map (·.2.1)).Nodup := by rw [List.map_append] at hidx; exact (List.nodup_append.mp hidx).2.1
  have hdisj : ∀ m ∈ M, m.1 ∉ T.map (·.1) := fun m hm hmT => by
    rw [List.map_append] at hcls
    obtain ⟨t, ht, hte⟩ := List.mem_map.mp hmT
    exact (List.nodup_append.mp hcls).2.2 _ (List.mem_map.mpr ⟨m, hm, rfl⟩) _
      (List.mem_map.mpr ⟨t, ht, rfl⟩) hte.symm
  have hTel : ∀ t ∈ T, elig t.1 = true := fun t ht => hel t (List.mem_append_right _ ht)
  have hTE : ∀ t ∈ T, E t.1 = t.1 := fun t ht => hE t (List.mem_append_right _ ht)
  have hTfM : ∀ t ∈ T, FreshIn M t.1 := fun t ht =>
    (FreshIn_append.mp (hfr t (List.mem_append_right _ ht))).1
  have hTfT : ∀ t ∈ T, FreshIn T t.1 := fun t ht =>
    (FreshIn_append.mp (hfr t (List.mem_append_right _ ht))).2
  -- The next forest.
  have hTself : ∀ t ∈ T, rwKids (ρL (M ++ T)) t.1 = t.1 := by
    intro t ht
    rw [rwKids_congr (ρ₂ := fun _ => none) _ (fun c hc => ?_), rwKids_none]
    apply ρL_eq_none
    intro hm
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
    rcases List.mem_append.mp hu with hu | hu
    · exact hTM t ht u hu hc.1
    · exact hinc t ht u hu hc
  have hF : (T ++ DL).map (fun t => rwKids (ρL (M ++ T)) t.1) ++ F0.map (rwE (ρL (M ++ T))) =
      T.map (·.1) ++ (DL.map (fun t => rwKids (ρL M) t.1) ++ F0.map (rwE (ρL M))).map
        (rwE (ρL T)) := by
    simp only [List.map_append, List.append_assoc, List.map_map]
    congr 1
    · exact List.map_congr_left (fun t ht => hTself t ht)
    · congr 1
      · apply List.map_congr_left
        intro t ht
        exact (rwKids_comp M T hTel hTM hTfM t.1 (hdisj t (hDL t ht))).symm
      · apply List.map_congr_left
        intro r _
        exact (rwE_comp M T hTel hTM hTfM r).symm
  refine ⟨hF, ?_⟩
  -- The current forest.
  generalize hFr : DL.map (fun t => rwKids (ρL M) t.1) ++ F0.map (rwE (ρL M)) = Fr at hcr hfn hF ⊢
  have hFrE : ∀ r ∈ Fr, E r = r ∧ FreshIn T r := by
    intro r hr
    rw [← hFr] at hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
      have htM := hDL t ht
      exact ⟨E_rwKids M t.1 (hE t (List.mem_append_left _ htM)),
        FreshIn_rwKids hidx (FreshIn_append.mp (hfr t (List.mem_append_left _ htM))).2⟩
    · obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      obtain ⟨h1, h2⟩ := hF0 r0 hr0
      exact ⟨E_rwE M r0 h1, FreshIn_rwE hidx (FreshIn_append.mp h2).2⟩
  obtain ⟨hR', hperm⟩ := one_step T Fr R hcr.1 (fun r hr => (hFrE r hr).1) hfn
    (fun r hr => (hFrE r hr).2) hTR hTcls hTidx hTel hinc
  rw [hF]
  -- The visits of the current forest are erased and mention no name of `T`.
  have hvis : ∀ z ∈ visits Fr R, E z = z ∧ FreshIn T z := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨r, hr, hz⟩ := List.mem_flatMap.mp hz
      obtain ⟨s, hs, rfl⟩ := (occ_sub r).1 z hz
      exact ⟨E_E s, fun t ht hv => (hFrE r hr).2 t ht (hs.vars_subset _ (by rwa [vars_E] at hv))⟩
    · obtain ⟨d, hd, hz⟩ := List.mem_flatMap.mp hz
      obtain ⟨-, r, hr, hdr⟩ := reachList_sub hcr.1 (fun r hr => (hFrE r hr).1) hd
      obtain ⟨s, hs, -, rfl⟩ := occK_sub d z hz
      exact ⟨E_E s, fun t ht hv => (hFrE r hr).2 t ht
        ((hs.trans hdr).vars_subset _ (by rwa [vars_E] at hv))⟩
  have hcntT : ∀ t ∈ T, cnt t.1 (T.map (·.1)) = 1 := fun t ht =>
    cnt_nodup_mem hTcls (List.mem_map.mpr ⟨t, ht, rfl⟩)
  have hL : ∀ x, cnt x (visits (T.map (·.1) ++ Fr.map (rwE (ρL T)))
      (T.map (·.1) ++ (R.filter (fun c => decide (c ∉ T.map (·.1)))).map (rwE (ρL T)))) =
      cnt x (T.map (·.1)) + cnt x ((visits Fr R).filterMap (gT T)) := by
    intro x; unfold visits; rw [perm_cnt_eq hperm, cnt_append]
  refine ⟨_, hR', fun c hc hcf hcM => ?_, fun t ht => ?_, fun x hx => ?_⟩
  · -- an unnamed class
    have hcf' := FreshIn_append.mp hcf
    have hcT : c ∉ T.map (·.1) := fun h => hcM (by rw [List.map_append]; exact List.mem_append_right _ h)
    have hcM' : c ∉ M.map (·.1) := fun h => hcM (by rw [List.map_append]; exact List.mem_append_left _ h)
    rw [← rwE_comp M T hTel hTM hTfM c, hL,
      cnt_eq_zero.mpr (rwE_not_mem T hTfT _),
      cnt_filterMap_gT T hTcls hTidx hTE hinc (E_rwE M c hc) (FreshIn_rwE hidx hcf'.2)
        (rwE_not_mem_T hTfM hcT) _ hvis, Nat.zero_add]
    exact hcr.2.1 c hc hcf'.1 hcM'
  · -- a declaration
    rcases List.mem_append.mp ht with ht | ht
    · rw [hTself t ht, hL, hcntT t ht, cnt_T_filterMap_gT T hTfT ht]
    · have htM := hDL t ht
      have htT := hdisj t htM
      rw [← rwKids_comp M T hTel hTM hTfM t.1 htT, hL,
        cnt_eq_zero.mpr (rwE_not_mem T hTfT _),
        cnt_filterMap_gT T hTcls hTidx hTE hinc (E_rwKids M t.1 (hE t (List.mem_append_left _ htM)))
          (FreshIn_rwKids hidx (FreshIn_append.mp (hfr t (List.mem_append_left _ htM))).2)
          (rwKids_not_mem M T hTfM htT) _ hvis, Nat.zero_add]
      exact hcr.2.2.1 t ht
  · -- nothing else
    unfold visits at hx
    rw [hperm.mem_iff] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      exact Or.inl ⟨t, List.mem_append_left _ ht, (hTself t ht).symm⟩
    · obtain ⟨y, hy, hg⟩ := List.mem_filterMap.mp hx
      have hyT : y ∉ T.map (·.1) := fun h => by
        unfold gT at hg; rw [ite_eq_left h] at hg; cases hg
      have hgx : x = rwE (ρL T) y := by
        unfold gT at hg; rw [ite_eq_right hyT] at hg; simp only [Option.some.injEq] at hg
        exact hg.symm
      subst hgx
      rcases hcr.2.2.2 y hy with ⟨t, ht, rfl⟩ | ⟨c, hc, hcM, rfl⟩
      · exact Or.inl ⟨t, List.mem_append_right _ ht,
          rwKids_comp M T hTel hTM hTfM t.1 (hdisj t (hDL t ht))⟩
      · refine Or.inr ⟨c, hc, ?_, rwE_comp M T hTel hTM hTfM c⟩
        rw [List.map_append]
        intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hcM hm
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
          rw [rwE_self M t.1 (hTM t ht)] at hyT
          exact hyT (List.mem_map.mpr ⟨t, ht, rfl⟩)

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## Levels are tight -/

/-- Pushing `v` to the entries `ks` leaves each entry as it was or at `v`. -/
theorem foldl_modify_cases (v : Nat) : ∀ (ks : List Nat) (up : Array Nat) (j : Nat),
    j < up.size →
    (ks.foldl (fun up k => up.modify k (max · v)) up)[j]! = up[j]! ∨
      (j ∈ ks ∧ (ks.foldl (fun up k => up.modify k (max · v)) up)[j]! = v) := by
  intro ks
  induction ks with
  | nil => intro up j _; exact Or.inl rfl
  | cons k ks ih =>
    intro up j hj
    simp only [List.foldl_cons]
    rcases ih (up.modify k (max · v)) j (by simpa using hj) with h | h
    · rw [h, modify_getElem! _ _ _ hj]
      split
      · by_cases hv : up[j]! ≤ v
        · exact Or.inr ⟨by simp [*], by omega⟩
        · exact Or.inl (by omega)
      · exact Or.inl rfl
    · exact Or.inr ⟨List.mem_cons_of_mem _ h.1, h.2⟩

/-- `propagateUp.go` gives each entry its initial value or the value of a processed parent
    plus that parent's bonus. -/
theorem propagateUp_go_cases (kids : Array (List Nat)) (marked : Array Bool)
    (hk : ∀ i < kids.size, ∀ k ∈ kids[i]!, k < i) :
    ∀ i (up : Array Nat), up.size = kids.size → i ≤ kids.size → ∀ j < kids.size,
      (propagateUp.go kids marked i up)[j]! = up[j]! ∨
        ∃ i' < i, j ∈ kids[i']! ∧ (propagateUp.go kids marked i up)[j]! =
          (propagateUp.go kids marked i up)[i']! + bonus marked i' := by
  intro i
  induction i with
  | zero => intro up _ _ j _; exact Or.inl rfl
  | succ i ih =>
    intro up hs hi j hj
    simp only [propagateUp.go]
    obtain ⟨f1, -, -, -⟩ := foldl_modify_spec (up[i]! + bonus marked i) (kids[i]!) up
    obtain ⟨g1, g2, -, -⟩ := propagateUp_go_spec kids marked hk i
      ((kids[i]!).foldl (fun a k => a.modify k (max · (up[i]! + bonus marked i))) up)
      (by rw [f1, hs]) (by omega)
    rcases ih _ (by rw [f1, hs]) (by omega) j hj with h | ⟨i', hi', hm, h⟩
    · rcases foldl_modify_cases (up[i]! + bonus marked i) (kids[i]!) up j (by omega) with h' | h'
      · exact Or.inl (h.trans h')
      · right
        refine ⟨i, by omega, h'.1, ?_⟩
        rw [h, h'.2]
        have hil := hk i (by omega) j h'.1
        have := g2 i (Nat.le_refl _) (by omega)
        rw [this]
        have hnot : i ∉ kids[i]! := fun hm' => by have := hk i (by omega) i hm'; omega
        obtain ⟨-, f2, -, -⟩ := foldl_modify_spec (up[i]! + bonus marked i) (kids[i]!) up
        rw [f2 i (by omega) hnot]
    · exact Or.inr ⟨i', by omega, hm, h⟩

/-- **Levels are witnessed.** Every positive entry of `propagateUp` is a parent's value plus the
    parent's bonus. -/
theorem propagateUp_witness (kids : Array (List Nat)) (marked : Array Bool)
    (hk : ∀ i < kids.size, ∀ k ∈ kids[i]!, k < i) (j : Nat) (hj : j < kids.size)
    (hpos : 0 < (propagateUp kids marked)[j]!) :
    ∃ i < kids.size, j ∈ kids[i]! ∧
      (propagateUp kids marked)[j]! = (propagateUp kids marked)[i]! + bonus marked i := by
  unfold propagateUp at hpos ⊢
  rcases propagateUp_go_cases kids marked hk kids.size (Array.replicate kids.size 0) (by simp)
    (Nat.le_refl _) j hj with h | ⟨i, hi, hm, h⟩
  · rw [h] at hpos
    rw [getElem!_pos _ _ (by simpa using hj)] at hpos
    simp at hpos
  · exact ⟨i, hi, hm, h⟩

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- `IsSub` passes to erasures. -/
theorem IsSub.erase {c e : Expression.Expr} (h : IsSub c e) : IsSub (E c) (E e) := by
  induction h with
  | refl => exact .refl _
  | app₁ m f x _ ih => exact .app₁ _ _ _ ih
  | app₂ m f x _ ih => exact .app₂ _ _ _ ih
  | ite₁ m c t f _ ih => exact .ite₁ _ _ _ _ ih
  | ite₂ m c t f _ ih => exact .ite₂ _ _ _ _ ih
  | ite₃ m c t f _ ih => exact .ite₃ _ _ _ _ ih
  | eq₁ m x y _ ih => exact .eq₁ _ _ _ ih
  | eq₂ m x y _ ih => exact .eq₂ _ _ _ ih
  | abs m n ty b _ ih => exact .abs _ _ _ _ ih
  | quant₁ m k n ty tr b _ ih => exact .quant₁ _ _ _ _ _ _ ih
  | quant₂ m k n ty tr b _ ih => exact .quant₂ _ _ _ _ _ _ ih

/-- A child in the DAG is a proper subterm, up to locations. -/
theorem DInv.kid_psub {g : Dag} (hg : DInv g) {i k : Nat} (hi : i < g.nodes.size)
    (hk : k ∈ g.kids[i]!) : IsPSub (E g.nodes[k]!) (E g.nodes[i]!) := by
  obtain ⟨jj, hjj, rfl⟩ := List.mem_iff_getElem.mp hk
  obtain ⟨h1, h2⟩ := hg.2.2.2.2 i hi
  obtain ⟨-, h4⟩ := h2 jj hjj
  have hjl : jj < (childList g.nodes[i]!).length := by omega
  obtain ⟨hs, hsz⟩ := childList_spec _ jj hjl
  rw [h4, getElem!_pos (childList g.nodes[i]!) jj hjl]
  refine ⟨hs.erase, fun he => ?_⟩
  have := congrArg esize he; simp only [esize_E] at this; omega

/-- Only set entries become `true`. -/
theorem foldl_set_true {α : Type} (ix : α → Nat) : ∀ (L : List α) (a : Array Bool) (j : Nat),
    (L.foldl (fun a x => a.set! (ix x) true) a)[j]! = true → a[j]! = true ∨ ∃ x ∈ L, ix x = j := by
  intro L
  induction L with
  | nil => intro a j h; exact Or.inl h
  | cons y ys ih =>
    intro a j h
    simp only [List.foldl_cons] at h
    rcases ih _ j h with h' | ⟨x, hx, hxj⟩
    · by_cases hy : ix y = j
      · exact Or.inr ⟨y, by simp, hy⟩
      · left
        have hne : (a.set! (ix y) true)[j]! = a[j]! := by
          simp only [getElem!_def, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hy]
        rw [← hne]; exact h'
    · exact Or.inr ⟨x, by simp [hx], hxj⟩

/-- A marked node is the node of a named node. -/
theorem spMarked_inv (body : Statements) (i : Nat) (h : (spMarked body)[i]! = true) :
    ∃ x ∈ spNamed body, spIndex body x.1 x.2.1 = i := by
  unfold spMarked at h
  rcases foldl_set_true (fun (x : UInt64 × Expression.Expr × LMonoTy) => spIndex body x.1 x.2.1)
    (spNamed body) _ i h with h' | h'
  · by_cases hi : i < (spDag body).nodes.size
    · rw [getElem!_pos _ _ (by simpa using hi)] at h'; simp at h'
    · rw [getElem!_neg _ _ (by simpa using hi)] at h'; simp at h'
  · exact h'

/-- **Levels are tight.** A DAG node with a positive level is a proper subterm (up to
    locations) of a named node whose level is one less. -/
theorem spLevel_tight (body : Statements) :
    ∀ k < (spDag body).nodes.size,
      0 < (propagateUp (spDag body).kids (spMarked body))[k]! →
      ∃ x ∈ spNamed body, IsPSub (E (spDag body).nodes[k]!) (E x.2.1) ∧
        (propagateUp (spDag body).kids (spMarked body))[spIndex body x.1 x.2.1]! + 1 =
          (propagateUp (spDag body).kids (spMarked body))[k]! := by
  obtain ⟨hg, -⟩ := spDag_spec body
  have hks : (spDag body).kids.size = (spDag body).nodes.size := hg.1
  suffices H : ∀ n k, (spDag body).nodes.size - k = n → k < (spDag body).nodes.size →
      0 < (propagateUp (spDag body).kids (spMarked body))[k]! →
      ∃ x ∈ spNamed body, IsPSub (E (spDag body).nodes[k]!) (E x.2.1) ∧
        (propagateUp (spDag body).kids (spMarked body))[spIndex body x.1 x.2.1]! + 1 =
          (propagateUp (spDag body).kids (spMarked body))[k]! from fun k hk => H _ k rfl hk
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k hn hk hpos
    obtain ⟨i, hi, hki, hval⟩ := propagateUp_witness _ _ hg.kids_lt k (by omega) hpos
    have hkl : k < i := hg.kids_lt i hi k hki
    have hpsub := hg.kid_psub (by omega) hki
    by_cases hm : (spMarked body)[i]! = true
    · obtain ⟨x, hx, rfl⟩ := spMarked_inv body _ hm
      have hb : bonus (spMarked body) (spIndex body x.1 x.2.1) = 1 := by simp [bonus, hm]
      rw [hb] at hval
      refine ⟨x, hx, ?_, hval.symm⟩
      rw [← (spIndex_spec body hx).2]; exact hpsub
    · have hb : bonus (spMarked body) i = 0 := by simp [bonus, hm]
      rw [hb, Nat.add_zero] at hval
      obtain ⟨x, hx, h1, h2⟩ := ih _ (by omega) i rfl (by omega) (by omega)
      refine ⟨x, hx, ⟨hpsub.1.trans h1.1, fun he => ?_⟩, by omega⟩
      have := hpsub.size_lt; have := h1.size_lt; rw [he] at *; omega

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## The named nodes -/

/-- The classes of the input's subterms. -/
def U0 (body : Statements) (a : Expression.Expr) : Prop :=
  ∃ r ∈ Statements.collectExprs body, ∃ s, IsSub s r ∧ E a = E s

/-- `U0` is closed under subterms. -/
theorem U0_sub {body : Statements} {a b : Expression.Expr} (hb : U0 body b) (h : IsSub a b) :
    U0 body a := by
  obtain ⟨r, hr, s, hs, hbs⟩ := hb
  obtain ⟨a', ha', hae⟩ := h.transport hbs
  exact ⟨r, hr, a', ha'.trans hs, hae⟩

section Blocked
variable (U : Expression.Expr → Prop)
  (hU : ∀ a b, U a → U b → hx a = hx b → E a = E b)
  (hUsub : ∀ a b, U b → IsSub a b → U a)

include hU hUsub in
/-- Collecting the proper-subterm hashes of the untyped entries of a list. -/
theorem foldlM_blocked_spec (n : Nat) : ∀ (ps : List (UInt64 × Expression.Expr × Option LMonoTy)),
    (∀ p ∈ ps, U p.2.1 ∧ esize p.2.1 ≤ n) → ∀ acc s, ClosedBelow U acc n →
      let r := ((ps.foldlM (fun acc (p : UInt64 × Expression.Expr × Option LMonoTy) =>
        if p.2.2.isNone then collectSubexprHashes acc true p.2.1 else pure acc) acc) s).1
      ClosedBelow U r n ∧ ∀ h, r.contains h = true ↔ acc.contains h = true ∨
        ∃ q ∈ ps, q.2.2 = none ∧ ∃ c, IsSub c q.2.1 ∧ E c ≠ E q.2.1 ∧ hx c = h := by
  intro ps
  induction ps with
  | nil => intro _ acc s hc; simp only [List.foldlM_nil, pure, stateT_pure_apply]; simp [hc]
  | cons p ps ih =>
    intro hps acc s hc
    obtain ⟨hu, hsz⟩ := hps p (by simp)
    simp only [List.foldlM_cons, bind, stateT_bind_apply]
    obtain ⟨h', d, ty⟩ := p
    cases ty with
    | none =>
      simp only [Option.isNone_none, ite_true]
      obtain ⟨a1, a2⟩ := csh_spec U hU hUsub d hu acc true n s hsz hc
      obtain ⟨b1, b2⟩ := ih (fun q hq => hps q (by simp [hq])) _
        ((collectSubexprHashes acc true d) s).2 a1
      refine ⟨b1, fun h => ?_⟩
      rw [b2, a2]
      simp only [true_implies, List.mem_cons]
      constructor
      · rintro ((h0 | ⟨c, hc', hce, hch⟩) | ⟨q, hq, hqn, c, hc', hce, hch⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨_, Or.inl rfl, rfl, c, hc', hce, hch⟩
        · exact Or.inr ⟨q, Or.inr hq, hqn, c, hc', hce, hch⟩
      · rintro (h0 | ⟨q, rfl | hq, hqn, c, hc', hce, hch⟩)
        · exact Or.inl (Or.inl h0)
        · exact Or.inl (Or.inr ⟨c, hc', hce, hch⟩)
        · exact Or.inr ⟨q, hq, hqn, c, hc', hce, hch⟩
    | some ty =>
      simp only [Option.isNone_some, Bool.false_eq_true, ite_false, pure, stateT_pure_apply]
      obtain ⟨b1, b2⟩ := ih (fun q hq => hps q (by simp [hq])) acc s hc
      simp only [pure] at b1 b2
      refine ⟨b1, fun h => ?_⟩
      rw [b2]
      simp only [List.mem_cons]
      constructor
      · rintro (h0 | ⟨q, hq, hqn, rest⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨q, Or.inr hq, hqn, rest⟩
      · rintro (h0 | ⟨q, rfl | hq, hqn, rest⟩)
        · exact Or.inl h0
        · simp at hqn
        · exact Or.inr ⟨q, hq, hqn, rest⟩

end Blocked

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- The duplicates are classes of the input's subterms. -/
theorem spDups_U0 (body : Statements) {p : UInt64 × Expression.Expr} (hp : p ∈ (spDups body).1) :
    U0 body p.2 ∧ hx p.2 = p.1 ∧ eligible p.2 := by
  obtain ⟨h1, h2, r, hr, c, hc, hce⟩ := (collectDups_spec (Statements.collectExprs body)).1 p hp
  exact ⟨⟨r, hr, c, hc, hce⟩, h1, h2⟩

/-- **The named nodes.** Without hash collisions among the input's subterms, the named nodes are
    the typed duplicates that are not (up to locations) a proper subterm of an untyped
    duplicate. -/
theorem spNamed_char (body : Statements)
    (hnc : ∀ a b, U0 body a → U0 body b → hx a = hx b → E a = E b)
    (x : UInt64 × Expression.Expr × LMonoTy) :
    x ∈ spNamed body ↔ (x.1, x.2.1) ∈ (spDups body).1 ∧ LExpr.typeCheck [] x.2.1 = some x.2.2 ∧
      ¬ ∃ q ∈ (spDups body).1, LExpr.typeCheck [] q.2 = none ∧
        ∃ c, IsSub c q.2 ∧ E c ≠ E q.2 ∧ E c = E x.2.1 := by
  have hU : ∀ a b, U0 body a → U0 body b → hx a = hx b → E a = E b := hnc
  have hUsub : ∀ a b, U0 body b → IsSub a b → U0 body a := fun a b hb h => U0_sub hb h
  let n := ((spTyped body).map (·.2.1)).foldr (fun d m => max (esize d) m) 0
  have hn : ∀ p ∈ spTyped body, U0 body p.2.1 ∧ esize p.2.1 ≤ n := by
    intro p hp
    rw [spTyped_eq] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    refine ⟨(spDups_U0 body hq).1, ?_⟩
    have := foldr_max_le ((spTyped body).map (·.2.1)) q.2 (by
      rw [spTyped_eq, List.map_map]; exact List.mem_map.mpr ⟨q, hq, rfl⟩)
    exact this
  obtain ⟨-, hbl⟩ := foldlM_blocked_spec (U0 body) hU hUsub n (spTyped body) hn {}
    (spDups body).2 (fun c _ _ h => by simp at h)
  have hblk : ∀ h, (spBlocked body).contains h = true ↔
      ∃ q ∈ spTyped body, q.2.2 = none ∧ ∃ c, IsSub c q.2.1 ∧ E c ≠ E q.2.1 ∧ hx c = h := by
    intro h
    have : spBlocked body = ((spTyped body).foldlM (fun acc (p : UInt64 × Expression.Expr × Option LMonoTy) =>
        if p.2.2.isNone then collectSubexprHashes acc true p.2.1 else pure acc)
      ({} : Std.HashSet UInt64) (spDups body).2).1 := rfl
    rw [this, hbl]
    simp
  have hblk' : ∀ q ∈ (spDups body).1, (spBlocked body).contains q.1 = true ↔
      ∃ q' ∈ (spDups body).1, LExpr.typeCheck [] q'.2 = none ∧
        ∃ c, IsSub c q'.2 ∧ E c ≠ E q'.2 ∧ E c = E q.2 := by
    intro q hq
    obtain ⟨hqU, hqh, -⟩ := spDups_U0 body hq
    rw [hblk, spTyped_eq]
    constructor
    · rintro ⟨q'', hq'', hn', c, hc, hce, hch⟩
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq''
      exact ⟨q', hq', hn', c, hc, hce, hnc _ _ (U0_sub (spDups_U0 body hq').1 hc) hqU
        (hch.trans hqh.symm)⟩
    · rintro ⟨q', hq', hn', c, hc, hce, hcq⟩
      exact ⟨_, List.mem_map.mpr ⟨q', hq', rfl⟩, hn', c, hc, hce, (hx_eq_of_E hcq).trans hqh⟩
  unfold spNamed
  rw [spTyped_eq, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hpx⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simp only at hpx
    split at hpx
    · cases hpx
    · next hb =>
      simp only [Option.map_eq_some_iff] at hpx
      obtain ⟨ty, hty, rfl⟩ := hpx
      exact ⟨hq, hty, fun h => hb ((hblk' q hq).mpr h)⟩
  · rintro ⟨hq, hty, hnb⟩
    refine ⟨_, List.mem_map.mpr ⟨_, hq, rfl⟩, ?_⟩
    simp only
    rw [ite_eq_right (fun h => hnb ((hblk' _ hq).mp h)), hty]
    rfl

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## Sorting by hash -/

/-- `merge` only compares an entry of the left list with one of the right list. -/
theorem merge_congr {α : Type} {le le' : α → α → Bool} : ∀ (n : Nat) (xs ys : List α),
    xs.length + ys.length = n → (∀ a ∈ xs, ∀ b ∈ ys, le a b = le' a b) →
    List.merge xs ys le = List.merge xs ys le' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs ys hn h
    match xs, ys with
    | [], ys => simp
    | x :: xs, [] => simp
    | x :: xs, y :: ys =>
      rw [List.cons_merge_cons, List.cons_merge_cons, h x (by simp) y (by simp)]
      split
      · rw [ih _ (by simp only [List.length_cons] at hn ⊢; omega) xs (y :: ys) rfl
          (fun a ha b hb => h a (by simp [ha]) b hb)]
      · rw [ih _ (by simp only [List.length_cons] at hn ⊢; omega) (x :: xs) ys rfl
          (fun a ha b hb => h a ha b (by simp [hb]))]

/-- `mergeSort` of a list without duplicates only compares distinct entries. -/
theorem mergeSort_congr {α : Type} {le le' : α → α → Bool} : ∀ (n : Nat) (l : List α),
    l.length = n → l.Nodup → (∀ a ∈ l, ∀ b ∈ l, a ≠ b → le a b = le' a b) →
    l.mergeSort le = l.mergeSort le' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro l hn hnd h
    match l with
    | [] => simp
    | [a] => simp
    | a :: b :: xs =>
      rw [List.mergeSort, List.mergeSort]
      simp only [List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd]
      have hklt : ((a :: b :: xs).length + 1) / 2 < (a :: b :: xs).length := by simp; omega
      have hkpos : 0 < ((a :: b :: xs).length + 1) / 2 := by simp
      generalize ((a :: b :: xs).length + 1) / 2 = k at hklt hkpos ⊢
      have hsplit := List.take_append_drop k (a :: b :: xs)
      have hnd' := hnd
      rw [← hsplit] at hnd'
      obtain ⟨hn1, hn2, hdisj⟩ := List.nodup_append.mp hnd'
      have hsub1 : ∀ x ∈ (a :: b :: xs).take k, x ∈ a :: b :: xs :=
        fun x hx => List.mem_of_mem_take hx
      have hsub2 : ∀ x ∈ (a :: b :: xs).drop k, x ∈ a :: b :: xs :=
        fun x hx => List.mem_of_mem_drop hx
      rw [ih _ (by rw [List.length_take]; omega) _ rfl hn1
          (fun x hx y hy hxy => h x (hsub1 x hx) y (hsub1 y hy) hxy),
        ih _ (by rw [List.length_drop]; omega) _ rfl hn2
          (fun x hx y hy hxy => h x (hsub2 x hx) y (hsub2 y hy) hxy)]
      apply merge_congr _ _ _ rfl
      intro x hx y hy
      have hx' := (List.mergeSort_perm _ _).mem_iff.mp hx
      have hy' := (List.mergeSort_perm _ _).mem_iff.mp hy
      exact h x (hsub1 x hx') y (hsub2 y hy') (fun hxy => hdisj x hx' y hy' hxy)

/-- Sorting entries with distinct keys by `<` gives them in increasing key order. -/
theorem mergeSort_lt_sorted {β : Type} (l : List (UInt64 × β))
    (hd : l.Pairwise (fun a b => a.1 ≠ b.1)) :
    (l.mergeSort (fun a b => decide (a.1 < b.1))).Pairwise (fun a b => a.1 < b.1) := by
  have hnd : l.Nodup := hd.imp (fun {a b} h he => h (by rw [he]))
  rw [mergeSort_congr (le' := fun a b => decide (a.1 ≤ b.1)) _ l rfl hnd (fun a ha b hb hab => by
    have : a.1 ≠ b.1 := by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
      have hij : i ≠ j := fun h => hab (by subst h; rfl)
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact List.pairwise_iff_getElem.mp hd i j hi hj h
      · exact Ne.symm (List.pairwise_iff_getElem.mp hd j i hj hi h)
    simp only [decide_eq_decide]
    exact ⟨UInt64.le_of_lt, fun h => UInt64.lt_of_le_of_ne h this⟩)]
  have hs := List.pairwise_mergeSort (le := fun (a b : UInt64 × β) => decide (a.1 ≤ b.1))
    (fun a b c hab hbc => by simp only [ne_eq, decide_eq_true_eq] at *; exact UInt64.le_trans hab hbc)
    (fun a b => by simpa using UInt64.le_total a.1 b.1) l
  have hd' := (List.mergeSort_perm l (fun (a b : UInt64 × β) => decide (a.1 ≤ b.1))).symm.pairwise hd
    (fun {a b} h => Ne.symm h)
  refine (hs.and hd').imp fun ⟨h1, h2⟩ => ?_
  simp only [decide_eq_true_eq] at h1
  exact UInt64.lt_of_le_of_ne h1 h2

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- **The duplicates come in increasing hash order**, when distinct duplicates have distinct
    hashes. -/
theorem collectDups_sorted (exprs : List Expression.Expr)
    (hinj : ∀ p ∈ (collectExprsToAbbreviate.collectDups exprs).1,
      ∀ q ∈ (collectExprsToAbbreviate.collectDups exprs).1, hx p.2 = hx q.2 → E p.2 = E q.2) :
    (collectExprsToAbbreviate.collectDups exprs).1.Pairwise (fun p q => p.1 < q.1) := by
  obtain ⟨hspec1, hspec2⟩ := collectDups_spec exprs
  obtain ⟨hinv, -⟩ := walk_foldl_spec exprs {} WInv_empty
  revert hinj hspec1 hspec2
  simp only [collectExprsToAbbreviate.collectDups]
  generalize exprs.foldl (fun st e => (collectSubexprs st e).2) {} = final at *
  intro hinj hspec1 hspec2
  have hmem : ∀ p, p ∈ final.dups.toList → p.2 = final.dups.getD p.1 #[] := by
    intro p hp
    have := (Std.HashMap.mem_toList_iff_getElem?_eq_some).mp hp
    rw [Std.HashMap.getD_eq_getD_getElem?, this]; rfl
  have hperm := List.mergeSort_perm final.dups.toList (fun a b => decide (a.1 < b.1))
  have hkeys := Std.HashMap.distinct_keys_toList (m := final.dups)
  have hsort := mergeSort_lt_sorted final.dups.toList (hkeys.imp fun {a b} h => by
    simpa using h)
  rw [List.pairwise_flatMap]
  refine ⟨fun ⟨h, b⟩ hb => ?_, hsort.imp_of_mem fun {a b} ha hb hab => ?_⟩
  · -- a bucket holds one class
    rw [List.pairwise_map]
    have hb' := hmem _ (hperm.mem_iff.mp hb)
    simp only at hb'
    subst hb'
    refine (hinv.2 h).2.imp_of_mem fun {x y} hx hy hxy => ?_
    exfalso
    have hx' : (h, x) ∈ (final.dups.toList.mergeSort fun a b => decide (a.1 < b.1)).flatMap
        (fun p => p.2.toList.map (p.1, ·)) :=
      List.mem_flatMap.mpr ⟨_, hb, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
    have hy' : (h, y) ∈ (final.dups.toList.mergeSort fun a b => decide (a.1 < b.1)).flatMap
        (fun p => p.2.toList.map (p.1, ·)) :=
      List.mem_flatMap.mpr ⟨_, hb, List.mem_map.mpr ⟨y, hy, rfl⟩⟩
    have h1 := (hspec1 _ hx').1
    have h2 := (hspec1 _ hy').1
    exact hxy (hinj _ hx' _ hy' (h1.trans h2.symm))
  · intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨x, -, rfl⟩ := hx
    obtain ⟨y, -, rfl⟩ := hy
    simpa using hab

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- The duplicates' classes are the `dups` classes of the walk. -/
theorem collectDups_classes (exprs : List Expression.Expr) (c : Expression.Expr) :
    (∃ p ∈ (collectExprsToAbbreviate.collectDups exprs).1, E p.2 = c) ↔
      dupC (exprs.foldl (fun st e => (collectSubexprs st e).2) {}) c := by
  simp only [collectExprsToAbbreviate.collectDups]
  generalize exprs.foldl (fun st e => (collectSubexprs st e).2) {} = final
  have hperm := List.mergeSort_perm final.dups.toList (fun a b => decide (a.1 < b.1))
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨⟨h, b⟩, hb, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    have := (Std.HashMap.mem_toList_iff_getElem?_eq_some).mp (hperm.mem_iff.mp hb)
    refine ⟨h, x, ?_, rfl⟩
    rw [Std.HashMap.getD_eq_getD_getElem?, this]; simpa using hx
  · rintro ⟨h, x, hx, rfl⟩
    rw [Std.HashMap.getD_eq_getD_getElem?] at hx
    cases hb : final.dups[h]? with
    | none => rw [hb] at hx; simp at hx
    | some b =>
      rw [hb] at hx
      refine ⟨(h, x), List.mem_flatMap.mpr ⟨(h, b), hperm.mem_iff.mpr
        ((Std.HashMap.mem_toList_iff_getElem?_eq_some).mpr hb), ?_⟩, rfl⟩
      exact List.mem_map.mpr ⟨x, by simpa using hx, rfl⟩

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## Which duplicates a round names -/

section Levels
variable (Sc : Expression.Expr → Prop) (ty : Expression.Expr → Option LMonoTy)
  (lvc : Expression.Expr → Nat)

/-- The classes the passes name: typed duplicates that are not a proper subterm of an untyped
    duplicate. -/
def Nc (c : Expression.Expr) : Prop :=
  Sc c ∧ ty c ≠ none ∧ ¬ ∃ b, Sc b ∧ ty b = none ∧ IsPSub c b

variable (hmono : ∀ c c', Nc Sc ty c → Nc Sc ty c' → IsPSub c' c → lvc c < lvc c')
  (htight : ∀ c, Nc Sc ty c → 2 ≤ lvc c → ∃ c', Nc Sc ty c' ∧ IsPSub c c' ∧ lvc c' + 1 = lvc c)
  (hpos : ∀ c, Nc Sc ty c → 1 ≤ lvc c)

include hmono in
/-- A duplicate not named before round `r` contains no class named before round `r`. -/
theorem intact_of_levels (r : Nat) {c m : Expression.Expr} (hc : Sc c)
    (hcM : ¬ (Nc Sc ty c ∧ lvc c < r)) (hm : Nc Sc ty m ∧ lvc m < r) : ¬ IsSub m c := by
  intro hs
  by_cases hmc : m = c
  · subst hmc; exact hcM hm
  have hps : IsPSub m c := ⟨hs, hmc⟩
  by_cases hN : Nc Sc ty c
  · have := hmono c m hN hm.1 hps
    exact hcM ⟨hN, by omega⟩
  · -- `c` is untyped or below an untyped duplicate, so `m` is below one
    obtain ⟨-, hmty, hmb⟩ := hm.1
    apply hmb
    by_cases hcty : ty c = none
    · exact ⟨c, hc, hcty, hps⟩
    · have : ∃ b, Sc b ∧ ty b = none ∧ IsPSub c b := by
        apply Classical.byContradiction
        intro h; exact hN ⟨hc, hcty, h⟩
      obtain ⟨b, hb, hbt, hcb⟩ := this
      exact ⟨b, hb, hbt, ⟨hs.trans hcb.1, fun he => by
        subst he; have := hps.size_lt; have := hcb.size_lt; omega⟩⟩

include hmono htight in
/-- **The round's targets.** At round `r ≥ 1`, a duplicate not named before is typed and
    maximal among the duplicates not named before iff it is named at level `r`. -/
theorem target_iff (r : Nat) (hr : 1 ≤ r) {c : Expression.Expr} (hc : Sc c)
    (hcM : ¬ (Nc Sc ty c ∧ lvc c < r)) :
    (ty c ≠ none ∧ ¬ ∃ d, Sc d ∧ ¬ (Nc Sc ty d ∧ lvc d < r) ∧ IsPSub c d) ↔
      (Nc Sc ty c ∧ lvc c = r) := by
  constructor
  · rintro ⟨hty, hmax⟩
    have hN : Nc Sc ty c := by
      refine ⟨hc, hty, ?_⟩
      rintro ⟨b, hb, hbt, hcb⟩
      exact hmax ⟨b, hb, fun h => by have := h.1.2.1; exact this hbt, hcb⟩
    refine ⟨hN, ?_⟩
    have hge : r ≤ lvc c := by
      apply Classical.byContradiction; intro h; exact hcM ⟨hN, by omega⟩
    apply Classical.byContradiction
    intro hne
    obtain ⟨c', hN', hcc', hlv⟩ := htight c hN (by omega)
    exact hmax ⟨c', hN'.1, fun h => by omega, hcc'⟩
  · rintro ⟨hN, hlv⟩
    refine ⟨hN.2.1, ?_⟩
    rintro ⟨d, hd, hdM, hcd⟩
    by_cases hdN : Nc Sc ty d
    · have := hmono d c hdN hN hcd
      exact hdM ⟨hdN, by omega⟩
    · apply hN.2.2
      by_cases hdty : ty d = none
      · exact ⟨d, hd, hdty, hcd⟩
      · have : ∃ b, Sc b ∧ ty b = none ∧ IsPSub d b := by
          apply Classical.byContradiction
          intro h; exact hdN ⟨hd, hdty, h⟩
        obtain ⟨b, hb, hbt, hdb⟩ := this
        exact ⟨b, hb, hbt, ⟨hcd.1.trans hdb.1, fun he => by
          subst he; have := hcd.size_lt; have := hdb.size_lt; omega⟩⟩

end Levels

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## List orders -/

/-- Filtering a stable sort to one key keeps the original order. -/
theorem filter_mergeSort_eq {α : Type} (κ : α → Nat) (l : List α) (r : Nat) :
    (l.mergeSort (fun a b => decide (κ a ≤ κ b))).filter (fun a => decide (κ a = r)) =
      l.filter (fun a => decide (κ a = r)) := by
  have htrans : ∀ a b c : α, decide (κ a ≤ κ b) = true → decide (κ b ≤ κ c) = true →
      decide (κ a ≤ κ c) = true := fun a b c h1 h2 => by simp at *; omega
  have htot : ∀ a b : α, (decide (κ a ≤ κ b) || decide (κ b ≤ κ a)) = true := fun a b => by
    simp; omega
  have hA : (l.filter (fun a => decide (κ a = r))).Pairwise (fun a b => decide (κ a ≤ κ b) = true) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj _
    have h1 := List.mem_filter.mp (List.getElem_mem hi)
    have h2 := List.mem_filter.mp (List.getElem_mem hj)
    simp only [decide_eq_true_eq] at h1 h2 ⊢; omega
  have hsub := List.sublist_mergeSort htrans htot hA List.filter_sublist
  have hsub' : List.Sublist (l.filter (fun a => decide (κ a = r)))
      ((l.mergeSort (fun a b => decide (κ a ≤ κ b))).filter (fun a => decide (κ a = r))) := by
    have := hsub.filter (fun a => decide (κ a = r))
    rwa [List.filter_filter, show (fun a => decide (κ a = r) && decide (κ a = r)) =
      (fun a => decide (κ a = r)) from funext fun a => Bool.and_self _] at this
  refine (hsub'.eq_of_length ?_).symm
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact ((List.mergeSort_perm l _).countP_eq _).symm

/-- Numbering a list sorted by key and keeping one key: a contiguous block of numbers. -/
theorem zip_range'_filter {α : Type} (κ : α → Nat) (r : Nat) : ∀ (l : List α) (s : Nat),
    l.Pairwise (fun a b => κ a ≤ κ b) →
    ((List.range' s l.length).zip l).filter (fun q => decide (κ q.2 = r)) =
      (List.range' (s + (l.filter (fun a => decide (κ a < r))).length)
        (l.filter (fun a => decide (κ a = r))).length).zip (l.filter (fun a => decide (κ a = r))) ∧
    ((List.range' s l.length).zip l).filter (fun q => decide (κ q.2 < r)) =
      (List.range' s (l.filter (fun a => decide (κ a < r))).length).zip
        (l.filter (fun a => decide (κ a < r))) := by
  intro l
  induction l with
  | nil => intro s _; simp
  | cons x xs ih =>
    intro s hs
    rw [List.pairwise_cons] at hs
    obtain ⟨ih1, ih2⟩ := ih (s + 1) hs.2
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.filter_cons]
    by_cases hlt : κ x < r
    · have hne : ¬ κ x = r := by omega
      simp only [decide_eq_true hlt, decide_eq_false hne, ite_true, Bool.false_eq_true, ite_false,
        List.length_cons, List.range'_succ, List.zip_cons_cons]
      refine ⟨by rw [ih1]; congr 2; omega, by rw [ih2]⟩
    · have hxs : xs.filter (fun a => decide (κ a < r)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha; have := hs.1 a ha; simp; omega
      by_cases heq : κ x = r
      · simp only [decide_eq_true heq, decide_eq_false hlt, ite_true, Bool.false_eq_true, ite_false,
          List.length_cons, List.range'_succ, List.zip_cons_cons]
        rw [hxs] at ih1 ih2 ⊢
        simp only [List.length_nil, Nat.add_zero] at ih1 ih2 ⊢
        exact ⟨by rw [ih1], by rw [ih2]; simp⟩
      · simp only [decide_eq_false heq, decide_eq_false hlt, Bool.false_eq_true, ite_false]
        rw [hxs] at ih1 ih2 ⊢
        simp only [List.length_nil, Nat.add_zero] at ih1 ih2 ⊢
        have hxs' : xs.filter (fun a => decide (κ a = r)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro a ha; have := hs.1 a ha; simp; omega
        rw [hxs'] at ih1 ⊢
        simp only [List.length_nil, List.range'_zero, List.zip_nil_left] at ih1 ⊢
        exact ⟨ih1, ih2⟩

/-- Keys below `r + 1` are keys below `r` followed by key `r`, in a list sorted by key. -/
theorem filter_lt_succ {α : Type} (κ : α → Nat) (r : Nat) : ∀ (l : List α),
    l.Pairwise (fun a b => κ a ≤ κ b) →
    l.filter (fun a => decide (κ a < r + 1)) =
      l.filter (fun a => decide (κ a < r)) ++ l.filter (fun a => decide (κ a = r)) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hs
    rw [List.pairwise_cons] at hs
    simp only [List.filter_cons]
    by_cases hlt : κ x < r
    · simp [decide_eq_true hlt, decide_eq_true (show κ x < r + 1 by omega),
        show ¬ κ x = r by omega, ih hs.2]
    · have hxs : xs.filter (fun a => decide (κ a < r)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha; have := hs.1 a ha; simp; omega
      by_cases heq : κ x = r
      · simp only [decide_eq_true (show κ x < r + 1 by omega), decide_eq_false hlt,
          decide_eq_true heq, ite_true, Bool.false_eq_true, ite_false]
        rw [ih hs.2, hxs, List.nil_append, List.nil_append]
      · have hxs1 : xs.filter (fun a => decide (κ a < r + 1)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro a ha; have := hs.1 a ha; simp; omega
        have hxs2 : xs.filter (fun a => decide (κ a = r)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro a ha; have := hs.1 a ha; simp; omega
        simp only [decide_eq_false (show ¬ κ x < r + 1 by omega), decide_eq_false hlt,
          decide_eq_false heq, Bool.false_eq_true, ite_false, hxs, hxs1, hxs2, List.append_nil]

/-- Two lists in strictly increasing key order with the same entries are equal. -/
theorem eq_of_sorted_lt {α : Type} (κ : α → UInt64) : ∀ (l₁ l₂ : List α),
    l₁.Pairwise (fun a b => κ a < κ b) → l₂.Pairwise (fun a b => κ a < κ b) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ _ h; cases l₂ with
    | nil => rfl
    | cons y ys => exact absurd ((h y).mpr (by simp)) (by simp)
  | cons x xs ih =>
    intro l₂ h₁ h₂ h
    cases l₂ with
    | nil => exact absurd ((h x).mp (by simp)) (by simp)
    | cons y ys =>
      rw [List.pairwise_cons] at h₁ h₂
      have hxy : x = y := by
        rcases List.mem_cons.mp ((h x).mp (by simp)) with hx | hx
        · exact hx
        · rcases List.mem_cons.mp ((h y).mpr (by simp)) with hy | hy
          · exact hy.symm
          · have := h₂.1 x hx; have := h₁.1 y hy
            exact absurd (UInt64.lt_trans ‹κ y < κ x› ‹κ x < κ y›) (UInt64.lt_irrefl _)
      subst hxy
      congr 1
      refine ih ys h₁.2 h₂.2 fun z => ⟨fun hz => ?_, fun hz => ?_⟩
      · rcases List.mem_cons.mp ((h z).mp (by simp [hz])) with h' | h'
        · subst h'; exact absurd (h₁.1 _ hz) (UInt64.lt_irrefl _)
        · exact h'
      · rcases List.mem_cons.mp ((h z).mpr (by simp [hz])) with h' | h'
        · subst h'; exact absurd (h₂.1 _ hz) (UInt64.lt_irrefl _)
        · exact h'

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## Subterms of a rewrite -/

/-- A subterm of a rewrite is a generated variable or the rewrite (children rewritten) of an
    unnamed subterm. -/
theorem sub_rwE (M : List NTarget) : ∀ (e x : Expression.Expr), IsSub x (rwE (ρL M) e) →
    (∃ t ∈ M, x = cseVar t.2.1 t.2.2) ∨
      ∃ s, IsSub s e ∧ s ∉ M.map (·.1) ∧ x = rwKids (ρL M) s := by
  intro e
  induction e with
  | app m f a ihf iha =>
    intro x hx
    rcases rwE_cases M (.app m f a) with ⟨t, ht, -, h2⟩ | ⟨hm, h2⟩
    · rw [h2] at hx; cases hx; exact Or.inl ⟨t, ht, rfl⟩
    · rw [h2] at hx
      cases hx with
      | refl => exact Or.inr ⟨_, .refl _, hm, rfl⟩
      | app₁ _ _ _ h =>
        rcases ihf x h with h | ⟨s, hs1, hs2, hs3⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, .app₁ _ _ _ hs1, hs2, hs3⟩
      | app₂ _ _ _ h =>
        rcases iha x h with h | ⟨s, hs1, hs2, hs3⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, .app₂ _ _ _ hs1, hs2, hs3⟩
  | ite m c t f ihc iht ihf =>
    intro x hx
    rcases rwE_cases M (.ite m c t f) with ⟨t', ht, -, h2⟩ | ⟨hm, h2⟩
    · rw [h2] at hx; cases hx; exact Or.inl ⟨t', ht, rfl⟩
    · rw [h2] at hx
      cases hx with
      | refl => exact Or.inr ⟨_, .refl _, hm, rfl⟩
      | ite₁ _ _ _ _ h =>
        rcases ihc x h with h | ⟨s, hs1, hs2, hs3⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, .ite₁ _ _ _ _ hs1, hs2, hs3⟩
      | ite₂ _ _ _ _ h =>
        rcases iht x h with h | ⟨s, hs1, hs2, hs3⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, .ite₂ _ _ _ _ hs1, hs2, hs3⟩
      | ite₃ _ _ _ _ h =>
        rcases ihf x h with h | ⟨s, hs1, hs2, hs3⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, .ite₃ _ _ _ _ hs1, hs2, hs3⟩
  | eq m a b iha ihb =>
    intro x hx
    rcases rwE_cases M (.eq m a b) with ⟨t, ht, -, h2⟩ | ⟨hm, h2⟩
    · rw [h2] at hx; cases hx; exact Or.inl ⟨t, ht, rfl⟩
    · rw [h2] at hx
      cases hx with
      | refl => exact Or.inr ⟨_, .refl _, hm, rfl⟩
      | eq₁ _ _ _ h =>
        rcases iha x h with h | ⟨s, hs1, hs2, hs3⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, .eq₁ _ _ _ hs1, hs2, hs3⟩
      | eq₂ _ _ _ h =>
        rcases ihb x h with h | ⟨s, hs1, hs2, hs3⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, .eq₂ _ _ _ hs1, hs2, hs3⟩
  | abs m n ty b ih =>
    intro x hx
    rcases rwE_cases M (.abs m n ty b) with ⟨t, ht, -, h2⟩ | ⟨hm, h2⟩
    · rw [h2] at hx; cases hx; exact Or.inl ⟨t, ht, rfl⟩
    · rw [h2] at hx
      cases hx with
      | refl => exact Or.inr ⟨_, .refl _, hm, rfl⟩
      | abs _ _ _ _ h =>
        rcases ih x h with h | ⟨s, hs1, hs2, hs3⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, .abs _ _ _ _ hs1, hs2, hs3⟩
  | quant m k n ty tr b ihtr ihb =>
    intro x hx
    rcases rwE_cases M (.quant m k n ty tr b) with ⟨t, ht, -, h2⟩ | ⟨hm, h2⟩
    · rw [h2] at hx; cases hx; exact Or.inl ⟨t, ht, rfl⟩
    · rw [h2] at hx
      cases hx with
      | refl => exact Or.inr ⟨_, .refl _, hm, rfl⟩
      | quant₁ _ _ _ _ _ _ h =>
        rcases ihtr x h with h | ⟨s, hs1, hs2, hs3⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, .quant₁ _ _ _ _ _ _ hs1, hs2, hs3⟩
      | quant₂ _ _ _ _ _ _ h =>
        rcases ihb x h with h | ⟨s, hs1, hs2, hs3⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, .quant₂ _ _ _ _ _ _ hs1, hs2, hs3⟩
  | _ =>
    intro x hx
    rcases rwE_cases M _ with ⟨t, ht, -, h2⟩ | ⟨hm, h2⟩
    · rw [h2] at hx; cases hx; exact Or.inl ⟨t, ht, rfl⟩
    · rw [h2] at hx
      cases hx
      exact Or.inr ⟨_, .refl _, hm, rfl⟩

/-- No node of `T` is an application's function in a rewrite by `M`, when no node of `T` is an
    application's function in the original and the nodes of `T` mention no generated name of
    `M`. -/
theorem NoFnT_rwE (M T : List NTarget) (hTf : ∀ t ∈ T, FreshIn M t.1) (e : Expression.Expr)
    (he : NoFnT T e) : NoFnT T (rwE (ρL M) e) := by
  intro m f a hs hfm
  rcases sub_rwE M e _ hs with ⟨t, -, ht⟩ | ⟨s, hs1, hs2, hs3⟩
  · simp [cseVar] at ht
  · cases s with
    | app m' f' a' =>
      simp only [rwKids, LExpr.app.injEq] at hs3
      obtain ⟨-, rfl, -⟩ := hs3
      exact rwE_not_mem_T hTf (he m' f' a' hs1) hfm
    | _ => simp [rwKids] at hs3

/-- No node of `T` is an application's function in a node with rewritten children, when it is
    not one in the original and the nodes of `T` mention no generated name of `M`. -/
theorem NoFnT_rwKids (M T : List NTarget) (hTf : ∀ t ∈ T, FreshIn M t.1) (e : Expression.Expr)
    (he : NoFnT T e) : NoFnT T (rwKids (ρL M) e) := by
  intro m f a hs hfm
  cases e with
  | app m' f' a' =>
    simp only [rwKids] at hs
    cases hs with
    | refl => exact rwE_not_mem_T hTf (he _ _ _ (.refl _)) hfm
    | app₁ _ _ _ h => exact NoFnT_rwE M T hTf f' (he.sub T (.app₁ _ _ _ (.refl _))) m f a h hfm
    | app₂ _ _ _ h => exact NoFnT_rwE M T hTf a' (he.sub T (.app₂ _ _ _ (.refl _))) m f a h hfm
  | ite m' c t f' =>
    simp only [rwKids] at hs
    cases hs with
    | ite₁ _ _ _ _ h => exact NoFnT_rwE M T hTf c (he.sub T (.ite₁ _ _ _ _ (.refl _))) m f a h hfm
    | ite₂ _ _ _ _ h => exact NoFnT_rwE M T hTf t (he.sub T (.ite₂ _ _ _ _ (.refl _))) m f a h hfm
    | ite₃ _ _ _ _ h => exact NoFnT_rwE M T hTf f' (he.sub T (.ite₃ _ _ _ _ (.refl _))) m f a h hfm
  | eq m' x y =>
    simp only [rwKids] at hs
    cases hs with
    | eq₁ _ _ _ h => exact NoFnT_rwE M T hTf x (he.sub T (.eq₁ _ _ _ (.refl _))) m f a h hfm
    | eq₂ _ _ _ h => exact NoFnT_rwE M T hTf y (he.sub T (.eq₂ _ _ _ (.refl _))) m f a h hfm
  | abs m' n ty b =>
    simp only [rwKids] at hs
    cases hs with
    | abs _ _ _ _ h => exact NoFnT_rwE M T hTf b (he.sub T (.abs _ _ _ _ (.refl _))) m f a h hfm
  | quant m' k n ty tr b =>
    simp only [rwKids] at hs
    cases hs with
    | quant₁ _ _ _ _ _ _ h =>
      exact NoFnT_rwE M T hTf tr (he.sub T (.quant₁ _ _ _ _ _ _ (.refl _))) m f a h hfm
    | quant₂ _ _ _ _ _ _ h =>
      exact NoFnT_rwE M T hTf b (he.sub T (.quant₂ _ _ _ _ _ _ (.refl _))) m f a h hfm
  | _ => exact he m f a hs hfm

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## The rounds of `stmtRunCSE`, concretely -/

section Rounds
variable (body0 : Statements) (idx0 : Nat)

/-- The level of a named node, from 1. -/
def lvOf (x : UInt64 × Expression.Expr × LMonoTy) : Nat :=
  (propagateUp (spDag body0).kids (spMarked body0))[spIndex body0 x.1 x.2.1]! + 1

/-- The named nodes with their indices, in naming order. -/
def NLi : List (Nat × Target) :=
  (List.range' idx0 (spByRound body0).length).zip (spByRound body0)

/-- A numbered named node as a named class. -/
def toNT (q : Nat × Target) : NTarget := (E q.2.2.1, q.1, q.2.2.2.1)

/-- The classes named before round `r`, in naming order. -/
def Mr (r : Nat) : List NTarget :=
  ((NLi body0 idx0).filter (fun q => decide (q.2.2.2.2 < r))).map toNT

/-- The classes named at round `r`, in hash order. -/
def Tr (r : Nat) : List NTarget :=
  ((NLi body0 idx0).filter (fun q => decide (q.2.2.2.2 = r))).map toNT

/-- The declarations before round `r`, in declaration order (latest round first). -/
def DLr : Nat → List NTarget
  | 0 => []
  | r + 1 => Tr body0 idx0 r ++ DLr r

/-- The declaration of a named class, its children rewritten by `M`, up to locations. -/
def declE (M : List NTarget) (t : NTarget) : Statement :=
  Statement.init ⟨s!"{cseVarPrefix}{t.2.1}", ()⟩ (LTy.forAll [] t.2.2)
    (.det (rwKids (ρL M) t.1)) .empty

/-- The input's expressions, up to locations. -/
def F0 : List Expression.Expr := (Statements.collectExprs body0).map E

/-- The round forest before round `r`: the declarations' right-hand sides, then the input's
    expressions rewritten. -/
def Fr (r : Nat) : List Expression.Expr :=
  (DLr body0 idx0 r).map (fun t => rwKids (ρL (Mr body0 idx0 r)) t.1) ++
    (F0 body0).map (rwE (ρL (Mr body0 idx0 r)))

/-- The state before round `r`, up to locations. -/
def RInv (r : Nat) (body : Statements) (idx : Nat) : Prop :=
  Statements.mapExprs E body = (DLr body0 idx0 r).map (declE (Mr body0 idx0 r)) ++
      Statements.mapExprs (fun e => rwE (ρL (Mr body0 idx0 r)) (E e)) body0 ∧
    idx = idx0 + (Mr body0 idx0 r).length

/-- The naming order sorts by level. -/
theorem spByRound_sorted : (spByRound body0).Pairwise (fun a b => a.2.2.2 ≤ b.2.2.2) := by
  have := List.pairwise_mergeSort (le := fun (a b : Target) => decide (a.2.2.2 ≤ b.2.2.2))
    (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) (spTargets body0)
  exact this.imp fun h => by simpa using h

/-- The numbered named nodes are sorted by level. -/
theorem NLi_sorted : (NLi body0 idx0).Pairwise (fun a b => a.2.2.2.2 ≤ b.2.2.2.2) := by
  unfold NLi
  have h1 : ((List.range' idx0 (spByRound body0).length).zip (spByRound body0)).map Prod.snd =
      spByRound body0 := List.map_snd_zip (by simp)
  have h2 := spByRound_sorted body0
  rw [← h1, List.pairwise_map] at h2
  exact h2

/-- The classes named before round `r + 1`: those before round `r`, then round `r`'s. -/
theorem Mr_succ (r : Nat) : Mr body0 idx0 (r + 1) = Mr body0 idx0 r ++ Tr body0 idx0 r := by
  unfold Mr Tr
  rw [filter_lt_succ (fun q : Nat × Target => q.2.2.2.2) r _ (NLi_sorted body0 idx0), List.map_append]

/-- The declarations before round `r` are classes named before round `r`. -/
theorem DLr_sub : ∀ r, ∀ t ∈ DLr body0 idx0 r, t ∈ Mr body0 idx0 r := by
  intro r
  induction r with
  | zero => intro t ht; simp [DLr] at ht
  | succ r ih =>
    intro t ht
    rw [Mr_succ]
    simp only [DLr, List.mem_append] at ht ⊢
    rcases ht with ht | ht
    · exact Or.inr ht
    · exact Or.inl (ih t ht)

end Rounds

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section Rounds2
variable (body0 : Statements) (idx0 : Nat)

/-- A numbered named node: a named node with its level, numbered from `idx0`. -/
theorem NLi_mem {q : Nat × Target} (hq : q ∈ NLi body0 idx0) :
    (q.2.1, q.2.2.1, q.2.2.2.1) ∈ spNamed body0 ∧
      q.2.2.2.2 = lvOf body0 (q.2.1, q.2.2.1, q.2.2.2.1) ∧
      idx0 ≤ q.1 ∧ q.1 < idx0 + (spByRound body0).length := by
  unfold NLi at hq
  have h2 := List.of_mem_zip hq
  obtain ⟨h3, h4⟩ := spByRound_mem body0 h2.2
  have := List.mem_range'_1.mp h2.1
  exact ⟨h3, h4, this.1, this.2⟩

/-- The numbered named nodes as named classes: distinct classes and distinct indices. -/
theorem NLi_nodup : ((NLi body0 idx0).map (fun q => (toNT q).1)).Nodup ∧
    ((NLi body0 idx0).map (fun q => (toNT q).2.1)).Nodup := by
  constructor
  · have h1 : (NLi body0 idx0).map (fun q => (toNT q).1) =
        (spByRound body0).map (fun t => E t.2.1) := by
      unfold NLi toNT
      rw [show (fun q : Nat × Target => E q.2.2.1) = (fun t : Target => E t.2.1) ∘ Prod.snd from rfl,
        ← List.map_map, List.map_snd_zip (by simp)]
    rw [h1]
    have hperm : (spByRound body0).Perm (spTargets body0) := List.mergeSort_perm _ _
    rw [(hperm.map _).nodup_iff]
    unfold spTargets
    rw [List.map_map]
    rw [List.Nodup, List.pairwise_map]
    exact (spNamed_spec body0).2
  · have h1 : (NLi body0 idx0).map (fun q => (toNT q).2.1) =
        List.range' idx0 (spByRound body0).length := by
      unfold NLi toNT
      rw [show (fun q : Nat × Target => q.1) = Prod.fst from rfl, List.map_fst_zip (by simp)]
    rw [h1]; exact List.nodup_range'

end Rounds2

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section Classes
variable (body0 : Statements) (R0 : List Expression.Expr)
  (hR0 : IsReachList ((Statements.collectExprs body0).flatMap occ) R0)

/-- `occ` of erasures. -/
theorem flatMap_occ_map_E (l : List Expression.Expr) : (l.map E).flatMap occ = l.flatMap occ := by
  rw [List.flatMap_map]; exact flatMap_congr' l (fun x _ => occ_E x)

/-- The input's duplicate classes: visited twice by its walk. -/
def S0 (c : Expression.Expr) : Prop := 2 ≤ cnt c (visits (F0 body0) R0)

include hR0 in
/-- The input's duplicate classes are the classes of its duplicate list. -/
theorem S0_iff (c : Expression.Expr) :
    S0 body0 R0 c ↔ ∃ p ∈ (spDups body0).1, E p.2 = c := by
  obtain ⟨Rw, hRw, -, hd⟩ := walk_forest (Statements.collectExprs body0)
  unfold S0 spDups
  rw [collectDups_classes, hd]
  unfold visits F0
  rw [flatMap_occ_map_E, perm_cnt_eq ((hR0.perm hRw).flatMap_right occK |>.append_left _)]

/-- The level of a named class. -/
noncomputable def lvc (c : Expression.Expr) : Nat :=
  ((spNamed body0).find? (fun x => decide (E x.2.1 = c))).elim 0 (lvOf body0)

/-- The level of a named node's class is the node's level. -/
theorem lvc_eq {x : UInt64 × Expression.Expr × LMonoTy} (hx : x ∈ spNamed body0) :
    lvc body0 (E x.2.1) = lvOf body0 x := by
  unfold lvc
  have hsome : ((spNamed body0).find? (fun y => decide (E y.2.1 = E x.2.1))).isSome := by
    rw [List.find?_isSome]; exact ⟨x, hx, by simp⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
  rw [hy]
  have hym := List.mem_of_find?_eq_some hy
  have hye : E y.2.1 = E x.2.1 := by simpa using List.find?_some hy
  have hnd : ((spNamed body0).map (fun z => E z.2.1)).Nodup := by
    rw [List.Nodup, List.pairwise_map]; exact (spNamed_spec body0).2
  have := eq_of_nodup_map hnd hym hx hye
  subst this; rfl

include hR0 in
/-- **The named classes.** Without hash collisions, a class is named iff it is a typed
    duplicate class that is not a proper subterm of an untyped one. -/
theorem Nc_iff (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)
    (c : Expression.Expr) :
    Nc (S0 body0 R0) (LExpr.typeCheck []) c ↔ ∃ x ∈ spNamed body0, E x.2.1 = c := by
  constructor
  · rintro ⟨hS, hty, hnb⟩
    obtain ⟨p, hp, rfl⟩ := (S0_iff body0 R0 hR0 _).mp hS
    obtain ⟨ty, hty'⟩ := Option.ne_none_iff_exists'.mp (by rwa [typeCheck_E] at hty)
    refine ⟨(p.1, p.2, ty), (spNamed_char body0 hnc _).mpr ⟨hp, hty', ?_⟩, rfl⟩
    rintro ⟨q, hq, hqt, c', hc', hce, hcp⟩
    apply hnb
    refine ⟨E q.2, (S0_iff body0 R0 hR0 _).mpr ⟨q, hq, rfl⟩, by rw [typeCheck_E]; exact hqt, ?_⟩
    simp only at hcp
    refine ⟨?_, fun he => hce (by rw [hcp, he])⟩
    have := hc'.erase; rw [hcp] at this; exact this
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hp, hty, hnb⟩ := (spNamed_char body0 hnc x).mp hx
    refine ⟨(S0_iff body0 R0 hR0 _).mpr ⟨_, hp, rfl⟩, by rw [typeCheck_E, hty]; simp, ?_⟩
    rintro ⟨b, hb, hbt, hcb⟩
    obtain ⟨q, hq, rfl⟩ := (S0_iff body0 R0 hR0 _).mp hb
    apply hnb
    refine ⟨q, hq, by rwa [typeCheck_E] at hbt, ?_⟩
    obtain ⟨c', hc', hce⟩ := hcb.1.transport (E_E q.2)
    exact ⟨c', hc', fun he => hcb.2 (by rw [← E_E x.2.1, hce, he]), by rw [← hce, E_E]⟩

end Classes

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section Classes2
variable (body0 : Statements) (idx0 : Nat) (R0 : List Expression.Expr)
  (hR0 : IsReachList ((Statements.collectExprs body0).flatMap occ) R0)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)

/-- The naming order lists the named nodes with their levels. -/
theorem spByRound_mem_iff (t : Target) :
    t ∈ spByRound body0 ↔ ∃ x ∈ spNamed body0, t = (x.1, x.2.1, x.2.2, lvOf body0 x) := by
  unfold spByRound
  rw [(List.mergeSort_perm _ _).mem_iff]
  unfold spTargets
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

/-- The numbered named nodes are the named nodes. -/
theorem NLi_snd : (NLi body0 idx0).map Prod.snd = spByRound body0 := by
  unfold NLi; exact List.map_snd_zip (by simp)

/-- The classes named before round `r`. -/
theorem Mr_cls_iff (r : Nat) (c : Expression.Expr) :
    c ∈ (Mr body0 idx0 r).map (·.1) ↔ ∃ x ∈ spNamed body0, E x.2.1 = c ∧ lvOf body0 x < r := by
  unfold Mr
  simp only [List.map_map, List.mem_map, List.mem_filter, decide_eq_true_eq, Function.comp]
  constructor
  · rintro ⟨q, ⟨hq, hlt⟩, rfl⟩
    obtain ⟨h1, h2, -⟩ := NLi_mem body0 idx0 hq
    exact ⟨_, h1, rfl, h2 ▸ hlt⟩
  · rintro ⟨x, hx, rfl, hlt⟩
    have : (x.1, x.2.1, x.2.2, lvOf body0 x) ∈ spByRound body0 :=
      (spByRound_mem_iff body0 _).mpr ⟨x, hx, rfl⟩
    rw [← NLi_snd body0 idx0] at this
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp this
    refine ⟨q, ⟨hq, ?_⟩, ?_⟩
    · rw [hqe]; exact hlt
    · simp only [toNT, hqe]

include hR0 hnc in
/-- Levels grow towards proper subterms, on classes. -/
theorem lvc_mono : ∀ c c', Nc (S0 body0 R0) (LExpr.typeCheck []) c →
    Nc (S0 body0 R0) (LExpr.typeCheck []) c' → IsPSub c' c → lvc body0 c < lvc body0 c' := by
  intro c c' hc hc' hps
  obtain ⟨x, hx, rfl⟩ := (Nc_iff body0 R0 hR0 hnc c).mp hc
  obtain ⟨x', hx', rfl⟩ := (Nc_iff body0 R0 hR0 hnc c').mp hc'
  rw [lvc_eq body0 hx, lvc_eq body0 hx']
  have := spLevel_lt body0 hx hx' hps
  unfold lvOf; omega

include hR0 hnc in
/-- Levels are tight, on classes. -/
theorem lvc_tight : ∀ c, Nc (S0 body0 R0) (LExpr.typeCheck []) c → 2 ≤ lvc body0 c →
    ∃ c', Nc (S0 body0 R0) (LExpr.typeCheck []) c' ∧ IsPSub c c' ∧ lvc body0 c' + 1 = lvc body0 c := by
  intro c hc h2
  obtain ⟨x, hx, rfl⟩ := (Nc_iff body0 R0 hR0 hnc c).mp hc
  rw [lvc_eq body0 hx] at h2 ⊢
  obtain ⟨hk, hkE⟩ := spIndex_spec body0 hx
  obtain ⟨x', hx', hps, hlv⟩ := spLevel_tight body0 _ hk (by unfold lvOf at h2; omega)
  refine ⟨E x'.2.1, (Nc_iff body0 R0 hR0 hnc _).mpr ⟨x', hx', rfl⟩, ?_, ?_⟩
  · rw [← hkE]; exact hps
  · rw [lvc_eq body0 hx']; unfold lvOf; omega

include hR0 hnc in
/-- Levels start at 1. -/
theorem lvc_pos : ∀ c, Nc (S0 body0 R0) (LExpr.typeCheck []) c → 1 ≤ lvc body0 c := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := (Nc_iff body0 R0 hR0 hnc c).mp hc
  rw [lvc_eq body0 hx]; unfold lvOf; omega

end Classes2

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- The expressions of a concatenation. -/
theorem bExprs_append (l₁ l₂ : List Statement) : bExprs (l₁ ++ l₂) = bExprs l₁ ++ bExprs l₂ := by
  induction l₁ with
  | nil => simp [bExprs]
  | cons s ss ih => simp [bExprs, ih]

/-- The expressions of a list of `init`s. -/
theorem bExprs_inits {α : Type} (D : List α) (name : α → CoreIdent) (ty : α → Expression.Ty)
    (rhs : α → Expression.Expr) :
    bExprs (D.map fun t => Statement.init (name t) (ty t) (.det (rhs t)) .empty) = D.map rhs := by
  induction D with
  | nil => simp [bExprs]
  | cons t ts ih => simp only [List.map_cons, bExprs, ih]; simp [sExprs, eonExprs]

/-- The expressions of a mapped body. -/
theorem collectExprs_mapExprs (f : Expression.Expr → Expression.Expr) (ss : Statements) :
    Statements.collectExprs (Statements.mapExprs f ss) = (Statements.collectExprs ss).map f := by
  rw [collectExprs_eq, collectExprs_eq, mapExprs_eq_block, bExprs_mapExpr]

section Rounds3
variable (body0 : Statements) (idx0 : Nat)

/-- A round's forest is its expressions up to locations. -/
theorem collectExprs_of_RInv {r : Nat} {body : Statements} {idx : Nat}
    (h : RInv body0 idx0 r body idx) :
    (Statements.collectExprs body).map E = Fr body0 idx0 r := by
  have := congrArg Statements.collectExprs h.1
  have h2 : ∀ A B : Statements, Statements.collectExprs (A ++ B) =
      Statements.collectExprs A ++ Statements.collectExprs B := fun A B => by
    rw [collectExprs_eq, collectExprs_eq, collectExprs_eq, bExprs_append]
  rw [collectExprs_mapExprs, h2, collectExprs_mapExprs] at this
  rw [this, Fr, F0, List.map_map]
  congr 1
  rw [collectExprs_eq]
  exact bExprs_inits _ _ _ _

end Rounds3

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section Rounds4
variable (body0 : Statements) (idx0 : Nat) (R0 : List Expression.Expr)
  (hR0 : IsReachList ((Statements.collectExprs body0).flatMap occ) R0)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)
  (hfresh : FreshCSENames body0 idx0)

include hR0 in
/-- The input's visits are erased classes of its subterms. -/
theorem L0_sub {c : Expression.Expr} (hc : c ∈ visits (F0 body0) R0) :
    E c = c ∧ ∃ r ∈ Statements.collectExprs body0, ∃ s, IsSub s r ∧ c = E s := by
  have hR0' : IsReachList ((F0 body0).flatMap occ) R0 := by
    unfold F0; rw [flatMap_occ_map_E]; exact hR0
  have hFE : ∀ r ∈ F0 body0, E r = r := fun r hr => by
    unfold F0 at hr; obtain ⟨r', -, rfl⟩ := List.mem_map.mp hr; exact E_E r'
  have hsub : ∀ c', (∃ r ∈ F0 body0, IsSub c' r) →
      ∃ r ∈ Statements.collectExprs body0, ∃ s, IsSub s r ∧ c' = E s := by
    rintro c' ⟨r, hr, hs⟩
    unfold F0 at hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    obtain ⟨s, hs', hse⟩ := hs.transport (E_E r')
    exact ⟨r', hr', s, hs', by rw [← hse, hs.E_eq (E_E r')]⟩
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨r, hr, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨s, hs, rfl⟩ := (occ_sub r).1 c hc
    have hsE := hs.E_eq (hFE r hr)
    refine ⟨E_E s, hsub _ ⟨r, hr, ?_⟩⟩
    rw [hsE]; exact hs
  · obtain ⟨d, hd, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨-, r, hr, hdr⟩ := reachList_sub hR0' hFE hd
    obtain ⟨s, hs, -, rfl⟩ := occK_sub d c hc
    have hsE := (hs.trans hdr).E_eq (hFE r hr)
    refine ⟨E_E s, hsub _ ⟨r, hr, ?_⟩⟩
    rw [hsE]; exact hs.trans hdr

include hfresh in
/-- A class of the input's subterms mentions no generated name numbered from `idx0`. -/
theorem fresh_of_orig {M : List NTarget} (hM : ∀ t ∈ M, idx0 ≤ t.2.1) {c : Expression.Expr}
    (hc : ∃ r ∈ Statements.collectExprs body0, ∃ s, IsSub s r ∧ c = E s) : FreshIn M c := by
  obtain ⟨r, hr, s, hs, rfl⟩ := hc
  intro t ht hv
  rw [vars_E] at hv
  exact hfresh t.2.1 (hM t ht) (List.mem_flatMap.mpr ⟨r, hr, hs.vars_subset _ hv⟩)

/-- The classes named before round `r` have indices from `idx0`. -/
theorem Mr_idx (r : Nat) : ∀ t ∈ Mr body0 idx0 r, idx0 ≤ t.2.1 := by
  intro t ht
  unfold Mr at ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact (NLi_mem body0 idx0 (List.mem_filter.mp hq).1).2.2.1

end Rounds4

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section Rounds5
variable (body0 : Statements) (idx0 : Nat) (R0 : List Expression.Expr)
  (hR0 : IsReachList ((Statements.collectExprs body0).flatMap occ) R0)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)
  (hfresh : FreshCSENames body0 idx0)

/-- A class named before round `r` is a named class of level below `r`. -/
theorem Mr_cls_iff' (r : Nat) (c : Expression.Expr) :
    c ∈ (Mr body0 idx0 r).map (·.1) ↔ ∃ x ∈ spNamed body0, E x.2.1 = c ∧ lvc body0 c < r := by
  rw [Mr_cls_iff]
  constructor
  · rintro ⟨x, hx, rfl, h⟩; exact ⟨x, hx, rfl, by rw [lvc_eq body0 hx]; exact h⟩
  · rintro ⟨x, hx, rfl, h⟩; exact ⟨x, hx, rfl, by rw [lvc_eq body0 hx] at h; exact h⟩

include hR0 hnc in
/-- The classes named before round `r`, on classes. -/
theorem Mr_cls_Nc (r : Nat) (c : Expression.Expr) :
    c ∈ (Mr body0 idx0 r).map (·.1) ↔
      (Nc (S0 body0 R0) (LExpr.typeCheck []) c ∧ lvc body0 c < r) := by
  rw [Mr_cls_iff']
  constructor
  · rintro ⟨x, hx, rfl, h⟩
    exact ⟨(Nc_iff body0 R0 hR0 hnc _).mpr ⟨x, hx, rfl⟩, h⟩
  · rintro ⟨hN, h⟩
    obtain ⟨x, hx, rfl⟩ := (Nc_iff body0 R0 hR0 hnc _).mp hN
    exact ⟨x, hx, rfl, h⟩

include hR0 hnc hfresh in
/-- **The duplicates of round `r`** are the input's duplicate classes not named before. -/
theorem round_dups {r : Nat} {body : Statements} {idx : Nat} (h : RInv body0 idx0 r body idx)
    (R : List Expression.Expr)
    (hcr : CR (visits (F0 body0) R0) (Mr body0 idx0 r) (DLr body0 idx0 r) (Fr body0 idx0 r) R)
    (c : Expression.Expr) :
    dupC ((Statements.collectExprs body).foldl (fun st e => (collectSubexprs st e).2) {}) c ↔
      S0 body0 R0 c ∧ c ∉ (Mr body0 idx0 r).map (·.1) := by
  obtain ⟨Rw, hRw, -, hd⟩ := walk_forest (Statements.collectExprs body)
  have hF := collectExprs_of_RInv body0 idx0 h
  have hRw' : IsReachList ((Fr body0 idx0 r).flatMap occ) Rw := by
    rw [← hF, flatMap_occ_map_E]; exact hRw
  have hvis : ∀ x, cnt x ((Statements.collectExprs body).flatMap occ ++ Rw.flatMap occK) =
      cnt x (visits (Fr body0 idx0 r) R) := by
    intro x
    unfold visits
    rw [← hF, flatMap_occ_map_E]
    exact perm_cnt_eq (((hRw'.perm hcr.1).flatMap_right occK).append_left _) x
  -- Intact: a duplicate not named before round `r` contains no named class.
  have hint : ∀ c0, S0 body0 R0 c0 → c0 ∉ (Mr body0 idx0 r).map (·.1) →
      NoneIn (Mr body0 idx0 r) c0 := by
    intro c0 hS hM t ht hs
    have htM : t.1 ∈ (Mr body0 idx0 r).map (·.1) := List.mem_map.mpr ⟨t, ht, rfl⟩
    rw [Mr_cls_Nc body0 idx0 R0 hR0 hnc] at htM hM
    exact intact_of_levels (S0 body0 R0) (LExpr.typeCheck []) (lvc body0)
      (lvc_mono body0 R0 hR0 hnc) r hS hM htM hs
  have hL0 : ∀ c0, c0 ∈ visits (F0 body0) R0 → E c0 = c0 ∧ FreshIn (Mr body0 idx0 r) c0 :=
    fun c0 hc0 => ⟨(L0_sub body0 R0 hR0 hc0).1,
      fresh_of_orig body0 idx0 hfresh (Mr_idx body0 idx0 r) (L0_sub body0 R0 hR0 hc0).2⟩
  rw [hd, hvis]
  constructor
  · intro h2
    have hmem : c ∈ visits (Fr body0 idx0 r) R := cnt_pos.mp (by omega)
    rcases hcr.2.2.2 c hmem with ⟨t, ht, rfl⟩ | ⟨c0, hc0, hc0M, rfl⟩
    · rw [hcr.2.2.1 t ht] at h2; omega
    · obtain ⟨hE0, hf0⟩ := hL0 c0 hc0
      rw [hcr.2.1 c0 hE0 hf0 hc0M] at h2
      rw [rwE_self _ c0 (hint c0 h2 hc0M)]
      exact ⟨h2, hc0M⟩
  · rintro ⟨hS, hM⟩
    have hc0 : c ∈ visits (F0 body0) R0 := cnt_pos.mp (by unfold S0 at hS; omega)
    obtain ⟨hE0, hf0⟩ := hL0 c hc0
    have := hcr.2.1 c hE0 hf0 hM
    rw [rwE_self _ c (hint c hS hM)] at this
    rw [this]; exact hS

end Rounds5

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section Rounds6
variable (body0 : Statements) (idx0 : Nat) (R0 : List Expression.Expr)
  (hR0 : IsReachList ((Statements.collectExprs body0).flatMap occ) R0)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)
  (hfresh : FreshCSENames body0 idx0)

include hR0 in
/-- The input's duplicate classes are classes of its subterms. -/
theorem S0_U0 {c : Expression.Expr} (hc : S0 body0 R0 c) : U0 body0 c := by
  obtain ⟨p, hp, rfl⟩ := (S0_iff body0 R0 hR0 c).mp hc
  obtain ⟨hu, -, -⟩ := spDups_U0 body0 hp
  obtain ⟨r, hr, s, hs, he⟩ := hu
  exact ⟨r, hr, s, hs, by rw [E_E]; exact he⟩

/-- The named nodes come in increasing hash order. -/
theorem spNamed_sorted (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b) :
    (spNamed body0).Pairwise (fun x y => x.1 < y.1) := by
  have hs := collectDups_sorted (Statements.collectExprs body0) (fun p hp q hq hh =>
    hnc _ _ (spDups_U0 body0 hp).1 (spDups_U0 body0 hq).1 hh)
  unfold spNamed
  rw [spTyped_eq, List.pairwise_filterMap, List.pairwise_map]
  refine (hs : (spDups body0).1.Pairwise _).imp fun {a b} hab => ?_
  intro x hx y hy
  have key : ∀ (p : UInt64 × Expression.Expr) (z : UInt64 × Expression.Expr × LMonoTy),
      (match (p.1, p.2, LExpr.typeCheck [] p.2) with
        | (h, d, ty) => if (spBlocked body0).contains h = true then none
          else Option.map (fun x => (h, d, x)) ty) = some z → z.1 = p.1 := by
    intro p z hz
    obtain ⟨h, d⟩ := p
    simp only at hz
    split at hz
    · simp at hz
    · simp only [Option.map_eq_some_iff] at hz
      obtain ⟨_, _, rfl⟩ := hz; rfl
  rw [key a x hx, key b y hy]; exact hab

include hR0 hnc hfresh in
/-- **The targets of round `r`** are the named nodes of level `r`, in hash order (up to the
    locations of the nodes). -/
theorem round_targets {r : Nat} (hr : 1 ≤ r) {body : Statements} {idx : Nat}
    (h : RInv body0 idx0 r body idx) (R : List Expression.Expr)
    (hcr : CR (visits (F0 body0) R0) (Mr body0 idx0 r) (DLr body0 idx0 r) (Fr body0 idx0 r) R) :
    (itTargets body).map (fun p => (p.1, E p.2.1, p.2.2)) =
      ((spNamed body0).filter (fun x => decide (lvOf body0 x = r))).map
        (fun x => (x.1, E x.2.1, x.2.2)) := by
  have hdup := round_dups body0 idx0 R0 hR0 hnc hfresh h R hcr
  generalize hdl : collectExprsToAbbreviate.collectDups (Statements.collectExprs body) = dl at *
  have hcls : ∀ p ∈ dl.1, S0 body0 R0 (E p.2) ∧ E p.2 ∉ (Mr body0 idx0 r).map (·.1) := by
    intro p hp
    rw [← hdup, ← collectDups_classes, hdl]
    exact ⟨p, hp, rfl⟩
  obtain ⟨hspec1, -⟩ := hdl ▸ collectDups_spec (Statements.collectExprs body)
  have hU : ∀ p ∈ dl.1, U0 body0 p.2 ∧ hx p.2 = p.1 := fun p hp => by
    obtain ⟨hS, -⟩ := hcls p hp
    obtain ⟨r', hr', s, hs, he⟩ := S0_U0 body0 R0 hR0 hS
    exact ⟨⟨r', hr', s, hs, by rw [← he, E_E]⟩, (hspec1 p hp).1⟩
  have hsorted : dl.1.Pairwise (fun p q => p.1 < q.1) := by
    have := collectDups_sorted (Statements.collectExprs body) (fun p hp q hq hh => by
      rw [hdl] at hp hq
      exact hnc _ _ (hU p hp).1 (hU q hq).1 hh)
    rwa [hdl] at this
  rw [itTargets_eq, collectExprsToAbbreviate_eq, hdl,
    removeSubsumed_eq (U0 body0) hnc (fun a b hb h => U0_sub hb h) dl.2 dl.1 hU]
  apply eq_of_sorted_lt (fun x => x.1)
  · rw [List.pairwise_map, List.pairwise_filterMap]
    refine (hsorted.filter _).imp fun {a b} hab => ?_
    intro x hx y hy
    simp only [Option.map_eq_some_iff] at hx hy
    obtain ⟨_, -, rfl⟩ := hx; obtain ⟨_, -, rfl⟩ := hy
    exact hab
  · rw [List.pairwise_map]
    exact (spNamed_sorted body0 hnc).filter _
  · intro z
    have hkept : ∀ p ∈ dl.1, (∃ q ∈ dl.1, ∃ c, IsSub c q.2 ∧ E c ≠ E q.2 ∧ E c = E p.2) ↔
        ∃ d, S0 body0 R0 d ∧ ¬ (Nc (S0 body0 R0) (LExpr.typeCheck []) d ∧ lvc body0 d < r) ∧
          IsPSub (E p.2) d := by
      intro p hp
      constructor
      · rintro ⟨q, hq, c, hc, hce, hcp⟩
        obtain ⟨hS, hM⟩ := hcls q hq
        refine ⟨E q.2, hS, (not_congr (Mr_cls_Nc body0 idx0 R0 hR0 hnc r _)).mp hM, ?_, ?_⟩
        · have := hc.erase; rwa [hcp] at this
        · intro he; exact hce (by rw [hcp, he])
      · rintro ⟨d, hS, hM, hps⟩
        have hdup' : dupC ((Statements.collectExprs body).foldl
            (fun st e => (collectSubexprs st e).2) {}) d :=
          (hdup d).mpr ⟨hS, (not_congr (Mr_cls_Nc body0 idx0 R0 hR0 hnc r _)).mpr hM⟩
        rw [← collectDups_classes, hdl] at hdup'
        obtain ⟨q, hq, rfl⟩ := hdup'
        obtain ⟨c, hc, hce⟩ := hps.1.transport (E_E q.2)
        exact ⟨q, hq, c, hc, fun he => hps.2 (by rw [← E_E p.2, hce, he]), by rw [← hce, E_E]⟩
    have hti := fun p (hp : p ∈ dl.1) => target_iff (S0 body0 R0) (LExpr.typeCheck []) (lvc body0)
      (lvc_mono body0 R0 hR0 hnc) (lvc_tight body0 R0 hR0 hnc) r hr (hcls p hp).1
      ((not_congr (Mr_cls_Nc body0 idx0 R0 hR0 hnc r _)).mp (hcls p hp).2)
    simp only [List.mem_map, List.mem_filterMap, List.mem_filter, decide_eq_true_eq,
      Option.map_eq_some_iff]
    constructor
    · rintro ⟨_, ⟨p, ⟨hp, hk⟩, ty, hty, rfl⟩, rfl⟩
      have hk' : ¬ ∃ q ∈ dl.1, ∃ c, IsSub c q.2 ∧ E c ≠ E q.2 ∧ E c = E p.2 := by
        simpa using hk
      rw [hkept p hp] at hk'
      obtain ⟨hN, hlv⟩ := (hti p hp).mp ⟨by rw [typeCheck_E, hty]; simp, hk'⟩
      obtain ⟨x, hxm, hxe⟩ := (Nc_iff body0 R0 hR0 hnc _).mp hN
      obtain ⟨hxh, -, hxty, -⟩ := spNamed_mem body0 hxm
      refine ⟨x, ⟨hxm, by rw [← lvc_eq body0 hxm, hxe]; exact hlv⟩, ?_⟩
      have hpe : hx p.2 = p.1 := (hU p hp).2
      have : x.2.2 = ty := by
        rw [← typeCheck_E, hxe, typeCheck_E, hty] at hxty
        exact (Option.some.inj hxty).symm
      simp only [Prod.mk.injEq]
      exact ⟨by rw [← hxh, ← hpe]; exact hx_eq_of_E hxe, hxe, this⟩
    · rintro ⟨x, ⟨hxm, hlv⟩, rfl⟩
      obtain ⟨hxh, -, hxty, -⟩ := spNamed_mem body0 hxm
      have hN := (Nc_iff body0 R0 hR0 hnc (E x.2.1)).mpr ⟨x, hxm, rfl⟩
      have hlvc : lvc body0 (E x.2.1) = r := by rw [lvc_eq body0 hxm]; exact hlv
      have hdup' : dupC ((Statements.collectExprs body).foldl
          (fun st e => (collectSubexprs st e).2) {}) (E x.2.1) :=
        (hdup _).mpr ⟨hN.1, (not_congr (Mr_cls_Nc body0 idx0 R0 hR0 hnc r _)).mpr (fun h => by omega)⟩
      rw [← collectDups_classes, hdl] at hdup'
      obtain ⟨p, hp, hpe⟩ := hdup'
      have hti' := (hti p hp).mpr ⟨by rw [hpe]; exact hN, by rw [hpe]; exact hlvc⟩
      rw [hpe] at hti'
      obtain ⟨hty, hk⟩ := hti'
      have hty' : LExpr.typeCheck [] p.2 = some x.2.2 := by
        rw [← typeCheck_E, hpe, typeCheck_E, hxty]
      refine ⟨(p.1, p.2, x.2.2), ⟨p, ⟨hp, ?_⟩, x.2.2, hty', rfl⟩, ?_⟩
      · have : ¬ ∃ q ∈ dl.1, ∃ c, IsSub c q.2 ∧ E c ≠ E q.2 ∧ E c = E p.2 := by
          rw [hkept p hp, hpe]; exact hk
        simpa using this
      · simp only [Prod.mk.injEq]
        exact ⟨by rw [← (hU p hp).2, ← hxh]; exact hx_eq_of_E hpe, hpe, trivial⟩

end Rounds6

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- Mapping the expressions of a concatenation. -/
theorem mapExprs_append (f : Expression.Expr → Expression.Expr) (A B : Statements) :
    Statements.mapExprs f (A ++ B) = Statements.mapExprs f A ++ Statements.mapExprs f B := by
  simp [Statements.mapExprs]

/-- Mapping the expressions of a list of `init`s. -/
theorem mapExprs_inits {α : Type} (f : Expression.Expr → Expression.Expr) (D : List α)
    (name : α → CoreIdent) (ty : α → Expression.Ty) (rhs : α → Expression.Expr) :
    Statements.mapExprs f (D.map fun t => Statement.init (name t) (ty t) (.det (rhs t)) .empty) =
      D.map fun t => Statement.init (name t) (ty t) (.det (f (rhs t))) .empty := by
  induction D with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons]
    have : Statements.mapExprs f
        (Statement.init (name t) (ty t) (.det (rhs t)) .empty ::
          ts.map fun t => Statement.init (name t) (ty t) (.det (rhs t)) .empty) =
        Statement.mapExprs f (Statement.init (name t) (ty t) (.det (rhs t)) .empty) ::
          Statements.mapExprs f (ts.map fun t => Statement.init (name t) (ty t) (.det (rhs t)) .empty) :=
      rfl
    rw [this, ih]
    simp [Statement.mapExprs, Stmt.mapExpr, Command.mapExpr]

/-- Mapping twice, at the statement-list level. -/
theorem mapExprs_comp (f g : Expression.Expr → Expression.Expr) (ss : Statements) :
    Statements.mapExprs f (Statements.mapExprs g ss) = Statements.mapExprs (f ∘ g) ss := by
  rw [mapExprs_eq_block, mapExprs_eq_block, mapExprs_eq_block, block_mapExpr_comp]

/-- Mapping depends only on the function at the expressions. -/
theorem mapExprs_congr {f g : Expression.Expr → Expression.Expr} (ss : Statements)
    (h : ∀ e ∈ Statements.collectExprs ss, f e = g e) :
    Statements.mapExprs f ss = Statements.mapExprs g ss := by
  rw [mapExprs_eq_block, mapExprs_eq_block]
  exact block_mapExpr_congr ss (by rw [← collectExprs_eq]; exact h)

/-- The numbered list of a list depends only on the parts of the entries it keeps. -/
theorem zip_map_congr {α β γ : Type} (f₁ : α → γ) (f₂ : β → γ) (g : Nat × γ → NTarget) :
    ∀ (l₁ : List α) (l₂ : List β) (s : Nat), l₁.map f₁ = l₂.map f₂ →
      ((List.range' s l₁.length).zip l₁).map (fun q => g (q.1, f₁ q.2)) =
        ((List.range' s l₂.length).zip l₂).map (fun q => g (q.1, f₂ q.2)) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ s h; cases l₂ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    intro l₂ s h
    cases l₂ with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, h.1,
        ih ys (s + 1) h.2]

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section Rounds7
variable (body0 : Statements) (idx0 : Nat) (R0 : List Expression.Expr)
  (hR0 : IsReachList ((Statements.collectExprs body0).flatMap occ) R0)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)
  (hfresh : FreshCSENames body0 idx0)

/-- The classes named before round `r`, counted. -/
theorem Mr_length (r : Nat) :
    (Mr body0 idx0 r).length =
      ((spByRound body0).filter (fun t => decide (t.2.2.2 < r))).length := by
  unfold Mr NLi
  rw [List.length_map, (zip_range'_filter (fun t : Target => t.2.2.2) r _ idx0
    (spByRound_sorted body0)).2]
  simp

/-- The classes named at round `r`, as a numbered list. -/
theorem Tr_eq_zip (r : Nat) :
    Tr body0 idx0 r = ((List.range' (idx0 + (Mr body0 idx0 r).length)
        ((spByRound body0).filter (fun t => decide (t.2.2.2 = r))).length).zip
        ((spByRound body0).filter (fun t => decide (t.2.2.2 = r)))).map toNT := by
  unfold Tr NLi
  rw [(zip_range'_filter (fun t : Target => t.2.2.2) r _ idx0 (spByRound_sorted body0)).1,
    Mr_length]

/-- Round `r`'s named nodes in hash order. -/
theorem spByRound_filter (r : Nat) :
    (spByRound body0).filter (fun t => decide (t.2.2.2 = r)) =
      ((spNamed body0).filter (fun x => decide (lvOf body0 x = r))).map
        (fun x => (x.1, x.2.1, x.2.2, lvOf body0 x)) := by
  unfold spByRound
  rw [filter_mergeSort_eq (fun t : Target => t.2.2.2) (spTargets body0) r]
  unfold spTargets
  rw [List.filter_map]
  rfl

include hR0 hnc hfresh in
/-- **Round `r` names `Tr r`**: the targets numbered from the round's index are the classes
    named at round `r`. -/
theorem round_Tr {r : Nat} (hr : 1 ≤ r) {body : Statements} {idx : Nat}
    (h : RInv body0 idx0 r body idx) (R : List Expression.Expr)
    (hcr : CR (visits (F0 body0) R0) (Mr body0 idx0 r) (DLr body0 idx0 r) (Fr body0 idx0 r) R) :
    ((List.range' idx (itTargets body).length).zip (itTargets body)).map
        (fun q => (E q.2.2.1, q.1, q.2.2.2)) = Tr body0 idx0 r := by
  rw [Tr_eq_zip, h.2]
  have ht := round_targets body0 idx0 R0 hR0 hnc hfresh hr h R hcr
  have h1 : (itTargets body).map (fun p => (E p.2.1, p.2.2)) =
      ((spByRound body0).filter (fun t => decide (t.2.2.2 = r))).map
        (fun t => (E t.2.1, t.2.2.1)) := by
    rw [spByRound_filter, List.map_map]
    have := congrArg (List.map (fun z : UInt64 × Expression.Expr × LMonoTy => (z.2.1, z.2.2))) ht
    simp only [List.map_map] at this
    exact this
  have := zip_map_congr (fun p : UInt64 × Expression.Expr × LMonoTy => (E p.2.1, p.2.2))
    (fun t : Target => (E t.2.1, t.2.2.1)) (fun q => (q.2.1, q.1, q.2.2)) _ _
    (idx0 + (Mr body0 idx0 r).length) h1
  simp only at this
  rw [this]
  rfl

end Rounds7

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section Rounds8
variable (body0 : Statements) (idx0 : Nat) (R0 : List Expression.Expr)
  (hR0 : IsReachList ((Statements.collectExprs body0).flatMap occ) R0)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)
  (hfresh : FreshCSENames body0 idx0)

/-- An entry of `Tr r` or `Mr r`: a named node's class at its index. -/
theorem named_of_filter {p : Nat × Target → Bool} {t : NTarget}
    (ht : t ∈ ((NLi body0 idx0).filter p).map toNT) :
    ∃ q ∈ NLi body0 idx0, p q = true ∧ t = toNT q := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact ⟨q, (List.mem_filter.mp hq).1, (List.mem_filter.mp hq).2, rfl⟩

/-- The facts every named class has. -/
theorem named_facts {q : Nat × Target} (hq : q ∈ NLi body0 idx0) :
    E (toNT q).1 = (toNT q).1 ∧ elig (toNT q).1 = true ∧ idx0 ≤ (toNT q).2.1 ∧
      (∃ r ∈ Statements.collectExprs body0, ∃ s, IsSub s r ∧ (toNT q).1 = E s) ∧
      LExpr.typeCheck [] (toNT q).1 = some (toNT q).2.2 ∧
      lvc body0 (toNT q).1 = q.2.2.2.2 := by
  obtain ⟨h1, h2, h3, -⟩ := NLi_mem body0 idx0 hq
  obtain ⟨-, hel, hty, r, hr, c, hc, hce⟩ := spNamed_mem body0 h1
  refine ⟨E_E _, by rw [toNT, elig_E]; exact (eligible_iff_elig _).mp hel, h3, ⟨r, hr, c, hc, hce⟩,
    by rw [toNT, typeCheck_E]; exact hty, ?_⟩
  have := lvc_eq body0 h1
  simp only at this
  rw [toNT, this, h2]

end Rounds8

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- `NoFnT` for fewer named classes. -/
theorem NoFnT.mono {T T' : List NTarget} (h : ∀ t ∈ T, t.1 ∈ T'.map (·.1)) {e : Expression.Expr}
    (he : NoFnT T' e) : NoFnT T e := by
  intro m f a hs hf
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp hf
  exact he m f a hs (hte ▸ h t ht)

section Rounds9
variable (body0 : Statements) (idx0 : Nat) (R0 : List Expression.Expr)
  (hR0 : IsReachList ((Statements.collectExprs body0).flatMap occ) R0)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)
  (hfresh : FreshCSENames body0 idx0)
  (hfnN : ∀ r ∈ F0 body0, NoFnT ((NLi body0 idx0).map toNT) r)

include hR0 hnc hfresh in
/-- A duplicate not named before round `r` is visited twice by round `r`'s walk. -/
theorem round_dup_cnt {r : Nat} (R : List Expression.Expr)
    (hcr : CR (visits (F0 body0) R0) (Mr body0 idx0 r) (DLr body0 idx0 r) (Fr body0 idx0 r) R)
    {c : Expression.Expr} (hS : S0 body0 R0 c) (hM : c ∉ (Mr body0 idx0 r).map (·.1)) :
    2 ≤ cnt c (visits (Fr body0 idx0 r) R) := by
  have hc0 : c ∈ visits (F0 body0) R0 := cnt_pos.mp (by unfold S0 at hS; omega)
  obtain ⟨hE0, hsub⟩ := L0_sub body0 R0 hR0 hc0
  have hf0 := fresh_of_orig body0 idx0 hfresh (Mr_idx body0 idx0 r) hsub
  have hint : NoneIn (Mr body0 idx0 r) c := by
    intro t ht hs
    have htM : t.1 ∈ (Mr body0 idx0 r).map (·.1) := List.mem_map.mpr ⟨t, ht, rfl⟩
    rw [Mr_cls_Nc body0 idx0 R0 hR0 hnc] at htM hM
    exact intact_of_levels (S0 body0 R0) (LExpr.typeCheck []) (lvc body0)
      (lvc_mono body0 R0 hR0 hnc) r hS hM htM hs
  have := hcr.2.1 c hE0 hf0 hM
  rw [rwE_self _ c hint] at this
  rw [this]; exact hS

include hR0 hnc in
/-- An entry of `Tr r` is a named class of level `r`. -/
theorem Tr_mem {r : Nat} {t : NTarget} (ht : t ∈ Tr body0 idx0 r) :
    Nc (S0 body0 R0) (LExpr.typeCheck []) t.1 ∧ lvc body0 t.1 = r ∧
      ∃ q ∈ NLi body0 idx0, t = toNT q := by
  obtain ⟨q, hq, hp, rfl⟩ := named_of_filter body0 idx0 ht
  obtain ⟨h1, -⟩ := NLi_mem body0 idx0 hq
  obtain ⟨-, -, -, -, -, hlv⟩ := named_facts body0 idx0 hq
  refine ⟨(Nc_iff body0 R0 hR0 hnc _).mpr ⟨_, h1, rfl⟩, ?_, q, hq, rfl⟩
  rw [hlv]; simpa using hp

end Rounds9

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- `removeSubsumed` keeps some of its entries. -/
theorem removeSubsumed_sub (memo : PtrCache hx) (ps : List (UInt64 × Expression.Expr)) :
    ∀ p ∈ removeSubsumed memo ps, p ∈ ps := by
  intro p hp
  unfold removeSubsumed at hp
  simp only [StateT.run] at hp
  generalize ((ps.foldlM (fun acc p => collectSubexprHashes acc true p.2) {}) memo) = pr at hp
  obtain ⟨sub, _⟩ := pr
  exact (List.mem_filter.mp hp).1

/-- The targets of a round are hashed by their hash. -/
theorem itTargets_hash (body : Statements) : ∀ p ∈ itTargets body, hx p.2.1 = p.1 := by
  intro p hp
  rw [itTargets_eq, collectExprsToAbbreviate_eq] at hp
  obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.mp hp
  simp only [Option.map_eq_some_iff] at hqp
  obtain ⟨ty, -, rfl⟩ := hqp
  exact ((collectDups_spec _).1 q (removeSubsumed_sub _ _ q hq)).1

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- The classes named at round `r` are distinct. -/
theorem Tr_cls_nodup (body0 : Statements) (idx0 : Nat) (r : Nat) :
    ((Tr body0 idx0 r).map (·.1)).Nodup := by
  unfold Tr
  rw [List.map_map]
  exact ((List.filter_sublist).map _).nodup (by
    have := (NLi_nodup body0 idx0).1; exact this)

/-- The classes named before round `r` are distinct, and so are their indices. -/
theorem Mr_nodup (body0 : Statements) (idx0 : Nat) (r : Nat) :
    ((Mr body0 idx0 r).map (·.1)).Nodup ∧ ((Mr body0 idx0 r).map (·.2.1)).Nodup := by
  unfold Mr
  rw [List.map_map, List.map_map]
  exact ⟨((List.filter_sublist).map _).nodup (NLi_nodup body0 idx0).1,
    ((List.filter_sublist).map _).nodup (NLi_nodup body0 idx0).2⟩

/-- A node with no named node strictly inside keeps its children. -/
theorem rwKids_self_of {M T : List NTarget} {t : NTarget} (hTM : NoneIn M t.1)
    (hinc : ∀ t' ∈ T, ¬ IsPSub t'.1 t.1) : rwKids (ρL (M ++ T)) t.1 = t.1 := by
  rw [rwKids_congr (ρ₂ := fun _ => none) _ (fun c hc => ?_), rwKids_none]
  apply ρL_eq_none
  intro hm
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
  rcases List.mem_append.mp hu with hu | hu
  · exact hTM u hu hc.1
  · exact hinc u hu hc

/-- Mapping the expressions of declarations. -/
theorem mapExprs_declE (f : Expression.Expr → Expression.Expr) (M D : List NTarget) :
    Statements.mapExprs f (D.map (declE M)) = D.map (fun t => Statement.init
      ⟨s!"{cseVarPrefix}{t.2.1}", ()⟩ (LTy.forAll [] t.2.2) (.det (f (rwKids (ρL M) t.1))) .empty) :=
  mapExprs_inits f D (fun t => ⟨s!"{cseVarPrefix}{t.2.1}", ()⟩) (fun t => LTy.forAll [] t.2.2)
    (fun t => rwKids (ρL M) t.1)

/-- The rewritten body of a round, up to locations. -/
theorem itBody_E (body : Statements) (idx : Nat) :
    Statements.mapExprs E (itBody body idx) =
      Statements.mapExprs (fun e => rwE (ρOf (itFold body idx).2.1) (E e)) body := by
  unfold itBody
  simp only [StateT.run']
  exact (mapExprsM_spec (RwInv (ρOf (itFold body idx).2.1))
    (fun e => Prod.fst <$> replaceSubexprs (itFold body idx).2.1 e)
    (fun e => rwE (ρOf (itFold body idx).2.1) (E e))
    (fun e s hs => by
      obtain ⟨h1, h2, -⟩ := replaceSubexprs_spec (itFold body idx).2.1 e s hs
      simp only [stateT_map_fst_apply]
      exact ⟨h1, h2⟩) body _ (RwInv_empty _)).2

/-- The facts every class named before some round has. -/
theorem Mr_facts (body0 : Statements) (idx0 : Nat) (r : Nat) {t : NTarget}
    (htM : t ∈ Mr body0 idx0 r) :
    E t.1 = t.1 ∧ elig t.1 = true ∧ idx0 ≤ t.2.1 ∧
      (∃ r ∈ Statements.collectExprs body0, ∃ s, IsSub s r ∧ t.1 = E s) := by
  obtain ⟨q, hq, -, rfl⟩ := named_of_filter body0 idx0 htM
  obtain ⟨h1, h2, h3, h4, -⟩ := named_facts body0 idx0 hq
  exact ⟨h1, h2, h3, h4⟩

section Rounds10
variable (body0 : Statements) (idx0 : Nat) (R0 : List Expression.Expr)
  (hR0 : IsReachList ((Statements.collectExprs body0).flatMap occ) R0)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)
  (hfresh : FreshCSENames body0 idx0)
  (hfnN : ∀ r ∈ F0 body0, NoFnT ((NLi body0 idx0).map toNT) r)

include hR0 hnc hfresh hfnN in
/-- **One concrete round.** A state before round `r ≥ 1` with targets steps to the state
    before round `r + 1`. -/
theorem round_iter {r : Nat} (hr : 1 ≤ r) {body : Statements} {idx : Nat}
    (h : RInv body0 idx0 r body idx) (R : List Expression.Expr)
    (hcr : CR (visits (F0 body0) R0) (Mr body0 idx0 r) (DLr body0 idx0 r) (Fr body0 idx0 r) R)
    (hne : Tr body0 idx0 r ≠ []) :
    ∃ body' idx', stmtRunCSEIter body idx = some (body', idx') ∧
      RInv body0 idx0 (r + 1) body' idx' ∧
      ∃ R', CR (visits (F0 body0) R0) (Mr body0 idx0 (r + 1)) (DLr body0 idx0 (r + 1))
        (Fr body0 idx0 (r + 1)) R' := by
  classical
  have hT := round_Tr body0 idx0 R0 hR0 hnc hfresh hr h R hcr
  generalize hIT : itTargets body = IT at hT
  have hITne : IT ≠ [] := by intro h'; subst h'; exact hne (by rw [← hT]; rfl)
  have hlen : IT.length = (Tr body0 idx0 r).length := by
    rw [← hT]; simp
  -- Facts about the named classes of the round.
  have hTfacts : ∀ t ∈ Tr body0 idx0 r, Nc (S0 body0 R0) (LExpr.typeCheck []) t.1 ∧
      lvc body0 t.1 = r ∧ ∃ q ∈ NLi body0 idx0, t = toNT q :=
    fun t ht => Tr_mem body0 idx0 R0 hR0 hnc ht
  have hMfacts : ∀ m ∈ Mr body0 idx0 r, Nc (S0 body0 R0) (LExpr.typeCheck []) m.1 ∧
      lvc body0 m.1 < r := fun m hm =>
    (Mr_cls_Nc body0 idx0 R0 hR0 hnc r m.1).mp (List.mem_map.mpr ⟨m, hm, rfl⟩)
  have hmono := lvc_mono body0 R0 hR0 hnc
  have hTM : ∀ t ∈ Tr body0 idx0 r, NoneIn (Mr body0 idx0 r) t.1 := by
    intro t ht m hm hs
    obtain ⟨hN, hlv, -⟩ := hTfacts t ht
    obtain ⟨hN', hlv'⟩ := hMfacts m hm
    by_cases he : m.1 = t.1
    · rw [he] at hlv'; omega
    · have := hmono _ _ hN hN' ⟨hs, he⟩; omega
  have hinc : ∀ t ∈ Tr body0 idx0 r, ∀ t' ∈ Tr body0 idx0 r, ¬ IsPSub t'.1 t.1 := by
    intro t ht t' ht' hps
    obtain ⟨hN, hlv, -⟩ := hTfacts t ht
    obtain ⟨hN', hlv', -⟩ := hTfacts t' ht'
    have := hmono _ _ hN hN' hps; omega
  have hMsucc := Mr_succ body0 idx0 r
  -- The rewrite of the round.
  obtain ⟨hF1, hF2, hF3⟩ := itFold_eq body idx
  rw [hIT] at hF1 hF2 hF3
  let P : List (Nat × Target) :=
    (List.range' idx IT.length).zip (IT.map fun t => (t.1, t.2.1, t.2.2, 0))
  have hPlen : P.length = IT.length := by simp [P]
  have hPget : ∀ j (hj : j < P.length), P[j] = (idx + j, ((IT[j]'(by omega)).1,
      (IT[j]'(by omega)).2.1, (IT[j]'(by omega)).2.2, 0)) := by
    intro j hj; simp [P, List.getElem_zip, List.getElem_range']
  have hPmap : P.map (fun q => (E q.2.2.1, q.1, q.2.2.2.1)) = Tr body0 idx0 r := by
    rw [← hT]
    simp only [P, List.zip_map_right, List.map_map]
    rfl
  have hρ : ∀ c, E c = c → ρOf (itFold body idx).2.1 c = ρL (Tr body0 idx0 r) c := by
    intro c hc
    rw [← hPmap]
    refine ρOf_eq_ρL _ P (fun h p => ?_) (fun q hq => ?_) ?_ c hc
    · rw [hF3]
      constructor
      · rintro ⟨j, hj, h1, rfl⟩
        refine ⟨P[j]'(by omega), List.getElem_mem _, ?_, ?_⟩ <;> rw [hPget j (by omega)]
        · exact h1
      · rintro ⟨q, hq, h1, rfl⟩
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
        rw [hPget j hj] at h1 ⊢
        exact ⟨j, by omega, h1, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
      rw [hPget j hj]
      have := itTargets_hash body (IT[j]'(by omega)) (by rw [hIT]; exact List.getElem_mem _)
      exact this
    · rw [hPmap]
      exact Tr_cls_nodup body0 idx0 r
  -- Facts for composing namings.
  have hTsubM : ∀ t ∈ Tr body0 idx0 r, t ∈ Mr body0 idx0 (r + 1) := fun t ht => by
    rw [hMsucc]; exact List.mem_append_right _ ht
  have hTel : ∀ t ∈ Tr body0 idx0 r, elig t.1 = true := fun t ht =>
    (Mr_facts body0 idx0 (r + 1) (hTsubM t ht)).2.1
  have hfrM : ∀ M : List NTarget, (∀ m ∈ M, idx0 ≤ m.2.1) → ∀ t ∈ Mr body0 idx0 (r + 1),
      FreshIn M t.1 := fun M hM t ht =>
    fresh_of_orig body0 idx0 hfresh hM (Mr_facts body0 idx0 (r + 1) ht).2.2.2
  have hTfM : ∀ t ∈ Tr body0 idx0 r, FreshIn (Mr body0 idx0 r) t.1 := fun t ht =>
    hfrM _ (Mr_idx body0 idx0 r) t (hTsubM t ht)
  have hdisj : ∀ m ∈ Mr body0 idx0 r, m.1 ∉ (Tr body0 idx0 r).map (·.1) := by
    intro m hm hmT
    have := (Mr_nodup body0 idx0 (r + 1)).1
    rw [hMsucc, List.map_append] at this
    obtain ⟨t, ht, hte⟩ := List.mem_map.mp hmT
    exact (List.nodup_append.mp this).2.2 _ (List.mem_map.mpr ⟨m, hm, rfl⟩) _
      (List.mem_map.mpr ⟨t, ht, rfl⟩) hte.symm
  refine ⟨(itFold body idx).1.reverseAux (itBody body idx), (itFold body idx).2.2, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [stmtRunCSEIter_eq, hIT]
    simp [List.isEmpty_iff, hITne]
  · -- The statements.
    rw [List.reverseAux_eq, mapExprs_append, itBody_E, hF1]
    rw [mapExprs_congr (g := fun e => rwE (ρL (Tr body0 idx0 r)) (E e)) body
      (fun e _ => rwE_congr_E hρ (E e) (E_E e))]
    rw [show (fun e => rwE (ρL (Tr body0 idx0 r)) (E e)) = rwE (ρL (Tr body0 idx0 r)) ∘ E from rfl,
      ← mapExprs_comp, h.1, mapExprs_append, mapExprs_comp, mapExprs_declE]
    show _ = (Tr body0 idx0 r ++ DLr body0 idx0 r).map (declE (Mr body0 idx0 (r + 1))) ++ _
    rw [List.map_append, List.append_assoc]
    congr 1
    · refine (mapExprs_inits E ((List.range' idx IT.length).zip IT)
        (fun q => ⟨s!"{cseVarPrefix}{q.1}", ()⟩) (fun q => LTy.forAll [] q.2.2.2)
        (fun q => q.2.2.1)).trans ?_
      rw [← hT, List.map_map]
      apply List.map_congr_left
      intro q hq
      have hqT : (E q.2.2.1, q.1, q.2.2.2) ∈ Tr body0 idx0 r := by
        rw [← hT]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
      simp only [Function.comp, declE]
      rw [hMsucc, rwKids_self_of (hTM _ hqT) (hinc _ hqT)]
    · congr 1
      · apply List.map_congr_left
        intro t ht
        simp only [declE]
        rw [hMsucc, rwKids_comp _ _ hTel hTM hTfM t.1 (hdisj t (DLr_sub body0 idx0 r t ht))]
      · rw [hMsucc]
        congr 1
        funext e
        exact rwE_comp _ _ hTel hTM hTfM (E e)
  · rw [hF2, h.2, hlen, hMsucc, List.length_append]; omega
  · -- The counting relation.
    have hmem1 : ∀ t ∈ Mr body0 idx0 r ++ Tr body0 idx0 r, t ∈ Mr body0 idx0 (r + 1) := by
      intro t ht; rw [hMsucc]; exact ht
    obtain ⟨-, hstep⟩ := round_step (visits (F0 body0) R0) (F0 body0) R (Mr body0 idx0 r)
      (DLr body0 idx0 r) (Tr body0 idx0 r) hcr
      (by rw [← hMsucc]; exact (Mr_nodup body0 idx0 (r + 1)).2)
      (by rw [← hMsucc]; exact (Mr_nodup body0 idx0 (r + 1)).1)
      (fun t ht => (Mr_facts body0 idx0 (r + 1) (hmem1 t ht)).2.1)
      (fun t ht => (Mr_facts body0 idx0 (r + 1) (hmem1 t ht)).1)
      (fun t ht => hfrM _ (by rw [← hMsucc]; exact Mr_idx body0 idx0 (r + 1)) t (hmem1 t ht))
      (DLr_sub body0 idx0 r)
      (fun f hf => by
        refine ⟨?_, fresh_of_orig body0 idx0 hfresh (by rw [← hMsucc]; exact Mr_idx body0 idx0 (r + 1))
          ?_⟩
        · obtain ⟨g, -, rfl⟩ := List.mem_map.mp hf; exact E_E g
        · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf; exact ⟨g, hg, g, .refl _, rfl⟩)
      (fun x hx' => by
        have hTN : ∀ t ∈ Tr body0 idx0 r, t.1 ∈ ((NLi body0 idx0).map toNT).map (·.1) := by
          intro t ht
          obtain ⟨q, hq, -, rfl⟩ := named_of_filter body0 idx0 ht
          exact List.mem_map.mpr ⟨toNT q, List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩
        rcases List.mem_append.mp hx' with hx' | hx'
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx'
          apply NoFnT_rwKids _ _ hTfM
          obtain ⟨-, -, -, g, hg, s', hs', hte⟩ := Mr_facts body0 idx0 r (DLr_sub body0 idx0 r t ht)
          rw [hte]
          exact (NoFnT.mono hTN (hfnN (E g) (List.mem_map.mpr ⟨g, hg, rfl⟩))).sub _ hs'.erase
        · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx'
          exact NoFnT_rwE _ _ hTfM f (NoFnT.mono hTN (hfnN f hf)))
      (fun t ht => by
        obtain ⟨hN, -, -⟩ := hTfacts t ht
        have hM : t.1 ∉ (Mr body0 idx0 r).map (·.1) := fun h' => by
          obtain ⟨m, hm, hme⟩ := List.mem_map.mp h'
          exact hdisj m hm (hme ▸ List.mem_map.mpr ⟨t, ht, rfl⟩)
        have h2 := round_dup_cnt body0 idx0 R0 hR0 hnc hfresh R hcr hN.1 hM
        have hv : t.1 ∈ visits (Fr body0 idx0 r) R := cnt_pos.mp (by omega)
        exact (hcr.1.2.1 _).mpr hv)
      hinc hTM
    obtain ⟨R', hR'⟩ := hstep
    refine ⟨R', ?_⟩
    unfold Fr
    rw [hMsucc]
    exact hR'

end Rounds10

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- Without a marked function in the DAG, no named class is the function of an application
    in the input. -/
theorem noFnT_of_markedFunction (body0 : Statements) (idx0 : Nat)
    (hmf : markedFunction (spDag body0) (spMarked body0) = false) :
    ∀ r ∈ F0 body0, NoFnT ((NLi body0 idx0).map toNT) r := by
  intro r hr m f a hs hf
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  obtain ⟨c, hc, hce⟩ := hs.transport (e' := r') (E_E r')
  obtain ⟨hg, hsub⟩ := spDag_spec body0
  obtain ⟨i, hi, hie⟩ := hsub r' hr' c hc
  rw [← hce] at hie
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  obtain ⟨hqN, -⟩ := NLi_mem body0 idx0 hq
  obtain ⟨hk1, hk2⟩ := spIndex_spec body0 hqN
  have hmk := (spMarked_spec body0).2 _ hqN
  simp only at hk1 hk2 hmk
  generalize hni : (spDag body0).nodes[i]! = ni at hie
  cases ni with
  | app m' f' a' =>
    simp only [E_app, LExpr.app.injEq] at hie
    obtain ⟨hlen, hkid⟩ := hg.2.2.2.2 i hi
    rw [hni] at hlen hkid
    generalize hks : (spDag body0).kids[i]! = ks at hlen hkid
    cases ks with
    | nil => simp [childList] at hlen
    | cons k ks' =>
      obtain ⟨hk, hkE⟩ := hkid 0 (by simp)
      simp only [List.getElem_cons_zero, childList] at hk hkE
      have hkeq : k = spIndex body0 q.2.1 q.2.2.1 :=
        hg.2.2.2.1 k (by omega) _ hk1 (by
          rw [hkE, hk2]
          show E f' = E q.2.2.1
          have : E f' = E (toNT q).1 := by rw [hie.2.1]
          rw [this]; exact E_E _)
      have : markedFunction (spDag body0) (spMarked body0) = true := by
        unfold markedFunction
        rw [List.any_eq_true]
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        rw [hni, hks]
        simp only
        rw [hkeq]; exact hmk
      rw [hmf] at this; exact absurd this (by decide)
  | _ => simp at hie

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section Fuel
variable (U : Expression.Expr → Prop)
  (hU : ∀ a b, U a → U b → hx a = hx b → E a = E b)
  (hUsub : ∀ a b, U b → IsSub a b → U a)

include hU hUsub in
/-- Collecting the subterm hashes of a list of expressions. -/
theorem foldlM_fuel_spec (n : Nat) : ∀ (es : List Expression.Expr),
    (∀ e ∈ es, U e ∧ esize e ≤ n) → ∀ acc s, ClosedBelow U acc n →
      let r := ((es.foldlM (fun acc e => collectSubexprHashes acc false e) acc) s).1
      ClosedBelow U r n ∧ ∀ h, r.contains h = true ↔ acc.contains h = true ∨
        ∃ e ∈ es, ∃ c, IsSub c e ∧ hx c = h := by
  intro es
  induction es with
  | nil => intro _ acc s hc; simp only [List.foldlM_nil, pure, stateT_pure_apply]; simp [hc]
  | cons e es ih =>
    intro hes acc s hc
    obtain ⟨hu, hsz⟩ := hes e (by simp)
    simp only [List.foldlM_cons, bind, stateT_bind_apply]
    obtain ⟨a1, a2⟩ := csh_spec U hU hUsub e hu acc false n s hsz hc
    obtain ⟨b1, b2⟩ := ih (fun q hq => hes q (by simp [hq])) _
      ((collectSubexprHashes acc false e) s).2 a1
    refine ⟨b1, fun h => ?_⟩
    rw [b2, a2]
    simp only [Bool.false_eq_true, false_implies, true_and, List.mem_cons]
    constructor
    · rintro ((h0 | ⟨c, hc', hch⟩) | ⟨q, hq, c, hc', hch⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨e, Or.inl rfl, c, hc', hch⟩
      · exact Or.inr ⟨q, Or.inr hq, c, hc', hch⟩
    · rintro (h0 | ⟨q, rfl | hq, c, hc', hch⟩)
      · exact Or.inl (Or.inl h0)
      · exact Or.inl (Or.inr ⟨c, hc', hch⟩)
      · exact Or.inr ⟨q, hq, c, hc', hch⟩

end Fuel

/-- **Enough fuel.** Without hash collisions among the input's subterms, `fuel` is at least the
    number of named nodes. -/
theorem fuel_ge (body0 : Statements)
    (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b) :
    (spNamed body0).length ≤ fuel (Statements.collectExprs body0) := by
  let n := (Statements.collectExprs body0).foldr (fun d m => max (esize d) m) 0
  have hn : ∀ e ∈ Statements.collectExprs body0, U0 body0 e ∧ esize e ≤ n := fun e he =>
    ⟨⟨e, he, e, .refl _, rfl⟩, foldr_max_le _ e he⟩
  obtain ⟨-, hfs⟩ := foldlM_fuel_spec (U0 body0) hnc (fun a b hb h => U0_sub hb h) n
    (Statements.collectExprs body0) hn {} PtrCache.empty (fun c _ _ h => by simp at h)
  have hfe : fuel (Statements.collectExprs body0) =
      ((Statements.collectExprs body0).foldlM (fun acc e => collectSubexprHashes acc false e)
        ({} : Std.HashSet UInt64) PtrCache.empty).1.size := rfl
  rw [hfe]
  generalize ((Statements.collectExprs body0).foldlM (fun acc e => collectSubexprHashes acc false e)
    ({} : Std.HashSet UInt64) PtrCache.empty).1 = S at hfs
  have hsub : (spNamed body0).map (·.1) ⊆ S.toList := by
    intro h hh
    obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hh
    obtain ⟨h1, -, -, r, hr, c, hc, hce⟩ := spNamed_mem body0 hxm
    rw [Std.HashSet.mem_toList, ← Std.HashSet.contains_iff_mem, hfs]
    exact Or.inr ⟨r, hr, c, hc, by rw [← h1]; exact (hx_eq_of_E hce).symm⟩
  have hnd : ((spNamed body0).map (·.1)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (spNamed_sorted body0 hnc).imp (fun h => Nat.ne_of_lt h |> fun h' => by
      intro he; exact absurd he (UInt64.ne_of_lt h))
  have := hnd.length_le_of_subset hsub
  rw [List.length_map, Std.HashSet.length_toList] at this
  exact this

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- The single pass's replacement is the naming of its numbered named nodes. -/
theorem spRepl_ρ (body : Statements) (idx : Nat) :
    ∀ c, E c = c → ρOf (spRepl body idx).1 c = ρL ((NLi body idx).map toNT) c := by
  obtain ⟨-, hRmem⟩ := spRepl_spec body idx
  have hPget : ∀ j (hj : j < (NLi body idx).length), (NLi body idx)[j] =
      (idx + j, (spByRound body)[j]'(by simpa [NLi] using hj)) := by
    intro j hj; simp [NLi, List.getElem_zip, List.getElem_range']
  have hPlen : (NLi body idx).length = (spByRound body).length := by simp [NLi]
  intro c hc
  refine ρOf_eq_ρL _ (NLi body idx) (fun h p => ?_) (fun q hq => ?_) ?_ c hc
  · rw [hRmem]
    constructor
    · rintro ⟨j, hj, h1, rfl⟩
      refine ⟨(NLi body idx)[j]'(by omega), List.getElem_mem _, ?_, ?_⟩ <;> rw [hPget j (by omega)]
      · exact h1
    · rintro ⟨q, hq, h1, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
      rw [hPget j hj] at h1 ⊢
      exact ⟨j, by omega, h1, rfl⟩
  · exact (spNamed_mem body (NLi_mem body idx hq).1).1
  · have := (NLi_nodup body idx).1
    rw [List.map_map]; exact this

/-- **The single pass's output, up to locations**: the declarations of the numbered named
    nodes in declaration order, then the body with the named nodes replaced. -/
theorem spOut_E (body : Statements) (idx : Nat) :
    Statements.mapExprs E ((spOut body idx).1 ++ (spOut body idx).2) =
      ((spDeclOrder body idx).map toNT).map (declE ((NLi body idx).map toNT)) ++
        Statements.mapExprs (fun e => rwE (ρL ((NLi body idx).map toNT)) (E e)) body := by
  have hρ := spRepl_ρ body idx
  have hDmem : ∀ p ∈ spDeclOrder body idx, p ∈ NLi body idx := fun p hp =>
    (spDeclOrder_spec body idx).1.mem_iff.mp hp
  unfold spOut
  simp only [StateT.run', bind, pure, stateT_bind_apply, stateT_pure_apply, id_map_eq]
  obtain ⟨rhss, hlen, hdecls, hrhss, hinv⟩ := list_mapM_exists (RwInv (ρOf (spRepl body idx).1))
    (fun (p : Nat × Target) => do
        let (k, _, dup, ty, _) := p
        let rhs ← replaceKids (spRepl body idx).1 dup
        pure (Statement.init ⟨s!"{cseVarPrefix}{k}", ()⟩ (LTy.forAll [] ty) (.det rhs) .empty))
    (fun (pr : (Nat × Target) × Expression.Expr) =>
      Statement.init ⟨s!"{cseVarPrefix}{pr.1.1}", ()⟩ (LTy.forAll [] pr.1.2.2.2.1) (.det pr.2) .empty)
    (fun p rhs => E rhs = rwKids (ρOf (spRepl body idx).1) (E p.2.2.1))
    (spDeclOrder body idx) (fun p hp s hs => by
      obtain ⟨k, h, d, ty, r⟩ := p
      have hel := (spNamed_mem body (NLi_mem body idx (hDmem _ hp)).1).2.1
      obtain ⟨h1, h2⟩ := replaceKids_spec (spRepl body idx).1 d hel.1 s hs
      simp only [bind, pure, stateT_bind_apply, stateT_pure_apply]
      exact ⟨_, rfl, h2, h1⟩) {} (RwInv_empty _)
  obtain ⟨-, hbody⟩ := mapExprsM_spec (RwInv (ρOf (spRepl body idx).1))
    (fun e => Prod.fst <$> replaceSubexprs (spRepl body idx).1 e)
    (fun e => rwE (ρOf (spRepl body idx).1) (E e))
    (fun e s hs => by
      obtain ⟨h1, h2, -⟩ := replaceSubexprs_spec (spRepl body idx).1 e s hs
      simp only [stateT_map_fst_apply]
      exact ⟨h1, h2⟩) body _ hinv
  simp only [bind, pure] at hdecls hbody ⊢
  rw [mapExprs_append, hdecls, hbody]
  congr 1
  · refine (mapExprs_inits E ((spDeclOrder body idx).zip rhss)
      (fun pr => ⟨s!"{cseVarPrefix}{pr.1.1}", ()⟩) (fun pr => LTy.forAll [] pr.1.2.2.2.1)
      (fun pr => pr.2)).trans ?_
    rw [List.map_map]
    apply List.ext_getElem (by simp [hlen])
    intro i hi1 hi2
    have hiD : i < (spDeclOrder body idx).length := by simp only [List.length_map] at hi2; exact hi2
    simp only [List.getElem_map, List.getElem_zip, Function.comp, toNT, declE]
    rw [hrhss i hiD, rwKids_congr_E hρ _ (E_E _)]
  · rw [mapExprs_congr body (fun e _ => rwE_congr_E hρ (E e) (E_E e))]

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- Filtering a stable sort by non-increasing key to one key keeps the original order. -/
theorem filter_mergeSort_ge {α : Type} (κ : α → Nat) (l : List α) (r : Nat) :
    (l.mergeSort (fun a b => decide (κ a ≥ κ b))).filter (fun a => decide (κ a = r)) =
      l.filter (fun a => decide (κ a = r)) := by
  have htrans : ∀ a b c : α, decide (κ a ≥ κ b) = true → decide (κ b ≥ κ c) = true →
      decide (κ a ≥ κ c) = true := fun a b c h1 h2 => by simp at *; omega
  have htot : ∀ a b : α, (decide (κ a ≥ κ b) || decide (κ b ≥ κ a)) = true := fun a b => by
    simp; omega
  have hA : (l.filter (fun a => decide (κ a = r))).Pairwise (fun a b => decide (κ a ≥ κ b) = true) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj _
    have h1 := List.mem_filter.mp (List.getElem_mem hi)
    have h2 := List.mem_filter.mp (List.getElem_mem hj)
    simp only [decide_eq_true_eq] at h1 h2 ⊢; omega
  have hsub := List.sublist_mergeSort htrans htot hA List.filter_sublist
  have hsub' : List.Sublist (l.filter (fun a => decide (κ a = r)))
      ((l.mergeSort (fun a b => decide (κ a ≥ κ b))).filter (fun a => decide (κ a = r))) := by
    have := hsub.filter (fun a => decide (κ a = r))
    rwa [List.filter_filter, show (fun a => decide (κ a = r) && decide (κ a = r)) =
      (fun a => decide (κ a = r)) from funext fun a => Bool.and_self _] at this
  refine (hsub'.eq_of_length ?_).symm
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact ((List.mergeSort_perm l _).countP_eq _).symm

/-- Two lists sorted by non-increasing key are equal when they agree on each key. -/
theorem eq_of_sorted_ge {α : Type} (κ : α → Nat) : ∀ (l₁ l₂ : List α),
    l₁.Pairwise (fun a b => κ b ≤ κ a) → l₂.Pairwise (fun a b => κ b ≤ κ a) →
    (∀ k, l₁.filter (fun a => decide (κ a = k)) = l₂.filter (fun a => decide (κ a = k))) →
    l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _ _ h
    cases l₂ with
    | nil => rfl
    | cons b bs => have := h (κ b); simp at this
  | cons a as ih =>
    intro l₂ h₁ h₂ h
    cases l₂ with
    | nil => have := h (κ a); simp at this
    | cons b bs =>
      rw [List.pairwise_cons] at h₁ h₂
      have hab : κ a = κ b := by
        have ha : a ∈ (b :: bs).filter (fun x => decide (κ x = κ a)) := by
          rw [← h]; simp
        have hb : b ∈ (a :: as).filter (fun x => decide (κ x = κ b)) := by
          rw [h]; simp
        simp only [List.mem_filter, List.mem_cons, decide_eq_true_eq] at ha hb
        rcases ha.1 with rfl | ha'
        · rfl
        rcases hb.1 with rfl | hb'
        · rfl
        have := h₂.1 a ha'; have := h₁.1 b hb'; omega
      have hk := h (κ a)
      simp only [List.filter_cons, decide_eq_true_eq, hab, ite_true] at hk
      simp only [List.cons.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      rw [ih bs h₁.2 h₂.2 (fun k => by
        have := h k
        simp only [List.filter_cons] at this
        split at this
        · simp only [List.cons.injEq] at this; exact this.2
        · exact this)]

/-- The declarations before round `r`, as numbered named nodes. -/
def DLq (body0 : Statements) (idx0 : Nat) : Nat → List (Nat × Target)
  | 0 => []
  | r + 1 => (NLi body0 idx0).filter (fun q => decide (q.2.2.2.2 = r)) ++ DLq body0 idx0 r

/-- `DLr` is `DLq` as named classes. -/
theorem DLr_eq (body0 : Statements) (idx0 : Nat) :
    ∀ r, DLr body0 idx0 r = (DLq body0 idx0 r).map toNT := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih => simp only [DLr, DLq, Tr, ih, List.map_append]

/-- The numbered named nodes of `DLq r` with a given level. -/
theorem DLq_filter (body0 : Statements) (idx0 : Nat) : ∀ r k,
    (DLq body0 idx0 r).filter (fun q => decide (q.2.2.2.2 = k)) =
      if k < r then (NLi body0 idx0).filter (fun q => decide (q.2.2.2.2 = k)) else [] := by
  intro r
  induction r with
  | zero => intro k; simp [DLq]
  | succ r ih =>
    intro k
    simp only [DLq, List.filter_append, ih, List.filter_filter]
    by_cases hkr : k = r
    · subst hkr
      simp only [Nat.lt_irrefl, ite_false, List.append_nil, Nat.lt_succ_self, ite_true]
      congr 1; funext q; simp only [Bool.and_self]
    · have : (fun q : Nat × Target => decide (q.2.2.2.2 = k) && decide (q.2.2.2.2 = r)) =
          fun _ => false := by
        funext q; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      rw [this, List.filter_eq_nil_iff.mpr (fun _ _ => by simp), List.nil_append]
      by_cases hk : k < r
      · simp only [hk, show k < r + 1 by omega, ite_true]
      · simp only [hk, show ¬ k < r + 1 by omega, ite_false]

/-- The levels in `DLq r` are below `r`. -/
theorem DLq_lt (body0 : Statements) (idx0 : Nat) : ∀ r, ∀ q ∈ DLq body0 idx0 r, q.2.2.2.2 < r := by
  intro r
  induction r with
  | zero => intro q hq; simp [DLq] at hq
  | succ r ih =>
    intro q hq
    simp only [DLq, List.mem_append, List.mem_filter, decide_eq_true_eq] at hq
    rcases hq with ⟨-, h⟩ | h
    · omega
    · have := ih q h; omega

/-- `DLq r` is sorted by non-increasing level. -/
theorem DLq_sorted (body0 : Statements) (idx0 : Nat) :
    ∀ r, (DLq body0 idx0 r).Pairwise (fun a b => b.2.2.2.2 ≤ a.2.2.2.2) := by
  intro r
  induction r with
  | zero => simp [DLq]
  | succ r ih =>
    simp only [DLq]
    rw [List.pairwise_append]
    refine ⟨?_, ih, ?_⟩
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj _
      have h1 := List.mem_filter.mp (List.getElem_mem hi)
      have h2 := List.mem_filter.mp (List.getElem_mem hj)
      simp only [decide_eq_true_eq] at h1 h2; omega
    · intro a ha b hb
      have := (List.mem_filter.mp ha).2
      simp only [decide_eq_true_eq] at this
      have := DLq_lt body0 idx0 r b hb; omega

/-- **The declaration order.** Past the last level, the declarations of the rounds come in the
    single pass's declaration order. -/
theorem DLr_eq_declOrder (body0 : Statements) (idx0 : Nat) (r : Nat)
    (hr : ∀ q ∈ NLi body0 idx0, q.2.2.2.2 < r) :
    DLr body0 idx0 r = (spDeclOrder body0 idx0).map toNT := by
  rw [DLr_eq]
  congr 1
  have hdo : spDeclOrder body0 idx0 = (NLi body0 idx0).mergeSort
      (fun a b => decide ((fun q : Nat × Target => q.2.2.2.2) a ≥ (fun q : Nat × Target => q.2.2.2.2) b)) :=
    rfl
  apply eq_of_sorted_ge (fun q : Nat × Target => q.2.2.2.2) _ _ (DLq_sorted body0 idx0 r)
    (spDeclOrder_spec body0 idx0).2
  intro k
  rw [DLq_filter, hdo, filter_mergeSort_ge]
  split
  · rfl
  · symm
    rw [List.filter_eq_nil_iff]
    intro q hq; have := hr q hq; simp only [decide_eq_true_eq]; omega

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section Rounds12
variable (body0 : Statements) (idx0 : Nat) (R0 : List Expression.Expr)
  (hR0 : IsReachList ((Statements.collectExprs body0).flatMap occ) R0)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)
  (hfresh : FreshCSENames body0 idx0)
  (hfnN : ∀ r ∈ F0 body0, NoFnT ((NLi body0 idx0).map toNT) r)

/-- Levels start at 1. -/
theorem NLi_lvl_pos : ∀ q ∈ NLi body0 idx0, 1 ≤ q.2.2.2.2 := by
  intro q hq
  rw [(NLi_mem body0 idx0 hq).2.1]; unfold lvOf; omega

/-- Nothing is named before round 1. -/
theorem Mr_one : Mr body0 idx0 1 = [] := by
  unfold Mr
  rw [List.filter_eq_nil_iff.mpr (fun q hq => by
    have := NLi_lvl_pos body0 idx0 q hq; simp only [decide_eq_true_eq]; omega)]
  rfl

/-- Nothing is declared before round 1. -/
theorem DLr_one : DLr body0 idx0 1 = [] := by
  show Tr body0 idx0 0 ++ [] = []
  unfold Tr
  rw [List.filter_eq_nil_iff.mpr (fun q hq => by
    have := NLi_lvl_pos body0 idx0 q hq; simp only [decide_eq_true_eq]; omega)]
  rfl

/-- Naming nothing changes nothing. -/
theorem rwE_nil (e : Expression.Expr) : rwE (ρL []) e = e :=
  rwE_self [] e (fun t ht => by simp at ht)

/-- The state before round 1 is the input. -/
theorem RInv_one : RInv body0 idx0 1 body0 idx0 := by
  refine ⟨?_, by rw [Mr_one]; rfl⟩
  rw [DLr_one, Mr_one, List.map_nil, List.nil_append]
  exact mapExprs_congr body0 (fun e _ => (rwE_nil (E e)).symm)

include hR0 in
/-- The counting relation holds before round 1. -/
theorem CR_one : CR (visits (F0 body0) R0) (Mr body0 idx0 1) (DLr body0 idx0 1) (Fr body0 idx0 1) R0 := by
  have hF : Fr body0 idx0 1 = F0 body0 := by
    unfold Fr; rw [DLr_one, Mr_one, List.map_nil, List.nil_append]
    conv => rhs; rw [← List.map_id (F0 body0)]
    exact List.map_congr_left (fun e _ => rwE_nil e)
  rw [hF, Mr_one, DLr_one]
  refine ⟨?_, fun c _ _ _ => by rw [rwE_nil], fun t ht => by simp at ht,
    fun x hx' => Or.inr ⟨x, hx', by simp, (rwE_nil x).symm⟩⟩
  unfold F0; rw [flatMap_occ_map_E]; exact hR0

include hR0 hnc hfresh in
/-- A round with nothing to name stops the iteration. -/
theorem iter_none {r : Nat} (hr : 1 ≤ r) {body : Statements} {idx : Nat}
    (h : RInv body0 idx0 r body idx) (R : List Expression.Expr)
    (hcr : CR (visits (F0 body0) R0) (Mr body0 idx0 r) (DLr body0 idx0 r) (Fr body0 idx0 r) R)
    (he : Tr body0 idx0 r = []) : stmtRunCSEIter body idx = none := by
  have hT := round_Tr body0 idx0 R0 hR0 hnc hfresh hr h R hcr
  rw [he] at hT
  have : itTargets body = [] := by
    have := congrArg List.length hT
    simp only [List.length_map, List.length_zip, List.length_range', Nat.min_self,
      List.length_nil] at this
    exact List.eq_nil_of_length_eq_zero this
  rw [stmtRunCSEIter_eq, this]; rfl

include hR0 hnc in
/-- Levels are contiguous: a round with something to name follows one. -/
theorem Tr_ne_pred {r : Nat} (hr : 1 ≤ r) (hne : Tr body0 idx0 (r + 1) ≠ []) :
    Tr body0 idx0 r ≠ [] := by
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hN, hlv, -⟩ := Tr_mem body0 idx0 R0 hR0 hnc ht
  obtain ⟨c', hN', -, hlv'⟩ := lvc_tight body0 R0 hR0 hnc _ hN (by omega)
  have h1 : c' ∈ (Mr body0 idx0 (r + 1)).map (·.1) :=
    (Mr_cls_Nc body0 idx0 R0 hR0 hnc _ c').mpr ⟨hN', by omega⟩
  have h2 : c' ∉ (Mr body0 idx0 r).map (·.1) := fun h' => by
    have := ((Mr_cls_Nc body0 idx0 R0 hR0 hnc _ c').mp h').2; omega
  rw [Mr_succ, List.map_append, List.mem_append] at h1
  intro he
  rcases h1 with h1 | h1
  · exact h2 h1
  · rw [he] at h1; simp at h1

include hR0 hnc in
/-- Past an empty round, every level is smaller. -/
theorem lvl_lt_of_empty {r : Nat} (hr : 1 ≤ r) (he : Tr body0 idx0 r = []) :
    ∀ q ∈ NLi body0 idx0, q.2.2.2.2 < r := by
  have hall : ∀ k, Tr body0 idx0 (r + k) = [] := by
    intro k
    induction k with
    | zero => exact he
    | succ k ih =>
      apply Classical.byContradiction
      intro hne
      have h1 : 1 ≤ r + k := by omega
      exact Tr_ne_pred body0 idx0 R0 hR0 hnc (r := r + k) h1 hne ih
  intro q hq
  apply Classical.byContradiction
  intro hlt
  have : toNT q ∈ Tr body0 idx0 (r + (q.2.2.2.2 - r)) := by
    unfold Tr
    exact List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, by simp; omega⟩, rfl⟩
  rw [hall] at this; simp at this

/-- At most every node is named. -/
theorem Mr_length_le (r : Nat) : (Mr body0 idx0 r).length ≤ (NLi body0 idx0).length := by
  unfold Mr; rw [List.length_map]; exact List.length_filter_le _ _

include hR0 hnc hfresh hfnN in
/-- **The loop.** With enough fuel, the rounds run until one has nothing to name. -/
theorem go_spec : ∀ (f r : Nat) (body : Statements) (idx : Nat) (R : List Expression.Expr),
    1 ≤ r → RInv body0 idx0 r body idx →
    CR (visits (F0 body0) R0) (Mr body0 idx0 r) (DLr body0 idx0 r) (Fr body0 idx0 r) R →
    (NLi body0 idx0).length ≤ f + (Mr body0 idx0 r).length →
    ∃ r', 1 ≤ r' ∧ Tr body0 idx0 r' = [] ∧
      RInv body0 idx0 r' (stmtRunCSE.go f body idx).1 (stmtRunCSE.go f body idx).2 := by
  intro f
  induction f with
  | zero =>
    intro r body idx R hr h hcr hf
    refine ⟨r, hr, ?_, h⟩
    have := Mr_length_le body0 idx0 (r + 1)
    rw [Mr_succ, List.length_append] at this
    apply List.eq_nil_of_length_eq_zero
    omega
  | succ f ih =>
    intro r body idx R hr h hcr hf
    by_cases he : Tr body0 idx0 r = []
    · refine ⟨r, hr, he, ?_⟩
      simp only [stmtRunCSE.go, iter_none body0 idx0 R0 hR0 hnc hfresh hr h R hcr he]
      exact h
    · obtain ⟨body', idx', hit, h', R', hcr'⟩ :=
        round_iter body0 idx0 R0 hR0 hnc hfresh hfnN hr h R hcr he
      simp only [stmtRunCSE.go, hit]
      refine ih (r + 1) body' idx' R' (by omega) h' hcr' ?_
      rw [Mr_succ, List.length_append]
      have : 0 < (Tr body0 idx0 r).length := List.length_pos_iff.mpr he
      omega

end Rounds12

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- `stmtRunCSE` through its loop. -/
theorem stmtRunCSE_eq_go (body : Statements) (idx : Nat) :
    stmtRunCSE body idx = stmtRunCSE.go (fuel (Statements.collectExprs body)) body idx := by
  unfold stmtRunCSE
  simp only [ShareCommon.shareCommon']

/-- The named nodes, counted. -/
theorem NLi_length (body0 : Statements) (idx0 : Nat) :
    (NLi body0 idx0).length = (spNamed body0).length := by
  unfold NLi spByRound
  simp [List.length_mergeSort, spTargets]

/-- **The output of `stmtRunCSE`, up to locations**, when no named node is the function of an
    application: the declarations of the named nodes in the single pass's declaration order,
    then the input with the named nodes replaced. -/
theorem stmtRunCSE_E (body0 : Statements) (idx0 : Nat) (hfresh : FreshCSENames body0 idx0)
    (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)
    (hfnN : ∀ r ∈ F0 body0, NoFnT ((NLi body0 idx0).map toNT) r) :
    Statements.mapExprs E (stmtRunCSE body0 idx0).1 =
        ((spDeclOrder body0 idx0).map toNT).map (declE ((NLi body0 idx0).map toNT)) ++
          Statements.mapExprs (fun e => rwE (ρL ((NLi body0 idx0).map toNT)) (E e)) body0 ∧
      (stmtRunCSE body0 idx0).2 = idx0 + (spByRound body0).length := by
  obtain ⟨R0, hR0, -⟩ := walk_forest (Statements.collectExprs body0)
  obtain ⟨r', hr', he, hinv⟩ := go_spec body0 idx0 R0 hR0 hnc hfresh hfnN
    (fuel (Statements.collectExprs body0)) 1 body0 idx0 R0 (Nat.le_refl _)
    (RInv_one body0 idx0) (CR_one body0 idx0 R0 hR0)
    (by rw [Mr_one, List.length_nil, Nat.add_zero, NLi_length]; exact fuel_ge body0 hnc)
  have hlt := lvl_lt_of_empty body0 idx0 R0 hR0 hnc hr' he
  have hM : Mr body0 idx0 r' = (NLi body0 idx0).map toNT := by
    unfold Mr
    rw [List.filter_eq_self.mpr (fun q hq => by simpa using hlt q hq)]
  rw [stmtRunCSE_eq_go]
  obtain ⟨h1, h2⟩ := hinv
  rw [hM, DLr_eq_declOrder body0 idx0 r' hlt] at h1
  rw [hM, List.length_map, NLi_length] at h2
  refine ⟨h1, ?_⟩
  rw [h2]; unfold spByRound spTargets; simp [List.length_mergeSort]

/-- The single pass's next index. -/
theorem spRepl_idx (body : Statements) (idx : Nat) :
    (spRepl body idx).2 = idx + (spByRound body).length := (spRepl_spec body idx).1

end Core.CSE

namespace Core.CSE

open Lambda Imperative

public section

/-- No two subterms of `body`'s expressions that differ up to locations have the same
    structural hash. -/
def NoHashCollisions (body : Statements) : Prop :=
  ∀ r₁ ∈ Statements.collectExprs body, ∀ r₂ ∈ Statements.collectExprs body,
    ∀ a b, IsSub a r₁ → IsSub b r₂ → LExpr.hashExpr a = LExpr.hashExpr b →
      Core.eraseLocs a = Core.eraseLocs b

end

/-- Without hash collisions, equal hashes of classes of the input's subterms mean equal
    classes. -/
theorem U0_of_noHashCollisions (body : Statements) (hnc : NoHashCollisions body) :
    ∀ a b, U0 body a → U0 body b → hx a = hx b → E a = E b := by
  rintro a b ⟨r₁, hr₁, s₁, hs₁, ha⟩ ⟨r₂, hr₂, s₂, hs₂, hb⟩ hh
  rw [ha, hb]
  exact hnc r₁ hr₁ r₂ hr₂ s₁ s₂ hs₁ hs₂ (((hx_eq_of_E ha).symm.trans hh).trans (hx_eq_of_E hb))

public section

/-- **The single pass computes what `stmtRunCSE` computes**, up to locations: the same next
    index and the same statements once every expression's locations are erased. It assumes
    that the input mentions no generated name from `idx` on and that no two of its subterms
    that differ up to locations share a structural hash. -/
theorem stmtRunCSESinglePass_equiv (body : Statements) (idx : Nat)
    (hfresh : FreshCSENames body idx) (hnc : NoHashCollisions body) :
    (stmtRunCSESinglePass body idx).2 = (stmtRunCSE body idx).2 ∧
      Statements.mapExprs Core.eraseLocs (stmtRunCSESinglePass body idx).1 =
        Statements.mapExprs Core.eraseLocs (stmtRunCSE body idx).1 := by
  have hnc' := U0_of_noHashCollisions body hnc
  rw [stmtRunCSESinglePass_eq]
  by_cases hN : (spNamed body).isEmpty
  · -- Nothing to name: the rounds stop at once.
    have hnil : spNamed body = [] := List.isEmpty_iff.mp hN
    have hNL : NLi body idx = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [NLi_length, hnil]; rfl
    obtain ⟨h1, h2⟩ := stmtRunCSE_E body idx hfresh hnc' (fun r _ => by
      rw [hNL]; intro m f a _ hf; simp at hf)
    rw [ite_eq_left hN]
    have hBR : spByRound body = [] := by
      apply List.eq_nil_of_length_eq_zero
      unfold spByRound spTargets; simp [hnil]
    have hDO : spDeclOrder body idx = [] := by
      unfold spDeclOrder; rw [hBR]; simp
    refine ⟨by rw [h2, hBR]; rfl, ?_⟩
    rw [h1, hDO, hNL]
    simp only [List.map_nil, List.nil_append]
    exact mapExprs_congr body (fun e _ => (rwE_nil (E e)).symm)
  rw [ite_eq_right hN]
  by_cases hmf : markedFunction (spDag body) (spMarked body) = true
  · rw [ite_eq_left hmf]; exact ⟨rfl, rfl⟩
  rw [ite_eq_right hmf]
  obtain ⟨h1, h2⟩ := stmtRunCSE_E body idx hfresh hnc'
    (noFnT_of_markedFunction body idx (by simpa using hmf))
  refine ⟨by rw [h2, spRepl_idx], ?_⟩
  rw [h1]
  exact spOut_E body idx

end

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## Naming can only drop visits

Without the condition that no named class is the function of an application, naming a
class can hide the spine arguments below it from the walk, so visits can only be lost. -/

section NamingSub
variable (TL : List NTarget)

/-- **Visits of a rewritten expression, as a sublist.** The visits of the rewrite of an erased
    expression are among the rewrites of its visits, with the named classes dropped (and so for
    the spine walk). -/
theorem occ_rwE_sub (hel : ∀ t ∈ TL, elig t.1 = true) (hb : ∀ t ∈ TL, LExpr.hasBVar t.1 = false) :
    ∀ (e : Expression.Expr), E e = e →
      (occ (rwE (ρL TL) e)).Sublist ((occ e).filterMap (gT TL)) ∧
      (spOcc (rwE (ρL TL) e)).Sublist ((spOcc e).filterMap (gT TL)) := by
  have hnamed : ∀ e, E e = e → (∃ t ∈ TL, t.1 = e ∧ rwE (ρL TL) e = cseVar t.2.1 t.2.2) →
      occ (rwE (ρL TL) e) = (occ e).filterMap (gT TL) := by
    rintro e he ⟨t, ht, rfl, h2⟩
    rw [h2, occ_eq t.1, ite_eq_left (hel t ht), he]
    simp [cseVar, occ, gT, List.mem_map.mpr ⟨t, ht, rfl⟩]
  have hnamed2 : ∀ e, (∃ t ∈ TL, t.1 = e ∧ rwE (ρL TL) e = cseVar t.2.1 t.2.2) →
      (spOcc (rwE (ρL TL) e)).Sublist ((spOcc e).filterMap (gT TL)) := by
    rintro e ⟨t, -, -, h2⟩
    rw [h2]; simp [cseVar, spOcc]
  have helig : ∀ e, E e = e → e ∉ TL.map (·.1) → elig e = true →
      rwE (ρL TL) e = rwKids (ρL TL) e →
      occ (rwE (ρL TL) e) = (occ e).filterMap (gT TL) := by
    intro e he hm hel' h2
    have hel2 : elig (rwE (ρL TL) e) = true := by rw [h2, elig_rwKids TL hb]; exact hel'
    rw [occ_eq, ite_eq_left hel2, occ_eq e, ite_eq_left hel', he, E_rwE TL e he]
    simp [gT, hm]
  intro e
  induction e with
  | app m f a ihf iha =>
    intro he
    obtain ⟨rfl, hf, ha⟩ := E_eq_self_app he
    have ihf' := (ihf hf).2
    have iha' := (iha ha).1
    rcases rwE_cases TL (.app valueLoc f a) with hn | ⟨hm, h2⟩
    · exact ⟨(hnamed _ he hn) ▸ List.Sublist.refl _, hnamed2 _ hn⟩
    · refine ⟨?_, ?_⟩
      · by_cases hel' : elig (.app valueLoc f a) = true
        · exact (helig _ he hm hel' h2) ▸ List.Sublist.refl _
        · have hel2 : elig (rwE (ρL TL) (.app valueLoc f a)) = false := by
            rw [h2, elig_rwKids TL hb]; simpa using hel'
          rw [occ_eq, ite_eq_right (by simp [hel2]), occ_eq (.app valueLoc f a),
            ite_eq_right hel', h2]
          simp only [rwKids, occK, List.filterMap_append]
          exact ihf'.append iha'
      · rw [h2]; simp only [rwKids, spOcc, List.filterMap_append]; exact ihf'.append iha'
  | ite m c t f ihc iht ihf =>
    intro he
    simp only [E_ite, LExpr.ite.injEq] at he
    obtain ⟨rfl, hc, ht, hf⟩ := he
    have he : E (.ite valueLoc c t f) = .ite valueLoc c t f := by simp [hc, ht, hf]
    have ihc' := (ihc hc).1
    have iht' := (iht ht).1
    have ihf' := (ihf hf).1
    rcases rwE_cases TL (.ite valueLoc c t f) with hn | ⟨hm, h2⟩
    · exact ⟨(hnamed _ he hn) ▸ List.Sublist.refl _, hnamed2 _ hn⟩
    · refine ⟨?_, by rw [h2]; simp [rwKids, spOcc]⟩
      by_cases hel' : elig (.ite valueLoc c t f) = true
      · exact (helig _ he hm hel' h2) ▸ List.Sublist.refl _
      · have hel2 : elig (rwE (ρL TL) (.ite valueLoc c t f)) = false := by
          rw [h2, elig_rwKids TL hb]; simpa using hel'
        rw [occ_eq, ite_eq_right (by simp [hel2]), occ_eq (.ite valueLoc c t f),
          ite_eq_right hel', h2]
        simp only [rwKids, occK, List.filterMap_append]
        exact (ihc'.append iht').append ihf'
  | eq m a b iha ihb =>
    intro he
    simp only [E_eq, LExpr.eq.injEq] at he
    obtain ⟨rfl, ha, hb'⟩ := he
    have he : E (.eq valueLoc a b) = .eq valueLoc a b := by simp [ha, hb']
    have iha' := (iha ha).1
    have ihb' := (ihb hb').1
    rcases rwE_cases TL (.eq valueLoc a b) with hn | ⟨hm, h2⟩
    · exact ⟨(hnamed _ he hn) ▸ List.Sublist.refl _, hnamed2 _ hn⟩
    · refine ⟨?_, by rw [h2]; simp [rwKids, spOcc]⟩
      by_cases hel' : elig (.eq valueLoc a b) = true
      · exact (helig _ he hm hel' h2) ▸ List.Sublist.refl _
      · have hel2 : elig (rwE (ρL TL) (.eq valueLoc a b)) = false := by
          rw [h2, elig_rwKids TL hb]; simpa using hel'
        rw [occ_eq, ite_eq_right (by simp [hel2]), occ_eq (.eq valueLoc a b),
          ite_eq_right hel', h2]
        simp only [rwKids, occK, List.filterMap_append]
        exact iha'.append ihb'
  | const m c => leaf_rw (LExpr.const m c)
  | op m o ty => leaf_rw (LExpr.op m o ty)
  | bvar m i => leaf_rw (LExpr.bvar m i)
  | fvar m x ty => leaf_rw (LExpr.fvar m x ty)
  | abs m n ty b _ => leaf_rw (LExpr.abs m n ty b)
  | quant m k n ty tr b _ _ => leaf_rw (LExpr.quant m k n ty tr b)

/-- The expansion of a rewritten unnamed node, as a sublist of the rewrites of its expansion. -/
theorem occK_rwE_sub (hel : ∀ t ∈ TL, elig t.1 = true) (hb : ∀ t ∈ TL, LExpr.hasBVar t.1 = false)
    (d : Expression.Expr) (hd : E d = d) (hm : d ∉ TL.map (·.1)) :
    (occK (rwE (ρL TL) d)).Sublist ((occK d).filterMap (gT TL)) := by
  rcases rwE_cases TL d with ⟨t, ht, h1, -⟩ | ⟨-, h2⟩
  · exact absurd (List.mem_map.mpr ⟨t, ht, h1⟩) hm
  rw [h2]
  cases d with
  | app m f a =>
    obtain ⟨rfl, hf, ha⟩ := E_eq_self_app hd
    simp only [rwKids, occK, List.filterMap_append]
    exact (occ_rwE_sub TL hel hb f hf).2.append (occ_rwE_sub TL hel hb a ha).1
  | ite m c t f =>
    simp only [E_ite, LExpr.ite.injEq] at hd
    obtain ⟨rfl, hc, ht, hf⟩ := hd
    simp only [rwKids, occK, List.filterMap_append]
    exact ((occ_rwE_sub TL hel hb c hc).1.append (occ_rwE_sub TL hel hb t ht).1).append
      (occ_rwE_sub TL hel hb f hf).1
  | eq m a b =>
    simp only [E_eq, LExpr.eq.injEq] at hd
    obtain ⟨rfl, ha, hb'⟩ := hd
    simp only [rwKids, occK, List.filterMap_append]
    exact (occ_rwE_sub TL hel hb a ha).1.append (occ_rwE_sub TL hel hb b hb').1
  | _ => simp [rwKids, occK]

end NamingSub

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- `flatMap` of pointwise sublists. -/
theorem flatMap_sublist_congr {α β : Type} {f g : α → List β} :
    ∀ (l : List α), (∀ x ∈ l, (f x).Sublist (g x)) → (l.flatMap f).Sublist (l.flatMap g) := by
  intro l
  induction l with
  | nil => intro _; exact List.Sublist.slnil
  | cons x xs ih =>
    intro h
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih (fun y hy => h y (by simp [hy])))

/-- `flatMap` of a sublist. -/
theorem sublist_flatMap {α β : Type} (f : α → List β) {l₁ l₂ : List α} (h : l₁.Sublist l₂) :
    (l₁.flatMap f).Sublist (l₂.flatMap f) := by
  induction h with
  | slnil => exact List.Sublist.slnil
  | cons a _ ih => rw [List.flatMap_cons]; exact ih.trans (List.sublist_append_right _ _)
  | cons_cons a _ ih => rw [List.flatMap_cons, List.flatMap_cons]; exact (List.Sublist.refl _).append ih

/-- Counting in the `flatMap` of a list without duplicates inside another. -/
theorem cnt_flatMap_le_of_subset (f : Expression.Expr → List Expression.Expr)
    {l₁ l₂ : List Expression.Expr} (h1 : l₁.Nodup) (h2 : l₂.Nodup) (hs : ∀ x ∈ l₁, x ∈ l₂)
    (c : Expression.Expr) : cnt c (l₁.flatMap f) ≤ cnt c (l₂.flatMap f) := by
  classical
  have hp : l₁.Perm (l₂.filter (fun x => decide (x ∈ l₁))) :=
    (List.perm_ext_iff_of_nodup h1 (h2.filter _)).mpr fun x => by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => ⟨hs x h, h⟩, fun h => h.2⟩
  rw [perm_cnt_eq (hp.flatMap_right f)]
  exact (sublist_flatMap f List.filter_sublist).countP_le

open Classical in
/-- **Naming can only drop visits.** Name the classes `TL` of a list of erased expressions `F`
    that the walk reaches: distinct, eligible, none a proper subterm of another, with fresh
    distinct indices. The walk of the declarations followed by the rewritten `F` visits each
    class at most as often as the named classes followed by the rewrites of the visits of the
    walk of `F`, named classes dropped. -/
theorem one_step_le (TL : List NTarget) (F R : List Expression.Expr)
    (hR : IsReachList (F.flatMap occ) R)
    (hFE : ∀ r ∈ F, E r = r) (hFfr : ∀ r ∈ F, FreshIn TL r)
    (hTR : ∀ t ∈ TL, t.1 ∈ R) (hcls : (TL.map (·.1)).Nodup) (hidx : (TL.map (·.2.1)).Nodup)
    (hel : ∀ t ∈ TL, elig t.1 = true) (hinc : ∀ t ∈ TL, ∀ t' ∈ TL, ¬ IsPSub t'.1 t.1)
    (R' : List Expression.Expr)
    (hR' : IsReachList ((TL.map (·.1) ++ F.map (rwE (ρL TL))).flatMap occ) R') (x : Expression.Expr) :
    cnt x (visits (TL.map (·.1) ++ F.map (rwE (ρL TL))) R') ≤
      cnt x (TL.map (·.1) ++ (visits F R).filterMap (gT TL)) := by
  classical
  have hb : ∀ t ∈ TL, LExpr.hasBVar t.1 = false := fun t ht => by
    have := hel t ht; revert this; cases t.1 <;> simp [elig]
  have hRsub : ∀ c ∈ R, E c = c ∧ ∃ r ∈ F, IsSub c r := fun c hc => reachList_sub hR hFE hc
  have hRfr : ∀ c ∈ R, FreshIn TL c := fun c hc => by
    obtain ⟨-, r, hr, hs⟩ := hRsub c hc; exact (hFfr r hr).sub TL hs
  have hTE : ∀ t ∈ TL, E t.1 = t.1 := fun t ht => (hRsub _ (hTR t ht)).1
  have hTf : ∀ t ∈ TL, FreshIn TL t.1 := fun t ht => hRfr _ (hTR t ht)
  have hT1 : (TL.map (·.1)).flatMap occ = TL.map (·.1) := by
    have : ∀ (l : List NTarget), (∀ t ∈ l, elig t.1 = true ∧ E t.1 = t.1) →
        (l.map (·.1)).flatMap occ = l.map (·.1) := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons t ts ih =>
        intro h
        simp only [List.map_cons, List.flatMap_cons]
        rw [ih (fun t' ht' => h t' (by simp [ht'])), occ_eq, ite_eq_left (h t (by simp)).1,
          (h t (by simp)).2]; rfl
    exact this TL (fun t ht => ⟨hel t ht, hTE t ht⟩)
  have hF1 : ((F.map (rwE (ρL TL))).flatMap occ).Sublist ((F.flatMap occ).filterMap (gT TL)) := by
    rw [List.flatMap_map, List.filterMap_flatMap]
    exact flatMap_sublist_congr F (fun r hr => (occ_rwE_sub TL hel hb r (hFE r hr)).1)
  have hgT : ∀ y, y ∉ TL.map (·.1) → gT TL y = some (rwE (ρL TL) y) := fun y hy => by
    unfold gT; rw [ite_eq_right hy]
  have hgT' : ∀ y z, gT TL y = some z → y ∉ TL.map (·.1) ∧ z = rwE (ρL TL) y := fun y z h => by
    unfold gT at h
    by_cases hy : y ∈ TL.map (·.1)
    · rw [ite_eq_left hy] at h; cases h
    · rw [ite_eq_right hy] at h; exact ⟨hy, (Option.some.inj h).symm⟩
  obtain ⟨Rf, hRf⟩ : ∃ Rf, Rf = R.filter (fun c => decide (c ∉ TL.map (·.1))) := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = TL.map (·.1) ++ Rf.map (rwE (ρL TL)) := ⟨_, rfl⟩
  -- `L` has no duplicates.
  have hLnd : L.Nodup := by
    rw [hLdef, hRf]
    refine List.nodup_append.mpr ⟨hcls, ?_, ?_⟩
    · refine nodup_map_of_inj_on (hR.1.filter _) ?_
      intro x hx y hy hxy
      have hx' := (List.mem_filter.mp hx).1
      have hy' := (List.mem_filter.mp hy).1
      exact rwE_inj TL hcls hidx hTE hinc (hRsub x hx').1 (hRsub y hy').1 (hRfr x hx')
        (hRfr y hy') hxy
    · intro a ha b hb' hab
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hb'
      exact rwE_not_mem TL hTf y (hab ▸ ha)
  -- Everything the new walk reaches is in `L`.
  have hRL : ∀ c ∈ R', c ∈ L := by
    rw [hLdef, hRf]
    intro c hc
    have hreach := (hR'.mem_iff c).mp hc
    clear hc
    induction hreach with
    | root h =>
      rw [List.flatMap_append, hT1, List.mem_append] at h
      rcases h with h | h
      · exact List.mem_append_left _ h
      · obtain ⟨y, hy, hg⟩ := List.mem_filterMap.mp (hF1.subset h)
        obtain ⟨hyT, rfl⟩ := hgT' y _ hg
        exact List.mem_append_right _ (List.mem_map.mpr ⟨y, List.mem_filter.mpr
          ⟨(hR.2.1 y).mpr (List.mem_append_left _ hy), by simpa using hyT⟩, rfl⟩)
    | @step d c _ hcd ih =>
      rcases List.mem_append.mp ih with hd | hd
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
        obtain ⟨s, hs1, hs2, hs3⟩ := occK_sub _ _ hcd
        have hsE : E s = s := hs1.E_eq (hTE t ht)
        rw [hsE] at hs3
        rw [hs3] at hcd ⊢
        have hsT : s ∉ TL.map (·.1) := fun hm => by
          obtain ⟨t', ht', hts⟩ := List.mem_map.mp hm
          exact hinc t ht t' ht' (hts ▸ ⟨hs1, hs2⟩)
        have hsR : s ∈ R := (hR.2.1 s).mpr (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨t.1, hTR t ht, hcd⟩))
        refine List.mem_append_right _ (List.mem_map.mpr ⟨s, List.mem_filter.mpr
          ⟨hsR, by simpa using hsT⟩, ?_⟩)
        exact rwE_self TL s (fun t' ht' hsub => hinc t ht t' ht'
          ⟨hsub.trans hs1, fun he => hs2 (hs1.antisymm (he ▸ hsub))⟩)
      · obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
        obtain ⟨hd0R, hd0T⟩ := List.mem_filter.mp hd0
        have hd0T' : d0 ∉ TL.map (·.1) := by simpa using hd0T
        obtain ⟨y, hy, hg⟩ := List.mem_filterMap.mp
          ((occK_rwE_sub TL hel hb d0 (hRsub d0 hd0R).1 hd0T').subset hcd)
        obtain ⟨hyT, rfl⟩ := hgT' y _ hg
        exact List.mem_append_right _ (List.mem_map.mpr ⟨y, List.mem_filter.mpr
          ⟨(hR.2.1 y).mpr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨d0, hd0R, hy⟩)),
            by simpa using hyT⟩, rfl⟩)
  -- The expansions.
  have hK1 : (TL.map (·.1)).flatMap occK = ((TL.map (·.1)).flatMap occK).filterMap (gT TL) := by
    symm
    apply filterMap_eq_self
    intro c hc
    obtain ⟨t', htm, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp htm
    obtain ⟨s, hs1, hs2, rfl⟩ := occK_sub _ _ hc
    have hsE : E s = s := hs1.E_eq (hTE t ht)
    rw [hsE]
    have hnT : s ∉ TL.map (·.1) := fun hm => by
      obtain ⟨t', ht', hts⟩ := List.mem_map.mp hm
      exact hinc t ht t' ht' (hts ▸ ⟨hs1, hs2⟩)
    unfold gT
    rw [ite_eq_right hnT, rwE_self TL s (fun t' ht' hsub => hinc t ht t' ht'
      ⟨hsub.trans hs1, fun he => hs2 (hs1.antisymm (he ▸ hsub))⟩)]
  have hK2 : ((Rf.map (rwE (ρL TL))).flatMap occK).Sublist
      (Rf.flatMap (fun d => (occK d).filterMap (gT TL))) := by
    rw [List.flatMap_map]
    apply flatMap_sublist_congr
    intro d hd
    rw [hRf] at hd
    obtain ⟨hdR, hdT⟩ := List.mem_filter.mp hd
    exact occK_rwE_sub TL hel hb d (hRsub d hdR).1 (by simpa using hdT)
  have hRsplit : R.Perm (TL.map (·.1) ++ Rf) := by
    rw [hRf]
    have h1 := (List.filter_append_perm (fun c => decide (c ∈ TL.map (·.1))) R).symm
    simp only [decide_not] at h1 ⊢
    refine h1.trans (List.Perm.append_right _ ?_)
    · refine (List.perm_ext_iff_of_nodup (hR.1.filter _) hcls).mpr fun c => ?_
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro h; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h; exact ⟨hTR t ht, h⟩
  have hRK : cnt x ((R.flatMap occK).filterMap (gT TL)) =
      cnt x (((TL.map (·.1)).flatMap occK).filterMap (gT TL)) +
        cnt x (Rf.flatMap (fun d => (occK d).filterMap (gT TL))) := by
    rw [← cnt_append, List.filterMap_flatMap, List.filterMap_flatMap, ← List.flatMap_append]
    exact perm_cnt_eq (hRsplit.flatMap_right _) x
  -- Counting.
  have hA : cnt x ((F.map (rwE (ρL TL))).flatMap occ) ≤ cnt x ((F.flatMap occ).filterMap (gT TL)) :=
    hF1.countP_le
  have hB := cnt_flatMap_le_of_subset occK hR'.1 hLnd hRL x
  have hC : cnt x ((Rf.map (rwE (ρL TL))).flatMap occK) ≤
      cnt x (Rf.flatMap (fun d => (occK d).filterMap (gT TL))) := hK2.countP_le
  have hL : cnt x (L.flatMap occK) = cnt x ((TL.map (·.1)).flatMap occK) +
      cnt x ((Rf.map (rwE (ρL TL))).flatMap occK) := by
    rw [hLdef, List.flatMap_append, cnt_append]
  have key : cnt x (R'.flatMap occK) ≤ cnt x ((R.flatMap occK).filterMap (gT TL)) := by
    rw [hRK, ← hK1]
    exact Nat.le_trans hB (hL ▸ Nat.add_le_add_left hC _)
  unfold visits
  rw [List.flatMap_append, hT1, List.filterMap_append, cnt_append, cnt_append, cnt_append,
    cnt_append]
  rw [Nat.add_assoc]
  exact Nat.add_le_add_left (Nat.add_le_add hA key) _

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-! ## The rounds of `stmtRunCSE` in general

The rounds are followed without the condition that no named class is the function of an
application. Counts of visits can then only drop from round to round, which is enough to see
that a round never names a node containing an earlier generated name. -/

/-- The children of a node with rewritten children. -/
theorem childList_rwKids (ρ : Expression.Expr → Option Expression.Expr) (e : Expression.Expr) :
    childList (rwKids ρ e) = (childList e).map (rwE ρ) := by
  cases e <;> simp [rwKids, childList]

/-- A node with rewritten children that mentions no generated name of `M` is unchanged, and
    no named class is strictly inside it. -/
theorem rwKids_fresh (M : List NTarget) (s : Expression.Expr) (h : FreshIn M (rwKids (ρL M) s)) :
    (∀ m ∈ M, ¬ IsPSub m.1 s) ∧ rwKids (ρL M) s = s := by
  have hk : ∀ j (hj : j < (childList s).length), NoneIn M (childList s)[j] := by
    intro j hj m hm hsub
    obtain ⟨m', hm', hv⟩ := vars_rwE_of_sub M _ m hm hsub
    exact h m' hm' (vars_rwKids_child _ s j hj _ hv)
  have hps : ∀ m ∈ M, ¬ IsPSub m.1 s := by
    intro m hm hps
    obtain ⟨j, hj, hsub⟩ := hps.1.child_of_ne hps.2
    rw [getElem!_pos (childList s) j hj] at hsub
    exact hk j hj m hm hsub
  refine ⟨hps, ?_⟩
  rw [rwKids_congr (ρ₂ := fun _ => none) _ (fun c hc => ?_), rwKids_none]
  apply ρL_eq_none
  intro hcm
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hcm
  exact hps m hm hc

/-- An eligible subterm of a rewrite that mentions no generated name is a subterm of the
    original, not named and with nothing named inside. -/
theorem sub_rwE_fresh (M : List NTarget) (e c : Expression.Expr) (hs : IsSub c (rwE (ρL M) e))
    (hf : FreshIn M c) (hel : elig c = true) :
    IsSub c e ∧ c ∉ M.map (·.1) ∧ NoneIn M c := by
  rcases sub_rwE M e c hs with ⟨t, -, rfl⟩ | ⟨s', hse, hsM, rfl⟩
  · simp [cseVar, elig] at hel
  obtain ⟨hps, heq⟩ := rwKids_fresh M s' hf
  rw [heq] at hf hel ⊢
  refine ⟨hse, hsM, fun m hm hsub => ?_⟩
  by_cases he : m.1 = s'
  · exact hsM (he ▸ List.mem_map.mpr ⟨m, hm, rfl⟩)
  · exact hps m hm ⟨hsub, he⟩

/-- An eligible subterm of a node with rewritten children that mentions no generated name: the
    node itself, unchanged, or a subterm of a child as in `sub_rwE_fresh`. -/
theorem sub_rwKids_fresh (M : List NTarget) (d c : Expression.Expr) (hs : IsSub c (rwKids (ρL M) d))
    (hf : FreshIn M c) (hel : elig c = true) :
    (c = d ∧ ∀ m ∈ M, ¬ IsPSub m.1 d) ∨ (IsPSub c d ∧ c ∉ M.map (·.1) ∧ NoneIn M c) := by
  by_cases hc : c = rwKids (ρL M) d
  · subst hc
    obtain ⟨hps, heq⟩ := rwKids_fresh M d hf
    exact Or.inl ⟨heq, hps⟩
  · right
    obtain ⟨j, hj, hsub⟩ := hs.child_of_ne hc
    rw [getElem!_pos (childList (rwKids (ρL M) d)) j hj] at hsub
    simp only [childList_rwKids, List.getElem_map] at hsub
    rw [childList_rwKids, List.length_map] at hj
    obtain ⟨h1, h2, h3⟩ := sub_rwE_fresh M _ c hsub hf hel
    refine ⟨⟨h1.trans (childList_spec d j hj).1, fun he => ?_⟩, h2, h3⟩
    have := (childList_spec d j hj).2
    have := (he ▸ h1).size_le
    omega

/-- Dropping named classes and rewriting does not add occurrences of a class that mentions no
    generated name of `TL`. -/
theorem cnt_filterMap_gT_le (TL : List NTarget) (c : Expression.Expr) (hcf : FreshIn TL c) :
    ∀ (l : List Expression.Expr), cnt c (l.filterMap (gT TL)) ≤ cnt c l := by
  intro l
  induction l with
  | nil => exact Nat.le_refl _
  | cons y ys ih =>
    rw [List.filterMap_cons]
    cases hg : gT TL y with
    | none => rw [cnt_cons]; simp only; omega
    | some z =>
      simp only
      rw [cnt_cons, cnt_cons]
      have hz : z = rwE (ρL TL) y := by
        unfold gT at hg
        by_cases hy : y ∈ TL.map (·.1)
        · rw [ite_eq_left hy] at hg; cases hg
        · rw [ite_eq_right hy] at hg; exact (Option.some.inj hg).symm
      by_cases hzc : z = c
      · have hn : NoneIn TL y := by
          intro t ht hsub
          obtain ⟨t', ht', hv⟩ := vars_rwE_of_sub TL y t ht hsub
          rw [← hz, hzc] at hv
          exact hcf t' ht' hv
        have hyc : y = c := by rw [← rwE_self TL y hn, ← hz, hzc]
        rw [ite_eq_left hzc, ite_eq_left hyc]; omega
      · rw [ite_eq_right hzc]; split <;> omega

/-- An occurrence after dropping named classes and rewriting has a preimage counted as often. -/
theorem cnt_filterMap_gT_pre (TL : List NTarget) (hcls : (TL.map (·.1)).Nodup)
    (hidx : (TL.map (·.2.1)).Nodup) (hTE : ∀ t ∈ TL, E t.1 = t.1)
    (hinc : ∀ t ∈ TL, ∀ t' ∈ TL, ¬ IsPSub t'.1 t.1) (c : Expression.Expr)
    (l : List Expression.Expr) (hl : ∀ y ∈ l, E y = y ∧ FreshIn TL y)
    (h : 0 < cnt c (l.filterMap (gT TL))) :
    ∃ y ∈ l, y ∉ TL.map (·.1) ∧ c = rwE (ρL TL) y ∧ cnt c (l.filterMap (gT TL)) = cnt y l := by
  obtain ⟨y, hy, hg⟩ := List.mem_filterMap.mp (cnt_pos.mp h)
  have hyT : y ∉ TL.map (·.1) ∧ c = rwE (ρL TL) y := by
    unfold gT at hg
    by_cases hyt : y ∈ TL.map (·.1)
    · rw [ite_eq_left hyt] at hg; cases hg
    · rw [ite_eq_right hyt] at hg; exact ⟨hyt, (Option.some.inj hg).symm⟩
  refine ⟨y, hy, hyT.1, hyT.2, ?_⟩
  rw [hyT.2]
  exact cnt_filterMap_gT TL hcls hidx hTE hinc (hl y hy).1 (hl y hy).2 hyT.1 l hl

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- A named node of the rounds: index, class, type and round. -/
abbrev NE := Nat × Expression.Expr × LMonoTy × Nat

/-- A named node as a named class. -/
def toM (t : NE) : NTarget := (t.2.1, t.1, t.2.2.1)

section General
variable (body0 : Statements) (idx0 : Nat)

/-- The round forest after naming `N` (declared in the order `D`): the declarations'
    right-hand sides, then the input's expressions rewritten. -/
def Fg (N D : List NE) : List Expression.Expr :=
  D.map (fun t => rwKids (ρL (N.map toM)) t.2.1) ++ (F0 body0).map (rwE (ρL (N.map toM)))

/-- `c` mentions no generated name from `idx0` on. -/
def Fresh0 (c : Expression.Expr) : Prop := ∀ k, idx0 ≤ k → cseName k ∉ vars c

/-- The state of `stmtRunCSE` before round `r`, having named `N` (in naming order) and declared
    them in the order `D`. -/
structure GInv (r : Nat) (cur : Statements) (idx : Nat) (N D : List NE) : Prop where
  stmts : Statements.mapExprs E cur = D.map (fun t => declE (N.map toM) (toM t)) ++
    Statements.mapExprs (fun e => rwE (ρL (N.map toM)) (E e)) body0
  idx : idx = idx0 + N.length
  nums : N.map (·.1) = List.range' idx0 N.length
  cls : (N.map (·.2.1)).Nodup
  facts : ∀ t ∈ N, E t.2.1 = t.2.1 ∧ elig t.2.1 = true ∧
    LExpr.typeCheck [] t.2.1 = some t.2.2.1 ∧
    (∃ r ∈ Statements.collectExprs body0, ∃ s, IsSub s r ∧ t.2.1 = E s) ∧ t.2.2.2 < r
  lvl : ∀ t ∈ N, ∀ t' ∈ N, IsPSub t'.2.1 t.2.1 → t.2.2.2 < t'.2.2.2
  perm : D.Perm N
  sorted : D.Pairwise (fun a b => b.2.2.2 ≤ a.2.2.2)
  dupF : ∀ R, IsReachList ((Fg body0 N D).flatMap occ) R →
    ∀ c, 2 ≤ cnt c (visits (Fg body0 N D) R) → Fresh0 idx0 c
  once : ∀ R, IsReachList ((Fg body0 N D).flatMap occ) R →
    ∀ t ∈ N, cnt t.2.1 (visits (Fg body0 N D) R) ≤ 1

/-- The named classes of `N`. -/
theorem toM_cls (N : List NE) : (N.map toM).map (·.1) = N.map (·.2.1) := by
  simp [toM, List.map_map]

/-- The indices of `N`. -/
theorem toM_idx (N : List NE) : (N.map toM).map (·.2.1) = N.map (·.1) := by
  simp [toM, List.map_map]

/-- The expressions of a state. -/
theorem collectExprs_of_GInv {r : Nat} {cur : Statements} {idx : Nat} {N D : List NE}
    (h : GInv body0 idx0 r cur idx N D) :
    (Statements.collectExprs cur).map E = Fg body0 N D := by
  have := congrArg Statements.collectExprs h.stmts
  have h2 : ∀ A B : Statements, Statements.collectExprs (A ++ B) =
      Statements.collectExprs A ++ Statements.collectExprs B := fun A B => by
    rw [collectExprs_eq, collectExprs_eq, collectExprs_eq, bExprs_append]
  rw [collectExprs_mapExprs, h2, collectExprs_mapExprs] at this
  rw [this, Fg, F0, List.map_map]
  congr 1
  rw [collectExprs_eq]
  exact bExprs_inits _ _ _ _

/-- The forest before round 1 is the input's. -/
theorem Fg_nil : Fg body0 [] [] = F0 body0 := by
  unfold Fg
  simp only [List.map_nil, List.nil_append]
  conv => rhs; rw [← List.map_id (F0 body0)]
  exact List.map_congr_left (fun e _ => rwE_nil e)

/-- A class of the input's subterms mentions no generated name from `idx0` on. -/
theorem Fresh0_of_orig (hfresh : FreshCSENames body0 idx0) {c : Expression.Expr}
    (hc : ∃ r ∈ Statements.collectExprs body0, ∃ s, IsSub s r ∧ c = E s) : Fresh0 idx0 c := by
  obtain ⟨r, hr, s, hs, rfl⟩ := hc
  intro k hk hv
  rw [vars_E] at hv
  exact hfresh k hk (List.mem_flatMap.mpr ⟨r, hr, hs.vars_subset _ hv⟩)

/-- The state before round 1 is the input. -/
theorem GInv_one (hfresh : FreshCSENames body0 idx0) : GInv body0 idx0 1 body0 idx0 [] [] := by
  refine ⟨?_, rfl, rfl, List.nodup_nil, fun t ht => by simp at ht, fun t ht => by simp at ht,
    List.Perm.refl _, List.Pairwise.nil, ?_, fun _ _ t ht => by simp at ht⟩
  · simp only [List.map_nil, List.nil_append]
    exact mapExprs_congr body0 (fun e _ => (rwE_nil (E e)).symm)
  · intro R hR c hc
    rw [Fg_nil] at hR hc
    have hR0 : IsReachList ((Statements.collectExprs body0).flatMap occ) R := by
      unfold F0 at hR; rw [flatMap_occ_map_E] at hR; exact hR
    exact Fresh0_of_orig body0 idx0 hfresh
      (L0_sub body0 R hR0 (cnt_pos.mp (by omega))).2

end General

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- The visits of a walk are erased subterms of the walked expressions. -/
theorem visits_sub {F R : List Expression.Expr} (hR : IsReachList (F.flatMap occ) R)
    (hFE : ∀ r ∈ F, E r = r) {c : Expression.Expr} (hc : c ∈ visits F R) :
    E c = c ∧ ∃ x ∈ F, IsSub c x := by
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨r, hr, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨s, hs, rfl⟩ := (occ_sub r).1 c hc
    have hsE := hs.E_eq (hFE r hr)
    refine ⟨E_E s, r, hr, ?_⟩
    rw [hsE]; exact hs
  · obtain ⟨d, hd, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨-, r, hr, hdr⟩ := reachList_sub hR hFE hd
    obtain ⟨s, hs, -, rfl⟩ := occK_sub d c hc
    have hsE := (hs.trans hdr).E_eq (hFE r hr)
    refine ⟨E_E s, r, hr, ?_⟩
    rw [hsE]; exact hs.trans hdr

section General2
variable (body0 : Statements) (idx0 : Nat) (hfresh : FreshCSENames body0 idx0)

/-- The classes of a state: indices from `idx0`. -/
theorem GInv.idx_ge {r : Nat} {cur : Statements} {idx : Nat} {N D : List NE}
    (h : GInv body0 idx0 r cur idx N D) : ∀ m ∈ N.map toM, idx0 ≤ m.2.1 := by
  intro m hm
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  have : t.1 ∈ N.map (·.1) := List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [h.nums, List.mem_range'] at this
  simp only [toM]; omega

/-- The forest of a state is erased. -/
theorem GInv.Fg_E {r : Nat} {cur : Statements} {idx : Nat} {N D : List NE}
    (h : GInv body0 idx0 r cur idx N D) : ∀ x ∈ Fg body0 N D, E x = x := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact E_rwKids _ _ (h.facts t (h.perm.mem_iff.mp ht)).1
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e', -, rfl⟩ := List.mem_map.mp he
    exact E_rwE _ _ (E_E e')

include hfresh in
/-- The generated names in the forest of a state are names of `N`. -/
theorem GInv.Fg_names {r : Nat} {cur : Statements} {idx : Nat} {N D : List NE}
    (h : GInv body0 idx0 r cur idx N D) : ∀ x ∈ Fg body0 N D, ∀ k, idx0 ≤ k →
      cseName k ∈ vars x → k ∈ N.map (·.1) := by
  intro x hx k hk hv
  have hM : (∃ t ∈ N.map toM, cseName k = cseName t.2.1) → k ∈ N.map (·.1) := by
    rintro ⟨t, ht, he⟩
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    rw [cseName_inj he]; exact List.mem_map.mpr ⟨t', ht', rfl⟩
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    rcases vars_rwKids _ _ _ hv with hv | ⟨t', ht', he, -⟩
    · obtain ⟨-, -, -, hsub, -⟩ := h.facts t (h.perm.mem_iff.mp ht)
      exact absurd hv (Fresh0_of_orig body0 idx0 hfresh hsub k hk)
    · exact hM ⟨t', ht', he⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    rcases vars_rwE _ _ _ hv with hv | ⟨t', ht', he', -⟩
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      exact absurd hv (Fresh0_of_orig body0 idx0 hfresh ⟨e', he', e', .refl _, rfl⟩ k hk)
    · exact hM ⟨t', ht', he'⟩

/-- An eligible subterm of the forest that mentions no generated name: a class of the input's
    subterms, and either named or with nothing named inside. -/
theorem GInv.Fg_sub {r : Nat} {cur : Statements} {idx : Nat} {N D : List NE}
    (h : GInv body0 idx0 r cur idx N D) {x c : Expression.Expr} (hx : x ∈ Fg body0 N D)
    (hs : IsSub c x) (hf : Fresh0 idx0 c) (hel : elig c = true) :
    (∃ r ∈ Statements.collectExprs body0, ∃ s, IsSub s r ∧ c = E s) ∧
      (c ∈ N.map (·.2.1) ∨ (c ∉ N.map (·.2.1) ∧ NoneIn (N.map toM) c)) := by
  have hfM : FreshIn (N.map toM) c := fun m hm => hf _ (GInv.idx_ge body0 idx0 h m hm)
  have hcls := toM_cls N
  have horig : ∀ e : Expression.Expr, (∃ r ∈ Statements.collectExprs body0, ∃ s, IsSub s r ∧ e = E s) →
      IsSub c e → ∃ r ∈ Statements.collectExprs body0, ∃ s, IsSub s r ∧ c = E s := by
    rintro e ⟨r', hr', s, hs', rfl⟩ hce
    obtain ⟨s', hs'', hse⟩ := hce.transport (E_E s)
    exact ⟨r', hr', s', hs''.trans hs', by rw [← hse, hce.E_eq (E_E s)]⟩
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    have htN := h.perm.mem_iff.mp ht
    obtain ⟨-, -, -, hsub, -⟩ := h.facts t htN
    rcases sub_rwKids_fresh _ _ c hs hfM hel with ⟨rfl, -⟩ | ⟨hps, hcM, hnone⟩
    · exact ⟨hsub, Or.inl (List.mem_map.mpr ⟨t, htN, rfl⟩)⟩
    · refine ⟨horig _ hsub hps.1, Or.inr ⟨by rw [← hcls]; exact hcM, hnone⟩⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    obtain ⟨h1, h2, h3⟩ := sub_rwE_fresh _ _ c hs hfM hel
    exact ⟨horig _ ⟨e', he', e', .refl _, rfl⟩ h1, Or.inr ⟨by rw [← hcls]; exact h2, h3⟩⟩

end General2

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section General3
variable (body0 : Statements) (idx0 : Nat)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)

/-- The visits of the walk of a state's statements are those of its forest. -/
theorem GInv.visits_eq {r : Nat} {cur : Statements} {idx : Nat} {N D : List NE}
    (h : GInv body0 idx0 r cur idx N D) (R : List Expression.Expr)
    (hR : IsReachList ((Fg body0 N D).flatMap occ) R) (c : Expression.Expr) :
    dupC ((Statements.collectExprs cur).foldl (fun st e => (collectSubexprs st e).2) {}) c ↔
      2 ≤ cnt c (visits (Fg body0 N D) R) := by
  obtain ⟨Rw, hRw, -, hd⟩ := walk_forest (Statements.collectExprs cur)
  have hF := collectExprs_of_GInv body0 idx0 h
  have hRw' : IsReachList ((Fg body0 N D).flatMap occ) Rw := by
    rw [← hF, flatMap_occ_map_E]; exact hRw
  rw [hd]
  unfold visits
  rw [← hF, flatMap_occ_map_E]
  rw [perm_cnt_eq (((hRw'.perm hR).flatMap_right occK).append_left _) c]

include hnc in
/-- **The targets of a round** are visited twice, type, are hashed by their hash, are eligible,
    are no proper subterm of a class visited twice, and are distinct classes. -/
theorem GInv.targets {r : Nat} {cur : Statements} {idx : Nat} {N D : List NE}
    (h : GInv body0 idx0 r cur idx N D) (R : List Expression.Expr)
    (hR : IsReachList ((Fg body0 N D).flatMap occ) R) :
    (∀ p ∈ itTargets cur, 2 ≤ cnt (E p.2.1) (visits (Fg body0 N D) R) ∧
      LExpr.typeCheck [] p.2.1 = some p.2.2 ∧ hx p.2.1 = p.1 ∧ elig (E p.2.1) = true ∧
      ∀ v, 2 ≤ cnt v (visits (Fg body0 N D) R) → ¬ IsPSub (E p.2.1) v) ∧
    ((itTargets cur).map (fun p => E p.2.1)).Nodup := by
  have hdupc := GInv.visits_eq body0 idx0 h R hR
  have hF := collectExprs_of_GInv body0 idx0 h
  obtain ⟨hspec1, hspec2⟩ := collectDups_spec (Statements.collectExprs cur)
  generalize hdl : collectExprsToAbbreviate.collectDups (Statements.collectExprs cur) = dl at *
  have hcls : ∀ p ∈ dl.1, 2 ≤ cnt (E p.2) (visits (Fg body0 N D) R) := by
    intro p hp
    rw [← hdupc, ← collectDups_classes, hdl]
    exact ⟨p, hp, rfl⟩
  have hU : ∀ p ∈ dl.1, U0 body0 p.2 ∧ hx p.2 = p.1 := by
    intro p hp
    obtain ⟨h1, h2, r', hr', c, hc, hce⟩ := hspec1 p hp
    have hx' : E r' ∈ Fg body0 N D := by rw [← hF]; exact List.mem_map.mpr ⟨r', hr', rfl⟩
    have hsub : IsSub (E p.2) (E r') := by rw [hce]; exact hc.erase
    have hel : elig (E p.2) = true := by rw [elig_E]; exact (eligible_iff_elig _).mp h2
    obtain ⟨⟨r'', hr'', s, hs, hse⟩, -⟩ :=
      GInv.Fg_sub body0 idx0 h hx' hsub (h.dupF R hR _ (hcls p hp)) hel
    exact ⟨⟨r'', hr'', s, hs, by rw [hse]⟩, h1⟩
  rw [itTargets_eq, collectExprsToAbbreviate_eq, hdl,
    removeSubsumed_eq (U0 body0) hnc (fun a b hb h => U0_sub hb h) dl.2 dl.1 hU]
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.mp hp
    simp only [Option.map_eq_some_iff] at hqp
    obtain ⟨ty, hty, rfl⟩ := hqp
    obtain ⟨hqd, hk⟩ := List.mem_filter.mp hq
    simp only [decide_eq_true_eq] at hk
    obtain ⟨hU1, hU2⟩ := hU q hqd
    refine ⟨hcls q hqd, hty, hU2, ?_, fun v hv hps => ?_⟩
    · rw [elig_E]; exact (eligible_iff_elig _).mp (hspec1 q hqd).2.1
    · have : dupC ((Statements.collectExprs cur).foldl (fun st e => (collectSubexprs st e).2) {}) v :=
        (hdupc v).mpr hv
      rw [← collectDups_classes, hdl] at this
      obtain ⟨q', hq', rfl⟩ := this
      obtain ⟨c, hc, hce⟩ := hps.1.transport (E_E q'.2)
      exact hk ⟨q', hq', c, hc, fun he => hps.2 (by rw [← E_E q.2, hce, he]),
        by rw [← hce, E_E]⟩
  · rw [List.Nodup, List.pairwise_map, List.pairwise_filterMap]
    refine (hspec2.filter _).imp fun {a b} hab => ?_
    intro x hx' y hy
    simp only [Option.map_eq_some_iff] at hx' hy
    obtain ⟨_, -, rfl⟩ := hx'; obtain ⟨_, -, rfl⟩ := hy
    exact hab

end General3

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- The forest after a round: the round's named classes, then the previous forest rewritten. -/
theorem Fg_next (body0 : Statements) (N D TN : List NE)
    (hTel : ∀ t ∈ TN.map toM, elig t.1 = true)
    (hTM : ∀ t ∈ TN.map toM, NoneIn (N.map toM) t.1)
    (hTfM : ∀ t ∈ TN.map toM, FreshIn (N.map toM) t.1)
    (hinc : ∀ t ∈ TN.map toM, ∀ t' ∈ TN.map toM, ¬ IsPSub t'.1 t.1)
    (hdisj : ∀ d ∈ D, d.2.1 ∉ (TN.map toM).map (·.1)) :
    Fg body0 (N ++ TN) (TN ++ D) =
      (TN.map toM).map (·.1) ++ (Fg body0 N D).map (rwE (ρL (TN.map toM))) := by
  unfold Fg
  rw [List.map_append (f := toM)]
  simp only [List.map_append, List.append_assoc, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro t ht
    have htT : toM t ∈ TN.map toM := List.mem_map.mpr ⟨t, ht, rfl⟩
    exact rwKids_self_of (hTM _ htT) (hinc _ htT)
  · congr 1
    · apply List.map_congr_left
      intro d hd
      exact (rwKids_comp _ _ hTel hTM hTfM d.2.1 (hdisj d hd)).symm
    · apply List.map_congr_left
      intro e _
      exact (rwE_comp _ _ hTel hTM hTfM e).symm

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section General4
variable (body0 : Statements) (idx0 : Nat) (hfresh : FreshCSENames body0 idx0)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)

include hfresh hnc in
/-- **One round of `stmtRunCSE`, in general.** A state with targets steps to a state that has
    also named the targets. -/
theorem GInv.step {r : Nat} {cur : Statements} {idx : Nat} {N D : List NE}
    (h : GInv body0 idx0 r cur idx N D) :
    ∃ TN : List NE, GInv body0 idx0 (r + 1) ((itFold cur idx).1.reverseAux (itBody cur idx))
      (itFold cur idx).2.2 (N ++ TN) (TN ++ D) := by
  classical
  -- A walk of the forest.
  have hF := collectExprs_of_GInv body0 idx0 h
  obtain ⟨R, hR, -⟩ := walk_forest (Statements.collectExprs cur)
  rw [← flatMap_occ_map_E, hF] at hR
  obtain ⟨hTg, hTnd⟩ := GInv.targets body0 idx0 hnc h R hR
  obtain ⟨hF1, hF2, hF3⟩ := itFold_eq cur idx
  generalize hIT : itTargets cur = IT at hTg hTnd hF1 hF2 hF3
  let Z := (List.range' idx IT.length).zip IT
  let TN : List NE := Z.map (fun q => (q.1, E q.2.2.1, q.2.2.2, r))
  refine ⟨TN, ?_⟩
  let M := N.map toM
  let T := TN.map toM
  have hTZ : T = Z.map (fun q => (E q.2.2.1, q.1, q.2.2.2)) := by
    simp only [T, TN, List.map_map]; rfl
  have hZmem : ∀ q ∈ Z, q.2 ∈ IT := fun q hq => List.of_mem_zip hq |>.2
  have hZidx : ∀ q ∈ Z, idx ≤ q.1 := fun q hq => by
    have := (List.of_mem_zip hq).1; rw [List.mem_range'] at this; omega
  have hTmem : ∀ t ∈ T, ∃ q ∈ Z, t = (E q.2.2.1, q.1, q.2.2.2) := fun t ht => by
    rw [hTZ] at ht; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht; exact ⟨q, hq, rfl⟩
  -- Facts on the round's classes.
  have hT2 : ∀ t ∈ T, 2 ≤ cnt t.1 (visits (Fg body0 N D) R) := fun t ht => by
    obtain ⟨q, hq, rfl⟩ := hTmem t ht; exact (hTg q.2 (hZmem q hq)).1
  have hTel : ∀ t ∈ T, elig t.1 = true := fun t ht => by
    obtain ⟨q, hq, rfl⟩ := hTmem t ht; exact (hTg q.2 (hZmem q hq)).2.2.2.1
  have hTE : ∀ t ∈ T, E t.1 = t.1 := fun t ht => by
    obtain ⟨q, hq, rfl⟩ := hTmem t ht; exact E_E _
  have hT0 : ∀ t ∈ T, Fresh0 idx0 t.1 := fun t ht => h.dupF R hR _ (hT2 t ht)
  have hTmax : ∀ t ∈ T, ∀ v, 2 ≤ cnt v (visits (Fg body0 N D) R) → ¬ IsPSub t.1 v := fun t ht => by
    obtain ⟨q, hq, rfl⟩ := hTmem t ht; exact (hTg q.2 (hZmem q hq)).2.2.2.2
  have hinc : ∀ t ∈ T, ∀ t' ∈ T, ¬ IsPSub t'.1 t.1 := fun t ht t' ht' =>
    hTmax t' ht' t.1 (hT2 t ht)
  have hTcls : (T.map (·.1)).Nodup := by
    rw [hTZ, List.map_map]
    have : Z.map ((·.1) ∘ fun q : Nat × UInt64 × Expression.Expr × LMonoTy =>
        (E q.2.2.1, q.1, q.2.2.2)) = (Z.map (·.2)).map (fun p => E p.2.1) := by
      simp [List.map_map]
    rw [this, List.map_snd_zip (by simp)]; exact hTnd
  have hTidx : (T.map (·.2.1)).Nodup := by
    rw [hTZ, List.map_map]
    have : Z.map ((·.2.1) ∘ fun q : Nat × UInt64 × Expression.Expr × LMonoTy =>
        (E q.2.2.1, q.1, q.2.2.2)) = Z.map (·.1) := by simp []
    rw [this, List.map_fst_zip (by simp)]; exact List.nodup_range'
  have hNidx : ∀ t ∈ N, t.1 < idx := fun t ht => by
    have : t.1 ∈ N.map (·.1) := List.mem_map.mpr ⟨t, ht, rfl⟩
    rw [h.nums, List.mem_range'] at this; rw [h.idx]; omega
  have hdisjN : ∀ t ∈ N, t.2.1 ∉ T.map (·.1) := fun t ht hm => by
    obtain ⟨u, hu, hue⟩ := List.mem_map.mp hm
    have h1 := h.once R hR t ht
    have h2 := hT2 u hu
    rw [hue] at h2; omega
  have hdisjD : ∀ d ∈ D, d.2.1 ∉ T.map (·.1) := fun d hd => hdisjN d (h.perm.mem_iff.mp hd)
  have hTvis : ∀ t ∈ T, t.1 ∈ visits (Fg body0 N D) R := fun t ht => cnt_pos.mp (by
    have := hT2 t ht; omega)
  have hTsub : ∀ t ∈ T, (∃ r ∈ Statements.collectExprs body0, ∃ s, IsSub s r ∧ t.1 = E s) ∧
      NoneIn M t.1 := fun t ht => by
    obtain ⟨-, x, hx, hs⟩ := visits_sub hR (GInv.Fg_E body0 idx0 h) (hTvis t ht)
    obtain ⟨h1, h2⟩ := GInv.Fg_sub body0 idx0 h hx hs (hT0 t ht) (hTel t ht)
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | ⟨-, h2⟩
    · obtain ⟨u, hu, hue⟩ := List.mem_map.mp h2
      exact absurd (hue ▸ List.mem_map.mpr ⟨t, ht, rfl⟩) (hdisjN u hu)
    · exact h2
  have hTM : ∀ t ∈ T, NoneIn M t.1 := fun t ht => (hTsub t ht).2
  have hTfM : ∀ t ∈ T, FreshIn M t.1 := fun t ht m hm =>
    hT0 t ht _ (GInv.idx_ge body0 idx0 h m hm)
  have hTfT : ∀ t ∈ T, FreshIn T t.1 := fun t ht u hu => by
    obtain ⟨q, hq, rfl⟩ := hTmem u hu
    exact hT0 t ht _ (show idx0 ≤ q.1 by have := hZidx q hq; rw [h.idx] at this; omega)
  -- The forest mentions no name of `T`.
  have hFfr : ∀ x ∈ Fg body0 N D, FreshIn T x := by
    intro x hx u hu hv
    obtain ⟨q, hq, rfl⟩ := hTmem u hu
    have hq1 := hZidx q hq
    have := GInv.Fg_names body0 idx0 hfresh h x hx q.1 (by rw [h.idx] at hq1; omega) hv
    obtain ⟨t, ht, hte⟩ := List.mem_map.mp this
    have := hNidx t ht; omega
  -- The replacement of the round.
  let P : List (Nat × Target) :=
    (List.range' idx IT.length).zip (IT.map fun t => (t.1, t.2.1, t.2.2, 0))
  have hPget : ∀ j (hj : j < P.length), P[j] = (idx + j, ((IT[j]'(by simp [P] at hj; omega)).1,
      (IT[j]'(by simp [P] at hj; omega)).2.1, (IT[j]'(by simp [P] at hj; omega)).2.2, 0)) := by
    intro j hj; simp [P, List.getElem_zip, List.getElem_range']
  have hPlen : P.length = IT.length := by simp [P]
  have hPmap : P.map (fun q => (E q.2.2.1, q.1, q.2.2.2.1)) = T := by
    rw [hTZ]
    simp only [P, Z, List.zip_map_right, List.map_map]
    rfl
  have hρ : ∀ c, E c = c → ρOf (itFold cur idx).2.1 c = ρL T c := by
    intro c hc
    rw [← hPmap]
    refine ρOf_eq_ρL _ P (fun h' p => ?_) (fun q hq => ?_) ?_ c hc
    · rw [hF3]
      constructor
      · rintro ⟨j, hj, h1, rfl⟩
        refine ⟨P[j]'(by omega), List.getElem_mem _, ?_, ?_⟩ <;> rw [hPget j (by omega)]
        · exact h1
      · rintro ⟨q, hq, h1, rfl⟩
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
        rw [hPget j hj] at h1 ⊢
        exact ⟨j, by omega, h1, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
      rw [hPget j hj]
      exact (hTg _ (List.getElem_mem _)).2.2.1
    · rw [hPmap]; exact hTcls
  -- The new forest.
  have hFn : Fg body0 (N ++ TN) (TN ++ D) = T.map (·.1) ++ (Fg body0 N D).map (rwE (ρL T)) :=
    Fg_next body0 N D TN hTel hTM hTfM hinc hdisjD
  have hstep := fun R' (hR' : IsReachList ((Fg body0 (N ++ TN) (TN ++ D)).flatMap occ) R') x =>
    one_step_le T (Fg body0 N D) R hR (GInv.Fg_E body0 idx0 h) hFfr
      (fun t ht => (hR.2.1 _).mpr (hTvis t ht)) hTcls hTidx hTel hinc R' (hFn ▸ hR') x
  have hM' : (N ++ TN).map toM = M ++ T := List.map_append
  have hTNlen : TN.length = IT.length := by simp [TN, Z]
  have hTNcls : TN.map (·.2.1) = T.map (·.1) := by simp only [T, List.map_map]; rfl
  have hTNmem : ∀ t ∈ TN, ∃ q ∈ Z, t = (q.1, E q.2.2.1, q.2.2.2, r) := fun t ht => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht; exact ⟨q, hq, rfl⟩
  have hTNT : ∀ t ∈ TN, toM t ∈ T := fun t ht => List.mem_map.mpr ⟨t, ht, rfl⟩
  have hTNlv : ∀ t ∈ TN, t.2.2.2 = r := fun t ht => by
    obtain ⟨q, -, rfl⟩ := hTNmem t ht; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The statements.
    rw [List.reverseAux_eq, mapExprs_append, itBody_E, hF1]
    rw [mapExprs_congr (g := fun e => rwE (ρL T) (E e)) cur
      (fun e _ => rwE_congr_E hρ (E e) (E_E e))]
    rw [show (fun e => rwE (ρL T) (E e)) = rwE (ρL T) ∘ E from rfl, ← mapExprs_comp, h.stmts,
      mapExprs_append, mapExprs_comp,
      show D.map (fun t => declE (N.map toM) (toM t)) = (D.map toM).map (declE (N.map toM)) by
        rw [List.map_map]; rfl, mapExprs_declE, hM', List.map_append, List.append_assoc]
    congr 1
    · refine (mapExprs_inits E Z (fun q => ⟨s!"{cseVarPrefix}{q.1}", ()⟩)
        (fun q => LTy.forAll [] q.2.2.2) (fun q => q.2.2.1)).trans ?_
      simp only [TN, List.map_map]
      apply List.map_congr_left
      intro q hq
      have hqT : (E q.2.2.1, q.1, q.2.2.2) ∈ T := by
        rw [hTZ]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
      simp only [Function.comp, declE, toM]
      rw [rwKids_self_of (hTM _ hqT) (hinc _ hqT)]
    · congr 1
      · rw [List.map_map]
        apply List.map_congr_left
        intro d hd
        simp only [Function.comp, declE]
        rw [rwKids_comp _ _ hTel hTM hTfM (toM d).1 (hdisjD d hd)]
      · congr 1
        funext e
        exact rwE_comp _ _ hTel hTM hTfM (E e)
  · -- The next index.
    rw [hF2, h.idx, List.length_append, hTNlen]; omega
  · -- The indices.
    have h1 : TN.map (·.1) = List.range' idx IT.length := by
      simp only [TN, List.map_map]
      exact List.map_fst_zip (by simp)
    rw [List.map_append, h.nums, h1, List.length_append, hTNlen, h.idx, List.range'_append_1]
  · -- Distinct classes.
    rw [List.map_append, hTNcls]
    refine List.nodup_append.mpr ⟨h.cls, hTcls, ?_⟩
    intro a ha b hb hab
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    exact hdisjN t ht (hab ▸ hb)
  · -- The facts.
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨h1, h2, h3, h4, h5⟩ := h.facts t ht
      exact ⟨h1, h2, h3, h4, by omega⟩
    · obtain ⟨q, hq, rfl⟩ := hTNmem t ht
      have hqT : (E q.2.2.1, q.1, q.2.2.2) ∈ T := by rw [hTZ]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
      refine ⟨E_E _, hTel _ hqT, ?_, (hTsub _ hqT).1, by simp⟩
      rw [typeCheck_E]; exact (hTg q.2 (hZmem q hq)).2.1
  · -- Levels.
    intro t ht t' ht' hps
    rcases List.mem_append.mp ht with ht | ht <;> rcases List.mem_append.mp ht' with ht' | ht'
    · exact h.lvl t ht t' ht' hps
    · rw [hTNlv t' ht']; exact (h.facts t ht).2.2.2.2
    · exact absurd hps.1 (hTM (toM t) (hTNT t ht) (toM t') (List.mem_map.mpr ⟨t', ht', rfl⟩))
    · exact absurd hps (hinc (toM t) (hTNT t ht) (toM t') (hTNT t' ht'))
  · -- The declaration order is a permutation.
    exact (h.perm.append_left TN).trans List.perm_append_comm
  · -- Sorted.
    rw [List.pairwise_append]
    refine ⟨?_, h.sorted, ?_⟩
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj _
      rw [hTNlv _ (List.getElem_mem hi), hTNlv _ (List.getElem_mem hj)]
      exact Nat.le_refl _
    · intro a ha b hb
      rw [hTNlv a ha]
      exact Nat.le_of_lt (h.facts b (h.perm.mem_iff.mp hb)).2.2.2.2
  · -- Classes visited twice mention no generated name.
    intro R' hR' c hc
    have hle := hstep R' hR' c
    rw [hFn] at hc
    have hcT : c ∉ T.map (·.1) := by
      intro hm
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
      rw [cnt_append, cnt_nodup_mem hTcls hm, cnt_T_filterMap_gT T hTfT hu] at hle
      omega
    rw [cnt_append, cnt_eq_zero.mpr hcT, Nat.zero_add] at hle
    have hvl : ∀ y ∈ visits (Fg body0 N D) R, E y = y ∧ FreshIn T y := fun y hy => by
      obtain ⟨hyE, x, hx, hs⟩ := visits_sub hR (GInv.Fg_E body0 idx0 h) hy
      exact ⟨hyE, (hFfr x hx).sub T hs⟩
    obtain ⟨y, -, hyT, rfl, hcy⟩ := cnt_filterMap_gT_pre T hTcls hTidx hTE hinc c _ hvl
      (by omega)
    have hy2 : 2 ≤ cnt y (visits (Fg body0 N D) R) := by omega
    have hy0 := h.dupF R hR y hy2
    intro k hk hv
    rcases vars_rwE T y _ hv with hv | ⟨u, hu, hue, hsub⟩
    · exact hy0 k hk hv
    · exact hTmax u hu y hy2 ⟨hsub, fun he => hyT (he ▸ List.mem_map.mpr ⟨u, hu, rfl⟩)⟩
  · -- Named classes are visited at most once.
    intro R' hR' t ht
    have hle := hstep R' hR' t.2.1
    rw [hFn]
    rcases List.mem_append.mp ht with ht | ht
    · rw [cnt_append, cnt_eq_zero.mpr (hdisjN t ht), Nat.zero_add] at hle
      have hfT : FreshIn T t.2.1 := fun u hu => by
        obtain ⟨q, hq, rfl⟩ := hTmem u hu
        exact Fresh0_of_orig body0 idx0 hfresh (h.facts t ht).2.2.2.1 _
          (show idx0 ≤ q.1 by have := hZidx q hq; rw [h.idx] at this; omega)
      have := cnt_filterMap_gT_le T t.2.1 hfT (visits (Fg body0 N D) R)
      have := h.once R hR t ht
      omega
    · have hm : t.2.1 ∈ T.map (·.1) := by rw [← hTNcls]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
      rw [cnt_append, cnt_nodup_mem hTcls hm,
        show t.2.1 = (toM t).1 from rfl, cnt_T_filterMap_gT T hTfT (hTNT t ht)] at hle
      exact hle

end General4

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

/-- A statement whose mapped form is an `init` is an `init`. -/
theorem stmt_mapExprs_eq_init {f : Expression.Expr → Expression.Expr} {s : Statement}
    {n : Expression.Ident} {ty : Expression.Ty} {v : Expression.Expr} {md : MetaData Expression}
    (h : Statement.mapExprs f s = Statement.init n ty (.det v) md) :
    ∃ e, s = Statement.init n ty (.det e) md ∧ f e = v := by
  cases s with
  | cmd c =>
    cases c with
    | cmd c' =>
      cases c' with
      | init n' ty' e md' =>
        cases e with
        | det e =>
          simp only [Statement.mapExprs, Stmt.mapExpr, Command.mapExpr, Stmt.cmd.injEq,
            CmdExt.cmd.injEq, Cmd.init.injEq, ExprOrNondet.det.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨e, rfl, rfl⟩
        | nondet => simp [Statement.mapExprs, Stmt.mapExpr, Command.mapExpr] at h
      | set n' e md' => cases e <;> simp [Statement.mapExprs, Stmt.mapExpr, Command.mapExpr] at h
      | _ => simp [Statement.mapExprs, Stmt.mapExpr, Command.mapExpr] at h
    | call => simp [Statement.mapExprs, Stmt.mapExpr, Command.mapExpr] at h
  | block => simp [Statement.mapExprs, Stmt.mapExpr] at h
  | ite c => cases c <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | loop g => cases g <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | exit => simp [Statement.mapExprs, Stmt.mapExpr] at h
  | typeDecl => simp [Statement.mapExprs, Stmt.mapExpr] at h

/-- Statements whose mapped form starts with `init`s start with `init`s. -/
theorem mapExprs_split {α : Type} (f : Expression.Expr → Expression.Expr) (name : α → CoreIdent)
    (ty : α → Expression.Ty) (rh : α → Expression.Expr) :
    ∀ (D : List α) (out X : Statements),
      Statements.mapExprs f out =
        D.map (fun t => Statement.init (name t) (ty t) (.det (rh t)) .empty) ++ X →
      ∃ xs : List Expression.Expr, ∃ rest : Statements, xs.length = D.length ∧
        out = (D.zip xs).map (fun p => Statement.init (name p.1) (ty p.1) (.det p.2) .empty) ++ rest ∧
        (∀ i (hi : i < xs.length) (hi' : i < D.length), f xs[i] = rh D[i]) ∧
        Statements.mapExprs f rest = X := by
  intro D
  induction D with
  | nil => intro out X h; exact ⟨[], out, rfl, by simp, fun i hi => absurd hi (by simp), by simpa using h⟩
  | cons t ts ih =>
    intro out X h
    cases out with
    | nil => simp [Statements.mapExprs] at h
    | cons s out' =>
      have h' : Statement.mapExprs f s :: Statements.mapExprs f out' =
          Statement.init (name t) (ty t) (.det (rh t)) .empty ::
            (ts.map (fun t => Statement.init (name t) (ty t) (.det (rh t)) .empty) ++ X) := h
      simp only [List.cons.injEq] at h'
      obtain ⟨e, rfl, he⟩ := stmt_mapExprs_eq_init h'.1
      obtain ⟨xs, rest, hlen, h1, h2, h3⟩ := ih out' X h'.2
      refine ⟨e :: xs, rest, by simp [hlen], by simp [h1], fun i hi hi' => ?_, h3⟩
      cases i with
      | zero => exact he
      | succ i => exact h2 i (by simpa using hi) (by simpa using hi')

end Core.CSE

namespace Core.CSE

open Lambda Imperative Strata.PtrCache

section General5
variable (body0 : Statements) (idx0 : Nat) (hfresh : FreshCSENames body0 idx0)
  (hnc : ∀ a b, U0 body0 a → U0 body0 b → hx a = hx b → E a = E b)

include hfresh hnc in
/-- **The loop of `stmtRunCSE`, in general**: every round keeps the invariant. -/
theorem GInv.go : ∀ (f r : Nat) (cur : Statements) (idx : Nat) (N D : List NE),
    GInv body0 idx0 r cur idx N D →
    ∃ r' N' D', GInv body0 idx0 r' (stmtRunCSE.go f cur idx).1 (stmtRunCSE.go f cur idx).2 N' D' := by
  intro f
  induction f with
  | zero => intro r cur idx N D h; exact ⟨r, N, D, h⟩
  | succ f ih =>
    intro r cur idx N D h
    simp only [stmtRunCSE.go]
    rw [stmtRunCSEIter_eq]
    by_cases he : (itTargets cur).isEmpty = true
    · rw [ite_eq_left he]
      exact ⟨r, N, D, h⟩
    · rw [ite_eq_right he]
      obtain ⟨TN, h'⟩ := GInv.step body0 idx0 hfresh hnc h
      exact ih _ _ _ _ _ h'

include hfresh hnc in
/-- **`stmtRunCSE` is well formed.** -/
theorem stmtRunCSE_wf_U0 :
    CSEWellFormed body0 idx0 (stmtRunCSE body0 idx0).1 (stmtRunCSE body0 idx0).2 := by
  rw [stmtRunCSE_eq_go]
  obtain ⟨r, N, D, h⟩ := GInv.go body0 idx0 hfresh hnc _ 1 body0 idx0 [] [] (GInv_one body0 idx0 hfresh)
  generalize stmtRunCSE.go (fuel (Statements.collectExprs body0)) body0 idx0 = out at h
  obtain ⟨xs, rest, hlen, hout, hrhs, hrest⟩ := mapExprs_split E
    (fun t : NE => ⟨s!"{cseVarPrefix}{t.1}", ()⟩) (fun t => LTy.forAll [] t.2.2.1)
    (fun t => rwKids (ρL (N.map toM)) t.2.1) D out.1 _ h.stmts
  have hNE : ∀ t ∈ N, E t.2.1 = t.2.1 := fun t ht => (h.facts t ht).1
  have hNM : (N.map fun t => (E t.2.1, t.1, t.2.2.1)) = N.map toM :=
    List.map_congr_left (fun t ht => by simp only [toM, hNE t ht])
  let Z := D.zip xs
  have hZ1 : Z.map (·.1) = D := List.map_fst_zip (by omega)
  have key := wf_of_named body0 rest idx0 N Z h.nums
    (by rw [show (N.map fun t => E t.2.1) = N.map (·.2.1) from
      List.map_congr_left (fun t ht => hNE t ht)]; exact h.cls)
    (fun t ht => by
      obtain ⟨-, hel, hty, -⟩ := h.facts t ht
      refine ⟨hty, ?_⟩
      revert hel; cases t.2.1 <;> simp [elig])
    (fun t ht => by
      obtain ⟨-, -, -, ⟨r', hr', s', hs', he⟩, -⟩ := h.facts t ht
      exact ⟨r', hr', s', hs', by rw [he, E_E]⟩)
    (fun t ht t' ht' hps => by rw [hNE t ht, hNE t' ht'] at hps; exact h.lvl t ht t' ht' hps)
    (by rw [hZ1]; exact h.perm)
    (by
      have := h.sorted
      rw [← hZ1, List.pairwise_map] at this
      exact this)
    (fun z hz => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
      have hiD : i < D.length := by simp [Z] at hi; omega
      simp only [Z, List.getElem_zip]
      rw [hrhs i (by omega) hiD, hNM, hNE _ (h.perm.mem_iff.mp (List.getElem_mem hiD))])
    (by rw [hrest, hNM]) hfresh
  rw [hout, h.idx]
  have : (Z.map fun z => (z.1.1, z.1.2.2.1, z.2)).map (fun d =>
      Statement.init ⟨s!"{cseVarPrefix}{d.1}", ()⟩ (LTy.forAll [] d.2.1) (.det d.2.2) .empty) =
      Z.map (fun p => Statement.init ⟨s!"{cseVarPrefix}{p.1.1}", ()⟩ (LTy.forAll [] p.1.2.2.1)
        (.det p.2) .empty) := by
    rw [List.map_map]; rfl
  rw [this] at key
  exact key

end General5

end Core.CSE

namespace Core.CSE

open Lambda Imperative

public section

/-- **`stmtRunCSE` is well formed**: its output is declarations of fresh, consecutive indices,
    each typed and mentioning only earlier declarations and the input's variables, followed by
    a body that gives the input back, up to locations, once the declarations are inlined. It
    assumes that the input mentions no generated name from `idx` on and has no hash collisions
    among its subterms. -/
theorem stmtRunCSE_wellFormed (body : Statements) (idx : Nat) (hfresh : FreshCSENames body idx)
    (hnc : NoHashCollisions body) :
    CSEWellFormed body idx (stmtRunCSE body idx).1 (stmtRunCSE body idx).2 :=
  stmtRunCSE_wf_U0 body idx hfresh (U0_of_noHashCollisions body hnc)

/-- **The single pass is well formed** (see `CSEWellFormed`), under the same assumptions as
    `stmtRunCSE_wellFormed`. -/
theorem stmtRunCSESinglePass_wellFormed (body : Statements) (idx : Nat)
    (hfresh : FreshCSENames body idx) (hnc : NoHashCollisions body) :
    CSEWellFormed body idx (stmtRunCSESinglePass body idx).1 (stmtRunCSESinglePass body idx).2 := by
  rcases stmtRunCSESinglePass_wellFormed_or_fallback body idx hfresh with h | h
  · exact h
  · rw [h]; exact stmtRunCSE_wellFormed body idx hfresh hnc

end

end Core.CSE
