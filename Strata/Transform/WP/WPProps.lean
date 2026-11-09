/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WP
import Strata.Util.ExceptProps
import Strata.Transform.Passive.ProgramProps
import Strata.DL.Imperative.StmtProps
import Strata.Util.RopeProps
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm

/-! # Properties of the WP phase

The output of `wpBody` is a guarded program in which only obligations follow an `assert`
(`wpBody_shape`), and every arm of every `ite` of the output of `wpEntry`, at any depth, contains
an `assert` or a `cover` (`wpEntry_armsHaveObl`).

The `ite`s of the output come from the nesting of the flat items (`nest`): a side branch is the
`then` arm of an `ite` whose `else` arm is the nesting of the rest of the list, and a real branch
is an `ite` of the nestings of its arms.  The proof of `wpEntry_armsHaveObl` shows that every run
of obligations of the walk's output is nonempty, that every real branch has a run of obligations
or a real branch in each arm, and that a walk result carrying an obligation has a run of
obligations or a real branch in its output (`ROK`).  It proves the facts about the walk along the
computations of the WP monad: `Post m Q` says that every successful run of `m` returns a value
with `Q`, and the tactic `post_step` decomposes such a goal along the binds, conditionals, matches
and join points of a `do` block.

Key theorems: `wpBody_shape`, `wpEntry_armsHaveObl`. -/

namespace Imperative
namespace WP

open BigStep Strata.Util

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P] [iW : WPLang P]

/-! ## Shape of the output -/

/-- Is the statement an `init`, `set` or `assume` command? -/
private def plainG : PStmt P → Bool
  | .cmd (.cmd (.init _ _ _ _)) | .cmd (.cmd (.set _ _ _)) | .cmd (.cmd (.assume _ _ _)) => true
  | _ => false

mutual
/-- Are the items of a flat translation built from `init`, `set` and `assume` commands
    (`plainG`) and runs of obligations, at any depth? -/
private def itemsG : List (Item P) → Bool
  | [] => true
  | it :: rest => itemG it && itemsG rest
/-- Is the item built from `init`, `set` and `assume` commands (`plainG`) and runs of
    obligations, at any depth? -/
private def itemG : Item P → Bool
  | .plain s => plainG s
  | .obls _ cs => cs.all Stmt.isCheck
  | .branch t e => itemsG t && itemsG e
end

omit iB iLB iId iLI iHa in
/-- The nesting of items built from `init`, `set` and `assume` commands and runs of
    obligations is a guarded program with only obligations after each `assert`. -/
private theorem nest_shape : ∀ (l : List (Item P)), itemsG l = true →
    Block.treeForm (nest l) = true ∧ Block.onlyChecksAfterAssert (nest l) = true
  | [], _ => by simp [nest, Block.treeForm, Block.onlyChecksAfterAssert]
  | .plain s :: rest, h => by
    have ih := nest_shape rest (by simp_all [itemsG])
    rcases s with ((_ | _ | _ | _ | _) | _) | _ | _ | _ | _ | _ | _ <;>
      grind [itemsG, itemG, plainG, nest, nestCons, Block.treeForm, Block.onlyChecksAfterAssert]
  | .obls r cs :: rest, h => by
    have ih := nest_shape rest (by simp_all [itemsG])
    have hcs : cs.all Stmt.isCheck = true := by simp_all [itemsG, itemG]
    rcases r with _ | (_ | _ | _ | _) <;> grind [nest, nestCons, reachPre, Block.treeForm,
      Block.onlyChecksAfterAssert, Block.onlyChecksAfterAssert_of_all_isCheck hcs,
      Block.treeForm_of_all_isCheck hcs]
  | .branch t e :: rest, h => by
    have ht := nest_shape t (by simp_all [itemsG, itemG])
    have he := nest_shape e (by simp_all [itemsG, itemG])
    grind [nest, nestCons, Block.treeForm, Block.onlyChecksAfterAssert]

omit iLI in
/-- The output of the WP phase is a guarded program in which only obligations follow each
    `assert` in its list. -/
theorem wpBody_shape {st : FreshSt P} {ss : PStmts P} {w : WOut P} (h : wpBody st ss = .ok w) :
    Block.treeForm w.lay = true ∧ Block.onlyChecksAfterAssert w.lay = true := by
  have hres (tys tyOf) (l : List (WItem P)) : ∀ items, resolveItems tys tyOf l = .ok items →
      itemsG items = true := by
    induction l using resolveItems.induct tys tyOf
      (motive_2 := fun it => ∀ a, resolveItem tys tyOf it = .ok a → itemG a = true) <;> intros <;>
      simp only [resolveItems, resolveItem, Except.bind_is_ok, Except.pure_is_ok] at * <;>
      grind [itemsG, itemG, plainG, mkInit, → mapM_except_mem_right,
        Stmt.isCheck, Except.bind_is_ok, Except.pure_is_ok]
  have hm (l : List (Item P)) (h : itemsG l = true) : itemsG (mergeObls l) = true := by
    fun_induction mergeObls l <;> simp_all [itemsG, itemG]
  simp only [wpBody, emit, StateT.run, Except.bind_is_ok, Except.pure_is_ok] at h
  obtain ⟨⟨r, st1⟩, -, lay, ⟨items, hr, rfl⟩, rfl⟩ := h
  exact nest_shape _ (hm _ (hres _ _ _ _ hr))

end -- public section

/-! ## Obligations in every arm of the output -/

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iHS : HasSubstFvar P] [iHI : HasIdent P]
  [iHa : Hashable P.Ident] [iHV : HasFvars P] [iW : WPOps P]

/-! ## Flat items -/

mutual
/-- Does every item of the list have its side branch's obligations and the arms of its real
    branch as `itemArmsOK` requires, at any depth? -/
private def itemsArmsOK : List (Item P) → Bool
  | [] => true
  | it :: rest => itemArmsOK it && itemsArmsOK rest
/-- Is the item a statement whose `ite` arms contain obligations, a run of obligations that
    contains one, or a real branch whose two arms each leave the main path and whose items are
    `itemsArmsOK`? -/
private def itemArmsOK : Item P → Bool
  | .plain s => Stmt.armsHaveChecks s
  | .obls _ cs => Block.hasCheck cs && Block.armsHaveChecks cs
  | .branch t e => t.any Item.isBranching && e.any Item.isBranching && itemsArmsOK t &&
    itemsArmsOK e
end

omit iDE iBE iLB iHS iHI iHa iHV in
/-- The nesting of `itemsArmsOK` items has obligations in every `ite` arm, and an obligation when
    an item leaves the main path. -/
private theorem nest_arms : ∀ (l : List (Item P)), itemsArmsOK l = true →
    Block.armsHaveChecks (nest l) = true ∧
      (l.any Item.isBranching = true → Block.hasCheck (nest l) = true)
  | [], _ => by simp [nest, Block.armsHaveChecks]
  | .plain s :: rest, h => by
    have ih := nest_arms rest (by simp_all [itemsArmsOK])
    simp only [itemsArmsOK, itemArmsOK, Bool.and_eq_true] at h
    simp only [nest, nestCons]
    split <;> simp_all [Block.armsHaveChecks, Block.hasCheck, Item.isBranching]
  | .obls r cs :: rest, h => by
    have ih := nest_arms rest (by simp_all [itemsArmsOK])
    simp only [itemsArmsOK, itemArmsOK, Bool.and_eq_true] at h
    have hr : Block.armsHaveChecks (reachPre (P := P) r) = true := by
      rcases r with _ | (_ | _ | _ | _) <;> rfl
    simp only [nest, nestCons]
    split <;> simp_all [Block.armsHaveChecks, Stmt.armsHaveChecks, Block.hasCheck, Stmt.hasCheck,
      Block.armsHaveChecks_append, Block.hasCheck_append]
  | .branch t e :: rest, h => by
    simp only [itemsArmsOK, itemArmsOK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨ht, he⟩, hat⟩, hae⟩, -⟩ := h
    obtain ⟨at', ht'⟩ := nest_arms t hat
    obtain ⟨ae', he'⟩ := nest_arms e hae
    have nt := ht' ht
    have ne := he' he
    simp only [nest, nestCons]
    split
    · simp_all [Block.hasCheck]
    · simp_all [Block.hasCheck]
    · simp_all [Block.armsHaveChecks, Stmt.armsHaveChecks, Block.hasCheck, Stmt.hasCheck]
  termination_by l => sizeOf l

omit iBE iLB iHB iHF iHS iHI iHa iHV iW in
/-- Merging adjacent obligation runs keeps `itemsArmsOK` and which items leave the main path. -/
private theorem mergeObls_arms (l : List (Item P)) (h : itemsArmsOK l = true) :
    itemsArmsOK (mergeObls l) = true ∧
      (mergeObls l).any Item.isBranching = l.any Item.isBranching := by
  fun_induction mergeObls l <;> (try cases ‹Item P›) <;> simp_all [itemsArmsOK, itemArmsOK,
    Item.isBranching, Block.armsHaveChecks_append, Block.hasCheck_append]

/-! ## Items before resolution -/

mutual
/-- Is every item of the list `wItemArmsOK`? -/
private def wItemsArmsOK : List (WItem P) → Bool
  | [] => true
  | it :: rest => wItemArmsOK it && wItemsArmsOK rest
/-- Is the item a straight-line item, a nonempty run of obligations, or a real branch whose two
    arms each leave the main path and whose items are `wItemsArmsOK`? -/
private def wItemArmsOK : WItem P → Bool
  | .obls _ cs => !cs.isEmpty
  | .branch t e => t.any WItem.isBranching && e.any WItem.isBranching && wItemsArmsOK t &&
    wItemsArmsOK e
  | _ => true
end

omit iDE iBE iLB iHB iHF iHS iHI iHa iHV iW in
/-- The items of a concatenation are `wItemsArmsOK` when those of both parts are. -/
private theorem wItemsArmsOK_append (a b : List (WItem P)) :
    wItemsArmsOK (a ++ b) = (wItemsArmsOK a && wItemsArmsOK b) := by
  induction a <;> simp_all [wItemsArmsOK, Bool.and_assoc]

omit iDE iBE iLB iHB iHF iHS iHI iHa iHV iW in
/-- `wItemsArmsOK` holds of a list when `wItemArmsOK` holds of each item. -/
private theorem wItemsArmsOK_eq_all :
    ∀ l : List (WItem P), wItemsArmsOK l = l.all wItemArmsOK
  | [] => rfl
  | _ :: l => by simp [wItemsArmsOK, wItemsArmsOK_eq_all l]

omit iDE iBE iLB iHB iHF iHS iHI iHa iHV iW in
/-- Items none of which leaves the main path are `wItemsArmsOK`. -/
private theorem wItemsArmsOK_noBr :
    ∀ {l : List (WItem P)}, l.any WItem.isBranching = false → wItemsArmsOK l = true :=
  fun {l} => by induction l <;> (try cases ‹WItem P›) <;> simp_all [wItemsArmsOK, wItemArmsOK,
    WItem.isBranching]

omit iDE iLB iHS iHI iHV in
/-- Resolved obligations contain an obligation exactly when there are some, and contain no
    `ite`. -/
private theorem resolveObls_arms {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident} :
    ∀ (cs : List (Bool × String × WExpr P × MetaData P)) (cs' : PStmts P),
      cs.mapM (fun (isCover, l, e, md) => do
        let e ← resolveE T Y e
        pure (if isCover then (.cmd (.cmd (.cover l e md)) : PStmt P)
          else .cmd (.cmd (.assert l e md)))) = .ok cs' →
      Block.hasCheck cs' = !cs.isEmpty ∧ Block.armsHaveChecks cs' = true
  | [], _, rfl => by simp [Block.hasCheck, Block.armsHaveChecks]
  | (b, l, e, md) :: cs, cs', h => by
    simp only [List.mapM_cons, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨c, ⟨e', he, rfl⟩, cs'', hcs, rfl⟩ := h
    have ih := resolveObls_arms cs cs'' hcs
    cases b <;> simp_all [Block.hasCheck, Stmt.hasCheck, Block.armsHaveChecks, Stmt.armsHaveChecks]

omit iDE iLB iHS iHI iHV in
/-- Resolution of `wItemsArmsOK` items gives `itemsArmsOK` items, and keeps which items leave the
    main path. -/
private theorem resolveItems_arms {T : Std.HashMap P.Ident P.Ty}
    {Y : Std.HashMap P.Ident P.Ident} :
    ∀ (l : List (WItem P)) (items : List (Item P)), resolveItems T Y l = .ok items →
      wItemsArmsOK l = true →
      itemsArmsOK items = true ∧ items.any Item.isBranching = l.any WItem.isBranching
  | [], _, rfl, _ => ⟨rfl, rfl⟩
  | it :: rest, items, h, hok => by
    simp only [resolveItems, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨a, ha, r, hr, rfl⟩ := h
    simp only [wItemsArmsOK, Bool.and_eq_true] at hok
    obtain ⟨hbr, ih⟩ := resolveItems_arms rest r hr hok.2
    rcases hit : it with ⟨x, _ | ty, _ | e⟩ | ⟨x, _ | e⟩ | ⟨l, e, md⟩ | ⟨rc, cs⟩ | ⟨t, e⟩ <;>
      simp only [resolveItem, resolveOE, Except.bind_is_ok, Except.pure_is_ok, hit,
        exists_eq_left'] at ha
    rotate_right
    · obtain ⟨t', ht, e', he, rfl⟩ := ha
      simp only [hit, wItemArmsOK, Bool.and_eq_true] at hok
      obtain ⟨⟨⟨⟨hbt, hbe⟩, hot⟩, hoe⟩, -⟩ := hok
      obtain ⟨h1, h2⟩ := resolveItems_arms t t' ht hot
      obtain ⟨h3, h4⟩ := resolveItems_arms e e' he hoe
      simp_all [itemsArmsOK, itemArmsOK, Item.isBranching, WItem.isBranching]
    case obls =>
      obtain ⟨cs', hcs, rfl⟩ := ha
      simp only [hit, wItemArmsOK] at hok
      have hc := resolveObls_arms cs cs' hcs
      simp_all [itemsArmsOK, itemArmsOK, Item.isBranching, WItem.isBranching]
    all_goals grind [itemsArmsOK, itemArmsOK, Item.isBranching, WItem.isBranching, mkInit,
      Stmt.armsHaveChecks]
  termination_by l => sizeOf l
  decreasing_by all_goals subst_vars; simp_wf; omega

omit iLB iHS iHI iHV in
/-- The guarded program emitted from `wItemsArmsOK` items has obligations in every `ite` arm. -/
private theorem emit_arms {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}
    {s : Rope (WItem P)} {lay : PStmts P} (h : emit T Y s = .ok lay)
    (hok : wItemsArmsOK s.toList = true) : Block.armsHaveChecks lay = true := by
  obtain ⟨items, hi, ⟨⟩⟩ := (Except.bind_is_ok _ _ _).1 h
  exact (nest_arms _ (mergeObls_arms _ (resolveItems_arms _ _ hi hok).1).1).1

/-! ## Successful runs of the WP monad -/

/-- Every successful run of `m` returns a value with the property `Q`. -/
private structure Post {α : Type} (m : WM P α) (Q : α → Prop) : Prop where
  run : ∀ st a st', m.run st = .ok (a, st') → Q a

omit iW in
/-- Every successful run of a computation returns some value. -/
private theorem Post.any {α : Type} (m : WM P α) : Post m fun _ => True := ⟨fun _ _ _ _ => trivial⟩

omit iW in
/-- A run of `x >>= f` returns a value with `Q` when `x` returns values with `Q₁` and `f` maps
    each such value to a computation returning values with `Q`. -/
private theorem Post.bind {α β : Type} {x : WM P α} {f : α → WM P β} {Q₁ : α → Prop}
    {Q : β → Prop} (hx : Post x Q₁) (hf : ∀ a, Q₁ a → Post (f a) Q) : Post (x >>= f) Q := by
  refine ⟨fun st b st' h => ?_⟩
  rw [StateT.run_bind] at h
  cases hr : x.run st with
  | error e => rw [hr] at h; cases h
  | ok p => rw [hr] at h; exact (hf p.1 (hx.run st p.1 p.2 hr)).run _ _ _ h

omit iW in
/-- A run of `pure a` returns `a`. -/
private theorem Post.pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) :
    Post (Pure.pure a : WM P α) Q := ⟨fun _ _ _ hr => (Prod.mk.inj (Except.ok.inj hr)).1 ▸ h⟩

omit iW in
/-- A failing computation has no successful run. -/
private theorem Post.throw {α : Type} {e : String} {Q : α → Prop} :
    Post (MonadExcept.throw e : WM P α) Q := ⟨fun _ _ _ h => nomatch h⟩

omit iW in
/-- A computation using a join point `v` returns values with `Q` when every call of `v` does
    and the computation does for every join point whose calls do. -/
private theorem Post.jp {α γ : Type} {Q : γ → Prop} {v : α → WM P γ} {b : (α → WM P γ) → WM P γ}
    (hv : ∀ x, Post (v x) Q) (hb : ∀ jp : α → WM P γ, (∀ x, Post (jp x) Q) → Post (b jp) Q) :
    Post (b v) Q := hb v hv

omit iW in
/-- A run of `pure a >>= f` is a run of `f a`. -/
private theorem Post.pure_bind {α β : Type} {a : α} {f : α → WM P β} {Q : β → Prop}
    (h : Post (f a) Q) : Post (Pure.pure a >>= f) Q := by rw [LawfulMonad.pure_bind]; exact h

omit iW in
/-- A run of `(x >>= g) >>= f` is a run of `x >>= fun a => g a >>= f`. -/
private theorem Post.bind_assoc {α β γ : Type} {x : WM P α} {g : α → WM P β} {f : β → WM P γ}
    {Q : γ → Prop} (h : Post (x >>= fun a => g a >>= f) Q) : Post ((x >>= g) >>= f) Q := by
  rw [LawfulMonad.bind_assoc]; exact h

omit iW in
/-- A `for` loop returns a value with `I` when it starts from one and every step keeps `I`. -/
private theorem Post.forIn {β : Type} {I : β → Prop} {f : P.Ident → β → WM P (ForInStep β)}
    (hf : ∀ y b, I b → Post (f y b) fun r => I r.value) :
    ∀ (l : List P.Ident) (b : β), I b → Post (forIn l b f) I
  | [], _, hb => (List.forIn_nil (m := WM P)).symm ▸ Post.pure hb
  | y :: l, b, hb => (List.forIn_cons f y l b).symm ▸ Post.bind (hf y b hb) fun
    | .done _, hc => Post.pure hc
    | .yield c, hc => Post.forIn hf l c hc

omit iW in
/-- A run of a conditional is a run of the branch the condition selects. -/
private theorem Post.ite {α : Type} {c : Prop} [Decidable c] {x y : WM P α} {Q : α → Prop}
    (hx : c → Post x Q) (hy : ¬c → Post y Q) : Post (if c then x else y) Q := by
  by_cases h : c <;> simp [h, hx, hy]

omit iW in
/-- A run of a conditional followed by `f` is a run of the selected branch followed by `f`. -/
private theorem Post.ite_bind {α β : Type} {c : Prop} [Decidable c] {x y : WM P α}
    {f : α → WM P β} {Q : β → Prop} (hx : c → Post (x >>= f) Q) (hy : ¬c → Post (y >>= f) Q) :
    Post ((if c then x else y) >>= f) Q := by
  by_cases h : c <;> simp [h, hx, hy]

open Lean Meta Elab Tactic in
/-- On a goal `Post m Q` whose computation `m` is a beta-redex, reduces it; when `m` is headed by
    a `have`, applies `Post.jp` if `gen` holds and the value is a function (a join point of a `do`
    block), else substitutes the value. -/
private meta def postLet (gen : Bool) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let args := tgt.getAppArgs
  unless tgt.isAppOf ``Post && args.size ≥ 2 do throwError "post_let: not a Post goal"
  let m := args[args.size - 2]!.consumeMData
  let setM (m' : Expr) : TacticM Unit := do
    replaceMainGoal [← g.replaceTargetDefEq (mkAppN tgt.getAppFn (args.set! (args.size - 2) m'))]
  if m.isHeadBetaTarget then setM m.headBeta; return
  let .letE n t v b _ := m | throwError "post_let: no let"
  unless gen && (← whnf t).isForall do setM (b.instantiate1 v); return
  let e ← mkConstWithFreshMVarLevels ``Post.jp
  let (xs, _, concl) ← forallMetaTelescope (← inferType e)
  let k := xs.size
  unless ← isDefEq xs[k - 3]! (.lam n t b .default) do throwError "post_let: join point"
  unless ← isDefEq xs[k - 4]! v do throwError "post_let: join point"
  unless ← isDefEq concl tgt do throwError "post_let: join point"
  g.assign (mkAppN e xs)
  replaceMainGoal [xs[k - 2]!.mvarId!, xs[k - 1]!.mvarId!]

/-- Reduces a beta-redex or substitutes the `have` heading the computation of a `Post` goal. -/
local elab "post_let" : tactic => postLet false

/-- Reduces a beta-redex or substitutes the `have` heading the computation of a `Post` goal,
    except that a join point is generalized by `Post.jp`. -/
local elab "post_jp" : tactic => postLet true

open Lean Meta Elab Tactic in
/-- On a goal `Post m Q`, splits the `match` heading `m` or the first computation of `m` when `m`
    is a bind. -/
local elab "post_split" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let args := tgt.getAppArgs
  unless tgt.isAppOf ``Post && args.size ≥ 2 do throwError "post_split: not a Post goal"
  let m := args[args.size - 2]!.consumeMData
  let x := if m.isAppOfArity ``Bind.bind 6 then (m.getArg! 4).consumeMData else m
  let ok ← match x.getAppFn with
    | .const n _ => isMatcher n
    | _ => pure false
  unless ok do throwError "post_split: no `match` at the head"
  evalTactic (← `(tactic| split))

/-- One step of the decomposition of a goal `Post m Q` along the computation `m`, other than a
    beta-reduction or a `have`. -/
local macro "post_core" : tactic => `(tactic| first
  | intro _
  | with_reducible exact Post.throw
  | with_reducible apply Post.pure_bind
  | with_reducible apply Post.bind_assoc
  | (with_reducible apply Post.ite) <;> intro _
  | (with_reducible apply Post.ite_bind) <;> intro _
  | post_split
  | with_reducible apply Post.pure
  | (with_reducible apply Post.bind
     first | focus (with_reducible apply_assumption; done) | exact Post.any _)
  | focus (with_reducible apply_assumption; done))

/-- One step of the decomposition of a goal `Post m Q` along the computation `m`, substituting
    join points. -/
local macro "post_step" : tactic => `(tactic| first | post_let | post_core)

/-- One step of the decomposition of a goal `Post m Q` along the computation `m`, generalizing
    join points. -/
local macro "post_step_jp" : tactic => `(tactic| first | post_jp | post_core)

/-! ## The walk -/

/-- The output of the walk result `r` is `wItemsArmsOK`, and leaves the main path when `r`
    carries an obligation. -/
private def ROK (r : WRes P) : Prop :=
  wItemsArmsOK r.out.toList = true ∧ (r.hasObl = true → r.out.toList.any WItem.isBranching = true)

omit iW in
/-- A result without output and obligation has `ROK`. -/
private theorem rok_nil {r : WRes P} (ho : r.out = .nil) (hb : r.hasObl = false) : ROK r :=
  ⟨wItemsArmsOK_noBr (by simp [ho, Rope.toList_nil]), fun h => by simp [hb] at h⟩

omit iW in
/-- The combination of two results with `ROK` has `ROK`. -/
private theorem ROK.combine {a r : WRes P} (ha : ROK a) (hr : ROK r) : ROK (a.combine r) := by
  simp only [ROK, WRes.combine, Rope.toList_app, wItemsArmsOK_append, List.any_append,
    Bool.and_eq_true, Bool.or_eq_true] at *
  exact ⟨⟨ha.1, hr.1⟩, fun h => h.imp ha.2 hr.2⟩

/-- The saves, copies and restores of a run of `saveRestore` do not leave the main path. -/
private theorem saveRestore_noBr (xs : List P.Ident) : Post (saveRestore xs) fun r =>
    r.1.toList.any WItem.isBranching = false ∧ r.2.1.toList.any WItem.isBranching = false ∧
      r.2.2.1.toList.any WItem.isBranching = false := by
  unfold saveRestore
  dsimp only
  refine Post.bind (Post.forIn (fun y b hb => ?_) xs _ (by simp [Rope.toList_nil])) fun _ hb =>
    Post.pure hb
  exact Post.bind (Post.any _) fun _ _ => Post.bind (Post.any _) fun _ _ => Post.pure (by
    simp [Rope.toList_app, Rope.toList_one, WItem.isBranching, hb])

omit iDE iBE iLB iHB iHF iHS iHI iHa iHV iW in
/-- A fold appending one item per element, none of which leaves the main path, keeps which items
    leave it. -/
private theorem foldl_one_noBr {α : Type} (F : α → WItem P) (hF : ∀ q, (F q).isBranching = false) :
    ∀ (C : List α) (s : Rope (WItem P)),
      (C.foldl (fun acc q => acc.app (.one (F q))) s).toList.any WItem.isBranching =
        s.toList.any WItem.isBranching
  | [], _ => rfl
  | q :: C, s => by simp [foldl_one_noBr F hF C, Rope.toList_app, Rope.toList_one, hF]

omit iW in
/-- A result whose output is a straight-line item `x0` followed by the concatenation of the ropes
    `ps`, among them the outputs of two results `T` and `E` with `ROK` and otherwise ropes that
    do not leave the main path, and that carries an obligation exactly when `T` or `E` does, has
    `ROK`. -/
private theorem rok_pieces {a T E : WRes P} {x0 : WItem P} {ps : List (Rope (WItem P))}
    (RT : ROK T) (RE : ROK E) (hx0 : x0.isBranching = false)
    (hps : ∀ p ∈ ps, p = T.out ∨ p = E.out ∨ p.toList.any WItem.isBranching = false)
    (hT : T.out ∈ ps) (hE : E.out ∈ ps) (hobl : a.hasObl = (T.hasObl || E.hasObl))
    (hout : a.out = Rope.app (.one x0) (ps.foldl Rope.app .nil)) : ROK a := by
  obtain ⟨T1, T2⟩ := RT
  obtain ⟨E1, E2⟩ := RE
  have hok : ∀ x : WItem P, x.isBranching = false → wItemArmsOK x = true := by
    intro x
    cases x <;> simp [WItem.isBranching, wItemArmsOK]
  rw [wItemsArmsOK_eq_all, List.all_eq_true] at T1 E1
  refine ⟨?_, fun h => ?_⟩
  · simp only [hout, Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil,
      wItemsArmsOK_eq_all, List.all_eq_true, List.nil_append, List.singleton_append,
      List.mem_cons, List.mem_flatMap]
    rintro x (rfl | ⟨p, hp, hx⟩)
    · exact hok _ hx0
    rcases hps p hp with rfl | rfl | hb
    · exact T1 x hx
    · exact E1 x hx
    · exact hok x (Bool.eq_false_iff.2 fun h => (List.any_eq_false.1 hb x hx) h)
  · simp only [hout, Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil,
      List.nil_append, List.singleton_append, List.any_cons, List.any_flatMap, hx0, Bool.false_or,
      List.any_eq_true]
    rcases Bool.or_eq_true _ _ ▸ hobl ▸ h with h | h
    · exact ⟨T.out, hT, List.any_eq_true.1 (T2 h)⟩
    · exact ⟨E.out, hE, List.any_eq_true.1 (E2 h)⟩

omit iW in
/-- A block result whose output is the output of its body walk `B` followed by `Mg` and `J`,
    neither leaving the main path, or that tail behind the straight-line item `x` unless it is
    empty, has `ROK` when `B` has it. -/
private theorem block_rok {B a : WRes P} {x : WItem P} {Mg J : Rope (WItem P)} (RB : ROK B)
    (hM : Mg.toList.any WItem.isBranching = false) (hJ : J.toList.any WItem.isBranching = false)
    (hx : x.isBranching = false) (hobl : a.hasObl = B.hasObl)
    (hout : a.out = (if ((B.out.app Mg).app J).isNil then .nil
        else (Rope.one x).app ((B.out.app Mg).app J)) ∨ a.out = (B.out.app Mg).app J) :
    ROK a := by
  obtain ⟨R1, R2⟩ := RB
  have hB : wItemArmsOK x = true := by
    simpa [wItemsArmsOK] using wItemsArmsOK_noBr (l := [x]) (by simp [hx])
  refine ⟨?_, fun h => ?_⟩
  · rcases hout with ho | ho <;> rw [ho] <;> (try split) <;>
      simp [Rope.toList_nil, Rope.toList_app, Rope.toList_one, wItemsArmsOK_append, R1, hB,
        wItemsArmsOK_noBr hM, wItemsArmsOK_noBr hJ, wItemsArmsOK]
  · have hb := R2 (hobl ▸ h)
    rcases hout with ho | ho <;> rw [ho]
    · split
      · rename_i ht
        simp only [Rope.isNil_app', Bool.and_eq_true] at ht
        simp [Rope.isNil_toList ht.1.1] at hb
      all_goals simp [Rope.toList_app, Rope.toList_one, hb]
    · simp [Rope.toList_app, hb]

/-- Closes a goal `ROK r` for a walk result `r` whose output is empty or one straight-line item or
    run of obligations, or the combination of two results with `ROK`. -/
local macro "rok_close" : tactic => `(tactic| first
  | exact rok_nil rfl rfl
  | exact ROK.combine ‹_› ‹_›
  | (simp [ROK, Rope.toList_one, Rope.toList_app, Rope.toList_nil, setReach, WItem.isBranching,
      wItemsArmsOK, wItemArmsOK]; done))

/-- The walk of a laid-out `ite` has `ROK` when the walks of its arms (under every context, an
    obligation following them) have it. -/
private theorem iteOK_laid {κ : RE P} {d : Nat} {c : P.Expr} {tss ess : PStmts P}
    (hT : ∀ κ', Post (wpList κ' d true tss) ROK) (hE : ∀ κ', Post (wpList κ' d true ess) ROK) :
    Post (wpIteLaid κ d c tss ess) ROK := by
  have hsr := @saveRestore_noBr
  unfold wpIteLaid
  repeat' post_step_jp
  all_goals first
    | exact rok_nil rfl rfl
    | refine rok_pieces ‹_› ‹_› rfl (fun p hp => ?_) (by simp) (by simp) rfl rfl
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  all_goals rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact .inl rfl | exact .inr (.inl rfl) | refine .inr (.inr ?_)
  all_goals first
    | exact (foldl_one_noBr _ (fun _ => rfl) _ _).trans (by simp [Rope.toList_nil])
    | (simp only [Rope.toList_nil, Rope.toList_one, List.any_cons, List.any_nil, WItem.isBranching,
        Bool.or_false]; done)
    | (dsimp only at *; simp only [*]; done)
    | cases κ <;> (repeat' split) <;> simp [Rope.toList_nil, Rope.toList_one, setReach,
        WItem.isBranching]

/-- The walk of a real branch has `ROK` when the walks of its arms (under `top`, no obligation
    following them) have it. -/
private theorem iteOK_real {κ : RE P} {d : Nat} {c : P.Expr} {tss ess : PStmts P}
    (hT : Post (wpList .top d false tss) ROK) (hE : Post (wpList .top d false ess) ROK) :
    Post (wpIteReal κ d c tss ess) ROK := by
  unfold wpIteReal
  repeat' post_step
  all_goals first
    | exact rok_nil rfl rfl
    | split <;> (try split) <;> simp_all [ROK, Rope.toList_app, Rope.toList_one, wItemsArmsOK,
        wItemArmsOK, WItem.isBranching]

/-- The walk of a command has `ROK`. -/
private theorem stmtOK_cmd (κ : RE P) (d : Nat) (f : Bool) (c : CmdExt P) :
    Post (wpStmt κ d f (.cmd c)) ROK := by
  rcases c with ((⟨x, ty, e | _, md⟩ | ⟨x, e | _, md⟩ | ⟨l, e, md⟩ | ⟨l, e, md⟩ | ⟨l, e, md⟩) |
    ⟨p, args, md⟩) <;> unfold wpStmt <;> repeat' post_step
  all_goals rok_close

/-- The walk of an `exit` has `ROK`. -/
private theorem stmtOK_exit (κ : RE P) (d : Nat) (f : Bool) (l : String) (md : MetaData P) :
    Post (wpStmt κ d f (.exit l md)) ROK := by
  unfold wpStmt
  repeat' post_step
  all_goals (try cases κ) <;> rok_close

/-- The walk of a block has `ROK` when the walks of its body (at the next depth, under every
    context) have it. -/
private theorem stmtOK_block {κ : RE P} {d : Nat} {f : Bool} {l : String} {body : PStmts P}
    (md : MetaData P) (hB : ∀ κB, Post (wpList κB (d + 1) f body) ROK) :
    Post (wpStmt κ d f (.block l body md)) ROK := by
  unfold wpStmt
  repeat' post_step_jp
  all_goals split
  all_goals first
    | refine block_rok ?_ ?_ ?_ ?_ ?_ (.inl rfl)
    | refine block_rok (x := .assume "" (.lit true) .empty) ?_ ?_ ?_ ?_ ?_ (.inr rfl)
  all_goals first
    | assumption
    | rfl
    | exact (foldl_one_noBr _ (fun _ => rfl) _ _).trans (by simp [Rope.toList_nil])
    | (try cases κ) <;> (repeat' split) <;> simp [Rope.toList_nil, Rope.toList_one, setReach,
        WItem.isBranching]

mutual
/-- Every statement-list walk has a result with `ROK`. -/
private theorem listOK_all :
    ∀ (ss : PStmts P) (κ : RE P) (d : Nat) (fEnd : Bool), Post (wpList κ d fEnd ss) ROK
  | [], κ, d, fEnd => by
    rw [wpList]
    exact Post.pure (rok_nil rfl rfl)
  | s :: rest, κ, d, fEnd => by
    have hs := fun f => stmtOK_all s κ d f
    have hr := listOK_all rest κ d fEnd
    rw [wpList]
    repeat' post_step
    exact ROK.combine ‹_› ‹_›
/-- Every statement walk has a result with `ROK`. -/
private theorem stmtOK_all :
    ∀ (s : PStmt P) (κ : RE P) (d : Nat) (f : Bool), Post (wpStmt κ d f s) ROK
  | .cmd c, κ, d, f => stmtOK_cmd κ d f c
  | .exit l md, κ, d, f => stmtOK_exit κ d f l md
  | .block l body md, κ, d, f => stmtOK_block md fun κB => listOK_all body κB (d + 1) f
  | .ite (.det c) tss ess md, κ, d, f => by
    have hL := iteOK_laid (κ := κ) (c := c) (fun κ' => listOK_all tss κ' d true)
      (fun κ' => listOK_all ess κ' d true)
    have hR := iteOK_real (κ := κ) (c := c) (listOK_all tss .top d false)
      (listOK_all ess .top d false)
    unfold wpStmt
    repeat' post_step
  | .ite .nondet _ _ _, κ, d, f | .loop _ _ _ _ _, κ, d, f | .typeDecl _ _, κ, d, f => by
    unfold wpStmt
    repeat' post_step
    all_goals exact rok_nil rfl rfl
end

/-- **Every arm of every `ite` of the output of the WP phase**, at any depth, contains an
    `assert` or a `cover`. -/
theorem wpEntry_armsHaveObl {G : IdSet P} {tys : Tys P} {ss : PStmts P} {w : WOut P}
    (h : wpEntry G tys ss = .ok w) : Block.armsHaveChecks w.lay = true := by
  simp only [wpEntry, wpBody, StateT.run, Except.bind_is_ok, Except.pure_is_ok] at h
  obtain ⟨⟨r, st1⟩, hrun, lay, hlay, rfl⟩ := h
  exact emit_arms hlay ((listOK_all ss .top 0 false).run _ _ _ hrun).1

end -- public section

end WP
end Imperative
