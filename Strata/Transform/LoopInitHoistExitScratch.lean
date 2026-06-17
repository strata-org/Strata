/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.LoopInitHoistLoopDriver

import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd
import all Strata.Transform.LoopInitHoist
import all Strata.Transform.LoopInitHoistContains
import all Strata.Transform.LoopInitHoistFreshness
import all Strata.Transform.LoopInitHoistRewrite
import all Strata.Transform.LoopInitHoistInfra
import all Strata.Transform.DetToKleeneCorrect

public section

namespace Imperative
namespace LoopInitHoistExitScratch

open Imperative.LoopInitHoistLoopDriver

variable {P : PureExpr}

/-! # Phase 1 scratch: the exiting clause of a sum-typed BodySim.

PURPOSE.  This is the make-or-break feasibility probe for relaxing the
`pipeline_sound` `h_noexit` (Block.noExit body) precondition by admitting a
loop-body `.exit` (the break pattern).  We do NOT touch the downstream driver
here; we (a) state the new exiting clause and (b) prove IN ISOLATION that the
hoist body-transport establishes it for a single `.exit` in a loop body.

## KEY DESIGN CORRECTION (over the first attempt)

The first scratch attempt tried to conclude the exiting clause with a
`StoreAgreement` between the PROJECTED exit stores.  That is the WRONG target:
`StoreAgreement` is strictly weaker than `HoistInv` (it says nothing at undefined
source vars and, crucially, drops the parent-side hoist info), and the
projection step therefore cannot be discharged from `HoistInv` at the body-exit
stores alone — it needs the hoist parent to be related to the source parent.

The CORRECT target is the SAME relation the existing mutual already concludes for
its `.exiting` disjunct: `HoistInv A B subst` between the source and hoist exit
stores.  The §E mutual `Block.hoistLoopPrefixInits_preserves`
(`LoopInitHoistCorrect.lean`) is ALREADY sum-typed (terminal-OR-exiting) and its
`.block` arm propagates exits through `HoistInv.project_both` — see e.g. the
non-matching-label exit propagation at the `.block` arm, which concludes
`HoistInv.project_both h_hinv h_hinv_inner`.  The ONLY place `h_noexit` is
load-bearing is the `.loop` arm, which feeds `h_src_body_no_exit` to the driver
because the driver's `BodySim` predicate is terminal-only.

So the sum-typed `BodySim` exiting clause must conclude `HoistInv` at the
body-exit stores; the enclosing loop's `.block .none ρ_loop_entry.store` then
projects BOTH sides through `HoistInv.project_both`, exactly as the `.block` arm
does, re-establishing `HoistInv` at the projected (capped) exit stores.  This
matches the end-to-end forward-simulation relation and is what `loopDet_*`
recursion would propagate as the loop's early-exit outcome.

## Inverting a single-`.exit` body run

A body that is `[.exit l md]` run from `ρ` reaches `.exiting l ρ` (full store,
unchanged env): `.stmts [.exit l md] ρ` ⟶ `.seq (.stmt (.exit l md) ρ) []`
⟶ `.seq (.exiting l ρ) []` (step_exit under step_seq_inner) ⟶ `.exiting l ρ`
(step_seq_exit).  We invert ANY run to `.exiting l' ρ'` to learn `l' = l` and
`ρ' = ρ`. -/

private theorem exit_body_reaches_exiting_inv [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {l l' : String} {md : MetaData P} {ρ ρ' : Env P}
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmts [Stmt.exit l md] ρ) (.exiting l' ρ')) :
    l' = l ∧ ρ' = ρ := by
  -- .stmts [exit] ρ ⟶ .seq (.stmt (.exit l md) ρ) []
  cases h with
  | step _ _ _ h1 hr1 =>
    cases h1
    -- now: .seq (.stmt (.exit l md) ρ) [] ⟶* .exiting l' ρ'
    cases hr1 with
    | step _ _ _ h2 hr2 =>
      cases h2 with
      | step_seq_inner hinner =>
        -- inner: .stmt (.exit l md) ρ ⟶ ?  only step_exit
        cases hinner with
        | step_exit =>
          -- now: .seq (.exiting l ρ) [] ⟶* .exiting l' ρ'
          cases hr2 with
          | step _ _ _ h3 hr3 =>
            cases h3 with
            | step_seq_inner hinner3 => exact nomatch hinner3
            | step_seq_exit =>
              -- now: .exiting l ρ ⟶* .exiting l' ρ'
              cases hr3 with
              | refl => exact ⟨rfl, rfl⟩
              | step _ _ _ hd _ => exact nomatch hd

/-- Constructive direction: a single-`.exit` body run reaches `.exiting l ρ`. -/
private theorem exit_body_reaches_exiting [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {l : String} {md : MetaData P} {ρ : Env P} :
    StepStmtStar P (EvalCmd P) extendEval (.stmts [Stmt.exit l md] ρ) (.exiting l ρ) := by
  refine ReflTrans.step _ _ _ .step_stmts_cons ?_
  refine ReflTrans.step _ _ _ (.step_seq_inner .step_exit) ?_
  exact ReflTrans.step _ _ _ .step_seq_exit (.refl _)

/-- Renaming leaves a single `.exit` literally unchanged: `Block.applyRenames`
(a fold of `substIdent`) is the identity on `[.exit l md]`. -/
private theorem applyRenames_exit_singleton [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (renames : List (P.Ident × P.Ident)) (l : String) (md : MetaData P) :
    Block.applyRenames renames [Stmt.exit l md] = [Stmt.exit l md] := by
  unfold Block.applyRenames
  induction renames with
  | nil => rfl
  | cons p rest ih =>
      simp only [List.foldl_cons]
      have hstep : Block.substIdent p.1 p.2 [Stmt.exit l md] = [Stmt.exit l md] := by
        simp only [Block.substIdent, Stmt.substIdent_exit]
      rw [hstep]; exact ih

/-! ## Phase 1a — the sum-typed `BodySim`.

The TERMINAL clause is exactly the existing `LoopInitHoistLoopDriver.BodySim`.
The new EXITING clause concludes `HoistInv` at the body-exit stores (NOT
StoreAgreement), matching the existing mutual's `.exiting` disjunct shape.  The
`B`-boundedness conjunct is carried in the exiting clause too: the enclosing
loop's `.block .none` projection re-establishes it exactly as the terminal
clause's does (see `exit_clause_project_block` below). -/

/-- The sum-typed body simulation: a body run that TERMINATES is matched by a
terminating hoist run (the existing terminal clause), and a body run that EXITS
with label `l` is matched by a hoist run that exits with the SAME label `l`,
re-establishing `HoistInv` at the body-exit stores together with `hasFailure`
agreement and `B`-boundedness.  This is the predicate the redesigned two-guard
driver's `body_sim` slot must consume. -/
def BodySimSum [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident))
    (bsrc bh : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
    ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
    (∀ y ∈ B, ρ_h.store y ≠ none) →
    -- TERMINAL clause (unchanged from `BodySim`):
    (∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.terminal ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.terminal ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))
    ∧
    -- EXITING clause (new):
    (∀ (l : String) (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.exiting l ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.exiting l ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))

/-! ## Phase 1b — the core feasibility lemmas (build-green, sorry-free).

Two isolated proofs settle the make-or-break question:

(I) `exit_body_establishes_exiting_clause`: the hoist body-transport actually
ESTABLISHES the exiting clause for a single `.exit l md` in a loop body.  The
hoist body is the renamed source body; `Block.applyRenames renames [.exit l md] =
[.exit l md]` (renames leave `.exit` literally unchanged — `substIdent_exit`), so
both sides run the SAME residual.  The `.exit` copies the env unchanged, so the
body-exit stores are exactly the body-ENTRY stores `ρ_s.store`/`ρ_h.store`, at
which `HoistInv` is the BodySim precondition.  Hence the exiting clause holds.

(II) `exit_clause_project_block`: given the exiting clause's `HoistInv` at the
body-exit stores (delivered by (I) or by a recursive body-transport for a deep
`.exit`), the enclosing loop's `.block .none ρ_loop_entry.store` projection
re-establishes `HoistInv` at the projected (capped) exit stores via
`HoistInv.project_both`, AND drives the matching hoisted block/seq steps to the
loop's early-exit `.exiting` outcome.  This is the analogue of the existing
`.block` arm's non-matching-label exit propagation. -/

/-- **Feasibility lemma (I).**  A loop body that is a single `.exit l md`
satisfies the sum-typed BodySim's exiting clause.  The hoist body is the renamed
source body — and renaming leaves `.exit` unchanged, so the hoist body is the
SAME `[.exit l md]`.  The `.exit` copies the env, so the body-exit `HoistInv` is
the body-entry `HoistInv` supplied as the BodySim precondition. -/
theorem exit_body_establishes_exiting_clause
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P]
    [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {renames : List (P.Ident × P.Ident)}
    {l : String} {md : MetaData P}
    {ρ_s ρ_h : Env P}
    (h_hinv : HoistInv (P := P) A B subst ρ_s.store ρ_h.store)
    (h_hf : ρ_s.hasFailure = ρ_h.hasFailure)
    (h_bnd : ∀ y ∈ B, ρ_h.store y ≠ none) :
    ∀ (l' : String) (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts [Stmt.exit l md] ρ_s) (.exiting l' ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval
          (.stmts (Block.applyRenames renames [Stmt.exit l md]) ρ_h) (.exiting l' ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) := by
  intro l' ρ_s' h_run
  -- Invert the source run: l' = l, ρ_s' = ρ_s.
  obtain ⟨h_l, h_ρ⟩ := exit_body_reaches_exiting_inv h_run
  subst h_l; subst h_ρ
  -- The renamed hoist body is literally `[.exit l' md]`: renames leave `.exit` fixed.
  rw [applyRenames_exit_singleton renames l' md]
  -- The hoist body run reaches `.exiting l' ρ_h` (exit copies the env).
  exact ⟨ρ_h, exit_body_reaches_exiting, h_hinv, h_hf, h_bnd⟩

/-- **Feasibility lemma (II) — the core soundness step.**  Given the exiting
clause's `HoistInv` at the body-exit stores `ρ_s'`/`ρ_h'` (whatever the body
computed before the `.exit`), the enclosing loop's `.block .none σ_s_parent`
(source) / `.block .none σ_h_parent` (hoist) catch the unmatched label and
project BOTH stores.  The projected exit stores stay `HoistInv`-related via
`HoistInv.project_both`, given that the loop-ENTRY stores are also
`HoistInv`-related (which they are: that is the loop-iteration invariant the
driver maintains, the SAME `h_hinv` it threads into each body run).

This is the exact relation the loop's early-exit `.exiting` outcome carries, and
it is the analogue of the `.block` arm's non-matching-label propagation
(`HoistInv.project_both h_hinv h_hinv_inner`).  `B`-boundedness survives the
projection exactly as in the `.block` arm: a `b ∈ B` is bound in the hoist parent
(`h_h_parent_bnd`) so its parent slot is `some`, hence `projectStore` keeps the
inner value, which is `some` by the body-exit boundedness. -/
theorem exit_clause_project_block
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P]
    [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {σ_s_parent σ_h_parent : SemanticStore P}
    {ρ_s' ρ_h' : Env P}
    -- loop-entry stores are HoistInv-related (the loop-iteration invariant):
    (h_parent : HoistInv (P := P) A B subst σ_s_parent σ_h_parent)
    -- body-exit stores are HoistInv-related (the exiting clause's conclusion):
    (h_inner : HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store)
    -- hoist parent binds B (the driver's threaded boundedness):
    (h_h_parent_bnd : ∀ y ∈ B, σ_h_parent y ≠ none)
    -- body-exit hoist store binds B (the exiting clause's conclusion):
    (h_inner_bnd : ∀ y ∈ B, ρ_h'.store y ≠ none) :
    HoistInv (P := P) A B subst
        (projectStore σ_s_parent ρ_s'.store)
        (projectStore σ_h_parent ρ_h'.store)
      ∧ (∀ y ∈ B, projectStore σ_h_parent ρ_h'.store y ≠ none) := by
  refine ⟨HoistInv.project_both h_parent h_inner, ?_⟩
  intro y hy
  show projectStore σ_h_parent ρ_h'.store y ≠ none
  unfold projectStore
  have h_parent_some : (σ_h_parent y).isSome := by
    cases h : σ_h_parent y with
    | none => exact absurd h (h_h_parent_bnd y hy)
    | some _ => simp
  rw [h_parent_some]; exact h_inner_bnd y hy

/-! ## Phase 1 verdict (recorded in prose for the audit).

Both feasibility lemmas build green and sorry-free.  Together they answer the
make-or-break question affirmatively:

* (I) shows the hoist body-transport ESTABLISHES the sum-typed exiting clause for
  a `.exit` (the base case of the body-transport recursion); the renamed hoist
  body is the same `[.exit l md]` and the exit copies the env, so the body-exit
  `HoistInv` IS the body-entry `HoistInv`.

* (II) shows the loop's enclosing `.block .none` projection re-establishes
  `HoistInv` at the capped exit stores via `HoistInv.project_both`, given the
  loop-entry stores are `HoistInv`-related (the driver's iteration invariant).
  The projected-store agreement that the first scratch attempt could NOT close
  (because it targeted the weaker `StoreAgreement` and lost the parent-side hoist
  info) closes immediately once the target is `HoistInv` carrying the parent
  relation — which is precisely the relation the existing mutual already uses for
  its `.exiting` disjunct.

The remaining work (the DRIVER and the §E `.loop` arm rewire) is mechanical
threading of this exiting clause through `peelIterationDet` / `loopDet_*` and the
StepB body-transport (`BodyTransport`/`BodySimE`), which must gain a sum-typed
`.exit` constructor.  No NEW soundness obstruction remains at the body-exit /
projection seam — the hard part of the original §E close (the self-referential
body-transport core) is the only nontrivial downstream cost. -/

/-\! # Phase 2 (DONE — moved to the driver file).

The Phase 2 driver threading is COMPLETE and lives in
`Strata/Transform/LoopInitHoistLoopDriver.lean` (it must, because the fuel core
consumes the driver-private `buildLoopIterationDet` / `peelIterationDet`
helpers).  Three additive, build-verified, sorryAx-free declarations:

* `BodySimSum A B subst bsrc bh` — the sum-typed body simulation (terminal AND
  exiting clauses), the exact predicate from Phase 1's `BodySimSum`.
* `blockT_none_reaches_terminal` — no-exit-free block-terminal inversion for a
  `.none` block (an inner `.exiting` always mismatches `.none`, so reaching
  `.terminal` forces an inner `.terminal`); the recursive terminal-iteration case
  uses it without ruling out body exits.
* `loopDet_lift_2g_E_fuel` / `loopDet_lift_2g_E` — the exiting-target two-guard
  fuel recursion (+ Prop wrapper).  DROPS `h_src_body_no_exit`; consumes
  `BodySimSum`; produces the matching hoist `.exiting` outcome with `HoistInv` /
  `hasFailure` / `B`-boundedness at the projected (capped) exit stores.

`#print axioms` on all three: `[propext, (Classical.choice,) Quot.sound]` — no
`sorryAx`.  The terminal-only driver (`loopDet_lift_2g*`) and its `*_no_exit`
support lemmas are UNTOUCHED, so existing call paths build unchanged.

The Phase 1 isolated feasibility lemmas above remain as the design record.  The
remaining downstream work (Phase 3+) is: re-derive the StepB body-transport
(`BodySimE`/`BodyTransport`) with the exiting clause to PRODUCE a `BodySimSum`,
then rewire the §E `.loop` arm to consume `loopDet_lift_2g_E` and finally drop the
`h_noexit` precondition from `pipeline_sound`. -/

/-! # Phase 3 (provider/StmtSimES layer — DONE; build-green, sorryAx-free).

SCOPE CORRECTION discovered in Phase 3: the §E `.loop` arm does NOT consume the
simple two-guard driver `loopDet_lift_2g` directly — it consumes the HEAVIER
shapefree+undef union-carrier driver `loopDet_lift_sf_undef_recovers_single` (via
`BodySimUSF` / `compose_union_sf`).  So a SOUND end-to-end relaxation must make the
ENTIRE body-sim / compose / driver stack sum-typed, not just the simple driver.  The
make-or-break soundness questions are all answered AFFIRMATIVELY with build evidence;
the remaining cost is volume + two genuine sub-lemmas (sum-typed `compose_union_sf`
and the sf+undef exiting driver), with NO soundness obstruction at any seam.

NEW, build-green, sorryAx-free (`[propext(, Classical.choice, Quot.sound)]`):

Driver (`LoopInitHoistLoopDriver.lean`):
* `loopDet_lift_2g_TE_fuel` / `loopDet_lift_2g_TE` — sum-typed TERMINAL-target driver
  (drops `h_src_body_no_exit`; peels iterations via `blockT_none_reaches_terminal`).
* `loopDet_lift_renamedGuard_E` / `loopDet_lift_renamedGuard_TE` — thin renamed-guard
  wrappers over the exiting / terminal sum-typed drivers.

Provider (`LoopInitHoistOptEStepBProviderSpike.lean`):
* `BodySimES` / `StmtSimES` — eval-carrying SUM-TYPED sims.
* `bodySimES_nil` / `bodySimES_cons` (the sum-typed cons-sequencer) /
  `bodySimES_to_bodySimSum`.
* Every per-statement arm a sum-typed `Block.bodyTransport` needs, PROVEN standalone:
  `stmtSimE_to_stmtSimES_of_noExit` + `cmd_stmt_no_exit` (`.cmd`/`.typeDecl`),
  `exit_stmtSimES` (`.exit`), `block_stmtSimES` (the StepC-comment's hard `.block`
  arm — all three outcomes: terminal / label-match catch / label-mismatch propagate),
  `ite_stmtSimES` / `ite_nondet_stmtSimES` (`.ite`), `nestedLoop_stmtSimES` (`.loop`).

Support (`StmtSemanticsProps.lean`): `smallStep_noFuncDecl_preserves_eval_exiting`.

REMAINING (mechanical assembly + 2 sub-lemmas, NOT a soundness gap):
(a) `BodyTransport` inductive `.exit` + exit-permitting `.block` ctors; rewrite
    `Block.bodyTransport` to produce `BodySimES` (swap `bodySimE_cons`→`bodySimES_cons`
    and feed the proven arms above).
(b) sum-typed `BodySimUSF` + `compose_union_sf` (exiting clause composes sequentially
    body→body₁→body₃, parallel to the cons-sequencer).
(c) sum-typed `loopDet_lift_sf_2g_undef_fuel` (structurally = `loopDet_lift_2g_E_fuel`
    with `Vs`/`Vh`/`σ_sf` threaded, unused on the exit path).
(d) rewire `loop_arm_close` (dispatch the exiting `h_cfg_src` case to the sum-typed
    sf+undef driver instead of `loopDet_no_exit.elim`); supply `stepA`'s exiting clause
    (the underlying `hoistLoopPrefixInits_preserves` is already sum-typed); drop
    `h_noexit` from `hoistLoopPrefixInits_preserves(_kind)` and `pipeline_sound`. -/

end LoopInitHoistExitScratch
end Imperative
