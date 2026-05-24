# SI2 — Feasibility audit: simplifying (a) PC arithmetic and (b) foldlM preservation chain

**Worker:** SI2 (read-only feasibility analysis).
**Branch base:** htd/unstructured-to-goto (commit d10422c2b).
**Scope:** read-only investigation of whether sections (a) and (b) of
docs/CoreToGOTO_WhyDifficult.md (~4,900 LoC combined) contain
significant *boilerplate* that better abstractions could absorb,
versus *structural* difficulty that costs LoC by necessity.

This report is read-only. No .lean files were modified.

## Method and ground truth

I read each of the files cited in the task spec, sampled
representative lemmas, counted lines per recurring pattern, and traced
the predicate signatures to see why
[BlocksFoldClosed](../../Strata/Backends/CBMC/GOTO/BlocksFoldClosed.lean)
(465 LoC, lifts a P : Array Instruction → Prop through 9 fold steps)
saved only +201 LoC across 3 ports against
[L2 projection of +1,200-1,600](L2_preservation_combinator_design.md).
The L3 outcome is itself the most important data point: the
combinator works, but its abstraction shape (Class A) does not fit
~70% of the property classes the chain needs to cover.

LoC totals at the commit:

| File | LoC |
|---|---|
| CoreCFGToGOTOCorrect.lean (block-induction kernel) | 928 |
| CoreCFGToGOTOInvariants.lean (WF predicate) | 377 |
| CoreCFGToGotoTransformWF/Preservation.lean | 1,023 |
| CoreCFGToGotoTransformWF/StepPreservation.lean | 1,290 |
| CoreCFGToGotoTransformWF/FoldAndDecompose.lean | 1,192 |
| CoreCFGToGotoTransformWF/Shape.lean | 941 |
| CoreCFGToGotoTransformWF/BlockBodyClosures.lean | 862 |
| CoreCFGToGotoTransformWF/CondGotoClosures.lean | 1,412 |
| BlocksFoldClosed.lean | 465 |
| NoDead.lean | 317 |
| GotoTargetProvenance.lean | 567 |
| WfLabelMapAgree.lean | 398 |
| PcInversion.lean | 999 |
| CmdProvenance.lean | 304 |

The doc (a) ~1,500 LoC fingerprint corresponds to
block_body_cmds_simulation (~250 LoC) + WellFormedTranslation.layout_*
discharge (blocksFoldlM_layout_location 70, _with_labels 70,
_layout_finish 75, plus the coreCFGToGotoBlockStep_location_at_pc
family ~100 each, plus coreCFGToGotoBlockStep_condGoto_at_pc ~130,
plus cmdsPrefixInstrCount/DetBlockBodyInstrCount/gotoInstrCount
~30, plus innerCmdLoop_layout_block_body and supporting
foldl_gotoInstrCount_extract_acc ~250, plus various _advance lemmas).

The doc (b) ~3,400 LoC fingerprint is roughly
Preservation.lean (1,023) + StepPreservation.lean (1,290) +
FoldAndDecompose.lean (1,192) ~ 3,505. (BlocksFoldClosed.lean itself
was new infrastructure, not part of the original cost.)

## 1. Audit findings

### 1.1 Section (a): PC arithmetic — what is actually in the 1,500 LoC

The doc is honest that the kernel of block_body_cmds_simulation
(CoreCFGToGOTOCorrect.lean:315-568) is ~250 LoC because the same
skeleton recurs three times (one per transfer shape). Reading the
code, the actual breakdown is:

1. **Strong induction setup + cmd arm** (lines 315-468, ~150 LoC).
   This is *not* the boilerplate — it is the genuine PC-bookkeeping
   step. Constituents:
   - induction h_size : cs.length using Nat.strongRecOn (the
     non-mutual-induction workaround for EvalDetBlock/EvalCommand).
   - cases h_step then renaming back the pre-cases names.
   - Membership of c in blk.cmds from cs = blk.cmds.drop k.
   - Pulling layout for the head command via wf.layout_block_body.
   - The PC-prefix-step lemma h_prefix_step (lines 414-428):
     cmdsPrefixInstrCount blk.cmds (k + 1) = ... + Cmd.gotoInstrCount inner.
   - The IH application on the tail-suffix at index k+1.
   - The ReflTrans_Transitive concatenation.
   - The updateFailure ac_rfl boolean rearrangement.
   The volume here is real bookkeeping, not boilerplate. Each have
   discharges one fact the proof skeleton needs; nothing repeats.

2. **Three transfer arms** (lines 469-568, ~100 LoC). Here the doc
   skeleton-recurs-three-times claim is *only mostly true*. They share:
   - cs = [] from the constructor (1 LoC) yielding blk.cmds.length le k
     and cmdsPrefixInstrCount blk.cmds k = DetBlockBodyInstrCount blk
     (call to cmdsPrefixInstrCount_at_blk_length, 1 LoC).
   - wf.layout_* destructuring to get pc_* and instr_* (5-15
     fields, 4-6 LoC).
   - wf.layout_cond_goto_guards for the two condGoto arms (~7 LoC,
     reused in goto_true and goto_false).

   But the post-step-firing differs:
   - goto_true: 2-step trace (fallthrough on neg guard, then
     unconditional taken) = ~50 LoC.
   - goto_false: 1-step trace (negated GOTO taken) = ~35 LoC.
   - terminal: 1-step trace via END_FUNCTION = ~20 LoC.

   The asymmetry between goto_true and goto_false is structural:
   in the true case, the proof must thread *both* GOTO pcs through to
   the destination; in the false case only the first GOTO fires. They
   are *not* interchangeable instances of one schema.

3. **Off-block layout discharge** (WellFormedTranslation.layout_*
   shadow-recovery in FoldAndDecompose.lean and
   BlockBodyClosures.lean / CondGotoClosures.lean, ~1,000 LoC).
   Costs split:
   - coreCFGToGotoBlockStep_location_at_pc (~100 LoC) and
     _location_at_pc_with_labels (~100 LoC) — near-duplicates: both
     walk emitLabel then cmds-fold then transfer dispatching, the
     second additionally exposes labels = [l]. **This is real
     boilerplate** — the second is a strengthened-existential of the
     first.
   - coreCFGToGotoBlockStep_finish_at_pc (~70 LoC) and
     coreCFGToGotoBlockStep_condGoto_at_pc (~130 LoC) — separate
     because the existential they expose differs (END_FUNCTION
     witness vs two GOTOs + cond-expr witness). Hard to unify.
   - The per-cmd-shape Cmd_toGotoInstructions_*_ok lemmas
     (Shape.lean, ~250 LoC) — the 6 cmd-shape constructors each get
     one shape-extraction lemma. Hard to unify in Lean 4 without
     macro-level refactor.
   - innerCmdLoop_layout_block_body (~130 LoC) — the recursive
     proof that each (cmd, k) was emitted at
     trans.nextLoc + cmdsPrefixInstrCount cmds k. Genuine PC
     accounting. Uses foldl_gotoInstrCount_extract_acc (10 LoC).

The boilerplate fraction within the (a) bucket is concentrated in:
- _at_pc and _at_pc_with_labels near-duplicates (~50 LoC of saving).
- the 6-fold cmd-shape dispatch in Cmd_toGotoInstructions_*_ok and
  its consumers (~50-80 LoC of saving with a tactic macro).

The PC arithmetic per se (rewrites involving cmdsPrefixInstrCount,
DetBlockBodyInstrCount, gotoInstrCount) does not have many
opportunities for compression: each of those rewrite chains is
short (1-3 lines) and they only repeat across the three transfer
arms, which we just saw are not structurally parallel.

### 1.2 Section (b): foldlM preservation chain — what is actually in the 3,400 LoC

The 9-step chain (toGotoInstructions, cmdStep, cmdsFoldlM, emitLabel,
emitCondGoto, emitUncondGoto, endFunctionEmit, blockStep, blocksFoldlM)
is repeated for *each* property the translator output is shown to
satisfy. Reading the code:

**Preservation.lean** (1,023 LoC) carries the structural step
preservation for size_eq and locationNum_eq_index. Breakdown:

| Block | LoC | Notes |
|---|---|---|
| emitLabel preserves size_eq, locationNum_eq_index | ~50 | size: 6, loc: 40 |
| toGotoInstructions_preserves_size_eq | 50 | 6-arm Cmd dispatch |
| push_preserves_locationNum_eq_index, append_two_* | 70 | Generic helpers |
| toGotoInstructions_preserves_locationNum_eq_index | 70 | 6-arm Cmd dispatch, mirrors size |
| emitCondGoto, emitUncondGoto preserves (size+loc) | 50 | Each ~25 LoC, parallel |
| endFunction_emit_preserves_locationNum_eq_index | 15 | One-liner |
| patch_one_preserves_locationNum, _type, _labels | 200 | Patcher per-step lemmas + helpers |
| patchGotoTargets_preserves_locationNum, _type, _labels | 100 | Each ~30 LoC of foldl-induction |
| innerCmdLoop (recursive shadow definition) + lemmas | ~280 | The strong-induction shadow that backs layout_block_body (Section a). |
| Misc spaces + headers | ~140 | Doc comments, namespace/section, blanks |

So Preservation.lean locationNum/size duty is roughly 600-650 LoC;
the remaining ~280 is the layout_block_body backing. The doc 600/250/150
split is approximately right.

**StepPreservation.lean** (1,290 LoC) is the per-cmd-step / per-block
step layer. Pattern:

| Block | LoC | Notes |
|---|---|---|
| LabelMap operations (hashMapToLabelMap, emptyLabelMap, etc.) | 75 | Plumbing |
| coreCFGToGotoCmdStep_preserves_size_eq, _loc | 50 | 1-line dispatchers |
| cmdsFoldlM_preserves_size_eq, _loc | 80 | Each ~40 LoC induction |
| coreCFGToGotoCmdStep_nextLoc_advance / cmdsFoldlM_nextLoc_advance | 60 | Parallel advance pair |
| coreCFGToGotoBlockStep_preserves_size_eq | 60 | emitLabel, cmds-fold, dispatch |
| coreCFGToGotoBlockStep_preserves_locationNum_eq_index | 110 | Same walk threading h_size + h_loc |
| coreCFGToGotoBlockStep_labelMap | 40 | Block-step effect on labelMap |
| coreCFGToGotoBlockStep_nextLoc_advance_finish, _condGoto | 100 | nextLoc effect, two cases |
| coreCFGToGotoCmdStep_size_le, _instructions_prefix? | 30 | 1-line dispatchers |
| cmdsFoldlM_instructions_prefix?, _size_le | 60 | Each ~30 LoC induction |
| coreCFGToGotoBlockStep_size_le, _instructions_prefix? | 110 | Each ~50-60 LoC dispatching |
| coreCFGToGotoBlockStep_location_at_pc, _with_labels, _finish_at_pc, _condGoto_at_pc | 400 | Layout-fact extraction: 100+100+70+130 |
| blocksFoldlM_preserves_size_eq, _locationNum_eq_index | 70 | Each ~30 LoC induction |
| Misc spaces + headers | ~50 | |

The duplicative pattern across the 8 distinct blockstep_* lemmas is
visible — they all start with the same obtain on (label, blk), unfold,
simp only, generalize h_inner over the cmds-fold result, match inner with,
cases h_t : blk.transfer with, two transfer arms. That intro skeleton
is ~25 LoC, so 8 x 25 = ~200 LoC of same-intro boilerplate.

**FoldAndDecompose.lean** (1,192 LoC) is the outer-loop fold + decompose
+ shadow + top-level theorem assembly. Breakdown:

| Block | LoC | Notes |
|---|---|---|
| blocksFoldlM_size_le, _instructions_prefix? | 70 | Outer-loop induction |
| BlockLabelsDistinct_* lemmas | 35 | Distinctness propagation |
| blocksFoldlM_labelMap_preserves_external | 40 | Outer-loop, label-not-in-rest threading |
| blocksFoldlM_layout_location | 80 | admitted+distinct threading, cons step at hd |
| blocksFoldlM_layout_location_with_labels | 80 | Near-duplicate, exposes labels |
| blocksFoldlM_layout_finish | 80 | Same skeleton, finish-only |
| Patch step preservation | 60 | Each ~20 LoC |
| patchesFoldlM_no_contracts_* | 90 | Each ~30 LoC induction |
| coreCFGToGotoTransform_size_eq_and_loc, _direct | 100 | Composition theorems |
| coreCFGToGotoTransform_decompose | 80 | Translator decomposition |
| CoreCFGToGotoTransformShadow structure | 100 | WF mirror + structural fields |
| wellFormedTranslation_of_shadow | 70 | Field-by-field copy bridge |
| coreCFGToGotoTransform_wellFormed_nonempty | 230 | Top-level theorem |
| Misc | ~80 | |

The cleanest example of *boilerplate* in FoldAndDecompose.lean is the
trio blocksFoldlM_layout_location, _with_labels, _layout_finish: each
is ~80 LoC, all three implement the same pattern (nil case, cons step,
size_eq+admitted-rest propagation, dispatch, head/tail rcases). The
*skeleton* would compress to ~20 LoC if abstracted; per-property
differences (which _at_pc, what is in the existential) are 30-40 LoC
each. So this trio could compress to ~140 LoC from ~240 LoC.

## 2. Simplification candidates

For each candidate I give an API sketch, a concrete LoC saving
estimate (broken down), risk level, and a recommendation.

### 2.1 Candidate (a-1): Tactic macro for the 6-arm Cmd dispatch

The pattern recurs across:
- toGotoInstructions_preserves_size_eq (50 LoC),
- toGotoInstructions_preserves_locationNum_eq_index (70 LoC),
- toGotoInstructions_size_le (50 LoC),
- toGotoInstructions_instructions_prefix? (~70 LoC),
- toGotoInstructions_nextLoc_advance (50 LoC),
- toGotoInstructions_preserves_body_pc_covered (~120 LoC),
- BlocksFoldClosed.toGotoInstructions_preserves_of_pushSafe (60 LoC),
- cmdEmittedAt_*_of_toGotoInstructions constructors,
- coreCFGToGotoCmdStep_* 1-line wrappers.

Sketch: a cmd_dispatch tactic that expands cases-of-cases plus the
6 obtain branches with the right Cmd_toGotoInstructions_*_ok pulled in
by name. Body uses a case_cmd c | shape selector to provide the
one-line conclusion per branch.

Estimated saving: 50 LoC x 5-7 consumers = ~250-300 LoC absorbed.
Macro itself: ~80-120 LoC. **Net: ~150-180 LoC.**

Risk: medium. Lean 4 macros for tactic patterns are well-supported,
but reliable elaboration around obtain := name with name mangling is
finicky — debugging when it fails is painful, and @[expose] def
definitional equality matters.

Recommendation: **Pursue if the team has macro-Lean expertise.** The
saving is real and concentrated. Otherwise skip — the boilerplate is
mechanical but readable, and the macro debugging cost can exceed the
LoC saving.

### 2.2 Candidate (a-2): Unify _at_pc and _at_pc_with_labels

Currently coreCFGToGotoBlockStep_location_at_pc (~100 LoC) and
_with_labels (~100 LoC) are near-duplicates. The latter is a
strengthened existential. Same applies to blocksFoldlM_layout_location
and _with_labels in FoldAndDecompose.lean.

Sketch: drop _at_pc and use _with_labels everywhere (labels = [l] is
a free side-condition consumers do not need to use). Or: extract the
witness program once and project both shapes.

Estimated saving: 100 LoC at block-step layer + 80 LoC at blocks-fold
layer = **~180 LoC**.

Risk: low. The strengthened version subsumes the weaker one;
spot-check shows _with_labels is the more general form and consumers
of _at_pc just discard the extra fact.

Recommendation: **Pursue.** Cleanest win in the (a) bucket.

### 2.3 Candidate (a-3): omega-based PC normalization

The PC arithmetic per se (e.g., pc + 1 + cmdsPrefixInstrCount blk.cmds k +
gotoInstrCount inner = pc + 1 + cmdsPrefixInstrCount blk.cmds (k+1))
already uses omega after a rw [h_prefix_step]. Similar identities
recur ~10 times across block_body_cmds_simulation and the
blocksFoldlM_layout_* proofs.

A simp set with key normalization lemmas (cmdsPrefixInstrCount_succ,
DetBlockBodyInstrCount_eq_cmdsPrefixInstrCount_at_length, etc.) could
collapse these to 1-2 lines each.

Estimated saving: ~50-100 LoC across (a) ~1,500.

Risk: low. simp set expansion is well-understood. The risk is
incidental — adding too-aggressive lemmas could break proofs that
expected a different rewrite order.

Recommendation: **Pursue.** Mechanical and easy to add incrementally.

### 2.4 Candidate (b-1): Binary-property combinator (Class C)

L2 sketched this but L3 declined:

    class BlocksFoldClosedPair
        (P_inv : Array Instruction -> Prop)         -- e.g., size_eq
        (P     : Array Instruction -> Prop) where   -- e.g., locationNum_eq
      toGotoInstructions :
        forall T fname c trans ans,
          Imperative.Cmd.toGotoInstructions T fname c trans = .ok ans ->
          P_inv trans.instructions -> P_inv ans.instructions /          (P trans.instructions -> P ans.instructions)
      -- ... same for cmdStep, cmdsFold, emitLabel, emitCondGoto,
      --     emitUncondGoto, endFunction, blockStep, blocksFold

This would absorb the parallel _size_eq + _locationNum_eq_index chains
across Preservation.lean (~500 LoC of paired lemmas), StepPreservation.lean
(~400 LoC of paired blockstep+blocksfold lemmas), and FoldAndDecompose.lean
(~150 LoC of paired patcher lemmas).

Estimated saving: ~400-500 LoC absorbed; combinator cost ~150-200 LoC;
**net: ~200-300 LoC**.

But L2 already estimated this at ~400 LoC and said the combinator-API
tax (h_admitted and h_size plumbing through every closure, doubled
signatures, plus the GotoTransform-vs-array mismatch the L3 worker
noted) makes it borderline.

Risk: medium-high. The combinators API surface doubles every closure,
and h_admitted thread-through is non-trivial because the combinator
still needs to know cmdStep_call (the cmd is admitted) constraint to
discharge the FUNCTION_CALL case. The Lean 4 elaborator complications
L3 hit (abbrev vs def, eta-expansion of implicit binders) would
multiply with two coupled predicates.

Recommendation: **Borderline. Pursue only if the team has 1-2 weeks to
invest and accepts that the saving may end up in the 100-200 LoC
range** (matching L3 experience: projection 360 -> reality 196 for
GotoTargetProvenance because the cmd-shape dispatch could not be
absorbed). The 200-300 LoC saving estimate has the same risk profile
that turned L3 1,200 LoC projection into a 201 LoC outcome.

### 2.5 Candidate (b-2): Patcher-chain unification (cross-file)

Three files have parallel patcher chains:
- NoDead.patchGotoTargets_preserves_no_dead (10 LoC; uses
  patchGotoTargets_preserves_type from Preservation.lean).
- WfLabelMapAgree.patchGotoTargets_preserves (15 LoC; uses
  patchGotoTargets_preserves_type *and* _preserves_labels).
- GotoTargetProvenance.patchGotoTargets_target_some_in_patches (~50 LoC
  plus ~150 LoC of supporting last_occurrence_split / patch_foldl_*
  helpers).

Sketch: a patcher-respects-partial-instruction combinator that exposes
for every patched index, exists pre-instruction such that
post-instr.{type, labels} = pre-instr.{type, labels} and
post-instr.target = some _, as a *single* observation. Consumers
project the pieces they need.

Estimated saving: ~50-80 LoC. The reverse-direction
(target_some_in_patches) for GotoTargetProvenance is genuinely distinct
work and **cannot be unified**.

Risk: low for the forward chain; the reverse chain is structurally
unique.

Recommendation: **Marginal**. The forward chain is already short;
unifying it saves ~60 LoC and adds 1 layer of indirection.

### 2.6 Candidate (b-3): Unified blocksFoldlM_layout_* cons-step skeleton

The trio blocksFoldlM_layout_location, _with_labels, _layout_finish
all follow the identical cons-step pattern:
- size_eq propagation through coreCFGToGotoBlockStep_preserves_size_eq
- admitted-rest propagation through filter
- distinct-rest propagation through BlockLabelsDistinct_tail
- (l, blk) = hd or in rest rcases
- head case: invoke coreCFGToGotoBlockStep_*_at_pc, propagate through
  blocksFoldlM_instructions_prefix? and
  blocksFoldlM_labelMap_preserves_external.
- tail case: IH.

Sketch: a higher-order block-fold lifter that takes a per-block lemma
plus a post-propagates lemma and concludes the existential over
(l, blk) in blocks.

Estimated saving: ~100-130 LoC across the trio (240 LoC -> ~120 LoC).
Combinator cost: ~30-50 LoC.

Risk: medium. The propagation lemmas
(blocksFoldlM_instructions_prefix?, blocksFoldlM_labelMap_preserves_external)
need to be threaded through the lifter as additional arguments — more
parameters per call — and per-property P_at_pc shapes vary in subtle
ways (e.g., _finish carries a transfer = .finish md precondition that
others do not).

Recommendation: **Pursue if pursuing (b-1).** They share the abstract-
a-recurring-fold-step-skeleton theme, and combined they could save
~300-400 LoC. Standalone, this one is borderline.

### 2.7 Candidate (b-4): Tactic for the block-step intro boilerplate

This 5-line pattern starts ~10 lemmas in StepPreservation.lean and
~5 lemmas in FoldAndDecompose.lean:

    unfold Strata.coreCFGToGotoBlockStep at h_run
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
    generalize h_inner :
      blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
    match inner, h_inner with
    | .ok trans2, h_inner => ...
    | .error _, _ => simp at h_run

A block_step_intro macro could collapse this to one line. Saving:
~5 LoC x 15 lemmas = ~75 LoC, minus ~30 LoC for the macro. **Net: ~45 LoC.**

Risk: low.

Recommendation: **Pursue if (a-1) macro is on the table.** Combined
they share infrastructure and conventions; alone, this one is
marginal.

### 2.8 What does NOT compress

To balance the candidates above, here is what reading the code shows
*cannot* compress without changing the proof statement or the underlying
semantics:

- **PcInversion witness-program plumbing.** BodyPcCovered carries pgm
  plus 3 evaluators plus 5 auxiliary hypotheses (h_admitted, h_invariant,
  h_expr_corr, h_tx_eq, h_prefix). Any combinator must thread all of
  these through the typeclass. L2 analysis of Class E is correct: this
  is an irreducible API tax, not boilerplate. PcInversion 999 LoC is
  ~70-80% structural.
- **The patcher reverse-direction proof in GotoTargetProvenance.lean**
  (lines 142-300, ~160 LoC). The last_occurrence_split +
  patch_foldl_target_at_last chain is genuinely the meat of the two-pass
  argument from doc section (c). Cannot be absorbed by any abstraction
  without changing the translator design.
- **The WellFormedTranslation discharge as a whole.** size_eq +
  locationNum + 7 layout fields constitute an irreducible everything-
  we-need-to-know-about-the-translator-output. Each field has its own
  shape; the only real saving is collapsing the duplicated _at_pc
  family (Candidate a-2) and pairing size_eq with locationNum
  (Candidate b-1).
- **single_cmd_simulation** (CoreCFGToGOTOCorrect.lean:178-289, ~110
  LoC). The 7-arm dispatch over EvalCmd x CmdEmittedAt is not
  collapsible — each arm uses a different StepGoto constructor with
  different evaluator hypotheses (step_decl + step_assign for init_det,
  step_decl for init_nondet, step_assign_nondet for set_nondet, etc.).
  **This is genuinely structural.**
- **block_body_cmds_simulation strong induction on cs.length.** As doc
  section (g) notes, the use of Nat.strongRecOn is forced by Lean
  structural-recursion limitations on cs.drop k. The bookkeeping it
  adds is ~10-15 LoC of h_size, h_tail_size threading. Saved by
  *changing how the proof is structured*, not by abstraction.

## 3. Verdict

### What fraction of (a)+(b) LoC is boilerplate?

**Roughly 10-15%, not 30%.** Concrete tally of the candidates above
that I would characterize as abstraction-eliminable boilerplate:

- (a-2) _at_pc family duplicates: ~180 LoC saving.
- (a-3) omega/simp PC normalization: ~50-100 LoC saving.
- (b-2) Forward patcher chain unification: ~50-60 LoC saving.
- (b-3) blocksFoldlM_layout_* cons-step skeleton: ~100-130 LoC.
- (b-4) block_step_intro macro: ~45 LoC.
- Plus partial wins from (a-1) macro for cmd dispatch: ~150-180 LoC.

That sums to **~575-700 LoC of clean boilerplate compression** — roughly
**12-14% of (a)+(b) 4,900 LoC**.

(b-1) the binary-property combinator could push the savings up by
another **~200-300 LoC**, bringing the total to ~775-1,000 LoC,
**~16-20%** of (a)+(b) LoC. But (b-1) carries significant risk and is
structurally similar to L3 port that delivered 201 LoC against a
1,200-1,600 LoC projection.

### What fraction is genuinely structural?

**Roughly 80-85%.** The bulk of (a) is real PC arithmetic per transfer
arm + per-cmd-shape, none of which is parallel because the arms differ
in trace length and pc-target structure. The bulk of (b) is per-property
step-by-step preservation where each property predicate signature
differs in genuinely non-uniform ways:

- size_eq (size = nextLoc, takes h_size as input).
- locationNum_eq_index (binary-coupled with size_eq).
- HasNoDead (pure array -> Class A, fits BlocksFoldClosed).
- NoGotoHasTarget (Class D — patcher *breaks* it).
- LocationsTrackLabelMap (Class B — predicate over (array, labelMap)).
- BodyPcCovered (Class E — depends on δ, δ_goto, δ_goto_bool, witness pgm,
  plus 5 auxiliary hypotheses per closure).
- EveryGotoTargetIsLabelMapEntry (post-patcher reverse direction).
- labelMap_inj, entry_in_map, labelMap_total (live on hashmap operations).

These do not collapse into a single abstraction without sacrificing
the unifying API. L2 Class A through Class E taxonomy showed that there
is no single combinator: the predicate space is **irreducibly
heterogeneous**, and L3 measured saving of +201 LoC (against +1,200 to
+1,600 projected) confirms that even with the right abstraction, only
Class A predicates fit cleanly.

### Realistic upper bound on LoC savings, ~2 weeks of refactor time

**~600-1,000 LoC, with high uncertainty toward the lower end.**

Concretely:
- **Conservative estimate (Tier-1, ~1 week, low risk):** Pursue (a-2),
  (a-3), (b-2), (b-4). Saves ~325-435 LoC. Most of these are mechanical
  and low-risk; the main cost is review time.
- **Medium estimate (Tier-2, ~2 weeks, moderate risk):** Add (a-1) and
  (b-3). Saves ~575-745 LoC total. Tactic macros plus the
  blocksFoldlM_layout skeleton lifter — both require a few days to
  design and debug.
- **Aggressive estimate (Tier-3, ~3+ weeks, high risk):** Add (b-1)
  the binary-property combinator. Theoretical reach: ~775-1,000 LoC.
  But this is *exactly* the kind of refactor L3 attempted with a
  1,200-1,600 LoC projection and delivered 201 LoC. Setting expectations
  at 200-400 LoC of additional saving (against the +200-300 LoC
  theoretical) is more realistic, taking the total to ~775-1,135 LoC —
  only marginal improvement over Tier-2 for a significant time
  investment.

### The honest answer to the user intuition

The user intuition that (a) and (b) seem like boilerplate that could
be simplified is **partly right — for ~12-14% of the LoC (~575-700 LoC
of clean compression candidates).** It is **largely wrong for the
bulk** of the 4,900 LoC, which represents:

1. The 7-arm cmd-shape dispatch (genuinely 7 cases, each with its own
   StepGoto rule), the 3-arm transfer dispatch (genuinely 3 cases,
   each with different trace shape), and per-property step preservation
   across the 9-step fold chain.
2. The patcher two-pass discipline (forward: target = none invariant;
   reverse: target-some-implies-in-patches).
3. The five distinct predicate-signature classes (A-E) the preservation
   chain has to cover, only one of which (Class A) fits a single
   combinator.

The user 30% boilerplate intuition would be right if all 9-step
preservation chains used the same predicate signature. They do not.
L2 audit and L3 empirical outcome both confirm this. What looked like
opportunity in the doc every-property-is-a-9-step-chain prose is, in
code, 5 different chains for 5 different predicate classes, only one
of which is unary.

The marginal value of further refactoring (~600-1,000 LoC over 2-3
weeks) is real but small. **The proof is mostly as compressed as it
can be without changing the translator design or the
WellFormedTranslation predicate shape.**
