# Core → CBMC GOTO: Why the Simulation Proof Isn't Trivial

**Branch:** `htd/unstructured-to-goto`
**Last refreshed:** 2026-05-23

A common reaction when looking at `Strata.Core.DetCFG` and CBMC's
GOTO format side by side is: "These two are nearly the same thing.
Both are flat instruction streams with integer PCs. The translator
is a flatten-and-relabel pass. Surely the simulation proof is mostly
trivial?"

That intuition is not wrong. The forward-simulation **kernel** —
the central induction that walks one source command and emits the
corresponding GOTO instructions — is roughly 100 lines.

The proof is ~20,600 lines of Lean.

This document explains where the rest lives, with concrete examples
from the actual proof.

---

## 1. The naive picture

Source `Core.DetCFG` is a list of labelled blocks. Each block is a
list of `Core.Command`s followed by a transfer (`condGoto`,
`finish`, …). Target CBMC GOTO is a flat `Array Instruction` indexed
by integer PCs. The translator
(`Strata.coreCFGToGotoTransform`) walks the blocks, emits
instructions in order, builds a `labelMap : String → Option Nat`
recording each block's entry PC, and patches GOTO targets at the
end.

Forward simulation, in the obvious form: starting from
`(.cont entry σ false)` on the source side and `pc = labelMap entry`
on the target side, single-step both machines and show the post-step
configurations correspond. Pattern-match on `Core.Command`, fire the
matching `StepGoto` rule, take the next step.

That is, in fact, what the proof does. The actual induction
(`cfgStepStar_to_gotoStar` in
`CoreCFGToGOTOCorrect.lean:767-874`) is short and unsurprising. The
single-cmd dispatch (`single_cmd_simulation` higher up the same
file) is also short. The block-level induction
(`block_body_cmds_simulation`, lines 315-568) is ~250 lines, mostly
PC bookkeeping.

The bulk of the 20,600 lines is in the structural facts these short
inductions implicitly rely on.

---

## 2. Where the difficulty actually lives

### a) PC arithmetic, threaded across seven Cmd shapes and three transfer shapes

The block-induction step says "after `k` admitted commands of block
`(l, blk)`, the GOTO PC is exactly
`pc + 1 + cmdsPrefixInstrCount blk.cmds k`, where `pc = labelMap l`."
This is the connecting tissue between the source-side `EvalDetBlock`
derivation and the target-side `StepGotoStar`.

Every command shape contributes a different number of GOTO
instructions: `init _ _ (.det e)` emits two (a DECL plus an
ASSIGN); `init _ _ (.nondet)` emits two (DECL plus an ASSIGN-Nondet);
plain `set` emits one; `assert` emits one; `assume` emits one;
`cover` emits one. The transfer adds its own count
(`condGoto` emits two: a fallthrough conditional plus an
unconditional jump; `finish` emits one END_FUNCTION). All of this
lives in `cmdsPrefixInstrCount`, `DetBlockBodyInstrCount`,
`Imperative.Cmd.gotoInstrCount`.

The inductive step in `block_body_cmds_simulation`
(`CoreCFGToGOTOCorrect.lean:413-451`) has to prove the rewrite

```
pc + 1 + cmdsPrefixInstrCount blk.cmds k + Cmd.gotoInstrCount inner
  = pc + 1 + cmdsPrefixInstrCount blk.cmds (k + 1)
```

— a `List.foldl_append`/`omega` exercise, applied at every step of
the cmds-fold. That is one rewrite. The block body has 250 lines
because the same skeleton recurs three times (one per transfer
shape), each time reading off the cmds-prefix count, then applying
the per-transfer layout lemmas
(`wf.layout_cond_goto`, `wf.layout_cond_goto_guards`,
`wf.layout_finish`) to extract the emitted PCs.

This generalises. The translator is a `foldlM` chain
(blocks → cmds → emit-helpers → patcher). Anywhere a property has to
follow the PC, the proof is a chain of rewrites that walk the same
skeleton.

Volume contribution: ~1,500 LoC distributed across
`block_body_cmds_simulation`, the `WellFormedTranslation.layout_*`
fields, and the body-instruction-count lemmas in
`CoreCFGToGotoTransformWF/`.

### b) The translator is a `foldlM`, so every property needs a 7-step preservation chain

The translator is

```
cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName) ⋯
  >>= patchGotoTargets
```

with `coreCFGToGotoBlockStep` itself

```
emitLabel l ; cfg.cmds.foldlM coreCFGToGotoCmdStep ; emit transfer
```

and the `cmdStep` further dispatching to either
`Cmd.toGotoInstructions` (for `.cmd` commands) or a
function-call branch (for `.call`).

To prove a structural property `P : Array Instruction → Prop` of
`ans.instructions` you have to prove `P` is preserved by **every
layer** of the fold. `CoreCFGToGotoTransformWF/Preservation.lean`
contains the basic chain for the `size_eq` and `locationNum_eq_index`
properties; for one property the chain is:

```
toGotoInstructions_preserves_P
coreCFGToGotoCmdStep_preserves_P
cmdsFoldlM_preserves_P
emitLabel_preserves_P
emitCondGoto_preserves_P
emitUncondGoto_preserves_P
endFunction_emit_preserves_P
coreCFGToGotoBlockStep_preserves_P
blocksFoldlM_preserves_P
patch_one_preserves_P     ⎫
patchGotoTargets_preserves_P  ⎬ patcher chain
                                ⎭
```

That is the 7-step closure on a property over the blocks-fold, plus
2-3 patcher lemmas. **Roughly 9-12 preservation theorems per
property**, even when each individual theorem is one line of `simp` /
`unfold`. Some are not one line: the `emitCondGoto` step has to
account for the post-condition `target = none` invariant, and the
patcher analysis needs reverse-direction lemmas.

`BlocksFoldClosed.lean` is the abstraction over this skeleton: a
typeclass with six "leaf" closures (lines 63-90) plus three derived
theorems that do steps 7-9 generically. `NoDead`,
`GotoTargetProvenance`, and `WfLabelMapAgree` use it. But the
patcher chain still differs per predicate, so each consumer file
duplicates the patcher reasoning.

Volume contribution: `CoreCFGToGotoTransformWF/` is 6,720 LoC,
roughly half of which is preservation chains. `BlocksFoldClosed`
saves duplication where it applies but doesn't eliminate it.

### c) Cross-block GOTO targets force a two-pass translator

When `coreCFGToGotoBlockStep` emits a conditional `goto L`, the
target block `L` may not have been translated yet — its `labelMap`
entry doesn't exist. The translator's response is to emit GOTOs with
`target = none` and queue a "pending patch" record
`(emitted_pc, target_label)`. After the blocks-fold completes,
`patchGotoTargets` walks the pending-patches list, looks up each
target label in the now-complete `labelMap`, and rewrites the
`target` field of the emitted GOTO.

Two structural facts have to be proved separately for this design:

1. **Forward direction.** The blocks-fold maintains the invariant
   "no GOTO has `target = some _`"
   (`NoGotoHasTarget'` in `GotoTargetProvenance.lean:36`). The
   patcher fills in targets only at indices that came from a queued
   patch record. The patcher also preserves
   `size_eq`, `locationNum_eq_index`, and `labelMap`'s contents.
2. **Reverse direction.** Given a GOTO instruction at PC `pc` in
   the final array with `target = some t`, you have to show `t` is
   actually some block's `labelMap` entry. This is
   `patchGotoTargets_target_some_in_patches`
   (`GotoTargetProvenance.lean:294`) and downstream.

Plus: the `EveryGotoTargetIsLabelMapEntry` predicate that the WF
witness exposes is the reverse-direction post-condition of the
patcher, so the WF discharge has to thread through the patch
queue. `GotoTargetProvenance.lean` is 567 lines for this alone.

Volume contribution: `GotoTargetProvenance.lean` (567) +
`PcInversion.lean` (999, mostly DECL/ASSIGN-side analogues) =
~1,500 LoC for the two-pass discipline.

### d) Source and target use different value domains, with parametric evaluators

The source semantics
(`Core.EvalCmd`/`Core.CoreCFGStepStar`) thread an
`Imperative.SemanticStore Core.Expression` whose values are
`Core.Expression.Expr` — that is, source-language expression terms.
The target semantics (`StepGoto`, `StepInstr` in
`SemanticsTautschnig.lean`) thread a different store whose values
are CBMC `Value`s (`vBool b`, `vInt n`, `vBV w bv`, `vArray …`).

The simulation has to bridge these. Two approaches coexist:

* The **`StepGoto` layer** stays in `Core.Expression.Expr`-valued
  stores on both sides. This is what
  `coreCFGToGoto_forward_simulation`
  (`CoreCFGToGOTOCorrect.lean:893`) proves.
* The **`StepInstr` / `ExecProg` layer** uses CBMC's concrete
  `Value`-typed store. To get there, we need
  `StoreCorr nameMap σ_imp σ_goto` plus a
  `SemanticsTautschnig.ValueCorr P` instance plus a
  `Function.Injective nameMap` premise (so that distinct source
  identifiers map to distinct GOTO symbol names). Each
  `StepGoto` constructor has a per-rule bridge in `Bisim.lean`:
  `stepGoto_assign_to_stepInstr`,
  `stepGoto_decl_to_stepInstr`,
  `stepGoto_assign_nondet_to_stepInstr`, … — 14 bridges total
  across 587 lines, each of which has to commute the store-update
  with the value bridge.

Beyond the store bridge, the *evaluators* `δ` and `δ_goto` are
themselves parametric. They are abstract `SemanticEval` /
`SemanticEvalGoto` parameters supplied at the top of every theorem.
The proof can't compute with them; it only knows what the
caller-supplied evaluator-correspondence hypotheses say. The
`ExprTranslated` predicate
(`CoreCFGToGOTOInvariants.lean`) records the per-expression
agreement, and `ExprTranslationPreservesEvalBoolInt.lean` discharges
it for the bool+int fragment in 1,198 LoC by structural induction
over `LExpr`, given a `BoolIntOpHypotheses` bundle of per-operator
soundness facts. The bundle (lines 145-330) has roughly one field
per supported operator — ~25 fields — because there is no way to
collapse them: each integer operator has its own GOTO operator-id
(`Int.Add → multiary .Plus`,
`Int.DivT → binary .Div`, …) and the evaluators agree on each pair
*by axiom*, not by structure.

Some hypotheses provably can't move down. For example,
`h_init_extension` (the δ_goto evaluator is monotone across an
`InitState` mutation that introduces a fresh variable) is needed by
the block-induction kernel but cannot be derived from the
translator's structure — it's a property of `δ_goto` itself. The
same is true of the `BoolIntOpHypotheses` fields, the
`StoreCorr.update_*` axioms in the value-bridge layer, and the
trace-pinning hypotheses below. The `_v6` / `_v7` theorems in
`CoreCFGToGOTOConcrete.lean` collect all of these into a single
hypothesis surface and show that surface is irreducible: it lives
where the proof can't reach it.

Volume contribution: ~1,800 LoC
(`ExprTranslationPreservesEvalBoolInt` 1,198 +
`Bisim` 587 + value-bridge overhead).

### e) `step_assign_nondet` does double duty by language design

The `init _ _ (.det e)` Cmd shape compiles to **two** GOTO
instructions: a DECL (introduces the variable) followed by an ASSIGN
(initialises it from `e`). The `init _ _ (.nondet)` shape also
compiles to two: a DECL followed by an ASSIGN-Nondet (the rhs is a
distinguished `side_effect Nondet` expression, picked up by the
ASSIGN-Nondet step rule).

Naively, the source-side `eval_init_det` matches the GOTO trace
"DECL then ASSIGN", and `eval_init_nondet` matches "DECL then
ASSIGN-Nondet". The catch: the GOTO `step_assign_nondet` rule, as
originally written by tautschnig, was triggered by *any* ASSIGN
where the RHS lacked a deterministic value — including the
mid-instruction "no-op" padding step that the `eval_init_det`
source-side rule produces if you decompose its derivation finely.
Distinguishing the two cases at the consumer site cost ~100 LoC of
case analysis on every consumer.

The proof's response was to tighten the `StepGoto.step_assign_nondet`
constructor to carry the rhs-shape witness directly
(`Semantics.lean:196-203`):

```lean
  | step_assign_nondet :
    pgm.instrAt pc = some instr →
    instr.type = .ASSIGN →
    instr.code = Code.assign lhs rhs →
    rhs.id = .side_effect .Nondet →
    UpdateState P σ x v σ' →
    StepGoto P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ' failed)
```

That single `rhs.id = .side_effect .Nondet` premise rules out the
no-op padding case structurally and saves the case analysis at every
consumer site. But the mismatch between the source-side trace and
the target-side rule was real — it shows up whenever the source
rule and the target rule are not in 1:1 correspondence, which is
already a source of complexity.

Volume contribution: ~200 LoC across `Bisim`, the constructor
tightening, and the consumer sites that had to be updated to use
the strict form.

### f) Trace-level pinning is irreducible at the WF layer

`WellFormedTranslation` is a universal predicate over CFG blocks: it
says "for every `(l, blk) ∈ cfg.blocks` and every `k`, the layout
holds." But the simulation kernel walks a *specific* trace — a
specific `EvalDetBlock` derivation that fires a specific
`UpdateState` on a specific variable. To bridge "the WF layout
emitted ASSIGN with lhs symbol `s`" to "the source-side
`UpdateState` mutates the *same* variable", the proof needs a
*pinning* hypothesis: the trace's `UpdateState` is in fact for the
variable that the translator emitted at this PC.

These hypotheses have to be supplied by the caller because the WF
predicate doesn't see the trace. There are three of them on `_v6`
and `_v7` (`CoreCFGToGOTOConcrete.lean:269-310`):
`h_decl_x_pinned`, `h_assn_x_pinned`, `h_assn_rhs_pinned`. Each is
a roughly 10-line forall-statement that says "if the GOTO program
has a DECL/ASSIGN at PC `pc` with lhs symbol `s`, and the source-
side trace fires an `InitState`/`UpdateState`, then `s` is the
identifier the trace mutates."

For the standard caller these are trivial — both ends agree on
which variable each command refers to. But "trivial" requires
showing the trace's variable equals the translator's emitted
variable, which crosses the WF/trace boundary the proof
deliberately doesn't span.

Volume contribution: ~50 LoC of hypothesis-surface plumbing
distributed across `_v6` / `_v7` and downstream.

### g) Lean-mechanization tax

Even the obvious things take real LoC in Lean. Three recurring
costs:

* **Constructor-injection chains.** Every time the proof case-splits
  on `c₁ = .cont l σ failed` and a hypothesis says
  `c₁ = .cont l' σ' failed'`, you get back three `Option.some.inj`
  /`subst` rewrites. The codebase added the `inj_subst` macro
  (`Tactics.lean:22`) just to compress this idiom. There are dozens
  of uses.
* **Mutual induction.** `CoreCFGStepStar` is mutually inductive
  with `Core.EvalDetBlock`. Lean's `induction` tactic doesn't apply
  to mutual inductive types. The kernel uses
  `Core.CoreCFGStepStar_rec` directly with an explicit motive
  (`CoreCFGToGOTOCorrect.lean:804-815`), which adds ~10 LoC to a
  case split that would be `cases h_run` in a non-mutual setting.
* **Strong induction.** The cmds-fold induction in
  `block_body_cmds_simulation` uses
  `Nat.strongRecOn` rather than structural recursion because the
  recursive call has to land on a strictly shorter `cs` for a
  `cs := blk.cmds.drop k` suffix and Lean's structural recursion
  can't see through the `drop`. That adds the `h_size : cs.length`
  bookkeeping and the `h_tail_size : cs_tail.length < n` discharge.

Volume contribution: hard to pin precisely, but visible everywhere —
maybe 5-10% of every file is the tax of working in Lean rather than
on paper.

### h) Some accumulated cruft

Not all of the 20,600 LoC was necessary. A recent audit
(`docs/historical/CoreToGOTO_ShrinkAudit.md`) identified ~2,500
LoC of removable accumulation: dead waypoint theorems
(`_v2`/`_v3` of the concrete simulation), parallel preservation
skeletons in `NoDead`/`GotoTargetProvenance` that could share a
combinator, and a few ~140-LoC duplicate patcher lemma blocks. A
follow-up cleanup pass closed most of these.

The honest accounting is: of ~20,600 LoC, roughly 10-15% was
preventable accumulation; the rest was real structural work.

---

## 3. What the proof bought

For the 20,600 lines, the deliverable is:

* A closed forward-simulation theorem
  (`coreCFGToGotoTransform_forward_simulation_concrete_v7` in
  `CoreCFGToGOTOConcrete.lean:521`) under the standard Lean axiom
  set `[propext, Classical.choice, Quot.sound]`. No
  project-internal axioms.
* The theorem is instantiated against the actual
  `Strata.coreCFGToGotoTransform` output, not against an idealised
  abstract translator.
* The `WellFormedTranslation` hypothesis is built internally from
  the strengthened structural theorem; the caller never sees it.
* Every remaining hypothesis on `_v7`'s surface is one of:
  - **Trivial-by-construction** for any standard initial state
    (e.g., `h_init_size`, `h_init_no_dead` for
    `trans₀.instructions = #[]`).
  - **Caller-irreducible** — the kind of fact the proof
    deliberately doesn't span: B3 expression-side correspondence
    (`h_red`, `h_op`, `h_uniform`, `h_commutes_not`), trace-level
    pinning (`h_decl_x_pinned`, `h_assn_x_pinned`,
    `h_assn_rhs_pinned`), value-side correspondence
    (`h_decl_empty_value`, `h_assign_value_corr`,
    `h_assign_nondet_value_corr`), evaluator monotonicity
    (`h_init_extension`), and the consumer's own source-side run.

Crucially: there is no remaining hypothesis on `_v7` that is a
*structural* obligation on the translator. Any future tightening
must come from changing the theorem statement, the translator, or
the underlying semantics — not from further proof work on the same
goal.

---

## 4. The "easy" part that wasn't

The 20,600 LoC is **not** in proving "Core CFG ↔ GOTO simulation
works." That kernel — `cfgStepStar_to_gotoStar` in
`CoreCFGToGOTOCorrect.lean:767-874` — is ~107 lines including
docstrings and comments, and the actual case analysis is shorter.
Together with the `single_cmd_simulation` dispatch and the
`block_body_cmds_simulation` block-level induction, the
*simulation-shaped reasoning* is well under 1,000 LoC.

The 20,600 LoC is in proving every structural fact that simulation
implicitly relies on:

| Layer | LoC | What it does |
|---|---|---|
| `WellFormedTranslation` discharge against the actual translator (`CoreCFGToGotoTransformWF/` plus per-property files) | ~6,700 | Every layout fact is true for `coreCFGToGotoTransform`'s output |
| B3 expression-side correspondence (`ExprTranslationPreservesEvalBoolInt`) | ~1,200 | Per-operator soundness for the bool+int fragment |
| Per-`StepGoto` bridge to the `StepInstr`/`ExecProg` semantics (`Bisim`, `SteppingBridgesDischarge`, `TranslatorBridgeHypsDischarge`, `InstructionLookups`) | ~1,600 | Walking from `δ_goto`-valued stores to `Value`-typed CBMC stores |
| Layout closures, PC inversions, no-dead/no-goto-target preservation, labelMap-uniqueness (`PcInversion`, `GotoTargetProvenance`, `NoDead`, `WfLabelMapAgree`, `BlocksFoldClosed`, `CmdProvenance`) | ~3,000 | Per-property preservation chains over the foldlM + patcher |
| Concrete-version assembly (`CoreCFGToGOTOConcrete`, `CoreCFGToGOTOCorrectStore`) | ~950 | Wiring everything together at the public theorem boundary |
| The simulation kernel itself (`CoreCFGToGOTOCorrect`) | ~930 | The naive picture, made precise |

The "Core and GOTO are basically the same" intuition is correct.
What it underestimates is: making "basically" precise — making it
machine-checked across a `foldlM` translator, two value domains,
two parametric evaluators, a two-pass label resolver, and a
universally-quantified WF predicate — costs 20× the kernel that
the intuition is about.

---

## See also

* [`CoreToGOTO_CurrentStatus.md`](CoreToGOTO_CurrentStatus.md) —
  canonical proof status doc with theorem chain, hypothesis surface,
  and codebase layout.
* [`CoreToGOTO_SemanticsComparison.md`](CoreToGOTO_SemanticsComparison.md)
  — comparison with `tautschnig/goto-semantics`'s alternative
  semantics.
* [`historical/CoreToGOTO_CorrectnessAnalysis.md`](historical/CoreToGOTO_CorrectnessAnalysis.md)
  — full-stack analysis of correctness levels (the source for the
  B3/value-bridge category labels used here).
