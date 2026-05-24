# W1 — WfLabelMapAgree preservation combinator port

**Worker:** W1.
**Branch base:** `htd/unstructured-to-goto` (commit `37ac876c9`, after L3).
**Scope:** apply L3's `BlocksFoldClosed` combinator to
`Strata/Backends/CBMC/GOTO/WfLabelMapAgree.lean` (698 LoC). Decide
whether the existing combinator can be reused (with a clever predicate
reshape, **Option B**), needs a binary extension (**Option A**), or
should be skipped (**Tier 3**).

**Verdict:** **Tier 3 — skip with documented rationale.** The
abstraction tax of any combinator extension equals or exceeds the
local LoC saving in WfLabelMapAgree. The 698 LoC file stays as-is.

## Plan and approach explored

The `LocationsTrackLabelMap` predicate is binary:
`(Array Instruction × HashMap String Nat) → Prop`. Per L2's
classification (Class B), it doesn't fit `BlocksFoldClosed`'s unary
`P : Array Instruction → Prop` shape. **However** the hashmap is
*invariant* through every translator step except `emitLabel`.

I prototyped **Option B (predicate reshape)**: define an array-level
form `LocationsTrackLabelMap' (labelMap : HashMap) (a : Array Instruction)`
parameterised by a fixed labelMap, then build a small
`CmdsFoldClosed`-style subset combinator (just `toGotoInstructions`
and `cmdStep_call`) so the cmds-fold sub-chain (steps 1-3 of the L2
9-step matrix) could be derived. The cmds-fold uses `IsSafe = (· ≠ .LOCATION)`
because every instruction the cmds-fold pushes (DECL, ASSIGN, ASSERT,
ASSUME, FUNCTION_CALL) is non-LOCATION.

The full `BlocksFoldClosed` cannot be instantiated for a fixed
labelMap because `emitLabel` genuinely changes both `trans` *and*
`labelMap` together. So the block-step and outer-fold lemmas have to
stay manual, threading labelMap evolution explicitly.

## Numbers (prototype that I built and reverted)

| File | Before | After Option B | Δ |
|---|---|---|---|
| `BlocksFoldClosed.lean` (combinator) | 393 | 505 | **+112** |
| `WfLabelMapAgree.lean` | 698 | 585 | **−113** |
| **Net** | 1091 | 1090 | **−1** |

The internal LoC savings inside `WfLabelMapAgree.lean` were real
(113 LoC dropped — `toGotoInstructions_preserves` ~80, plus
`coreCFGToGotoCmdStep_preserves` ~15, plus `cmdsFoldlM_preserves` ~29),
but the cost of the `CmdsFoldClosed` extension to `BlocksFoldClosed.lean`
matched that almost exactly:

* `CmdsFoldClosed` typeclass declaration (~15 LoC)
* `BlocksFoldClosed → CmdsFoldClosed` bridge instance (~3 LoC)
* `coreCFGToGotoCmdStep_preserves` derived theorem (~15 LoC)
* `cmdsFoldlM_preserves` derived theorem (~22 LoC)
* `CmdsFoldClosed.ofPushSafe` helper (~75 LoC, the per-cmd-shape
  dispatch — the cost of a Class-B-style entry point that takes only
  the 5 cmd-fold vocabulary facts, not the 8 full BlocksFoldClosed ones)

Even after sharing — making `BlocksFoldClosed.ofPushSafe` delegate to
`CmdsFoldClosed.ofPushSafe` for its cmd-related fields and avoiding
the per-cmd-shape duplication — the combinator file still grew by
~112 LoC for the new typeclass + bridge + cmds-fold-only ofPushSafe.

The verified prototype build was green (`lake build` clean across all
227 jobs) and axiom counts on `_v6`/`_v7` were unchanged
(`[propext, Classical.choice, Quot.sound]`). I reverted the prototype
because the net saving doesn't justify the abstraction.

## Why the saving is so tight

L2 projected ~230 LoC of saving for WfLabelMapAgree. The reality:

1. **Only 124 LoC of step-lemma boilerplate is dedup-able** — the
   `toGotoInstructions_preserves` cmd-shape dispatch (~80 LoC), the
   `coreCFGToGotoCmdStep_preserves` dispatch (~15), and the
   `cmdsFoldlM_preserves` induction (~29). These collectively form
   "steps 1-3" of the L2 9-step matrix.

2. **Steps 4-9 (emitLabel through blocksFoldlM) all have to thread
   labelMap evolution explicitly** because the labelMap actually
   changes at `emitLabel`. None of these can be absorbed by a unary
   `Array Instruction → Prop` combinator. They're not boilerplate —
   they're load-bearing labelMap-arithmetic proofs (e.g., 54 LoC for
   `emitLabel_preserves` alone, none of which is dedup-able).

3. **The cost of any `CmdsFoldClosed`-style combinator extension is
   ~112 LoC** — typeclass declaration + bridge + two derived theorems
   + cmds-only `ofPushSafe`. The `ofPushSafe` itself is the dominant
   cost (~75 LoC of the 112). Sharing helpers across `BlocksFoldClosed`
   and `CmdsFoldClosed` saves a few LoC but doesn't change the
   structural cost.

So the cap on savings is **124 LoC of dedup-able boilerplate −
~112 LoC of necessary new abstraction = ~12 LoC at best.** That's
deep below the 50-LoC Tier 2 floor.

## Why future-payoff doesn't change the answer

The `CmdsFoldClosed` typeclass would benefit any *future* binary
Class-B predicate consumer. From L2's audit, the only other Class B
candidate is `labelMapBoundedAndInj` in
`CoreCFGToGotoTransformWF.lean`, which L2 itself said is "only 2
steps (block / blocks), already tight; nothing to dedup."
So the infrastructure has no concrete second consumer, and committing
~112 LoC of speculative-payoff abstraction is not justified.

## Comparison to L3's two ports

| Port | LoC saved in consumer file | Combinator cost share | Net (per port) |
|---|---|---|---|
| NoDead | 398 | 0 (uses existing API as-is) | +398 |
| GotoTargetProvenance | 196 | 0 | +196 |
| WfLabelMapAgree (W1) | 113 | 112 (new typeclass + helper) | **−1** to **+1** |

NoDead and GotoTargetProvenance amortised the combinator's 393 LoC
across two big-saving consumers. WfLabelMapAgree's saving (113 LoC) is
not enough to also amortise its required 112 LoC extension.

## Lean 4 elaboration notes (from the prototype)

Same `def` vs `abbrev` issue L3 documented:

* `def LocationsTrackLabelMap'` works for typeclass inference, but
  emit-helper preservation lemmas had to start their proofs with
  `intro pc instr l h_at h_ty h_labels` to dispatch the implicit
  binders before applying push-non-location lemmas. Otherwise Lean
  eagerly elaborates the result-type's implicit `∀ {pc instr l}` and
  the unification fails with "expected `LocationsTrackLabelMap' lm
  (push)`, got `(push)[?m]? = some ? → ...`".
* Switching to `abbrev` for both `LocationsTrackLabelMap'` and
  `LocationsTrackLabelMap` did not help — the issue is application
  side, not declaration side. The fix was the `intro` reshuffle.

## Tier verdict

**Tier 3.** The 698 LoC file stays as-is. Net saving is ~−1 to ~+10
LoC depending on how aggressively the combinator extension is shared,
which is squarely below the 50-LoC Tier 2 floor.

L2's `~230 LoC saving` projection over-counted because it didn't
account for: (i) only steps 1-3 of the 9-step matrix being dedup-able
(steps 4-9 thread labelMap evolution), and (ii) the necessary new
typeclass costing ~112 LoC. The L2 audit was right that
WfLabelMapAgree was a *Class B* predicate; the audit overestimated
how much of the file is structurally common with the unary cases.

The existing 698-LoC `WfLabelMapAgree.lean` is well-structured for
its job; the abstraction tax of forcing it into the combinator
framework isn't worth it.

## Acceptance check

* `labelMap_agree_of_translator` — public signature unchanged (file
  not modified).
* `_v6`/`_v7` axioms — unchanged
  (`[propext, Classical.choice, Quot.sound]`, verified by hand against
  the post-revert state via `#print axioms`).
* `lake build` — green (227 jobs, baseline build).
* No new sorries, no new axioms.

The W1 stub plan claimed the prototype could probably hit "Tier 2
(50–150 LoC saved)". It didn't — the abstraction tax inside
`BlocksFoldClosed.lean` cancelled the savings inside
`WfLabelMapAgree.lean` almost exactly, so the honest call per the
task's risk-management note ("if WfLabelMapAgree won't budge below
50 LoC, the code is fine as-is and the abstraction tax isn't worth
it") is Tier 3.
