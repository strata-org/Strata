# Worker R7a — Discharge `h_goto_target_in_range`

**Goal.** Discharge R6a's `h_goto_target_in_range` from a
`WellFormedTranslation` value, possibly under a small auxiliary
hypothesis. New file:
`Strata/Backends/CBMC/GOTO/GotoTargetInRange.lean`.

## Status (in progress)

- [x] Stub created.
- [ ] Decide auxiliary-hypothesis shape (Tier 2 deliverable).
- [ ] Write proof.
- [ ] `lake build` green.
- [ ] `#print axioms` standard.

## Strategy

The hypothesis to discharge (from
`TranslatorBridgeHypsDischarge.lean`):

```lean
∀ {pc target : Nat} {instr : Instruction},
  pgm.instrAt pc = some instr → instr.type = .GOTO →
  instr.target = some target →
  ∃ instr_target, pgm.instrAt target = some instr_target
```

**What `WellFormedTranslation` (round-5,
`CoreCFGToGOTOInvariants.lean`) gives us:**

* `layout_cond_goto`: every `condGoto` block has two GOTOs
  immediately after the body, with `instr_neg.target = some pc_lf`
  and `instr_uncond.target = some pc_lt`, and the targets equal
  `labelMap lf` / `labelMap lt`.
* `layout_location`: every `(l, blk) ∈ cfg.blocks` with `labelMap l
  = some pc` has `pgm.instrAt pc = some instr` with `instr.type =
  .LOCATION`.

**What's missing:** A direct fact "every GOTO instruction in `pgm`
originated from a `condGoto` block." `WellFormedTranslation` was
written from the *forward* direction (CFG → program), so it doesn't
expose the *backward* direction (program → CFG).

## Tier choice

**Tier 2 (Good).** We surface one auxiliary hypothesis:

```lean
EveryGotoFromCondGoto cfg pgm wf : Prop :=
  ∀ {pc target : Nat} {instr : Instruction},
    pgm.instrAt pc = some instr → instr.type = .GOTO →
    instr.target = some target →
    ∃ l blk pc_blk lt lf md cond,
      (l, blk) ∈ cfg.blocks ∧
      wf.labelMap l = some pc_blk ∧
      blk.transfer = .condGoto cond lt lf md ∧
      (target = ... )  -- target equals labelMap lt or labelMap lf
```

Given that hypothesis, we use `layout_cond_goto` to extract the
specific labelMap entry of the target, then `labelMap_total` +
`layout_location` to produce a valid `instrAt` at that target.

The auxiliary hypothesis is mechanically discharable from the
translator (it never emits GOTOs except in `emitCondGoto` /
`emitUncondGoto`), but proving that requires structural induction
over `coreCFGToGotoTransform`'s output.

## Files added

* `Strata/Backends/CBMC/GOTO/GotoTargetInRange.lean` (new).

## Build verification

(pending)
