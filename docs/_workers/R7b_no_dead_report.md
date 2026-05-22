# Worker R7b — `h_no_dead` from translator induction

**Goal.** Discharge R6a's `h_no_dead` hypothesis: `coreCFGToGotoTransform`
never emits DEAD instructions. Provided as `no_dead_of_translator` (and
related forms) in a new file
`Strata/Backends/CBMC/GOTO/NoDead.lean`.

## Outcome

**Tier 1 (Best).** `h_no_dead` fully closed under one stable side
hypothesis (`h_loopContracts_empty_post`, the same one A4's
`coreCFGToGotoTransform_size_eq_and_loc_direct` already takes). The
translator structure-induction is fully discharged.

| Form | Closes | Status |
|---|---|---|
| `no_dead_of_translator_no_contracts_explicit` | takes blocks-fold + patches-fold + patchGotoTargets results | discharged |
| `no_dead_of_translator` | takes only `h_run` + side condition | discharged via `coreCFGToGotoTransform_decompose` |
| `no_dead_program_of_translator` | wrapper at `Program.instrAt` level (the form R6a needs) | discharged |

Build green. Axioms across all three theorems:
`[propext, Classical.choice, Quot.sound]` — same as the round-6 baseline.

## Files added

* **Added** `Strata/Backends/CBMC/GOTO/NoDead.lean` (~640 LoC).
* **Added** `StrataTest/Backends/CBMC/GOTO/NoDeadAxioms.lean` —
  smoke test that elaborates each theorem and prints its axiom set.

## Predicate

```lean
def HasNoDead (trans : Imperative.GotoTransform Core.Expression.TyEnv) : Prop :=
  ∀ {pc : Nat} {instr : Instruction},
    trans.instructions[pc]? = some instr → instr.type ≠ .DEAD
```

## Preservation lemmas (all in this file)

| Lemma | Step | What's pushed/appended |
|---|---|---|
| `toGotoInstructions_preserves_no_dead` | `Cmd.toGotoInstructions` | DECL + ASSIGN (init.det) / DECL (init.nondet) / ASSIGN (set.{det,nondet}) / ASSERT (assert) / ASSUME (assume) / ASSERT (cover) |
| `coreCFGToGotoCmdStep_preserves_no_dead` | per-cmd CFG step | delegates to (1) for `.cmd`; pushes FUNCTION_CALL for `.call` |
| `cmdsFoldlM_preserves_no_dead` | cmds-fold | induction on cmds list |
| `emitLabel_preserves_no_dead` | `emitLabel` | LOCATION |
| `emitCondGoto_preserves_no_dead` | `emitCondGoto` | GOTO |
| `emitUncondGoto_preserves_no_dead` | `emitUncondGoto` | GOTO |
| `endFunction_emit_preserves_no_dead` | `.finish md` END_FUNCTION emit | END_FUNCTION |
| `coreCFGToGotoBlockStep_preserves_no_dead` | per-block CFG step | LOCATION + cmds + (2 GOTOs OR 1 END_FUNCTION) |
| `blocksFoldlM_preserves_no_dead` | blocks-fold | induction on blocks list |
| `coreCFGToGotoPatchStep_preserves_no_dead_no_contracts` | per-patch step (no loop contracts) | trivial — `acc.2` unchanged per A4's `_no_contracts_trans_eq` |
| `patchesFoldlM_preserves_no_dead_no_contracts` | patches-fold (no loop contracts) | trivial — `acc.2` unchanged per A4's `patchesFoldlM_no_contracts_trans_eq` |
| `patchGotoTargets_preserves_no_dead` | final patcher pass | type field preserved per A4's `patchGotoTargets_preserves_type` |

## Final composition

```lean
theorem no_dead_of_translator
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_dead : HasNoDead trans₀)
    (h_loopContracts_empty_post : ...)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    HasNoDead ans
```

The `h_loopContracts_empty_post` side condition is the same one A4
uses in `coreCFGToGotoTransform_size_eq_and_loc_direct`: it says the
post-blocks-fold loop-contracts map is empty (true when the CFG has
no loop-invariant or decreases metadata, which is the case for the
forward-simulation pipeline).

## Program-level wrapper

R6a's bridge consumes `h_no_dead` at the `Program.instrAt` level (not
directly on the `trans.instructions[pc]?` array). We provide the
`Program.instrAt`-shaped form:

```lean
theorem no_dead_program_of_translator ... :
  ∀ {pc : Nat} {instr : Instruction},
    ({ name := "", parameterIdentifiers := #[],
       instructions := ans.instructions } : Program).instrAt pc =
      some instr →
    instr.type ≠ .DEAD
```

This is the precise shape of R6a's `h_no_dead` parameter to
`wellFormedTranslation_to_translatorBridgeHyps`.

## Why the `.call` and `.cover` branches needed extra care

* The `.cover` branch in `Cmd.toGotoInstructions` lacks a
  `_ok`-style shape lemma (Worker A didn't land one). We replay the
  same direct unfold pattern as `toGotoInstructions_preserves_size_eq`
  and identify the pushed instruction as a literal ASSERT with a
  comment-tagged source location.
* The `.call` branch in `coreCFGToGotoCmdStep` pushes a FUNCTION_CALL
  whose body involves `dbg_trace` calls (debug warnings printed when
  type lookup fails). The elaborated form has implicit `dbgTrace`
  applications that don't unify cleanly with hand-written instruction
  literals. We bypass the issue by inlining the `push_preserves_no_dead`
  proof directly: case-analysing `pc < trans.instructions.size`,
  `pc = trans.instructions.size`, `pc > trans.instructions.size + 0`,
  and pulling out the `.type = .FUNCTION_CALL` fact only at the size-
  equal sub-case (where `instr` is unified to the unfolded
  `FUNCTION_CALL` literal via `injection h with h; subst h`).

## Build verification

```
$ lake build Strata.Backends.CBMC.GOTO.NoDead
Build completed successfully (210 jobs).

$ lake build
Build completed successfully (585 jobs).

$ lake build StrataTest.Backends.CBMC.GOTO.NoDeadAxioms
info: 'CProverGOTO.NoDead.no_dead_of_translator_no_contracts_explicit'
        depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'CProverGOTO.NoDead.no_dead_of_translator'
        depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'CProverGOTO.NoDead.no_dead_program_of_translator'
        depends on axioms: [propext, Classical.choice, Quot.sound]
```

No new project-internal axioms beyond round 6's baseline.

## Status checklist

- [x] Report stub.
- [x] Read all required context.
- [x] Per-instruction-emit lemmas (push / append).
- [x] Cmd-step preservation (`Cmd.toGotoInstructions` + `.call`).
- [x] Cmds-fold preservation.
- [x] Block-step preservation (label + cmds + transfer).
- [x] Blocks-fold preservation.
- [x] Patch-step preservation (no-contracts case).
- [x] Patches-fold preservation (no-contracts case).
- [x] `patchGotoTargets` preservation.
- [x] Final composition: `no_dead_of_translator{,_no_contracts_explicit}`.
- [x] Program-level wrapper: `no_dead_program_of_translator`.
- [x] `lake build` green.
- [x] Axiom check matches round-6 baseline.

## Suggested follow-ups

1. Wire `no_dead_program_of_translator` into R6a's
   `wellFormedTranslation_to_translatorBridgeHyps` consumer site —
   replacing the caller-passed `h_no_dead` with the discharged
   theorem reduces the bridge's hypothesis surface by 1.
2. Generalise the no-loop-contracts hypothesis to handle programs
   with loop invariants. The patcher mutates `guard` (not `type`)
   when contracts are present, so the same `patchGotoTargets_preserves_type`
   argument applies — only the patches-fold preservation lemma needs
   to drop the `_no_contracts` qualifier and use a more general
   "patch step never changes `type`" lemma. Modest extra work
   (~50 LoC).
3. The `.call` branch's brittle elaboration (due to `dbg_trace`)
   could be cleaned up by hoisting the type-lookup logic into a
   helper function (no `dbg_trace`) plus an "ok shape" lemma.
