# Worker A6 — Smaller Correctness-Chain Files Cleanup (Final Report)

**Branch base:** `htd/unstructured-to-goto` @ `a012a1c01`
**Goal:** Aggressively cleanup the smaller correctness-chain files (all ≤1.5k LoC), targeting 200-400 LoC saved.

## Result: **Tier 2** (236 LoC saved)

## Per-file delta

| File | Initial | Final | Delta |
|---|---|---|---|
| `CoreCFGToGOTOCorrect.lean` | 929 | 928 | -1 |
| `Bisim.lean` | 650 | 587 | **-63** |
| `CoreCFGToGOTOInvariants.lean` | 399 | 377 | -22 |
| `SteppingBridgesDischarge.lean` | 403 | 357 | **-46** |
| `BlocksFoldClosed.lean` | 393 | 393 | 0 |
| `TranslatorBridgeHypsDischarge.lean` | 373 | 334 | **-39** |
| `InstructionLookups.lean` | 351 | 338 | -13 |
| `CmdProvenance.lean` | 351 | 304 | **-47** |
| `NoDead.lean` | 318 | 317 | -1 |
| `CoreCFGToGOTOCorrectStore.lean` | 239 | 235 | -4 |
| `Tactics.lean` | 27 | 27 | 0 |
| **Total** | **4,433** | **4,197** | **-236** |

## Audit findings

### Dead declarations (16 LoC)

W5 methodology: `grep -rn '<name>' Strata/ StrataTest/`. Only one decl
across all files appeared exactly once (its own definition).

| Decl | File | LoC | Status |
|---|---|---|---|
| `storeCorr_preserve_skip` | Bisim.lean | 10 | Deleted |
| `Core.CmdExt.isPlainCmd` | CoreCFGToGOTOInvariants.lean | 5 | Deleted |
| `DetBlockTransferInstrCount` | CoreCFGToGOTOInvariants.lean | 6 | Deleted |
| `DetBlockTotalInstrCount` | CoreCFGToGOTOInvariants.lean | 5 | Deleted |

Note: most decls in these files are part of the public API. The
correctness-chain bridge surface is genuinely lean (15-20 theorems
each, all referenced ≥2x).

### Round/role/phase archaeology (~220 LoC)

The bulk of the savings: prose comments and section headers that
encoded development history (Round-6a/7/7c/8, Worker A/B/C, R7c/R8b/R10a/R11,
Phase 0/3, Gap A/B/C, "deliverable", "at this commit", "Tier-2 (Good)",
"Tier-3 (Acceptable)") were trimmed.

The largest single block was a 44-LoC "Structural divergences not yet
bridged at this commit" section at the end of `Bisim.lean` that listed
exactly the per-constructor bridges already proved earlier in the
same file.

### `inj_subst` macro

Already used in `CmdProvenance.lean`. No `Option.some.inj` patterns
found in any of the other target files — no further opportunity.

### Cross-file dedup

None found. Each file has a distinct role. The closest candidates
were the v1/v2 bridges in `TranslatorBridgeHypsDischarge.lean`, but
v1 is referenced by `GotoTargetInRange.lean` and v2 by
`CoreCFGToGOTOConcrete.lean`, so both must stay.

### Verbose proofs

No proofs >40 LoC matched a "mechanical pattern" candidate for
extraction. The proofs that are long are non-mechanical
case-splits over `CmdEmittedAt`, `EvalCmd`, etc., and each branch
is doing real work.

### Imports

All imports are used (verified by reading the consuming code).

## Commits (10)

1. `2bae2b833` docs(A6): stub plan
2. `16a6d68ce` cleanup(A6): drop dead defs in CoreCFGToGOTOInvariants (16 LoC)
3. `df9c0e6ef` cleanup(A6): drop dead lemma + stale archaeology in Bisim (63 LoC)
4. `37bb9d5a4` cleanup(A6): trim role/round archaeology in SteppingBridgesDischarge (46 LoC)
5. `b91cd73d1` cleanup(A6): trim round/role archaeology in TranslatorBridgeHypsDischarge (39 LoC)
6. `36717e5b3` cleanup(A6): trim Round-7c/R11 markers in InstructionLookups (13 LoC)
7. `1b0746278` cleanup(A6): trim Round-7/Round-8/R7c markers in CmdProvenance (47 LoC)
8. `1412b7056` cleanup(A6): drop Round-7b/L3/R6a markers in NoDead docs
9. `89108323f` cleanup(A6): drop Round-7/R10a/R11 markers in Invariants & Correct
10. `5b3cba7ec` cleanup(A6): drop 'Phase 3' markers in CoreCFGToGOTOCorrectStore

## Verification

* **Lake build green at every commit.** All targets in
  `Strata/Backends/CBMC/GOTO/*` plus the SemanticsTests / NoDeadAxioms
  / SteppingBridgesDischargeAxioms / WfLabelMapAgreeAxioms /
  CoreCFGToGOTOConcreteAxioms test files build clean.
* **Public API preserved.** Every public theorem/structure name is
  unchanged; verified by `grep` of consumer files.
* **Axioms unchanged.**
  - `coreCFGToGoto_forward_simulation` — `[propext, Classical.choice, Quot.sound]`
  - `steppingBridges_of_translator` — `[propext, Classical.choice, Quot.sound]`
  - `no_dead_of_translator_no_contracts_explicit` / `no_dead_of_translator` /
    `no_dead_program_of_translator` — `[propext, Classical.choice, Quot.sound]`
  - `coreCFGToGotoTransform_forward_simulation_concrete_v6` —
    `[propext, Classical.choice, Quot.sound]`
  - `coreCFGToGotoTransform_forward_simulation_concrete_v7` —
    `[propext, Classical.choice, Quot.sound]`
  - `labelMap_agree_of_translator` — `[propext, Classical.choice, Quot.sound]`

## Tier classification

**Tier 2** (100-300 LoC). The 236-LoC saving is dominated by stripping
round/role archaeology rather than removing dead code. The dead-code
contribution (16 LoC across 4 declarations) is small because these
files are already lean and load-bearing — almost every declaration is
either part of the public bridge surface or is referenced internally.

The cleanup makes the surviving prose substantially more useful for
new readers, who no longer need to mentally translate "Round-7c
deliverable" into "this file does X" or hunt for which "Worker"
discharged which obligation.
