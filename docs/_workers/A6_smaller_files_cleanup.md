# Worker A6 — Smaller Correctness-Chain Files Cleanup (Stub)

**Branch base:** `htd/unstructured-to-goto` @ `a012a1c01`
**Goal:** Aggressively cleanup the smaller correctness-chain files (all ≤1.5k LoC), targeting 200-400 LoC saved.

## Target files (initial LoC)

| File | LoC |
|---|---|
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrect.lean` | 929 |
| `Strata/Backends/CBMC/GOTO/Bisim.lean` | 650 |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOInvariants.lean` | 399 |
| `Strata/Backends/CBMC/GOTO/SteppingBridgesDischarge.lean` | 403 |
| `Strata/Backends/CBMC/GOTO/BlocksFoldClosed.lean` | 393 |
| `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean` | 373 |
| `Strata/Backends/CBMC/GOTO/InstructionLookups.lean` | 351 |
| `Strata/Backends/CBMC/GOTO/CmdProvenance.lean` | 351 |
| `Strata/Backends/CBMC/GOTO/NoDead.lean` | 318 |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrectStore.lean` | 239 |
| `Strata/Backends/CBMC/GOTO/Tactics.lean` | 27 |
| **Total** | **4,433** |

## Plan

1. **Audit phase**: For each file, search for:
   - Dead lemmas (single-reference, non-`@[simp]`, non-`instance`)
   - Unused imports
   - Stale round-archaeology comments
   - Verbose proofs >40 lines with mechanical structure
   - Repeated `Option.some.inj/subst` patterns (apply `inj_subst` macro from `Tactics.lean`)
   - Cross-file dedup
2. **Cleanup phase**: file-by-file, commit per file, lake build green at each commit.
3. **Final report**: tier classification (1: ≥300, 2: 100-300, 3: <100).

## Process notes

- Work in this isolated worktree.
- No new `axiom`. No `sorry`. No `git push`.
- Public API preserved (all bridge lemmas, `coreCFGToGoto_forward_simulation` chain).
- Verify axioms unchanged at end.

## Audit results

(filled in next pass)

## Cleanup results

(filled in after each pass)
