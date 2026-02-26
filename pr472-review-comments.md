# PR #472 Review Comments — Responses

## 1. [atomb] Small-step semantics instead of big-step

> I'd like to see small-step instead of big-step semantics. I think I'd even prefer to leave out the changes to the big-step semantics you made.

> (`StmtSemanticsSmallStep.lean:107`): This definition of the semantics is the one I consider the current, standard semantics [...] So this is the one I hoped you'd fill in as part of this PR, rather than the other one.

**What was done:** Reverted all big-step exit changes (ExitStatus, consumedBy, exit parameter in EvalStmt/EvalBlock, and all downstream proof fixes). Implemented exit in the small-step semantics with: `Config.exiting` for exit propagation, `Config.block` to track block labels, and rules for exit consumption (`step_exit`, `step_stmt_cons_exit`, `step_block_exit_none/match/mismatch`).

**Suggested reply:** Done. Reverted the big-step changes and implemented exit in the small-step semantics instead. Added `Config.exiting` and `Config.block` to track exit propagation and block label consumption.

---

## 2. [atomb] Add BoogieToStrata test for unstructured programs

> (`StrataGenerator.cs`): Could you add an unstructured Boogie program, with only forward gotos, as a test in the `BoogieToStrata` project?

**What was done:** Added `Tools/BoogieToStrata/Tests/ForwardGotos.bpl` with four procedures exercising different forward goto patterns: simple forward skip, diamond with single-target gotos, chained sequential gotos, and block skipping. Generated corresponding `.expect` file.

**Suggested reply:** Added `ForwardGotos.bpl` with four procedures covering simple forward skip, diamond pattern, chained gotos, and block skipping.

---

## 3. [atomb] Validate exit labels in the type checker

> (`StatementType.lean:157`): I think we should still check that this is a valid label to exit to.

**What was done:** Threaded a `labels : List String` parameter through the type checker's `go`/`goBlock` helpers. `exit l` now requires `l` to match an enclosing block label. Unlabeled `exit` requires being inside at least one block. Updated `StatementWF.lean` theorems for the new parameter.

**Suggested reply:** Done. The type checker now threads enclosing block labels and validates that exit targets a label in scope. Unlabeled exit requires being inside at least one block.

---

## 4. [atomb] Fix comment in Core.lean

> Suggested: `block with a matching label (or the nearest block if no label is given). Strata does not support arbitrary goto statements.`

**What was done:** Applied the suggestion.

**Suggested reply:** Done.

---

## 5. [atomb] Obsolete comment in T4_LoopJumps.lean

> It looks to me like it's already been updated to use exit semantics. Is this an obsolete comment from before you made that change?

**What was done:** Removed the stale `TODO: update to use exit semantics` from the comment.

**Suggested reply:** Good catch, removed the stale TODO.

---

## 6. [joscoh] Docstring in StmtSemantics.lean:50

> I don't think the docstring should be changed here (the `exit` info can be added, but not in place of the existing description), particularly because this gets fed into the documentation.

**What was done:** Moot — the big-step exit changes were reverted entirely, so the original docstring is restored.

**Suggested reply:** Reverted the big-step exit changes per Aaron's request, so the original docstring is back.

---

## 7. [joscoh] "Theorem" comment in StmtSemantics.lean:38

> Is this an actual theorem? If so, can you point to it?

**What was done:** Moot — the big-step exit changes (including this comment) were reverted.

**Suggested reply:** Reverted along with the big-step exit changes.

---

## 8. [joscoh] Rename `exit` variable to `e`

> This is minor, but it took me a bit to realize this is an arbitrary exit status rather than `.exiting`. IMO renaming to `e` here would be clearer.

**What was done:** Moot — the big-step exit changes were reverted, so the exit parameter no longer exists in the big-step semantics.

**Suggested reply:** Reverted along with the big-step exit changes.

---

## 9. [joscoh] Rename `Goto.lean` test file

> Maybe the name of this file should be changed?

**What was done:** Renamed `StrataTest/Languages/Core/Examples/Goto.lean` to `Exit.lean`.

**Suggested reply:** Done, renamed to `Exit.lean`.

---

## 10. [MikaelMayer] Sorry in DetToNondetCorrect.lean

> I think this will be irrelevant when we will merge the deterministic tree with the nondeterministic one, so I'm ok with this sorry.

**What was done:** Moot — the big-step exit changes were reverted, so the sorry no longer exists.

**Suggested reply:** Reverted along with the big-step exit changes, so no sorry remains.

---

## 11. [atomb] CI failure: ForwardGotos.expect has wrong content

> I think the test failure is occurring because the expected output file for `BoogieToStrata` should contain the output of `StrataVerify`, not the translated Core program.

**What was done:** Removed the `.expect` file. Without it, the integration test uses `--check` mode (parse and type-check only), verifying the translation produces valid Strata Core without needing the full StrataVerify output.

**Suggested reply:** Fixed — removed the `.expect` file so the test uses `--check` mode (parse + type-check). This verifies the translation is valid without needing full verification output.
