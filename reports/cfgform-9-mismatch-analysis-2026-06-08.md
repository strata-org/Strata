# Deep analysis: 9 CFGForm test mismatches

**Date:** 2026-06-08
**Status:** Working draft (uncommitted)
**Inputs:** `/tmp/claude-503/cfgformtests-build-final.log`, `/tmp/claude-503/cfgformtests-diffs.txt`, source programs at `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/*.lean`.
**Helper:** `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/_CFGFormHelper.lean` (`Core.Program.toCFGForm` + `verifyCFG`).
**Test surface:** 31 per-source files at `StrataTest/Languages/Core/Examples/CFGForm/*.lean`, 90 verify blocks total. **21 leaves green** (verdict-preserving byte-for-byte). **9 leaves red, 1 OOM-killed.**

## Headline

Three substantive findings. Two are real defects in `Imperative.stmtsToCFG`; one is a benign asymmetry in path-condition handling.

1. **`stmtsToCFG` produces a malformed CFG when a procedure body's first statement is `if`.** The entry label points to a non-existent block; the conditional dispatch is dropped on the floor. 4 of 9 mismatches (RecursiveProcIte, BinaryTreeSize/LenAppend, BinaryTreeSize/SizeIsLen, Cover/Test, possibly MapBranching's nested case) hit this. **Real bug; surfaced by this work.**

2. **`stmtsToCFG` silently drops `.typeDecl` and `.funcDecl` statements from procedure bodies.** Programs that declare a type inside a procedure (e.g. `type T;` followed by `var x : T;`) fail type-checking after the rewrite because T is no longer in scope. 4 of 9 mismatches are TypeDeclStmt's 4 verify blocks. **Soundness violation in the rewrite as currently written; explicit per the source comment "Not yet supported, so just continue with `rest`".**

3. **The CFG form's path-condition assumptions are different in shape from the structured form's, but verdict-equivalent on simple ites.** UnreachableAssert, ProcedureCall, SelectiveVerification, SafeMap diverge in obligation labels, gen-counter suffixes, and assumption text — but every verdict matches (`✅ pass` on both sides). **Cosmetic, not a bug.**

The 21 green leaves give us **86 ✅ pass / 2 ❓ unknown / 9 ❌ fail** SMT verdicts byte-identical between structured and CFG forms — strong empirical confirmation that the proof's soundness theorem holds on its target program shape.

---

## Failure-class table

| # | Class | Files | Severity | Root cause |
|---|-------|-------|----------|------------|
| F1 | Empty-accum at proc-body start drops conditional dispatch | RecursiveProcIte, BinaryTreeSize (LenAppend, SizeIsLen), Cover (Test) | **Bug** in `stmtsToCFG` | `flushCmds`/`stmtsToBlocks` interaction at `StructuredToUnstructured.lean:32-44, 85-102` |
| F2 | typeDecl/funcDecl statements silently dropped | TypeDeclStmt (4 blocks) | **Soundness violation** | `StructuredToUnstructured.lean:65-70` explicit "Not yet supported" drop |
| F3 | Cosmetic obligation-label/assumption-shape differences | SelectiveVerification, SafeMap, ProcedureCall, UnreachableAssert | **Verdict-preserving asymmetry** | Different gen-counter trajectory; CFG path conditions vs structured merge-with-conditional |
| F4 | Nested ite chain hits same empty-accum case mid-body | MapBranching (testmap) | **Bug** (variant of F1) | First ite's join leaves empty accum; second ite's entry label dangles |
| F5 | Build OOM at >10 sequential SMT calls per Lean process | FunctionPreconditions (13 blocks) | Operational | Per-leaf-process isolation insufficient at this density |

---

## F1 — Empty-accum-at-proc-body-start drops conditional dispatch

**Symptom.** After `Core.Program.toCFGForm`, the verifier rejects the program at type-check with:

```
[F]: Entry label "ite_1" not found in CFG blocks. Available labels: [l$_2, l$_3, end$_0]
```

**Affected programs (all share "first stmt is `if`" shape):**
- `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/RecursiveProcIte.lean:21-31` — proc F starts with `if (100 < n) { ... } else { call F(n+11, ...); call F(r, ...); }`.
- `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/BinaryTreeSize.lean:54-58` — proc LenAppend starts with `if (IntList..isCons(xs)) { call LenAppend(...); }`.
- `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/BinaryTreeSize.lean:66-72` — proc SizeIsLen starts with `if (IntTree..isNode(t)) { call SizeIsLen(IntTree..left(t)); ... }`.
- `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/Cover.lean` — second `Test()` proc starts with `if (x <= 1) { cover ... }`.

**Root-cause trace.** Walking `Strata/Transform/StructuredToUnstructured.lean`:

In `stmtsToBlocks` (line 50), the `.ite` case at line 85-102:

```lean
| .ite c tss fss md :: rest => do
  let (kNext, bsNext) ← stmtsToBlocks k rest exitConts []
  let l ← StringGenState.gen "ite"            -- generates `ite_1`
  let (tl, tbs) ← stmtsToBlocks kNext tss exitConts []
  let (fl, fbs) ← stmtsToBlocks kNext fss exitConts []
  ...
  let (accumEntry, accumBlocks) ← flushCmds "ite$" (accum ++ extraCmds)
    (.some (.condGoto condExpr tl fl md)) l   -- ← passes l as `k`
  pure (accumEntry, accumBlocks ++ tbs ++ fbs ++ bsNext)
```

In `flushCmds` (line 32-44):

```lean
def flushCmds (pfx : String) (accum : List CmdT) (tr? : Option (DetTransferCmd String P)) (k : String) :
  StringGenM (String × DetBlocks String CmdT P) := do
  if accum.isEmpty then
    pure (k, [])               -- ← when accum empty, return k unchanged, NO blocks
  else
    let l ← StringGenState.gen pfx
    let b := (l, { cmds := accum.reverse, transfer := tr?.getD (.goto k) })
    pure (l, [b])
```

When `accum` is empty (procedure body's first statement is `if`, no commands accumulated before it), `flushCmds` returns `(k=ite_1, [])`. The condGoto transfer is **silently discarded.** No block is emitted at label `ite_1`. The caller returns `(ite_1, accumBlocks=[] ++ tbs ++ fbs ++ bsNext)`, claiming `ite_1` is the entry of the CFG (via `accumEntry`), but `cfg.blocks` doesn't contain it.

Downstream, `stmtsToCFG` at line 183 wires this up:

```lean
let (l, bs) ← stmtsToBlocks lend ss [] []
pure { entry := l, blocks := bs ++ [bend] }
```

`entry := ite_1`, but `blocks` only has `[l$_2 (then-arm), l$_3 (else-arm), end$_0]`. Type-checker rejects.

**Fix candidates.** Three options, in order of locality:

1. **Patch `flushCmds`'s empty-accum branch to honor `tr?`.** When `accum` is empty *and* `tr?` is `.some`, we need to emit a transfer-only block. Cleanest:

   ```lean
   if accum.isEmpty then
     match tr? with
     | .some tr =>
       let l ← StringGenState.gen pfx
       let b := (l, { cmds := [], transfer := tr })
       pure (l, [b])
     | .none =>
       pure (k, [])
   ```

   This makes empty-accum-with-transfer create a single transfer-only block named via the requested prefix. Caller's `l` (generated separately at line 89) is unused on that path, which is fine since we wire to the new label.

2. **Move the entry-label generation into `flushCmds`** so it's always coherent with whether a block is emitted. Bigger refactor.

3. **Guard at the `.ite` site:** if `accum` is empty, emit a `.condGoto`-bearing block manually rather than going through `flushCmds`. Ugly and duplicative.

I'd recommend (1).

**Test that closes it:** the existing CFGForm/RecursiveProcIte.lean leaf becomes green. (Plus BinaryTreeSize and Cover.)

---

## F2 — typeDecl/funcDecl statements dropped

**Symptom.** After `toCFGForm`, the verifier rejects with:

```
error: ❌ Type checking error.
Type T is not an instance of a previously registered type!
Known Types: [arrow, Sequence, TriggerGroup, real, string, bitvec, Triggers, int, bool, Map, regex]
```

Note that T is not in the Known Types list — it's been dropped.

**Affected programs:**
- `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/TypeDeclStmt.lean:16-24` (`typeDeclStmt1`): `procedure P () { type T; var a : T; var b : T; var c : T; assume ab; assume bc; assert trans; };`. Original ✅ pass; rewrite type-error.
- TypeDeclStmt:78-91 (`typeDeclStmt3`): two stmt-level types (`type T; type U;`). Same pattern.
- TypeDeclStmt:121-132 (`typeDeclStmt4`): parameterized `type T (a : Type, b : Type);`. Same pattern.
- TypeDeclStmt:162-170 (`shadowTopLevelType`): the **inverse** — original expects the type-checker to *reject* with `Type 'T' is already declared` (because it's both top-level AND statement-level). Under rewrite, the inner `type T;` is dropped, so the rejection doesn't fire — verdict flips from "expected error" to "passes type-check vacuously". The structured form's golden encodes the structured-form type-checker's error message exactly; under rewrite, that error message vanishes.

**Root cause.** `Strata/Transform/StructuredToUnstructured.lean:65-70`:

```lean
| .funcDecl _ _ :: rest => do
  -- Not yet supported, so just continue with `rest`.
  stmtsToBlocks k rest exitConts accum
| .typeDecl _ _ :: rest => do
  -- Not yet supported, so just continue with `rest`.
  stmtsToBlocks k rest exitConts accum
```

The cases drop the declaration without emitting anything, but the rest of the procedure body (and the whole program's type-checker) still expects the declared types/functions to be in scope. **This breaks soundness whenever any procedure body contains a typeDecl or funcDecl Stmt.** "Not yet supported" should be "rewrite refuses to convert this body" — silent drop is unsound.

**Fix candidates.**

1. **Refuse to convert procedures containing `.typeDecl` or `.funcDecl`.** Add a precondition check at the top of `stmtsToBlocks` (or at `Procedure.body` rewrite time in `Core.Program.toCFGForm`) that fails with a clear error rather than silently dropping. This is the soundness-preserving but feature-limiting fix.

2. **Hoist statement-level type/func declarations to top-level scope before rewrite.** Compatible with the proof's `simpleShape` predicate if that predicate already excludes type/funcDecl in body. Complex but feature-preserving.

3. **Emit type/func declarations as cmds inside the entry block.** Requires the underlying `Cmd` type to support type-decl as a command, which it currently does not.

The proof on `htd/structured-to-unstructured-small-step-proof` likely already requires `Block.simpleShape ∧ noFuncDecl ∧ no .typeDecl` per the corpus-coverage workflow's enumeration. So fix (1) — refuse rather than silently drop — is the soundness-aligned move that matches the formal precondition.

**Test that closes it:** add a precondition-violation predicate; CFGFormTests.lean for TypeDeclStmt explicitly skips its 4 blocks (declared not-applicable to the soundness theorem).

---

## F3 — Cosmetic asymmetry: same verdict, different label/assumption text

**Symptom.** Goldens differ in 4 leaves but every SMT verdict is byte-identical (`✅ pass` on both sides). Concrete shape:

**SelectiveVerification:** Obligation suffixes renumbered from `_6` (structured) to `_2` (CFG):
```
- Obligation: callElimAssert_n_positive_6
+ Obligation: callElimAssert_n_positive_2
```

**SafeMap:** Two paired renumberings:
```
- Obligation: callElimAssert_id_not_in_registry_12
+ Obligation: callElimAssert_id_not_in_registry_7
- Obligation: callElimAssert_id_ge_zero_3
+ Obligation: callElimAssert_id_ge_zero_13
```

**ProcedureCall:** Renumberings + reordering of assumptions in goldens (assumption emission order changes; same set of assumptions, same obligations, same ✅ pass).

**UnreachableAssert:** Genuinely different obligation. Structured form computes:
```
Obligation: x_eq_y, with assumptions
  z_false: z == false
  <label_ite_cond_true: z == false>: if z == false then z == false else true
  <label_ite_cond_false: !(z == false)>: if if z == false then false else true then if z == false then false else true else true
  Obligation: x == if z == false then x else y
```
CFG form computes:
```
Obligation: x_eq_y, with assumptions
  z_false: z == false
  <cfgBranch_true: z == false>: z == false
  <cfgBranch_false: !(z == false)>: if z == false then false else true
  Obligation: x == y
```

Both ✅ pass. The structured form merges the two ite branches and substitutes the conditional `if z == false then x else y` into the obligation; the CFG form keeps the two branches as separate path conditions and produces a simpler obligation `x == y` because the branch is straight-line. **Same logical content, simpler under the CFG semantics.** The CFG form is better here.

**Root cause.** Two compounding factors:

1. **`StringGenState.gen` counter trajectory differs.** The structured form runs through path-eval which generates fresh names along its merge path; the CFG form generates fresh names along its straight-line eval per branch. Both are deterministic but produce different counter values for the same logical obligation.

2. **Path-condition assumption shape differs.** Structured-form ite produces `<label_ite_cond_<true|false>: cond>: <conditional-shadowed obligation>`. CFG-form condGoto produces `<cfgBranch_<true|false>: cond>: <direct path condition>`. The latter is what the CFG semantics in `evalCFGStep` (`Strata/Languages/Core/ProcedureEval.lean:113-114`) emits per branch.

**Fix candidates.**

These are not bugs. The verdicts agree exactly. Three reactions are reasonable:

1. **Update the CFGForm goldens to match the CFG form's actual output.** Ship the CFGForm test file with the CFG-form goldens, accept that the structured-form and CFG-form goldens differ in label text and gen-counter, document that `.cfg`-form is verdict-preserving but not text-preserving. Most pragmatic.

2. **Stabilize the gen-counter to be path-shape-independent.** Hard; would require reworking `StringGenState`. Not justified.

3. **Restrict the test goldens to verdict-only digests** (extract `Result: ✅/❌/❓` lines, drop the assumption text, then golden-check). Cleanest in concept; medium-effort to implement (a verdict-extracting wrapper around `verifyCFG`).

I'd recommend (1) for the immediate test surface — keep the existing `verifyCFG` calls and update the 4 leaves' goldens to the CFG-form's actual output, with a comment explaining the asymmetry. The resulting goldens still encode "verdict-preservation" at the bucket level (every PASS stays PASS).

For long-term maintainability, (3) is what one would ideally want.

---

## F4 — Nested-ite empty-accum (variant of F1)

**Symptom.** MapBranching's testmap proc has two consecutive ites with no commands between them. After rewrite:

```
[testmap]: Block "l$_6" branches to unknown label "ite_2".
Available labels: [ite$_8, l$_6, l$_7, l$_3, l$_4, l$_1, end$_0]
```

The first ite's then-and-else arms both flush their commands and return their `kNext` continuation; that `kNext` is the second ite's entry label. But because the second ite was processed via the same `stmtsToBlocks .ite` path with empty accum (everything before the second ite was already consumed by the first), the second ite's entry-label-without-block bug strikes.

**Fix:** same as F1. Patching `flushCmds` to honor non-empty `tr?` on empty accum closes both F1 and F4.

---

## F5 — OOM at 13 sequential SMT calls in one Lean process

**Symptom.** `CFGForm/FunctionPreconditions.lean` (13 verify blocks) is killed by SIGKILL after 147s of building. Per-leaf process isolation gives each leaf its own Lean process, but 13 sequential `#eval verify` calls within that one process accumulate enough state to OOM the box.

**Mitigation already designed (see [`feedback memory: smt-test-memory-pressure`]):** per-test `maxHeartbeats` ceiling, separate Lake target outside default build, `/usr/bin/time -l` observability. For Task 3 closure, simplest fix is to split FunctionPreconditions's 13 blocks into two leaves: `FunctionPreconditions_part1.lean` (7 blocks) and `FunctionPreconditions_part2.lean` (6 blocks). Each gets its own Lean process and stays under the OOM line.

This is the right design lever for any future leaves that grow large.

---

## Coverage state after this analysis

| Bucket | Count | What it tells us |
|--------|------:|------------------|
| Green leaves | 21 | `.cfg` rewrite is verdict-preserving |
| ✅ pass results within green | 86 | Structured-form PASS preserved under rewrite |
| ❓ unknown results within green | 2 | Structured-form UNKNOWN preserved |
| ❌ fail results within green | 9 | Structured-form FAIL preserved (the rewrite is faithful even on intentionally-failing programs) |
| F1+F4 (real bug, ite-at-empty-accum) | 4 | A `flushCmds` defect; closes with 1 patch |
| F2 (real bug, dropped typeDecl/funcDecl) | 4 | A soundness-violating silent drop; closes by refusing to convert |
| F3 (cosmetic) | 4 | Verdict-preserving; goldens need updating per CFG form |
| F5 (OOM) | 1 | Per-leaf split required |

**Net "real bugs surfaced by this work": 2** (F1+F4 as one, F2 as another). Both are in `Imperative.stmtsToCFG`, neither is in the verifier itself.

## Recommended next steps

1. **Fix F1.** Patch `Strata/Transform/StructuredToUnstructured.lean:32-44` (`flushCmds`) to emit a transfer-only block when `accum` is empty and `tr?` is non-none. ~10 LoC change. Closes 4 of 9 mismatches.

2. **Fix F2 by refusal, not silent drop.** Either (a) extend `Core.Program.toCFGForm` to throw an error on procedures whose body contains `.typeDecl` or `.funcDecl` Stmts, or (b) leave `stmtsToBlocks` as-is and handle this at the proof's precondition level. This is a soundness fix; please coordinate with the proof branch's author.

3. **Update F3 goldens to match the CFG form's actual output.** Add a comment in CFGForm/<file>.lean explaining the path-condition asymmetry. ~30 LoC of golden updates.

4. **Split FunctionPreconditions for F5.** Two leaves of 6-7 blocks each.

After 1+3+4, expected: **31 of 31 leaves green, 90 of 90 verify blocks landing identical-verdict goldens.** F2 remains as 4 explicitly-skipped blocks documented as "not in the soundness theorem's scope".

## Files referenced

- /Users/htd/Documents/Strata-smack/Strata/Transform/StructuredToUnstructured.lean (F1 root cause at lines 32-44, F2 at lines 65-70)
- /Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/_CFGFormHelper.lean (the helper that surfaced these)
- /Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/CFGForm/*.lean (31 leaf test files)
- /Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/CFGFormTests.lean (index)
- /tmp/claude-503/cfgformtests-build-final.log (build log with all 9 diffs)
- /tmp/claude-503/cfgformtests-diffs.txt (extracted diff hunks)
- /Users/htd/Documents/Strata-smack/reports/plan-verify-unstructured-form-coverage-2026-06-08.md (the plan that generated this work)
