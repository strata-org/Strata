# Three issues, distinct root causes: non‑TCO walkers (issues 1, 2) + symbolic-eval array blowup (issue 3)

> **Resolution status (2026-06-02).** Diagnoses below have been updated
> against empirical bisection on origin/main:
>
> - **Issue (3) — RESOLVED on `htd/smack-timeout-fix`** (commit `277c468cb`).
>   Root cause was width-O(2^K) growth of `Env.deferred` inside
>   `Program.eval`, *before* `oblProgram` is constructed. In `evalCFGStep`'s
>   symbolic-`condGoto` arm, both `env_t` and `env_f` inherited the parent
>   env's `deferred` array; every symbolic branch doubled the pre-split
>   obligation set (28 → 56 → 4,928 → 9,856 → 68,992 → 896,896 →
>   3,960,692,736 across the 17 procedures of `cjson_cJSON_Parse_harness.bpl`).
>   Fix: one line, `deferred := #[]` on the false branch, mirroring the
>   existing `StatementEval.lean:673` dedup for structured `.ite`.
>   Soundness verified empirically (full 94-program sweep: 83 PASS /
>   11 PARTIAL with identical PARTIAL identities to the v4 baseline).
>
> - **Issue (1) — partially resolved** (commit `15b84c160` on a local
>   `draft-fix/precondelim-iterative` branch off origin/main `75f005566`).
>   The actual overflowing walker is **not** `programToCST` as the
>   original report suspected. Empirical phase-bisection on origin/main
>   localised the hang to `transformDecls` in
>   `Strata/Transform/PrecondElim.lean` (the `PrecondElim` pipeline
>   phase). That function walked `decls` via direct list-recursion
>   (`let (changed, rest') ← transformDecls rest`); converting it to a
>   for-loop with reverse-accumulation moves the threshold from N≈30K to
>   beyond 50K. Per-decl side effects (factory updates, call-graph leaf
>   nodes, stat increments) all commute across declarations, so the
>   ordering change is benign. PrecondElim's own tests + 7 sibling
>   Transform tests pass with the change. **At N≥100K a different
>   downstream walker still SIGABRTs** — `--parse-only` succeeds but
>   `--type-check` overflows; that walker has not been identified yet,
>   it's a follow-up. The original `programToCST` hypothesis is wrong
>   for the reproducible threshold; programToCST may still overflow at
>   higher N but isn't on the documented failure path.
>
> - **Issue (2) — diagnosis corrected, fix not landed.** The original
>   report cited `partial def translateExpr` at
>   `Strata/Languages/Core/DDMTransform/Translate.lean:818` as the
>   overflowing walker. Empirically, the SIGABRT happens *before*
>   `Successfully parsed.` is printed — i.e. inside DDM elaboration,
>   *before* `Translate.lean`'s walkers ever run. The actual culprit is
>   **`elabExpr` at `StrataDDM/StrataDDM/Elab/Core.lean:1694`** (in the
>   relocated `StrataDDM` package on origin/main; was at
>   `Strata/DDM/Elab/Core.lean:1659` pre-relocation). The recursion is
>   a 3-function monadic cycle: `elabExpr → runSyntaxElaborator →
>   elabSyntaxArg → elabExpr`, costing ~3 native frames per ITE level.
>   The cycle threads typing context with sequential side effects
>   (`unifyTypes`, etc.), which makes a clean trampoline rewrite
>   substantially harder than the `translateExpr` shape (which only
>   needed an internal worklist). An attempt at a full CPS rewrite
>   was started and discarded as multi-day work; left as upstream
>   memo. Trampolining `translateExpr` *would have* helped if the bug
>   had been there, but doesn't reach the actual walker. See §4.

> The "shared root cause across (1)/(2)/(3)" framing in the original
> Conjecture A is wrong on multiple axes:
> - (3) was a different bug class entirely (missing dedup in symbolic
>   eval, not a non-TCO walker).
> - (1) IS a non-TCO walker, but in `PrecondElim.transformDecls` —
>   not `programToCST`.
> - (2) IS a non-TCO walker, but in `elabExpr`/`runSyntaxElaborator`/
>   `elabSyntaxArg` (DDM elaboration) — not `translateExpr` (Core
>   translation, which runs *after* parsing).
>
> The general "non-TCO walker" anti-pattern is real and pervasive
> across the codebase, but the specific walkers identified in the
> original report were guesses based on grep, not validated by
> running. The actual culprits were found by empirical phase
> bisection (stop-flag walks + `dbg_trace` instrumentation in
> the pipeline loop).

## 1. Facts about each issue

### Issue (1) — flat-list stack overflow (~30K-50K axioms) [PARTIALLY RESOLVED on `draft-fix/precondelim-iterative`]

- Trigger: `prog.decls : List Decl` of length tens of thousands; default `--check-mode deductive` path.
- Symptom: SIGABRT (rc=-6), "Stack overflow detected. Aborting."
- `strata verify --parse-only` on 100K axioms completes in ≤2s; **the bug is not in parsing**. Empirically, the SIGABRT happens after `Successfully parsed.` is printed.
- **Actual culprit (verified by phase bisection on origin/main `75f005566`)**: `transformDecls` (the `where`-bound helper inside `precondElim`) at `Strata/Transform/PrecondElim.lean:374-456`. Each arm did `let (changed, rest') ← transformDecls rest` then `cons` the current decl(s) onto the result. With ~50K axioms, ~50K nested calls → SIGABRT.
- Pre-fix bisection (origin/main `75f005566`):
  - `--parse-only` on 50K axioms: PASS in 1s
  - `--type-check` on 50K axioms: PASS in 1s
  - `--check` (full transformation pipeline) on 50K axioms: SIGABRT
  - With `--profile` + a one-line `[phase-start]` log added to the pipeline loop in `Verifier.lean`: the crash happens during the `PrecondElim` phase. Adding `dbg_trace` inside `transformDecls` confirmed the recursion depth equals `decls.length`.
- **Fix landed** locally as commit `15b84c160` on `draft-fix/precondelim-iterative`: split per-decl logic into `processOneDecl`, drive with a for-loop that builds the result in reverse and reverses once at the end. Empirical results (origin/main vs. fix):

| N axioms | Pre-fix | Post-fix |
| --- | --- | --- |
| 30,000 | PASS (7s) | PASS (8s) |
| 50,000 | SIGABRT (12s) | PASS (23s) |
| 100,000 | SIGABRT | SIGABRT (different walker — see below) |

- **Residual at N≥100K**: a *different* downstream walker still SIGABRTs. `--parse-only` succeeds but `--type-check` overflows. Not yet identified; likely another `partial def` mutual block in the `mapM`-over-decls shape (candidates: `programToCST.mapM declToCST`, `translateLMonoTys.args.mapM`, `translateExprs.args.mapM (translateExpr …)`, `preconds.toArray.mapM`). Follow-up needed.
- The original report's `programToCST` hypothesis was incorrect for the documented threshold but may apply at higher N. `ChunkedFormat.formatProgramChunked` mentioned in the original report does not exist in the tree.

### Issue (2) — deeply-nested-Expr stack overflow (~4100+ deep ITE) [DIAGNOSIS CORRECTED, NO FIX]

`/Users/htd/Documents/Strata-smack/strata-verify-stack-overflow-deeply-nested-expr.md`. Status: present on origin/main `75f005566`.

- Trigger: a single expression nested ~4100+ deep (e.g. 5000-deep `if/then/else` in an ensures clause).
- Symptom: SIGABRT before the parse banner is printed; `--parse-only`, `--type-check`, `--check`, `--no-solve` all crash. Wall ~90-280 ms.
- **Original diagnosis was wrong about location.** The report cited `partial def translateExpr` at `Strata/Languages/Core/DDMTransform/Translate.lean:818`. Empirically, the SIGABRT happens *before* `Successfully parsed.` is printed — i.e. inside DDM elaboration, *before* `Translate.lean` runs. Tested by building a trampolined `translateExpr` (commit attempted then discarded): the fix had **zero effect** on the reproducer at any depth.
- **Actual culprit (verified by code reading + reproduction)**: `partial def elabExpr` at `StrataDDM/StrataDDM/Elab/Core.lean:1694` (origin/main `75f005566`; was at `Strata/DDM/Elab/Core.lean:1659` before the StrataDDM package extraction in commit `703404f66`). Recursion is a 3-function monadic cycle inside the file's `mutual` block:
  - `elabExpr` recurses on itself for `Init.exprParen` (1 frame).
  - `elabExpr` calls `runSyntaxElaborator` for op-elaboration (2nd frame).
  - `runSyntaxElaborator` iterates over args, calling `elabSyntaxArg` (3rd frame).
  - `elabSyntaxArg` for `.typeExpr`/`.preType` calls back into `elabExpr` (back to 1st).
  - Net depth per ITE level: ~3 frames in the elabExpr/runSyntaxElaborator/elabSyntaxArg cycle, plus 1 frame per paren wrap.
- **Why a fix is hard**: the cycle threads typing context with sequential side effects (`tctx` for arg N+1 may depend on `trees[N].resultContext` per `runSyntaxElaborator`'s loop body lines 1264-1268; `unifyTypes` mutates the trees vector in-place). A trampoline equivalent has to model "elaborate one arg, do bookkeeping, elaborate next" as worklist tasks with intermediate state — not the simple "elaborate all sub-args, combine results" shape that `translateExpr` admitted. Estimated 8-12 hours for a tested fix; an attempted CPS rewrite was started and discarded.
- The `translateExpr`/`toSMTTerm`/`appToSMTTerm`/`FormatCore.lean lexprToExpr` walkers cited in the original report **do** have the same anti-pattern shape, but they're downstream of DDM elaboration. They could overflow on a different reproducer (one whose syntax parses but whose Core IR is deep), but not on the documented N=5000 deep-ITE input.

### Issue (3) — pipeline hang on ≥20K-line `.bpl` (no SIGABRT, no z3 child) [RESOLVED]

- Trigger (was): large `.bpl` files (≥20,817 lines) translated to Core IR and run with `--call-policy bodyOrContract --inline-fuel 100 --check-level full`. (Empirically also `--call-policy contract` and every `--inline-fuel` value — call-policy and fuel were red herrings.)
- Threshold (was): `skipAnyScalar_harness.bpl` (20,817 lines) hangs; `jsmn_jsmn_parse_harness.bpl` (19,434) passes. (Threshold was actually shape-dependent — programs with many sequential CFG `condGoto` symbolic branches across procedures hit the multiplicative-growth wall regardless of total line count.)
- Symptom (was): strata alive and CPU-bound, no stack-overflow message, no z3 spawned.
- **Actual root cause**: in `Strata/Languages/Core/ProcedureEval.lean` `evalCFGStep`, the symbolic-`condGoto` arm built `env_t` and `env_f` by record-update on the parent `env'` — both inherited `env'.deferred` wholesale. Each symbolic branch doubled the pre-split obligation set; `mergeResults` then concatenated terminal envs without further dedup, propagating duplicates into the next procedure's eval. The structured `.ite` path already deduped at `Strata/Languages/Core/StatementEval.lean:673` (clearing `deferred` on the false branch); the CFG path missed the symmetric clear.
- **Diagnostic data** (per-procedure `E.deferred.size` after each `Procedure.eval` call on `cjson_cJSON_Parse_harness.bpl`): `cJSON_Delete:28`, `cJSON_ParseWithOpts:56`, `cJSON_ParseWithLengthOpts:4928`, `cJSON_New_Item:9856`, `skip_utf8_bom:68992`, `buffer_skip_whitespace:896896`, `parse_value:3960692736`, hang in `parse_string`. Materialising a 4-billion-element `Array (Imperative.ProofObligation Expression)` was the hang.
- **Fix**: commit `277c468cb` adds `deferred := #[]` to `env_f` in `evalCFGStep`'s symbolic-condGoto arm (one-line change with comment + regression test). The four previously-hanging programs now PASS deductive verification: `cjson_cJSON_Parse_harness.bpl` in 22s end-to-end (was: TIMEOUT under every flag combination on the 8-cell sweep).
- **Soundness**: each `ProofObligation` snapshots its `assumptions` (path conditions) at creation time (`Strata/DL/Imperative/CmdEval.lean:64-83`); each obligation is self-contained — the verifier proves `assumptions ⊨ predicate` without consulting the env's current state. `Env.deferred` is otherwise write-only during eval (verified by grep — only post-eval consumers at `Core.lean:168` and `ProcedureEval.lean:60` read it). Dropping a duplicate from one branch removes a redundant obligation that the sibling branch still carries. Empirically verified: full 94-program sweep produces 83 PASS / 11 PARTIAL / 0 FAIL; PARTIAL identities match the v4 baseline exactly (no silent PASSes that should be PARTIAL).
- **Why the conjectures missed it**: Conjecture A correctly observed the obligation-count correlation but located the failure in *post-eval* traversal of `oblProgram`'s ITE chain. The actual failure was earlier — `Program.eval` never returns, so `oblProgram` is never built and the ITE chain is never traversed. Conjecture B was directionally right (some kind of multiplicative state growth) but located it in the active-paths worklist rather than in the deferred-obligation array. Conjecture C's claim that body-eval doesn't introduce a new walker turned out to be irrelevant (the bug predates body-eval and is independent of `--call-policy`).

## 2. Conjectures, ranked

> **Note:** All three conjectures pre-date the resolution of issue (3). They
> are kept here for historical context; the actual root cause for (3) is
> documented in the Resolution box at the top and in the "Actual root
> cause" bullet under Issue (3) above. Conjectures A and B were both
> partly right about *symptoms* (obligation-count correlation; multiplicative
> growth) but wrong about *location* (post-eval ITE traversal vs. eval-time
> deferred-array allocation). Conjectures (1) and (2) were correctly
> diagnosed; their fix paths still apply and they remain unresolved.

### Conjecture A (now disproven for issue (3); still applies to (1) and (2)): non-TCO walkers in the verify pipeline

All three were hypothesised to be non-TCO walkers in the verify pipeline. The **same family of `partial def` mutual blocks in `DDMTransform/FormatCore.lean` and `DDMTransform/Translate.lean`** was thought to be hit by all three on different axes:

- (2) overflows because **a single expression** is deep → `lexprToExpr`/`translateExpr` mutual recursion (depth = expression depth). **(Confirmed.)**
- (1) overflows because **`prog.decls`** is long → `programToCST` does `prog.decls.mapM declToCST` under `StateT` (depth = `prog.decls.length` × ~4 frames per `bind`). **(Confirmed.)**
- ~~(3) overflows or thrashes because the `oblProgram` produced by `toCoreProofObligationProgram` nests a per-obligation ITE chain whose depth equals the number of obligations.~~ **DISPROVEN.** `Program.eval` never returns, so `oblProgram` is never built. The hang is *inside eval*, on a width-O(2^K) `Env.deferred` array, not on a depth-O(N) ITE chain in any post-eval walker. See the Resolution note above.

### Conjecture B (close on shape, wrong on location): exponential symbolic-state blowup, unrelated to (1)/(2)

The original framing pointed at `evalCalleeCFG`'s active-paths worklist as the source of multiplicative growth. The actual multiplier was in `Env.deferred` (proof-obligation accumulator), not in the active-paths list. Mechanism similar in spirit (each symbolic branch doubles something), location different. The active-paths worklist is correctly bounded by fuel; the deferred array was not deduped across symbolic branches.

### Conjecture C (correctly ruled out): brand-new walker introduced by body-eval

The bug is independent of `--call-policy` and `--inline-fuel` — `--call-policy contract` (no body inlining at all) hangs identically. The bug also predates the body-eval feature commit (`dd0c0d7cd`); it lives in `evalCFGStep` which is part of the original CFG-eval support. Body-eval only made the bug more visible by adding more procedures to typical traces.

## 3. Evidence

### Evidence for A — the per-obligation ITE chain in `toCoreProofObligationProgram`

`Strata/Languages/Core/Core.lean:178-182`:

```lean
let body := match blocks with
  | [] => []
  | [b] => b
  | b :: rest => rest.foldl (fun acc block =>
      [Imperative.Stmt.ite .nondet acc block .empty]) b
```

This builds a left-deep nest of `.ite` statements, **one level per proof obligation**. With ~9K `assumes`/`asserts` per large `.bpl`, the resulting body is a single statement list whose first element is an `.ite` ~`#obligations` deep. Multiple downstream walkers then descend that tree:

- `Strata/Languages/Core/ObligationExtraction.lean:80-83` — `extractGo` recurses on `.ite .nondet thenSs elseSs _md => do  let thenObs ← extractFromStatements pc thenSs; let elseObs ← extractFromStatements pc elseSs; extractGo pc rest …`. Each level is two recursive calls into `extractFromStatements`, which call back into `extractGo`. Depth = ITE chain depth = #obligations. This is `def`/`mutual` (not `partial`), but Lean's compiled code still allocates a frame per call; with 9K depth on the 8MB default stack, ~1KB/frame is enough to overflow.
- `Strata/Languages/Core/DDMTransform/FormatCore.lean:865-867` — `stmtToCST` on `.ite cond thenb elseb _md => do let thenCST ← blockToCST thenb; let elseCST ← elseToCST elseb`. `blockToCST` (line 893) does `stmts.toArray.mapM stmtToCST`, mutually recursing back into `stmtToCST`. Same depth. This walker runs every time `Core.formatProgram` is called.
- `Strata/Languages/Core/DDMTransform/Translate.lean:1338, 1385` — `translateStmt` on `.if_statement` ↔ `translateBlock` (1499) ↔ `translateElse` (1509), mutually recursive `partial def` under `StateT`. Same depth on parse.

The strongest piece of evidence that this is what hits issue (3): `Core.formatProgram p` is called inside `verifySingleEnv` at lines 814, 964, 1095, 1115, 1139 of `Verifier.lean` — most of those guarded by `options.verbose >= .debug`, but `getObligationResult` constructs `let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"` **unconditionally** at line 964. Even if the lazy `Format` defers most work, the call sites at lines 814 and 1095 evaluate it eagerly when emitting `dbg_trace`. So the pipeline traverses the per-obligation ITE chain at least once; given the chain depth scales linearly with the number of obligations, the program crosses the 8MB stack limit somewhere around the 20K-line `.bpl` boundary — exactly the threshold the bisection in `project_pipeline_hang_large_bpl.md` pinned.

### Evidence for issue (1)

- `Strata/Languages/Core/DDMTransform/ASTtoCST.lean:255-261`:

```lean
def programToCST {M} [Inhabited M] (prog : Core.Program) … :=
  let (cmds, finalCtx) := (do
    let cmdLists ← prog.decls.mapM declToCST
    pure cmdLists.flatten).run initCtx
  (finalCtx, cmds)
```

`declToCST` is at line 224. It does `match decl … pure [cmd]` returning `ToCSTM M (List (Command M))`. `ToCSTM` is `StateT ToCSTContext`; `List.mapM` over a `StateT`-flavoured monad expands as a left-nested `bind` chain whose runtime call depth equals the list length. With 30K decls this is ~30K stacked `bind` frames → SIGABRT.

- The same anti-pattern hits other walkers:
  - `Strata/Languages/Core/DDMTransform/Translate.lean:291` — `translateLMonoTys … args.mapM`.
  - `Strata/Languages/Core/DDMTransform/Translate.lean:1186-1188` — `translateExprs … args.mapM (translateExpr …)`.
  - `Strata/Languages/Core/DDMTransform/Translate.lean:1546` — `ops.mapM (translateInitMkBinding …)`.
  - `Strata/Languages/Core/DDMTransform/FormatCore.lean:711` — `preconds.toArray.mapM`.
- The proposed `ChunkedFormat.formatProgramChunked` workaround **is not in the tree** — `rg ChunkedFormat` returns no hits. So this fix is described in the ticket but not yet implemented.

### Evidence for issue (2)

Quoted directly from the report and corroborated:

- `Strata/Languages/Core/DDMTransform/Translate.lean:818` — `partial def translateExpr` recurses for every binary/ternary operator (e.g. `Core.equal` at line 854: `let x ← translateExpr p bindings xa; let y ← translateExpr p bindings ya`). Direct stack-bound recursion under `StateT`, no fuel.
- `Strata/Languages/Core/SMTEncoder.lean:258` — `partial def toSMTTerm`; line 333 — `partial def appToSMTTerm`. Both are mutually-recursive expression walkers.
- `Strata/Languages/Core/DDMTransform/FormatCore.lean:537-704` — the `mutual / lexprToExpr / labsToExpr / lquantToExpr / liteToExpr / leqToExpr / lappToExpr` block. `liteToExpr` (line 666) directly calls itself three times via `lexprToExpr c`, `lexprToExpr t`, `lexprToExpr f` — depth = expression depth.

### Evidence against C (body-eval introduces a *new* depth axis)

`evalCalleeCFG` (`StatementEval.lean:776`) recurses on `(newActive, newFinished ++ finished)` and the recursive call is in tail position (line 811). `Command.inlineCallBody` (line 825) doesn't directly self-recurse; it calls `eval` / `evalCalleeCFG`. The fuel parameter (`E.fuel`) is decremented per CFG block visit (line 787, 847) and per call (line 847), bounded by `options.inlineFuel` (`Core.lean:91` → `Env.fuel`). With `--inline-fuel 100`, total work is bounded.

So body-eval's contribution to (3) is not introducing a new non-TCO walker; it is **expanding the per-obligation ITE chain** by inlining callee bodies into the caller — which then feeds back into the `extractGo` / `stmtToCST` / `formatProgram` walkers identified in Evidence-for-A above. That's why issue (3) tracks linearly with `.bpl` line count rather than with depth or fuel.

### Quantitative correlation

- Hanging `skipAnyScalar_harness.bpl`: 20,817 lines, ~9,636 `(assert|assume|requires|ensures)`. Passing `jsmn_jsmn_parse_harness.bpl`: 19,434 lines, ~8,933. The threshold is at ~9K obligations per program, which on an 8MB default thread stack with ~1KB/frame is exactly where a depth-9K ITE chain would overflow. (The user's issue-(1) workaround `ulimit -s 65536` would be the first thing to test on a hanging issue-(3) `.bpl` to confirm Conjecture A.)
- Hanging programs are not unusual in call density (~890 calls vs ~822 for the largest passing). They are unusual in total `assume`/`assert` count after translation. This matches A and is inconsistent with C.

## 4. Status and recommendation

**Issue (3) — DONE.** Resolved by commit `277c468cb` (`fix(eval): clear Env.deferred on false branch of CFG condGoto`) on `htd/smack-timeout-fix`. Diagnosed via per-procedure `dbg_trace s!"[proc-eval-end] {name} (deferred={E.deferred.size})"` instrumentation in `Program.eval`; fixed in one line in `evalCFGStep`. Verification: full 94-program sweep produces 83 PASS / 11 PARTIAL with PARTIAL identities matching the v4 baseline exactly.

**Issue (1) — partial fix landed locally.** Commit `15b84c160` on local branch `draft-fix/precondelim-iterative` (off origin/main `75f005566`). Converts `transformDecls` in `Strata/Transform/PrecondElim.lean` to iterative form. Empirically shifts the threshold from N≈30K to beyond 50K (verified: 50K SIGABRT pre-fix → PASS post-fix). PrecondElim's own tests + 7 sibling Transform tests pass with the change. Branch not pushed; awaiting decision on whether to file as PR.

Residual at N≥100K: a different downstream walker still SIGABRTs. The fix path remains the same shape: identify the next `partial def`-with-direct-recursion or `mapM`-over-long-list and convert to iterative. Candidates to investigate: `programToCST.decls.mapM declToCST`, `translateLMonoTys.args.mapM`, the various `mapM` chains in `DDMTransform/`, `translateStmt` if the program has nested-block depth.

**Issue (2) — diagnosis corrected, no fix landed.** The original `translateExpr` cite was wrong; the actual walker is `elabExpr`/`runSyntaxElaborator`/`elabSyntaxArg` in `StrataDDM/StrataDDM/Elab/Core.lean` (the 3-function monadic cycle described in §1). A trampoline rewrite of `translateExpr` was attempted, built clean, and verified to have **zero effect on the reproducer** (because the walker overflows during DDM elaboration, before `translateExpr` runs). That work was discarded.

A real fix for (2) requires CPS-converting the elaboration cycle, which is genuinely 8-12 hours of work given the sequential typing-context threading and per-arg side effects. An attempt was started and discarded. Recommendation: file as upstream-maintained issue; the fix touches a critical component that warrants maintainer collaboration.

**Cross-cutting observation about the original report.** Both (1) and (2) had walker locations identified by *grep + heuristic* (find `partial def` X with direct recursion that takes a list/expr-tree). The actual walkers were elsewhere on the call graph. **The reliable diagnostic is empirical bisection** — combine `--parse-only`/`--type-check`/`--check` stop-flag walks with a one-line `[phase-start]` log inserted into the pipeline loop in `Verifier.lean`. This identifies the failing phase by name. Then `dbg_trace` inside the suspect phase localises the failing function. This worked for both (3) and (1); was the right approach we should have used from the start for (2) too (and would have located `elabExpr` immediately).

## 5. Method note: how to diagnose stack/hang issues

The diagnostics that worked, in order of escalation. **Skip lldb on
macOS** — DevToolsSecurity blocks attaching to locally-built strata
binaries and the workaround takes longer to set up than the
alternatives below.

1. **CLI stop-flag bisection.** `strata verify --parse-only` →
   `--type-check` → `--check` → `--no-solve` → full verify. Whichever
   stage transitions from PASS to SIGABRT/TIMEOUT contains the bug.
   This pinpoints the failure to one of: parser/elaborator, Core
   type-check, transformation pipeline, SMT generation, SMT solving.
   - For (3): localised to "transformation pipeline" (`--type-check` PASS, `--check` TIMEOUT).
   - For (1): localised to "transformation pipeline" (`--type-check` PASS, `--check` SIGABRT).
   - For (2): localised to "parser/elaborator" (`--parse-only` SIGABRT).

2. **Per-phase logging in the pipeline loop.** When the failure is in
   "transformation pipeline" (the broadest of the stop-flag buckets),
   add a one-line `IO.println s!"[phase-start] {pp.phase.name}"` to
   the `for pp in pipelinePhases do` loop in
   `Strata/Languages/Core/Verifier.lean:1177`, gated on the existing
   `profile` flag. Rebuild strata (incremental, ~3-5s), re-run. The
   last-printed phase name is the hanging/overflowing phase.
   - For (3): identified `symbolicEval` (= `Core.toCoreProofObligationProgram`).
   - For (1): identified `PrecondElim`.

3. **Per-element `dbg_trace` inside the suspect phase.** Drop a
   `dbg_trace` on the recursive arm to log per-element progress
   (procedure name, decl index, list-length, accumulator size, etc.).
   `dbg_trace` works in `Except`-monadic Strata code where
   `IO.println` isn't available. Combined with `stdbuf -oL -eL` for
   line-buffered stdout and `gtimeout N` for bounded wall-clock, this
   produces useful traces even when the process is killed mid-run.
   - For (3): `dbg_trace` on `Program.eval`'s `.proc` arm at
     `Strata/Languages/Core/ProgramEval.lean:61` printing
     `proc.header.name` and `E.deferred.size`. Exponential growth in
     deferred size was immediately visible.
   - For (1): direct read of the recursive `transformDecls` source
     was sufficient (the `let (changed, rest') ← transformDecls rest`
     pattern is unmistakable once you know the failing phase).

4. **For parser/elaborator failures (issue (2)):** stop-flag bisection
   identifies the broad area but doesn't help further because no
   phase-loop runs yet at that point. Code reading on the relevant
   `mutual` blocks — looking for `partial def` walkers with direct
   recursion on syntax-tree children — is the right next step. Look
   in `StrataDDM/StrataDDM/Elab/Core.lean` (DDM elaboration), not in
   `Strata/Languages/Core/DDMTransform/Translate.lean` (Core
   translation, runs after parsing).

5. **Always validate empirically before committing to a fix.** The
   biggest mistake in the original report (and in the first attempted
   fix for issue (2)) was identifying a walker by grep without
   confirming it was actually on the failure path. Build a candidate
   fix, run the reproducer, *check whether the SIGABRT message
   changes or the threshold shifts*. If neither, you have the wrong
   walker.
