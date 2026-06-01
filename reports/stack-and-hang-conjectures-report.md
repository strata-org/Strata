# Three issues, distinct root causes: non‑TCO walkers (issues 1, 2) + symbolic-eval array blowup (issue 3)

> **Resolution status (2026-06-01).** Issue (3) is **resolved** by commit
> `277c468cb` on `htd/smack-timeout-fix`. The actual root cause **is not**
> what Conjecture A predicted: the hang was width-O(2^K) array growth in
> `Env.deferred` *inside* `Program.eval`, *before* `oblProgram` and the
> ITE chain are constructed. Specifically, in `evalCFGStep`'s symbolic-
> `condGoto` arm, both `env_t` and `env_f` inherited the parent env's
> `deferred` array; every symbolic branch doubled the pre-split obligation
> set, growing 28 → 56 → 4,928 → 9,856 → 68,992 → 896,896 → 3,960,692,736
> across the 17 procedures of `cjson_cJSON_Parse_harness.bpl`. Materialising
> a 4-billion-element `Array (Imperative.ProofObligation Expression)` was
> the actual hang. Fix: one line, `deferred := #[]` on the false branch,
> mirroring the existing `StatementEval.lean:673` dedup for structured
> `.ite`. Soundness verified empirically (full 94-program sweep: 83 PASS /
> 11 PARTIAL with identical PARTIAL identities to the v4 baseline).
>
> Issues **(1) and (2) remain unsolved**. The analysis below correctly
> identifies them as non-TCO `partial def` walker problems on different
> axes (flat-list mapM for (1), expression-tree depth for (2)); those
> root causes still hold and the proposed fix path (convert to
> explicit-stack / iterative) still applies. The "shared root cause
> across (1)/(2)/(3)" framing in the original Conjecture A is wrong:
> (3) was a different bug (missing dedup in symbolic eval) that
> superficially correlated with obligation count for an unrelated
> reason (more procedures with symbolic branches → more multiplicative
> growth steps).

## 1. Facts about each issue

### Issue (1) — flat-list stack overflow (30K axioms in 34s)

- Trigger: `prog.decls : List Decl` of length tens of thousands; default `--check-mode deductive` path.
- Symptom: SIGABRT (rc=-6), "Stack overflow detected. Aborting." Wall ~34s on 30K axioms; identical at 50K.
- Workaround the user reports: `ulimit -s 65536` (8MB → 64MB) lets the same input complete.
- `strata verify --parse-only` on 100K axioms completes in 1.5s. Only the **post-parse** verify pipeline overflows.
- The user's hypothesis is that `programToCST` walks `prog.decls.mapM declToCST` inside `StateT ToCSTContext`, and that `StateT.bind` is not TCO-ed in the Lean runtime, so each list element grows the native stack by ~4 frames. `ChunkedFormat.formatProgramChunked` is described as a 500-decl chunked workaround. **Note: `ChunkedFormat`/`formatProgramChunked` does not currently exist in the working tree** (`grep` returns zero hits); this is a proposed fix that hasn't landed.

### Issue (2) — deeply-nested-Expr stack overflow (~5000 deep ITE)

`/Users/htd/Documents/Strata-smack/strata-verify-stack-overflow-deeply-nested-expr.md`. Status: present on origin/main.

- Trigger: a single expression nested ~4100+ deep (e.g. 5000-deep `if/then/else` in an ensures clause).
- Symptom: SIGABRT before the parse banner is printed; `--parse-only`, `--type-check`, `--check`, `--no-solve` all crash. Wall ~90 ms.
- Implicates `partial def translateExpr` at `Strata/Languages/Core/DDMTransform/Translate.lean:818` (DDM elaboration) and the same anti-pattern in `toSMTTerm` / `appToSMTTerm` (`SMTEncoder.lean:258, 333`) and in several `partial def` walkers in `DDMTransform/FormatCore.lean`.
- Root-cause shape: direct recursive descent through expression branches with no fuel/iterative fallback; depth bounded by native stack rather than heap.

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

## 4. One-line recommendation

**For (3) — DONE.** Resolved by commit `277c468cb` (`fix(eval): clear Env.deferred on false branch of CFG condGoto`). Diagnosed via per-procedure `dbg_trace s!"[proc-eval-end] {name} (deferred={E.deferred.size})"` instrumentation in `Program.eval`; fixed in one line in `evalCFGStep`. Verification: full 94-program sweep produces 83 PASS / 11 PARTIAL with PARTIAL identities matching the v4 baseline exactly.

**For (1) and (2) — still open. Empirically confirmed against post-fix strata (`htd/smack-timeout-fix` HEAD `2d6c295f2`):**

- Issue (2) reproducer (`N=5000` deep ITE in `ensures`): `Stack overflow detected. Aborting.`, ~1s wall-clock. **Unchanged from pre-fix behaviour.**
- Issue (1) reproducer (flat axiom list, `axiom [axN]: (1 == 1);`): N=30,000 passes (7s — threshold drifted up slightly vs the report's 30K trigger, likely because the simple `1 == 1` axiom is cheaper than the report's actual axioms); N=50,000 SIGABRTs at 13s with `Stack overflow detected. Aborting.`; N=100,000 SIGABRTs at 2s. **Still broken.**

The fix path described originally still applies: convert the `partial def` mutual walkers (`lexprToExpr`/`liteToExpr` for (2); `programToCST`'s `mapM` chain for (1); plus `translateExpr`, `toSMTTerm`/`appToSMTTerm` if the same shape recurs there) to explicit-stack / iterative form. `ulimit -s 65536` is a viable workaround for the user-reported (1) cases until the root-cause fix lands.

## 5. Method note: how (3) was actually diagnosed

For future reference if a similar hang appears: the diagnostic that worked was *not* `lldb` (blocked by macOS DevToolsSecurity codesigning) and *not* `--profile` alone (`profileStep` only prints *after* a step completes — hung steps print nothing). The methods that worked, in order of escalation:

1. **CLI stop-flag bisection.** `strata verify --parse-only` (1s) → `--type-check` (1s) → `--check --no-solve` (TIMEOUT) localised the hang to the transformation pipeline (between Core type-check and SMT generation), not to parsing or solving.
2. **Per-phase logging.** Added a one-line `IO.println s!"[phase-start] {pp.phase.name}"` at `Strata/Languages/Core/Verifier.lean:1177` (gated on `--profile`), rebuilt strata, re-ran. Output identified `symbolicEval` (= `Core.toCoreProofObligationProgram`) as the hung phase.
3. **Per-procedure logging inside `Program.eval`.** Added `dbg_trace` on the `.proc` arm at `Strata/Languages/Core/ProgramEval.lean:61`, printing `proc.header.name` and `E.deferred.size` after `Procedure.eval`. The exponential growth in deferred size was visible in the output; this localised the bug to the symbolic evaluator, not any later phase.

`dbg_trace` is the right tool for instrumenting `Except`-monadic Strata code where `IO.println` is unavailable; combined with line-buffered stdout (`stdbuf -oL -eL`) and `gtimeout`, it produces useful traces even when the process is killed mid-run.
