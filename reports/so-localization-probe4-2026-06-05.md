# SO Offender Localization — Probe 4 Results

## 1. Per-tag count table

| Tag | Site (file:line) | Count | Notes |
|---|---|---|---|
| `[CFG-CONDGOTO]` | ProcedureEval.lean:112 | 76 | CFG cond-goto walker fired 76× |
| `[ITE-FORK]` | StatementEval.lean:661 | **0** | Never reached — ITE-fork path inactive in this run |
| `[CFG-CALL]` | StatementEval.lean:780 | 1552 | CFG call-frame fork |
| `[INLINE-CALL]` | StatementEval.lean:831 | 1131 | Inline-call expansion |
| `[VERIFY-TOP]` | Verifier.lean:1154 | 1 | `Core.verify` entered once |
| `[PROGRAM-EVAL]` | ProgramEval.lean:35 | 1 | `Program.eval` entered once |
| `[FOLD-DEFERRED]` | Core.lean:184 | 1 | Fold built `blocks=2,857,392 deferred=2,857,392` |
| `[ENCODE-VC]` | ANFEncoder.lean:197 | 1 | `anfEncodeBody entered: stmts=1 startIdx=0` |
| `[OBLIGATIONS]` | ObligationExtraction.lean:119 | **0** | Never reached |

## 2. Last-trace-before-SIGABRT analysis

The terminal sequence is unambiguous:

```
[CFG-CALL] active=0 finished=40                           ← CFG walker drained cleanly
[FOLD-DEFERRED] ... blocks=2857392 deferred=2857392       ← fold accepted 2.86M-block input
[ENCODE-VC] anfEncodeBody entered: stmts=1 startIdx=0     ← entered ANF, never returned
Stack overflow detected. Aborting.
```

`[ENCODE-VC]` is the **last tag printed**. `[OBLIGATIONS]` (which follows ANF in the pipeline) was never reached. The stack blew **inside `anfEncodeBody`** while traversing the single, monolithic 2.86M-deep ITE statement built by `[FOLD-DEFERRED]`.

Critical finding from `[FOLD-DEFERRED]`: `blocks=2,857,392`, not 40 as the recon synthesis predicted. The earlier "40 obligations" figure was the count of CFG completions (`finished=40`), but each completion deferred ~71k obligations on average — the deferred queue is three orders of magnitude deeper than assumed.

## 3. Offender localization

**Primary offender: `Core.toCoreProofObligationProgram` body builder**
File: `/Users/htd/Documents/Strata-so-dbgtrace/Strata/Languages/Core/Core.lean:185-189`

```lean
let body := match blocks with
  | [] => []
  | [b] => b
  | b :: rest => rest.foldl (fun acc block =>
      [Imperative.Stmt.ite .nondet acc block .empty]) b
```

This `foldl` constructs a **left-nested `Stmt.ite .nondet` tree of depth 2,857,391**. The fold itself completes (foldl is TCO), but produces a single statement whose AST depth equals the number of deferred blocks.

**Trigger site: `ANFEncoder.anfEncodeBody`**
File: `/Users/htd/Documents/Strata-so-dbgtrace/Strata/Transform/ANFEncoder.lean:197+` (and its callee `Statements.collectExprs` at `Statement.lean:486-518`)

`anfEncodeBody` receives `stmts=1` (the monolithic ITE) and recurses non-tail through `Statement.collectExprs` / `Statements.collectExprs`'s `.ite` arm, which walks then-branch then else-branch with `++`. At depth 2.86M, the C stack exhausts long before the recursion completes.

## 4. Mechanism

**Single deep call chain, not fork-compounded.** The depth-driver is the `foldl` at Core.lean:188 transforming a 2.86M-element list into a 2.86M-deep nested ITE. Every downstream consumer that recurses structurally on `Stmt.ite` arms inherits this depth. ANF is the *first* such consumer, so it's the one that fires the abort. Even if ANF were tail-recursive, ObligationExtraction.extractGo (also non-TCO) would blow next.

The ITE-FORK count of 0 confirms this isn't a runaway fork during evaluation — evaluation completed (`active=0 finished=40`). The pathology is purely in the **post-evaluation lowering shape**.

## 5. Concrete fix sketch

The fix is in **Core.lean:185-189**, not in ANF. Two options, in order of preference:

**Option A (recommended): eliminate the ITE tree entirely.** Each deferred block is an independent obligation. Make the procedure body a flat sequence (or, since blocks must remain logically alternative for nondet-choice semantics, generate one top-level decl per block):

```lean
-- Instead of folding into nested .ite .nondet, just concatenate:
let body := blocks.flatten   -- flat list of statements, all obligations preserved
```

This changes obligation semantics from "verify any one of N alternatives" to "verify all N" — but ObligationExtraction already iterates per-obligation, so the nondet wrapping was redundant scaffolding.

**Option B (if alternatives semantics required): balanced tree.** Replace the left-nested `foldl` with a balanced bisection so depth is `log2(2.86M) ≈ 22` instead of 2.86M:

```lean
let rec balanced : List (List Stmt) → List Stmt
  | [] => []
  | [b] => b
  | bs => let (l, r) := bs.splitAt (bs.length / 2)
          [Stmt.ite .nondet (balanced l) (balanced r) .empty]
```

Either fix removes the SO without touching ANF/ObligationExtraction.

## 6. Confidence assessment

**Empirically established:**
- Last tag printed = `[ENCODE-VC]` → SO is in or below `anfEncodeBody` (high confidence).
- `blocks=2,857,392` → the depth-driver is real and three orders of magnitude beyond prior assumption (measured directly).
- CFG walker drained (`active=0 finished=40`) → not a CFG-walker bug (ruled out empirically).
- `[OBLIGATIONS]` never fired → SO precedes ObligationExtraction (sequenced empirically).

**Still inferred (not directly measured):**
- That `Statements.collectExprs` specifically (vs another callee inside `anfEncodeBody`) is the recursive descent that overflows. ANFEncoder calls multiple non-TCO walkers; we haven't pinned which.
- That balanced-tree (Option B) actually compiles within ANF's stack budget at depth ~22.

**Tightening probe (probe 5):** insert `dbg_trace` at the entry of each callee `anfEncodeBody` invokes — `Statements.collectExprs`, `collectSubexprs`, `replaceExprs.go`, `collectSubexprHashes.go` — with a depth counter. The last one to fire pins the exact recursion. Cheap: 4 more `dbg_trace`s, one rebuild.

## 7. BACKLOG update recommendation

Replace the probe-3 "process of elimination" section in `/Users/htd/Documents/Strata/reports/BACKLOG.md` with:

> **SO offender pinned (probe 4, 2026-06-05)** — root cause is `Core.toCoreProofObligationProgram` at `Strata/Languages/Core/Core.lean:185-189`. The `rest.foldl` builds a left-nested `Stmt.ite .nondet` AST of depth = `postEvalEnv.deferred.size`. Probe 4 measured 2,857,392 blocks on the failing input (sce3.bpl), producing a 2.86M-deep tree. Stack overflows at the first downstream non-TCO consumer (`ANFEncoder.anfEncodeBody` at `Strata/Transform/ANFEncoder.lean:197+`) before `ObligationExtraction.extractObligations` is reached. CFG walker drains cleanly (`active=0 finished=40`); evaluation is not at fault. Fix lives in Core.lean:185-189, not ANF — either flatten blocks (Option A) or balance the tree (Option B). Probe-3's "process of elimination" framing was correct in direction (post-evaluation) but underestimated depth by 5 orders of magnitude (40 → 2.86M). Probe 5 would pin which ANF callee specifically overflows; not on critical path for the fix.

Files to update:
- `/Users/htd/Documents/Strata/reports/BACKLOG.md` (replace probe-3 elimination section)
- `/Users/htd/Documents/Strata/reports/INDEX.md` (cross-link to the pinned localization)
