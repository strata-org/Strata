# `procedureToGotoCtx` rename collision: inout params re-bound to a non-existent local symbol, blocking every CBMC translation with inout call sites

- **Status:** present on origin/main (HEAD: `a845a654b36fbb520c9c920d278cbb3656d76ba3`)
- **Severity:** high
- **Component:** `Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline` (Core → CProverGOTO translator)
- **File / lines:** [`Strata/Backends/CBMC/GOTO/CoreToGOTOPipeline.lean:271-277`](https://github.com/strata-org/Strata/blob/a845a654b36fbb520c9c920d278cbb3656d76ba3/Strata/Backends/CBMC/GOTO/CoreToGOTOPipeline.lean#L271-L277)

## What's wrong

Strata Core inout parameters appear in both `Procedure.Header.inputs` and `Procedure.Header.outputs` ([`StatementType.lean:25-30`](https://github.com/strata-org/Strata/blob/a845a654b36fbb520c9c920d278cbb3656d76ba3/Strata/Languages/Core/StatementType.lean#L25-L30)). `procedureToGotoCtx` builds the body-rewrite rename map by folding `formals.zip new_formals ++ outputs.zip new_outputs ++ locals.zip new_locals` (line 276); outputs come second, so for any inout name the formal entry (`pname::x`) is overwritten by the local entry (`pname::1::x`). After `renameExpr` rewrites the body, every inout reference resolves to a local that has no parameter-passing semantics. At call sites, [`getInputExprs`](https://github.com/strata-org/Strata/blob/a845a654b36fbb520c9c920d278cbb3656d76ba3/Strata/Languages/Core/Statement.lean#L105-L109) synthesizes `LExpr.fvar () id none` for inout args, and [`toGotoExprCtx`](https://github.com/strata-org/Strata/blob/a845a654b36fbb520c9c920d278cbb3656d76ba3/Strata/Backends/CBMC/GOTO/LambdaToCProverGOTO.lean#L274-L276) (only matches `(some ty)`) falls through to its catchall.

| Call form                       | Expected             | Actual on origin/main                              |
|---------------------------------|----------------------|----------------------------------------------------|
| `call helper(inout y)`          | translation succeeds | error: `LExpr.fvar … name := "main::1::y" … none`  |
| `call helper(out y)` (control)  | translation succeeds | translation succeeds                               |

## Reproduction

Save as `repro.lean` at the repo root, then `lake build Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline && lake env lean repro.lean`:

```lean
import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
open Strata

def InoutCall := #strata
program Core;
procedure helper(inout x : int) { x := x; };
procedure main(inout y : int)   { call helper(inout y); };
#end

#eval do
  let cprog := (TransM.run Inhabited.default (translateProgram InoutCall)).fst
  let procs := cprog.decls.filterMap fun d => Core.Decl.getProc? d
  match procs[1]? with
  | some p => match procedureToGotoCtx Lambda.TEnv.default p with
              | .ok _    => IO.println "OK"
              | .error e => IO.println (toString e)
  | none => pure ()
```

Output: `[toGotoExprCtx] Not yet implemented: LExpr.fvar () { name := "main::1::y", metadata := () } none`. Replacing `inout` with `out` in both procedures (control case) makes the same program translate cleanly.

## Impact

Any caller of `procedureToGotoCtx` on a procedure that passes an inout argument at a call site fails outright. The in-tree `StrataCoreToGoto` binary on `main` happens to use the older `transformToGoto` path so the bug isn't yet visible from the binary, but downstream branches wiring `coreToGotoFiles` to the binary (e.g. for SMACK pipeline integration) hit this on essentially every realistic C translation.

## Fix

Two coordinated changes in `CoreToGOTOPipeline.lean`:

1. Filter outputs that are also formals before zipping into the rename map and `outputEntries` — inouts should rename to the formal-symbol form.
2. In `coreStmtsToGoto`'s call-translation arm ([line 150](https://github.com/strata-org/Strata/blob/a845a654b36fbb520c9c920d278cbb3656d76ba3/Strata/Backends/CBMC/GOTO/CoreToGOTOPipeline.lean#L150)), look up the type for typeless inout-arg fvars from `trans.T.context.types` (already used a few lines down for the lhs) before calling `toGotoExprCtx`.

Both verified empirically: change #1 alone mutates the error name from `main::1::y` to `main::y`; change #1 + #2 together produces well-formed `symtab.json` and `goto.json`.

## Plan to test

- Positive: the repro above prints `OK` and the emitted FUNCTION_CALL references `main::y`, not `main::1::y`.
- Negative: replacing `inout` with `out` in the repro continues to succeed, with `y` resolved to `main::1::y`.
- Round-trip: a procedure with both an inout and a pure out produces a symbol table where the inout maps to the formal and the out to the local, with no collision.
