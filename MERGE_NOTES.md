# Merge with upstream/main (strata-org/Strata) — resolution notes

This merge integrates `upstream/main` while preserving the fork's Core typing
specifications (needed by the `strata-generators` repo, which derives sound &
complete generators against them).

## Resolution strategy

- **Prefer upstream** for everything except the Core typing-spec cluster.
- Upstream removed several subprojects (StrataPython, StrataDDM, StrataBoole,
  Tools, StrataCLI) — deletions accepted.
- Adopted upstream's **new factory API** (commit `2e627b784`: `WFLFunc`/`FuncWF`
  gained `concreteEval_freeVars`, `body_freevars`, `precond_freevars`).
- Kept the fork's **typing layer** (LExprTypeSpec, LExprTypeEnv, LTyUnify(Props),
  LExprWF, LTy, Factory's `arrowsBinary` guard, CmdType `checkAnnotCompat`,
  Util/Tactics) and all fork-only `*TypeSpec*` files.

## Notable seam decisions

- Reverted upstream's quant-unify commit `3f079df8f` in `LExprT.lean` and
  `Denote/LExprResolveAnnotated.lean` to match the fork's non-unifying
  `resolveAux` (the fork's typing specs are written against it).
- `LExprWF.lean` / `Map.lean`: additive merges (upstream lemmas + fork lemmas).
- `Expressions.lean`: re-added fork's `HasVarsPure Expression Expression.Expr`
  instance on top of upstream.

## Build status

- **`Strata` main library: builds green** on the new factory API.
- **All modules imported by `strata-generators`: build green.**
- 10 of 12 fork-only Core spec files build.

## Known follow-ups (WIP — not blocking strata-generators)

These are NOT imported by `strata-generators`:

1. `FunctionTypeSpecProps.lean` / `StatementTypeSpecProps.lean` — carry `sorry`:
   - 3 pre-existing WIP sorries (predate this merge).
   - 2 new `sorry`s for upstream's new `FuncWF` obligations `body_freevars` /
     `precond_freevars` (the typechecker's `freeVarChecks` guard should
     establish these; the bridge lemma is not yet ported).

2. 9 upstream-verbatim tests fail because the fork's typechecker intentionally
   differs from upstream (these `#guard_msgs`-assert upstream behavior):
   - `StrataTest/DL/Lambda/LExprTTests.lean` (quant body must already be bool)
   - `StrataTest/Languages/Core/Tests/StatementTypeTests.lean`,
     `ProgramTypeTests.lean` (monomorphic-annotation check)
   - `StrataTest/Languages/Core/Examples/TypeAlias.lean`
   - `StrataTest/DL/Imperative/ArithType.lean` (`checkAnnotCompat` field)
   - `StrataTest/EmbeddedDataFreshness.lean`
   - 3 Laurel `Composites/*` end-to-end tests
   - 2 fork-only probes (`AmbientTyvarGenProbe`, `RhoProbe`) with `#eval` syntax

   To resolve later: regenerate the `#guard_msgs` expected outputs to match the
   fork's typechecker behavior.
