/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.CallGraph

/-! # Per-goal irrelevant-axiom filtering for Strata Core verification

This module provides a two-step API designed for use inside a verification loop:

1. `Cache.build` precomputes the function call graph and the
   function-to-immediate-axioms map once per program.
2. `getIrrelevantAxioms` uses that cached data to answer per-goal relevance
   queries efficiently.

This avoids rebuilding the call graph and axiom map on every proof obligation,
which would be expensive for programs with many goals.

See `IrrelevantAxiomsMode` in `Options.lean` for the soundness discussion and
the distinction between `Aggressive` and `Precise` modes.
-/

namespace Core

public section

namespace IrrelevantAxioms

/-- Precomputed data for efficient per-goal axiom relevance queries.
  Build once with `Cache.build` before a verification loop and reuse
  across all goals for the same program. -/
structure Cache where
  funcCG   : FunctionCG
  axiomMap : FuncAxMap

/-- Build the cache from `prog`. -/
def Cache.build (prog : Program) : Cache :=
  { funcCG   := prog.toFunctionCG
    axiomMap := prog.functionImmediateAxiomMap }

/-- Compute the axioms irrelevant to `functions` using precomputed `cache`.
  This is the efficient per-goal counterpart of the old
  `Program.getIrrelevantAxioms`: it uses the transitive fixed-point algorithm
  (`computeRelevantAxioms`) but reuses the prebuilt call graph and axiom map
  instead of reconstructing them on every call. -/
def getIrrelevantAxioms (prog : Program) (cache : Cache) (functions : List String)
    : List String :=
  let allAxioms := prog.decls.filterMap (fun decl =>
    match decl with | .ax a _ => some a.name | _ => none)
  let relevantAxioms := functions.flatMap (fun f =>
    let initialFns :=
      (f :: cache.funcCG.getCalleesClosure f ++ cache.funcCG.getCallersClosure f).dedup
    computeRelevantAxioms prog cache.funcCG cache.axiomMap initialFns []) |>.dedup
  allAxioms.filter (fun a => a ∉ relevantAxioms)

end IrrelevantAxioms

end -- public section
end Core
