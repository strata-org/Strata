/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.Statistics

/-! # Core evaluator statistics keys -/

public section

namespace Core
namespace Evaluator

/-- Statistics keys tracked by type checking, partial evaluation, and the
    statement evaluator. -/
inductive Stats where
  /-- Number of function/operator definitions in the Factory at evaluation start. -/
  | factoryOps
  /-- Number of type declarations in the input program. -/
  | typeDecls
  /-- Number of axiom declarations in the input program. -/
  | axioms
  /-- Number of distinct declarations in the input program. -/
  | distincts
  /-- Number of procedure declarations in the input program. -/
  | procedures
  /-- Number of top-level function declarations in the input program. -/
  | functions
  /-- Number of functions inside recursive function in the input program. -/
  | recursiveFunctions
  /-- Number of (Program × Env) pairs produced by Program.eval. -/
  | verificationEnvironments
  /-- ITE where both branches yielded a single result with no exit label,
      allowing the evaluator to merge them into one path. -/
  | processIteBranches_merged
  /-- ITE where branches could not be merged, causing path explosion.
      This is the primary source of exponential evaluation cost. -/
  | processIteBranches_diverged
  /-- Between-statement merge: path cap was exceeded after a statement
      produced multiple `.none`-exit paths, merged before continuing. -/
  | betweenStmt_capMerged
  /-- Total number of statements stepped through by the partial evaluator. -/
  | simulatedStmts
  /-- Number of times the stmt evaluator ran out of fuel (step budget exhausted). -/
  | simulatingStmtHitOutOfFuel
  /-- Total number of proof obligations (deferred assertions) across all
      verification environments. -/
  | verify_numObligations
  /-- Total number of assumption terms (distinct + path condition) per proof
      obligation, summed across all obligations encoded to SMT. -/
  | smtProofObligation_numAssumptions

#derive_prefixed_toString Stats "Evaluator"

end Evaluator
end Core

end
