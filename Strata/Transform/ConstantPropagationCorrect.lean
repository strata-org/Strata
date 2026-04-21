/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.ConstantPropagation

/-! # Constant Propagation Correctness

Constant propagation replaces variable references with their known
constant values. This is semantics-preserving because:

1. We only propagate ground values (literals and `from_str(literal)`)
   that have no free variables.
2. Substituting a variable with its assigned value in subsequent
   expressions is equivalent to evaluating the original program
   where the variable holds that value.
3. We conservatively kill propagated values at control-flow joins
   (loops reset the environment to empty).

## Proved properties

- `propagateConstantsInProgram_decls_length`: the transform preserves
  the number of program declarations (proved in ConstantPropagation.lean).

## Semantics preservation (not yet formalized)

A full semantics-preservation proof would require:
- A store model mapping variables to values
- An evaluation relation for Core statements
- Showing that `substFvars e [(x,v)]` where `v` is ground produces
  the same evaluation result as `e` in a store where `x ↦ v`

This is standard but requires infrastructure not yet formalized in Strata.
The key insight is that ground values (constants and `from_str(literal)`)
have no free variables, so substitution commutes with evaluation.
-/
