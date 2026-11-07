/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Transform.FoldAxiomsCorrect

meta section

/-! ## Folding can give a value to an expression that has none

`Core.FoldAxioms.fold_gives_value` proves that `unannotatedSum`, `1 + 2` with the operator
left without a type annotation, has no value in any runtime factory, while the literal `3`
has one. This test pins the other half: Core's factory folds the first to the second. It is
why the folding soundness conditions (`AxiomFoldSound`, `FoldSound`, `RewriteSound`) say
that folding keeps the value an expression has, rather than that folding and the original
evaluate alike, which no runtime factory satisfies. -/

#guard Core.Simplify.fold Core.Factory 100 Core.FoldAxioms.unannotatedSum == .intConst () 3

/-! `Core.FoldAxioms.mistypedSum` is `1 + 2` with `+` annotated at `int → int → bool`, a type
its signature does not have: it denotes a Boolean, and Core's factory folds it to the integer
`3`. This is why the folding conditions ask the operators of an expression to be consistent
with the folding factory (`Lambda.OpsConsistentR`). -/

#guard Core.Simplify.fold Core.Factory 100 Core.FoldAxioms.mistypedSum == .intConst () 3

end
