/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.Denote.LExprAnnotatedProps
import Strata.DL.Lambda.Denote.LExprResolveAnnotated

/-!
## Axioms of the annotated-to-polymorphic typing bridge

Pins the axioms of the bridge from annotated typing to polymorphic typing, of
its composition with `resolve`, and of the agreement of `resolve`'s free-variable
annotations with a type map. Each depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.
-/

/-- info: 'Lambda.HasType_of_HasTypeA_of_annots' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Lambda.HasType_of_HasTypeA_of_annots

/-- info: 'Lambda.resolve_output_HasType' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Lambda.resolve_output_HasType

/-- info: 'Lambda.resolve_fvars_annotated_by' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Lambda.resolve_fvars_annotated_by
