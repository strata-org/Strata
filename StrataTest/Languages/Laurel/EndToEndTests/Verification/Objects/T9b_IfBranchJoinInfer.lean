/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Why an annotation is sometimes load-bearing, not bureaucratic: it lets typing be
*deferred* to a context that supplies a common type.

`Left` and `Right` are siblings under `Top`. Their branch *join* is invariant and
has no gradual escape hatch: `isConsistent Left Right` bottoms out in structural
equality (`Left ≠ Right`), and there is no least-common-supertype rule, so
`Left ⊔ Right` is undefined even though both extend `Top`.

Consequently the two ways of writing the same binding diverge:

* `var y : Top := if c then new Left else new Right` — the annotation is pushed
  *into both branches* (check mode, rule If⇐). Each branch is checked against
  `Top`, both satisfy `<: Top`, and the binding is accepted. The annotation
  defers the join to the expected type `Top`.

* `var y := if c then new Left else new Right` — with no annotation, the binding
  *synthesizes* the initializer (rule Decl-Synth → If⇒). Synthesis must join the
  branches itself, `Left ⊔ Right` is undefined, and the binding is rejected.

This is the concrete payoff of optional annotations cutting *both* ways: dropping
the annotation defers typing to the use site only when the initializer can
synthesize on its own; when it cannot (an unjoinable `if`, a bare hole, …), the
annotation is exactly what supplies the missing type. Compare `T9_IfBranchJoin`,
which covers the annotated branch-mismatch case.
-/

-- Annotated: `Top` is pushed into both branches; both `<: Top`, so accepted.
#eval testLaurelResolution <|
#strata
program Laurel;
composite Top { }
composite Left extends Top { }
composite Right extends Top { }
procedure annotatedDefersJoin(c: bool) opaque {
  var y: Top := if c then new Left else new Right
};
#end

-- Unannotated: the binding synthesizes the `if`, whose branches do not join
-- (`Left ⊔ Right` is undefined — invariant, no `Unknown` escape), so it is
-- rejected. The annotation in the previous procedure is what made it type.
#eval testLaurelResolution <|
#strata
program Laurel;
composite Top { }
composite Left extends Top { }
composite Right extends Top { }
procedure inferredCannotJoin(c: bool) opaque {
  var y := if c then new Left else new Right
//         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: 'if' branches have incompatible types 'Left' and 'Right'
};
#end
