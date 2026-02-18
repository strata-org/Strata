/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Integration.Lean

/-
This test for regressions involving TypeP and empty types.
-/


#dialect
dialect TestTypeP;

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

#end

#strata_gen TestTypeP

/--
info: private inductive TypeP : Type → Type
number of parameters: 1
constructors:
_private.StrataTest.DDM.TypeP.0.TypeP.expr : {α : Type} → TestTypePType α → TypeP α
_private.StrataTest.DDM.TypeP.0.TypeP.type : {α : Type} → α → TypeP α
-/
#guard_msgs in #print TypeP
