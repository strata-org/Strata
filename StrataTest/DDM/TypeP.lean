/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

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
info: inductive TypeP : Type → Type
number of parameters: 1
constructors:
TypeP.expr : {α : Type} → TestTypePType α → TypeP α
TypeP.type : {α : Type} → α → TypeP α
-/
#guard_msgs in #print TypeP
