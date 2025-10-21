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
info: inductive TypeP : Type
number of parameters: 0
constructors:
TypeP.expr : TestTypePType → TypeP
TypeP.type : TypeP
-/
#guard_msgs in #print TypeP
