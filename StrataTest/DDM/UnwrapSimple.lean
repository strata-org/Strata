/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

open Strata

#dialect
dialect TestUnwrap;

category Expression;

op var (name : Ident) : Expression => name;
op index (id : Num) : Expression => id:Nat;

#end

namespace TestUnwrap

#strata_gen TestUnwrap

end TestUnwrap

/--
info: TestUnwrap.Expression (α : Type) : Type
-/
#guard_msgs in
#check TestUnwrap.Expression

/--
info: TestUnwrap.Expression.var {α : Type} : α → (name : Ann String α) → TestUnwrap.Expression α
-/
#guard_msgs in
#check TestUnwrap.Expression.var

/--
info: TestUnwrap.Expression.index {α : Type} : α → (id : Nat) → TestUnwrap.Expression α
-/
#guard_msgs in
#check TestUnwrap.Expression.index

-- Verify that index uses unwrapped Nat (not Ann Nat α)
example : TestUnwrap.Expression Unit := .index () 42
