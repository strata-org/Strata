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
op index_nounwrap (id : Num) : Expression => id;

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

/--
info: TestUnwrap.Expression.index_nounwrap {α : Type} : α → (id : Ann Nat α) → TestUnwrap.Expression α
-/
#guard_msgs in
#check TestUnwrap.Expression.index_nounwrap

-- Verify that index uses unwrapped Nat (not Ann Nat α)
example : TestUnwrap.Expression Unit := .index () 42

-- Verify that index_nounwrap uses wrapped Ann Nat
example : TestUnwrap.Expression Unit := .index_nounwrap () ⟨(), 42⟩
