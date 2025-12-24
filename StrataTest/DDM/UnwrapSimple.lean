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
op index (@[unwrap] id : Num) : Expression => id;
op index_nounwrap (id : Num) : Expression => id;
op name (@[unwrap] n : Ident) : Expression => n;
op text (@[unwrap] s : Str) : Expression => s;
op decimal_val (@[unwrap] d : Decimal) : Expression => d;
op bytes_val (@[unwrap] b : ByteArray) : Expression => b;
op bool_unwrapped (@[unwrap] b : Bool) : Expression => b;
op bool_wrapped (b : Bool) : Expression => b;

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

/--
info: TestUnwrap.Expression.name {α : Type} : α → (n : String) → TestUnwrap.Expression α
-/
#guard_msgs in
#check TestUnwrap.Expression.name

/--
info: TestUnwrap.Expression.text {α : Type} : α → (s : String) → TestUnwrap.Expression α
-/
#guard_msgs in
#check TestUnwrap.Expression.text

/--
info: TestUnwrap.Expression.decimal_val {α : Type} : α → (d : Decimal) → TestUnwrap.Expression α
-/
#guard_msgs in
#check TestUnwrap.Expression.decimal_val

/--
info: TestUnwrap.Expression.bytes_val {α : Type} : α → (b : ByteArray) → TestUnwrap.Expression α
-/
#guard_msgs in
#check TestUnwrap.Expression.bytes_val

/--
info: TestUnwrap.Expression.bool_unwrapped {α : Type} : α → (b : Bool) → TestUnwrap.Expression α
-/
#guard_msgs in
#check TestUnwrap.Expression.bool_unwrapped

/--
info: TestUnwrap.Expression.bool_wrapped {α : Type} : α → (b : Ann Bool α) → TestUnwrap.Expression α
-/
#guard_msgs in
#check TestUnwrap.Expression.bool_wrapped

-- Verify that index uses unwrapped Nat (not Ann Nat α)
example : TestUnwrap.Expression Unit := .index () 42

-- Verify that index_nounwrap uses wrapped Ann Nat
example : TestUnwrap.Expression Unit := .index_nounwrap () ⟨(), 42⟩

-- Verify that name uses unwrapped String
example : TestUnwrap.Expression Unit := .name () "foo"

-- Verify that text uses unwrapped String
example : TestUnwrap.Expression Unit := .text () "bar"

-- Verify that decimal_val uses unwrapped Decimal
example : TestUnwrap.Expression Unit := .decimal_val () { mantissa := 123, exponent := -2 }

-- Verify that bytes_val uses unwrapped ByteArray
example : TestUnwrap.Expression Unit := .bytes_val () (ByteArray.mk #[0x48, 0x69])

-- Verify that bool_unwrapped uses unwrapped Bool
example : TestUnwrap.Expression Unit := .bool_unwrapped () true

-- Verify that bool_wrapped uses wrapped Ann Bool
example : TestUnwrap.Expression Unit := .bool_wrapped () ⟨(), false⟩
