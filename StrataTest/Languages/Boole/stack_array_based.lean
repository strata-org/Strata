/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- CLRS Chapter 10: Stacks (array implementation)
-- Page 223 of 3rd edition
-- STACK-EMPTY(S)
-- 1  if S.top == 0
-- 2      return TRUE
-- 3  else return FALSE
--
-- PUSH(S, x)
-- 1  S.top = S.top + 1
-- 2  S[S.top] = x
--
-- POP(S)
-- 1  if STACK-EMPTY(S)
-- 2      error "underflow"
-- 3  else
-- 4      x = S[S.top]
-- 5      S.top = S.top - 1
-- 6      return x

private def stackArrayPgm :=
#strata
program Boole;

// Represent the stack array as a map from int to int.
// We follow CLRS and treat indices as 1..n, with `top` in [0..n].
type Array := Map int int;

// Global stack storage, capacity, and top pointer
var S   : Array;
var n   : int;   // capacity of S
var top : int;   // index of top element; 0 means "empty"

// Initialize stack with capacity `cap`
procedure StackInit(cap : int) returns ()
spec
{
  requires cap >= 0;
  modifies n;
  modifies top;
  ensures n == cap;
  ensures top == 0;
}
{
  n := cap;
  top := 0;
};

// STACK-EMPTY(S)
procedure StackEmpty() returns (b : bool)
spec
{
  ensures (b ==> top == 0);
  ensures (top == 0 ==> b);
}
{
  if (top == 0) {
    b := true;
  } else {
    b := false;
  }
};

// PUSH(S, x)
procedure Push(x : int) returns ()
spec
{
  // No overflow: must have room for one more element
  requires top < n;
  modifies S;
  modifies top;

  ensures top == old(top) + 1;
  ensures S[top] == x;

  // Older elements are preserved
  ensures (
    ∀ i:int .
      1 <= i && i <= old(top) ==> S[i] == old(S[i])
  );
}
{
  top := top + 1;
  S := S[top := x];
};

// POP(S)
procedure Pop() returns (x : int)
spec
{
  // No underflow: must be non-empty
  requires top > 0;
  modifies top;

  ensures top == old(top) - 1;
  ensures x == old(S[old(top)]);
}
{
  x := S[top];
  top := top - 1;
};

#end

/--
info:

[DEBUG] Boole program:
 type Array := Map int int;
 var S : Array;
 var n : int;
 var top : int;
 procedure StackInit (cap : int) returns ()
spec {
  requires cap >= 0;
  modifies n;
  modifies top;
  ensures n == cap;
  ensures top == 0;
  } {
  n := cap;
  top := 0;
};
 procedure StackEmpty () returns (b : bool)
spec {
  ensures b ==> top == 0;
  ensures top == 0 ==> b;
  } {
  if (top == 0) {
    b := true;
  } else {
    b := false;
  }
};
 procedure Push (x : int) returns ()
spec {
  requires top < n;
  modifies S;
  modifies top;
  ensures top == old top + 1;
  ensures S[top] == x;
  ensures ∀ i : int :: 1 <= i && i <= old top ==> S[i] == old (S[i]);
  } {
  top := top + 1;
  S := S[top:=x];
};
 procedure Pop () returns (x : int)
spec {
  requires top > 0;
  modifies top;
  ensures top == old top - 1;
  ensures x == old (S[old top]);
  } {
  x := S[top];
  top := top - 1;
};

[Strata.Core] Type checking succeeded.


VCs:
Label: StackInit_ensures_1_1066
Property: assert
Assumptions:
StackInit_requires_0_1015: cap@1 >= 0
Obligation:
true

Label: StackInit_ensures_2_1086
Property: assert
Assumptions:
StackInit_requires_0_1015: cap@1 >= 0
Obligation:
true

Label: StackEmpty_ensures_3_1205
Property: assert
Assumptions:
<label_ite_cond_true: top == 0>: if top@3 == 0 then top@3 == 0 else true
<label_ite_cond_false: !(top == 0)>: if if top@3 == 0 then false else true then if top@3 == 0 then false else true else true
Obligation:
if top@3 == 0 then true else false ==> top@3 == 0

Label: StackEmpty_ensures_4_1233
Property: assert
Assumptions:
<label_ite_cond_true: top == 0>: if top@3 == 0 then top@3 == 0 else true
<label_ite_cond_false: !(top == 0)>: if if top@3 == 0 then false else true then if top@3 == 0 then false else true else true
Obligation:
top@3 == 0 ==> if top@3 == 0 then true else false

Label: Push_ensures_6_1494
Property: assert
Assumptions:
Push_requires_5_1443: top@4 < n@4
Obligation:
true

Label: Push_ensures_7_1525
Property: assert
Assumptions:
Push_requires_5_1443: top@4 < n@4
Obligation:
(S@3[top@4 + 1:=x@1])[top@4 + 1] == x@1

Label: Push_ensures_8_1583
Property: assert
Assumptions:
Push_requires_5_1443: top@4 < n@4
Obligation:
forall __q0 : int :: 1 <= __q0 && __q0 <= top@4 ==> (S@3[top@4 + 1:=x@1])[__q0] == S@3[__q0]

Label: Pop_ensures_10_1840
Property: assert
Assumptions:
Pop_requires_9_1803: top@6 > 0
Obligation:
true

Label: Pop_ensures_11_1871
Property: assert
Assumptions:
Pop_requires_9_1803: top@6 > 0
Obligation:
true

---
info:
Obligation: StackInit_ensures_1_1066
Property: assert
Result: ✅ pass

Obligation: StackInit_ensures_2_1086
Property: assert
Result: ✅ pass

Obligation: StackEmpty_ensures_3_1205
Property: assert
Result: ✅ pass

Obligation: StackEmpty_ensures_4_1233
Property: assert
Result: ✅ pass

Obligation: Push_ensures_6_1494
Property: assert
Result: ✅ pass

Obligation: Push_ensures_7_1525
Property: assert
Result: ✅ pass

Obligation: Push_ensures_8_1583
Property: assert
Result: ✅ pass

Obligation: Pop_ensures_10_1840
Property: assert
Result: ✅ pass

Obligation: Pop_ensures_11_1871
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" stackArrayPgm

example : Strata.smtVCsCorrect stackArrayPgm := by
  gen_smt_vcs
  all_goals (try grind)
