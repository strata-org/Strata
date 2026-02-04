/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! # Function Preconditions Tests -/

namespace Strata

-- Simple function with a precondition
def divPgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x div y }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify "cvc5" divPgm

-- Function with multiple preconditions
def multiPrecondPgm :=
#strata
program Core;

function safeSub(x : int, y : int) : int
  requires x >= 0;
  requires y >= 0;
  requires x >= y;
{ x - y }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify "cvc5" multiPrecondPgm

-- Datatype destructor with precondition
def listHeadPgm :=
#strata
program Core;

datatype List { Nil(), Cons(head : int, tail : List) };

function safeHead(xs : List) : int
  requires List..isCons(xs);
{ List..head(xs) }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify "cvc5" listHeadPgm

-- Option type with precondition
def optionGetPgm :=
#strata
program Core;

datatype Option { None(), Some(value : int) };

function get(x : Option) : int
  requires Option..isSome(x);
{ Option..value(x) }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify "cvc5" optionGetPgm

-- Multiple preconditions where second depends on first (WF check)
def dependentPrecondPgm :=
#strata
program Core;

function foo(x : int, y : int) : int
  requires y > 0;
  requires (x div y) > 0;
{ x div y }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify "cvc5" dependentPrecondPgm

-- Call to function with precondition - unconditionally true
def callUnconditionalPgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x div y }

procedure test() returns ()
{
  var z : int := safeDiv(10, 2);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify "cvc5" callUnconditionalPgm

-- Call to function with precondition - depends on path condition (if)
def callWithIfPgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x div y }

procedure test(a : int) returns ()
{
  var z : int;
  if (a > 0) {
    z := safeDiv(10, a);
  } else {
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify "cvc5" callWithIfPgm

-- Call to function with precondition - depends on path condition (assume)
def callWithAssumePgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x div y }

procedure test(a : int) returns ()
{
  assume a != 0;
  var z : int := safeDiv(10, a);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify "cvc5" callWithAssumePgm

end Strata
