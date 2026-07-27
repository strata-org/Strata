/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the resolution pass detects type checking errors — e.g. using an int
where a bool is expected, or passing the wrong type to a procedure.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Non-boolean conditions -/

#eval testLaurelResolution <|
#strata
program Laurel;

procedure voidReturn(x: int)
  returns (r: int)
{
  r := 1;
  return
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(x: int): int {
  if x then 1 else 0
//   ^ error: expected 'bool', got 'int'
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure baz() opaque {
  var x: int := 42;
  assert x
//       ^ error: expected 'bool', got 'int'
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure qux() opaque {
  var x: int := 42;
  assume x
//       ^ error: expected 'bool', got 'int'
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure wh() opaque {
  var x: int := 1;
  while (x) { }
//       ^ error: expected 'bool', got 'int'
};
#end

/-! ## Logical operator type checks -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(x: int, y: bool): bool {
  x && y
//^ error: expected 'bool', got 'int'
};
#end

/-! ## Numeric operator type checks -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure cmp(x: string, y: int): bool {
  x < y
//^ error: '<' expected a numeric type, got 'string'
};
#end

/-! ## Assignment type checks -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure invalidAssignment() opaque {
  var x: int := true
//              ^^^^ error: expected 'int', got 'bool'
};
#end

/-! ## Procedure return type checks -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(): int {
  return true
//       ^^^^ error: expected 'int', got 'bool'
};
#end

/-! ## Call argument type checks -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure bar(x: int): int { x };
procedure foo(): int {
  bar(true)
//    ^^^^ error: expected 'int', got 'bool'
};
#end

/-! ## Equality operator type checks -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure cmp(x: int, y: string): bool {
  x == y
//^^^^^^ error: cannot compare 'int' with 'string' using '=='
};
#end

/-! ## Multi-output procedures -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure multi(x: int) returns (a: int, b: int) opaque;
procedure test() opaque {
  assert multi(1) == 1
//       ^^^^^^^^ error: multi-output call cannot be used as a value here
};
#end

/-! A multi-output call in operator-operand (value) position is rejected with a
position-oriented diagnostic, even when both operands have the *same*
`MultiValuedExpr` shape (so `isConsistent` would otherwise accept them). Without
this guard `multi(1) == multi(2)` passes resolution and crashes a later pass as
a `StrataBug`, since `MultiValuedExpr` has no Core lowering. The guard fires per
offending operand (here both), short-circuiting the per-family equality check. -/
#eval testLaurelResolution <|
#strata
program Laurel;
procedure multi(x: int) returns (a: int, b: int) opaque;
procedure test() opaque {
  assert multi(1) == multi(2)
//       ^^^^^^^^ error: multi-output call cannot be used as a value here
//                   ^^^^^^^^ error: multi-output call cannot be used as a value here
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure multi() returns (a: int, b: int) opaque;
procedure test() opaque {
  var x: int := multi()
//              ^^^^^^^ error: expected 'int', got '(int, int)'
};
#end

/-! ## UserDefined cross-type assignment

Assignments between unrelated composites are rejected: `isSubtype` walks
`extending` chains, so two composites with no common ancestor are not
subtypes of each other. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Dog { }
composite Cat { }
procedure test() opaque {
  var x: Dog := new Cat
//              ^^^^^^^ error: expected 'Dog', got 'Cat'
};
#end

/-! ## Field type is read from the field, not a shadowing local

A field reference (`c#flag`) carries the field's `uniqueId`, but its bare
name can collide with a same-named local. `getVarType` must read the field's
declared type (`bool`) — not the shadowing local's type (`int`) — so the
assignment of an `int` to a `bool` field is still rejected. (Regression guard
for the scope-first lookup that previously returned the local's type and
silently dropped the mismatch.) -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite C {
  var flag: bool
}
procedure test() opaque {
  var c: C := new C;
  var flag: int := 0;
  c#flag := flag
//          ^^^^ error: expected 'bool', got 'int'
};
#end

/-! ## `if`/`block` in synth-only operand position

An `if`/`then`/`else` (or non-empty block) used where operands are
synthesized — e.g. as an operand of `==`/`<`/`++` — now has a synth rule
(`Synth.ifThenElse` / `Synth.block`). Previously it hit the synth wildcard
and emitted a spurious "type cannot be synthesized" error. With both
branches consistent, the `if` synthesizes the branch type and resolves
cleanly (no diagnostics). -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(c: bool): bool {
  (if c then 1 else 2) == 3
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(): bool {
  { 1 } == 1
};
#end

/-! ## `if` with incompatible branch types (synth position)

When an `if` is synthesized and its two branches have mutually
inconsistent types, `Synth.ifThenElse` reports the mismatch at the `if`
and synthesizes `Unknown` to suppress cascading errors. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(c: bool): bool {
  (if c then 1 else true) == 3
// ^^^^^^^^^^^^^^^^^^^^^ error: 'if' branches have incompatible types 'int' and 'bool'
};
#end

/-! ## `if` in operand position synthesizes a *symmetric* branch join

`Synth.ifThenElse` returns the symmetric join of the two consistent branch
types as the representative type (`(join ctx thenTy elseTy).getD thenTy`),
not just the then-branch type. So a hole branch (`<?>`, type `Unknown`)
promotes to the other branch's concrete type regardless of branch order:
both `(if c then <?> else "x")` and `(if c then "x" else <?>)` synthesize
`string`. As the operand of a numeric `<`, both orders therefore report the
*same* "expected a numeric type, got 'string'" diagnostic at the *same*
span — locking in symmetry. (Before the join, the then-first order returned
`Unknown` and was silently accepted, while only the else-first order
errored.) -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(c: bool): bool {
  (if c then <?> else "x") < 1
// ^^^^^^^^^^^^^^^^^^^^^^ error: '<' expected a numeric type, got 'string'
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(c: bool): bool {
  (if c then "x" else <?>) < 1
// ^^^^^^^^^^^^^^^^^^^^^^ error: '<' expected a numeric type, got 'string'
};
#end

/-! ## `if` branch join recovers precision from a hole

When one branch is a hole (`Unknown`) and the other is a concrete numeric
type, the join recovers the concrete type (`Unknown ⊔ int = int`) rather
than collapsing to `Unknown`. So `if c then <?> else 5` synthesizes a usable
`int` and resolves cleanly where an `int` is expected — no diagnostics. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure bar(c: bool): int {
  if c then <?> else 5
};
#end

/-! ## Void procedure call in value position

A call to a `void` procedure (no `returns` clause) used where a value is
expected now synthesizes `TVoid` rather than the internal-only empty
`MultiValuedExpr []`. The diagnostic therefore reports the type as `'void'`
instead of the placeholder `'()'` that an empty tuple rendered as. (Regression
guard for `getCallInfo` mapping an empty output list to `TVoid`.) -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure act() opaque;
procedure test() opaque {
  assert act() == 1
//       ^^^^^^^^^^ error: cannot compare 'void' with 'int' using '=='
};
#end

/-! ## Bitvectors are numeric

Bitvector operands (`bv n`) participate in arithmetic and comparison
operators just like the other numeric primitives. `isNumeric` therefore
accepts `TBv`, so a comparison of two bitvector parameters resolves
cleanly with no diagnostics. (Regression guard for `isNumeric` previously
rejecting `TBv` and emitting a spurious "expected a numeric type" error.) -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure cmp(x: bv 32, y: bv 32): bool {
  x < y
};
#end

/-! ## Over-arity calls are rejected

A call that supplies more arguments than the callee declares is rejected with
an arity diagnostic. The check fires only when the callee genuinely resolves to
a procedure with a known parameter count (`procArity`). Under-arity (too few
arguments) is deliberately not flagged. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(x: int): int { x };
procedure bar(): int {
  foo(1, 2)
//^^^^^^^^^ error: call to 'foo' expects 1 argument(s) but 2 were provided
};
#end

/-! ## A too-many-args call to an *unresolved* name does not double-report

Calling a name that does not resolve to any definition with surplus arguments
reports only the name-resolution error — not a spurious arity error on top.
`procArity` returns `none` for an unresolved name (its empty `paramTypes` is an
artifact of the name not being found, not a zero-arity procedure), so the
over-arity check is skipped. (Regression guard for the no-duplicate-diagnostic
behavior.) -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure bar(): int {
  nope(1, 2)
//^^^^^^^^^^ error: 'nope' is not defined
};
#end

/-! ## An unresolved declared type collapses to `Unknown` (no cascade)

A variable declared with an undefined type name reports only the single
"is not defined" name-resolution error. `resolveHighType` collapses the
dangling `UserDefined` to `Unknown` once its name fails to resolve, so the
variable's later uses are not type-checked against a phantom type and no
cascade of follow-on mismatches (`0` vs the bad type, `x` vs `int`) is emitted.
(Regression guard: before the collapse-to-`Unknown` fix this program produced
three diagnostics — the name-resolution error plus the `0`-vs-`UndefinedType`
initializer mismatch and the `x`-vs-`int` use mismatch; it must now produce
exactly one.) -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure useUndef() opaque {
  var x: UndefinedType := 0;
//       ^^^^^^^^^^^^^ error: 'UndefinedType' is not defined
  var y: int := x + 2
};
#end

/-! ## Compound assignment on an unresolved-type target does not cascade

A `+=` (or any compound op) on a target whose type collapsed to `Unknown` reports
only the single "is not defined" error — `compoundAssignAccepts` treats `Unknown`
as acceptable, so no spurious "operator only supported on ..." message stacks on
top (matching how `x++` behaves via `checkIncrDecrTargetType`). -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure compoundOnUndef() opaque {
  var x: UndefinedType := 0;
//       ^^^^^^^^^^^^^ error: 'UndefinedType' is not defined
  x += 1
};
#end

/-! ## TVoid is consistent with any type (TVoid is a supertype)

A nested `if` without an `else` synthesizes `TVoid`. When such an `if` appears
as one branch of an outer `if-else` whose other branch synthesizes a concrete
type (e.g. `int`), the two branches must be consistent. Since `TVoid` means
"I don't care about the value", any type can fill a void position — `TVoid` is
a supertype of everything in the consistency relation.

Regression test for the JVerify switch desugaring bug: a non-exhaustive
statement-form switch desugars to nested `IfThenElse` where the innermost has
no else branch (none → TVoid). The outer cascade's else sees `TVoid` from the
inner if and `int` from other branches, which must be consistent. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure switchStmtNonExhaustive(i: int) opaque {
  var num: int := -1;
  // Desugared non-exhaustive switch: innermost if has no else
  if i == 0 then
    num := 10
  else
    if i == 1 then
      num := 20
    else
      if i == 3 then
        num := 30;
  assert num == 10 || num == 20 || num == 30 || num == -1
};
#end

/-! ## Multi-output procedure calls in transparent bodies and contracts

A Core *function* has exactly one output, so a multi-output procedure — one
declaring ≥ 2 outputs, or a heap-writing procedure, which gains an implicit
`$heap` output during heap parameterization — cannot be lowered to the pure
`$asFunction` twin that transparent bodies and contracts are translated
against. Until that is supported, such a call is rejected at resolution. -/

-- A procedure declaring two outputs, called from a transparent procedure body.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure multi() returns (a: int, b: int) opaque;
procedure callsMultiFromTransparent(): int {
  assign var x: int, var y: int := multi();
//                                 ^^^^^^^ error: calling multi-output procedure 'multi' is not (yet) supported from a transparent procedure or contract
  x
};
#end

-- Same procedure called from a `requires` contract expression.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure multi() returns (a: int, b: int) opaque;
procedure callsMultiFromContract()
  requires { assign var x: int, var y: int := multi(); x == y }
//                                            ^^^^^^^ error: calling multi-output procedure 'multi' is not (yet) supported from a transparent procedure or contract
  opaque
{
};
#end

-- Same procedure called from an `ensures` (postcondition) contract expression.
-- Postconditions are a distinct branch of `restrictedContextExprs` (collected
-- from the opaque body's `posts`), separate from the precondition path above.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure multi() returns (a: int, b: int) opaque;
procedure callsMultiFromPostcondition()
  opaque
  ensures { assign var x: int, var y: int := multi(); x == y }
//                                           ^^^^^^^ error: calling multi-output procedure 'multi' is not (yet) supported from a transparent procedure or contract
{
};
#end

-- A heap-writing procedure with a single declared output has *two* effective
-- outputs after heap parameterization ($heap plus its result), so calling it
-- from a contract is rejected too.
#eval testLaurelResolution <|
#strata
program Laurel;
composite C {
  var value: int
}
procedure bumpAndGet(c: C) returns (r: int)
  opaque
  modifies c
{
  c#value := c#value + 1;
  c#value
};
procedure callsHeapWriterFromContract(c: C)
  requires { var r: int := bumpAndGet(c); r > 0 }
//                         ^^^^^^^^^^^^^ error: calling multi-output procedure 'bumpAndGet' is not (yet) supported from a transparent procedure or contract
  opaque
{
};
#end

-- Negative: a single-output procedure called from a transparent body is fine.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure single(x: int) returns (r: int) opaque;
procedure callsSingleFromTransparent(): int {
  var r: int := single(1);
  r
};
#end

-- Negative: a multi-output call from an ordinary opaque implementation is
-- allowed (opaque bodies are verified as procedures, not lowered to functions).
#eval testLaurelResolution <|
#strata
program Laurel;
procedure multi() returns (a: int, b: int) opaque;
procedure callsMultiFromOpaque() opaque {
  assign var x: int, var y: int := multi();
  assert x == x
};
#end

-- Negative: a void heap-writing procedure has exactly one effective output
-- ($heap only), so it lowers to a single-output function and may be called
-- from a contract.
#eval testLaurelResolution <|
#strata
program Laurel;
composite C {
  var value: int
}
procedure bump(c: C)
  opaque
  modifies c
{
  c#value := c#value + 1
};
procedure callsVoidHeapWriterFromContract(c: C)
  requires { bump(c); true }
  opaque
{
};
#end

-- A multi-output *instance* method called via `self#...` from a transparent
-- instance body. This exercises the `.InstanceCall` arm of `calleesOf` and the
-- container-scoped `refToDef` lookup — a static-call test can't reach either.
#eval testLaurelResolution <|
#strata
program Laurel;
composite D {
  var value: int
  procedure pair(self: D) returns (a: int, b: int) opaque;
  procedure callsPair(self: D): int {
    assign var x: int, var y: int := self#pair();
//                                   ^^^^^^^^^^^ error: calling multi-output procedure 'pair' is not (yet) supported from a transparent procedure or contract
    x
  };
}
#end

-- Cross-composite collision — false positive guard. `A.foo` is multi-output and
-- `B.foo` is single-output; the transparent call `self#foo()` in `B` must
-- resolve to *B's* `foo` (single-output) and NOT be flagged. A name-text keying
-- would resolve to whichever `foo` won the insertion race and could reject this
-- legitimate call. Declaration order A-before-B is the arrangement most likely
-- to trigger a false positive under a name-text keying scheme.
#eval testLaurelResolution <|
#strata
program Laurel;
composite A {
  var w: int
  procedure foo(self: A) returns (a: int, b: int) opaque;
}
composite B {
  var v: int
  procedure foo(self: B) returns (r: int) opaque;
  procedure callerB(self: B): int {
    var r: int := self#foo();
    r
  };
}
#end

-- Cross-composite collision — false negative guard. Mirror of the above with
-- the roles swapped: `A.foo` is multi-output and is genuinely called from A's
-- own transparent body, so the diagnostic MUST fire. `B.foo` (single-output,
-- declared after) must not mask it. A name-text keying with B winning the race
-- would silently accept this call.
#eval testLaurelResolution <|
#strata
program Laurel;
composite A {
  var w: int
  procedure foo(self: A) returns (a: int, b: int) opaque;
  procedure callerA(self: A): int {
    assign var x: int, var y: int := self#foo();
//                                   ^^^^^^^^^^ error: calling multi-output procedure 'foo' is not (yet) supported from a transparent procedure or contract
    x
  };
}
composite B {
  var v: int
  procedure foo(self: B) returns (r: int) opaque;
}
#end

-- Cross-composite collision on the *heap-writer* set. `A.foo` is a heap writer
-- (one declared output + implicit `$heap` = two effective outputs); `B.foo` is
-- pure with one output. The transparent call `self#foo()` in `B` resolves to
-- B's pure `foo` and must not be flagged: keying the heap-writer set by
-- `uniqueId` keeps A's write effect from contaminating B's same-named method.
#eval testLaurelResolution <|
#strata
program Laurel;
composite A {
  var w: int
  procedure foo(self: A) returns (r: int)
    opaque
    modifies self
  {
    self#w := self#w + 1;
    self#w
  };
}
composite B {
  var v: int
  procedure foo(self: B) returns (r: int) opaque;
  procedure callerB(self: B): int {
    var r: int := self#foo();
    r
  };
}
#end
