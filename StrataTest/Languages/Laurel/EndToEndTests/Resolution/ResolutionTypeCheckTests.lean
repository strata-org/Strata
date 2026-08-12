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
//^^^^^ error: no overload of '$lt' matches the argument types
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
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: no overload of '$lt' matches the argument types
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(c: bool): bool {
  (if c then "x" else <?>) < 1
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: no overload of '$lt' matches the argument types
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

/-! ## Datatype constructor argument type checks

A datatype constructor call is type-checked against its declared field types at
resolution time (rather than deferred to Core): an argument whose type is
inconsistent with a *concrete* declared field type is rejected here. -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Box {
  Wrap(value: int)
}
procedure foo() opaque {
  var b: Box := Wrap(true)
//                   ^^^^ error: expected 'int', got 'bool'
};
#end

/-! The success side of the same dispatch: a concrete declared field type accepts
an argument of that type. Pinned separately from the error case because the two
share one code path — the polymorphic-slot test — and a change that widened that
test too far would silently stop checking concrete slots without failing the
negative above. -/
#eval testLaurelResolution <|
#strata
program Laurel;
datatype Box {
  Wrap(value: int)
}
procedure fooOk() opaque {
  var b: Box := Wrap(5)
};
#end

/-! A field whose declared type is one of the datatype's own type parameters is a
polymorphic (erased) slot: it accepts an argument of any type, so a generic
constructor call resolves cleanly regardless of the argument's concrete type —
there is nothing to check against the type variable at the call site. -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
procedure foo() opaque {
  var a: Option<int> := Some(42);
  var b: Option<bool> := Some(true)
};
#end

/-! A constructor may mix polymorphic and concrete slots, and the two are decided
per *field*, not per datatype: `value: T` is erased (any argument is accepted)
while `count: int` is still checked. So the same call can pass on one argument and
be rejected on the next. -/

-- The concrete slot rejects a bad argument even though the constructor also has a
-- polymorphic one.
#eval testLaurelResolution <|
#strata
program Laurel;
datatype Box2<T> {
  Wrap(value: T, count: int)
}
procedure mixedSlotsBad() opaque {
  var b: Box2<int> := Wrap(42, "oops")
//                             ^^^^^^ error: expected 'int', got 'string'
};
#end

-- And the polymorphic slot stays unchecked in the same constructor: an argument
-- whose type has nothing to do with the instantiation is accepted for `value`,
-- while `count` still takes an `int`.
#eval testLaurelResolution <|
#strata
program Laurel;
datatype Box2<T> {
  Wrap(value: T, count: int)
}
procedure mixedSlotsOk() opaque {
  var b: Box2<int> := Wrap(true, 7)
};
#end

/-! ## Optional type annotations (type hints)

The binding annotation is optional. `var x := e` (no annotation) recovers the
type by *synthesizing* the initializer and adopting its type for the binding
(rule **Decl-Synth**); `var x` (neither annotation nor initializer) has no type
to read off, so it binds `x : Unknown` and reports a diagnostic. -/

/-! ### Decl-Synth: `var x := e` infers `x`'s type from the initializer.

`x` is inferred `int` from `42`; using it where `bool` is expected reports a
mismatch with `got 'int'` — proving the recovered type is the precise `int`,
not the gradual `Unknown` (which would silently absorb the `assert`). -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferFromInit() opaque {
  var x := 42;
  assert x
//       ^ error: expected 'bool', got 'int'
};
#end

/-! ### Decl-Synth: a consistent later use produces no diagnostics.

`x` is inferred `int` and returned where `int` is expected, so the program is
accepted with no errors. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferConsistent(): int {
  var x := 42;
  return x
};
#end

/-! ### Decl-Synth: the inferred type flows through a checked position.

`x` is inferred `bool`; returning it where the procedure's declared output
`int` is expected fails — the inferred type participates in subsumption like
any annotated one. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferThenReturn(): int {
  var x := true;
  return x
//       ^ error: expected 'int', got 'bool'
};
#end

/-! ### `var x` with neither annotation nor initializer binds `Unknown` + diagnoses.

There is nothing to read a type from, so the declaration is diagnosed and `x`
is bound at the gradual `Unknown`. The single diagnostic is the inference
failure; the later `assert x` is *not* re-reported (Unknown is consistent with
`bool`), confirming the binding suppresses cascades. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure noAnnotationNoInit() opaque {
  var x;
//^^^^^ error: cannot infer a type for 'x'
  assert x
};
#end

/-! ### Decl-Synth works with a synthesizing `if` initializer.

`if c then 1 else 2` synthesizes `int` (its branches are mutually consistent),
so `var x := if …` infers `x : int`; the later `assert x` then reports the
int/bool mismatch. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferFromIf(c: bool) opaque {
  var x := if c then 1 else 2;
  assert x
//       ^ error: expected 'bool', got 'int'
};
#end

/-! ### A `var x := e` with an unresolved initializer does not cascade.

The initializer fails name resolution (one diagnostic); `x` is inferred
`Unknown` from the failed synthesis, so the later `assert x` is not
re-reported. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferFromUndef() opaque {
  var x := nope;
//         ^^^^ error: 'nope' is not defined
  assert x
};
#end

/-! ### The inferred type is enforced on later reassignment.

`x` is inferred `int` from `1`; a later `x := "hello"` is rejected exactly as
if `x` had been annotated `int` — inference fixes the binding's type once and
for all, it does not leave the variable gradually retypable. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferThenReassign() opaque {
  var x := 1;
  x := "hello";
//     ^^^^^^^ error: expected 'int', got 'string'
  assert x
//       ^ error: expected 'bool', got 'int'
};
#end

/-! ### A void initializer is rejected: there is no value to bind.

A call to a procedure with no outputs synthesizes `TVoid` (the n = 0 case of
Static-Call). Decl-Synth requires the initializer to synthesize a *value*
type (`declInferValueType`), so `var x := doNothing()` is diagnosed at the
initializer rather than silently binding `x : void`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure doNothing() opaque { };
procedure inferFromVoidCall() opaque {
  var x := doNothing()
//         ^^^^^^^^^^^ error: cannot infer a type for 'x': the initializer yields no value (type 'void')
};
#end

/-! ### …and the rejected binding falls back to `Unknown`, not `void`.

After the void-initializer diagnostic, `x` is bound at the gradual `Unknown`,
so the later `assert x` does not cascade a second error. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure doNothing() opaque { };
procedure voidBindingSuppressesCascade() opaque {
  var x := doNothing();
//         ^^^^^^^^^^^ error: cannot infer a type for 'x': the initializer yields no value (type 'void')
  assert x
};
#end

/-! ### A multi-output call as initializer is rejected.

A call to a procedure with two outputs synthesizes `MultiValuedExpr [int, int]`
(Static-Call-Multi) — an internal pseudo-type a single variable cannot hold
(the surface syntax for unpacking is `assign var a, var b := twoOut()`).
Decl-Synth rejects it with the same position-oriented diagnostic operators
use for multi-output operands, and binds `x : Unknown` so the later use does
not cascade. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure twoOut() returns (a: int, b: int)
  opaque;
procedure inferFromMultiOut() opaque {
  var x := twoOut();
//         ^^^^^^^^ error: multi-output call cannot be used as a value here
  assert x
};
#end

/-! ### A `while` initializer is rejected the same way.

Statement-shaped constructs (`while`, `if` without `else`, …) synthesize
`TVoid`, so `var x := while …` hits the same no-value guard as the void
call — rather than binding `x : void` silently. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferFromWhile(c: bool) opaque {
  var x := while (c) { };
//         ^^^^^^^^^^^^^ error: cannot infer a type for 'x': the initializer yields no value (type 'void')
  assert x
};
#end

/-! ### …and so is an `if` without an `else`.

An else-less `if` is statement-shaped (there is no value on the false path),
so it synthesizes `TVoid` and `var x := if c then 1` hits the same no-value
guard as `while` and void calls. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferFromIf() opaque {
  var c: bool := true;
  var x := if c then 1;
//         ^^^^^^^^^^^ error: cannot infer a type for 'x': the initializer yields no value (type 'void')
  assert x
};
#end

/-! ### Void expressions cannot be compared with `==` either.

`isConsistent` relates `TVoid ~ TVoid` (it is plain constructor equality), but
comparing two void expressions is meaningless — there are no values to
compare. Op-Eq now rejects a void operand even when both sides agree. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure doNothing() opaque { };
procedure compareVoid() opaque {
  assert doNothing() == doNothing()
//       ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: cannot compare 'void' with 'void' using '=='
};
#end

/-! ### `var x := x`: the initializer is resolved before the binding exists.

Decl-Synth synthesizes the initializer *before* introducing the binding, so a
self-referential `var x := x` with no outer `x` reports only "'x' is not
defined"; `x` is then bound `Unknown` from the failed synthesis, and the later
`assert x` does not cascade. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure selfRefNoOuter() opaque {
  var x := x;
//         ^ error: 'x' is not defined
  assert x
};
#end

/-! ### …and with an outer `x` in scope, the initializer reads the *outer* one.

Same order-of-events, other outcome: in a nested block, the initializer of
`var x := x` resolves in the enclosing scope (the new `x` is not yet defined),
so the inner `x` is inferred `int` from the outer binding — proved by the inner
`assert x` reporting `got 'int'`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure selfRefOuterShadow() opaque {
  var x := 1;
  {
    var x := x;
    assert x
//         ^ error: expected 'bool', got 'int'
  }
};
#end

/-! ### Inference chains: from a parameter, and from another inferred variable.

The initializer can be any synthesizing expression, including a parameter
reference or a previously *inferred* variable: `x` is inferred `int` from the
parameter `p`, `y` is inferred `int` from `x`, and the mismatch surfaces only
at the final use. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferChained(p: int) opaque {
  var x := p;
  var y := x;
  assert y
//       ^ error: expected 'bool', got 'int'
};
#end

/-! ### Decl-Synth infers from string and decimal literals too.

Same rule, other literal shapes: `"hi"` synthesizes `string` and `1.5`
synthesizes `real`; each later `bool` use names the precise inferred type. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferOtherLiterals() opaque {
  var s := "hi";
  var d := 1.5;
  assert s;
//       ^ error: expected 'bool', got 'string'
  assert d
//       ^ error: expected 'bool', got 'real'
};
#end

/-! ### Duplicate definition: the re-declaration is flagged, then rebinds gradually.

Inference does not change duplicate detection — re-declaring `x` reports the
usual duplicate diagnostic. The duplicate binding is recovered as *unresolved*,
whose type is `Unknown`, so after the duplicate, uses of `x` are gradually
typed: the `assert x` reports neither `int` (first binding) nor `bool`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferDuplicate() opaque {
  var x := 1;
  var x := true;
//    ^ error: Duplicate definition 'x' is already defined in this scope
  assert x
};
#end

/-! ### An unjoinable `if` initializer diagnoses once and binds `Unknown`.

The primitive cousin of `T9b_IfBranchJoinInfer` (which covers unjoinable
composite siblings and the annotated escape): synthesizing
`if c then 1 else "s"` fails to join `int` and `string`, so the `if` reports
one diagnostic and synthesizes `Unknown`; `x` adopts `Unknown` and the later
`assert x` does not cascade. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inferUnjoinableIf(c: bool) opaque {
  var x := if c then 1 else "s";
//         ^^^^^^^^^^^^^^^^^^^^ error: 'if' branches have incompatible types 'int' and 'string'
  assert x
};
#end

/-! ### Decl-Synth in value position: the inferred binding is consumed.

A declaration is an `Assign` node and synthesizes its bound type, so an
*unannotated* declaration in value position hands its inferred `int` to the
surrounding arithmetic — accepted with no diagnostics. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure declValueConsumed() opaque {
  var y: int := (var x := 5) + 1
};
#end

/-! ### Decl-Synth nests: the inner synthesized type is the outer's initializer.

`var x := 5` synthesizes `int`, which `var y := …` adopts in turn — proved by
the later `y := "hello"` reporting `expected 'int'`, exactly as in
`inferThenReassign`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure declValueNested() opaque {
  var y := (var x := 5);
  y := "hello"
//     ^^^^^^^ error: expected 'int', got 'string'
};
#end

/-! ### A mistyped declaration in a *checked* value position is rejected.

In checked positions `Check.declInfer` still runs the \[⇐\] Sub boundary
check after adopting the initializer's type, so a declaration argument whose
inferred `int` does not subsume into the parameter's `bool` is rejected at
resolution. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure takesBool(b: bool) opaque;
procedure declValueChecked() opaque {
  takesBool((var x := 1))
//           ^^^^^^^^^^ error: expected 'bool', got 'int'
};
#end

/-! ### …and as the last statement of a value-position block, it passes.

The block pushes its expected `int` to its last statement; `Check.declInfer`
synthesizes `int` for the unannotated declaration and the boundary check
passes — accepted with no diagnostics. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure declValueBlock() opaque {
  var y: int := { var x := 5 }
};
#end

/-! ### Multi-assign declared targets infer from the callee's outputs.

The `assign` form's declared targets may now omit the annotation, exactly like
`var x := e`: each unannotated `var` target adopts the callee's corresponding
declared output type. Here `a` infers `int` and `b` infers `bool` — proved by
the later asserts: `assert b` (a `bool`) is fine, `assert a` reports the
int/bool mismatch. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure intBool() returns (i: int, b: bool)
  opaque;
procedure multiAssignInfer() opaque {
  assign var a, var b := intBool();
  assert b;
  assert a
//       ^ error: expected 'bool', got 'int'
};
#end

/-! ### Mixed annotated/unannotated/existing multi-assign targets.

Inference is per-target: `x` keeps its annotation, `y` is an existing `int`
variable, `z` infers `bool` from the third output. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure threeOut() returns (i: int, j: int, b: bool)
  opaque;
procedure multiAssignMixed() opaque {
  var y: int := 0;
  assign var x: int, y, var z := threeOut();
  assert z;
  assert x
//       ^ error: expected 'bool', got 'int'
};
#end

/-! ### Multi-assign arity mismatch still diagnoses with unannotated targets.

With two targets against three outputs there is no component to adopt: the
mismatch is reported as a dedicated arity diagnostic naming the two counts
(rather than a tuple mismatch against the `Unknown` fallback bindings), the
unannotated targets bind `Unknown`, and `assert a` stays quiet (no cascade). -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure threeOut() returns (i: int, j: int, b: bool)
  opaque;
procedure multiAssignArity() opaque {
  assign var a, var b := threeOut();
//                       ^^^^^^^^^^ error: tried to unpack 3 values into 2 variables
  assert a
};
#end

/-! ### Multi-assign with a non-multi-valued RHS.

A scalar RHS has no components to distribute at all: the unannotated targets
bind `Unknown` and the tuple boundary check reports the single mismatch
against the scalar type. `assert a` then stays quiet (no cascade). -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure multiAssignScalarRhs() opaque {
  assign var a, var b := 5;
//                       ^ error: expected '(Unknown, Unknown)', got 'int'
  assert a
};
#end
