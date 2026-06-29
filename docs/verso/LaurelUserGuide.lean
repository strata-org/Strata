/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Laurel User Guide" =>
%%%
shortTitle := "Laurel User Guide"
%%%

# Summary

Laurel is an intermediate verification language. It is the common target for
verifiers built on top of garbage-collected, imperative source languages such
as Java, Python, and JavaScript. You usually do not write Laurel by hand;
a front-end translates your annotated source program into Laurel, and Laurel is
then checked for correctness. Understanding Laurel helps you understand what the
front-end checks and why a verification succeeds or fails.

Laurel is built to be both *complete* and *accurate*. It is complete because you
can specify any behavior you want and have it checked against the
implementation. It is accurate because, when the underlying solver cannot decide
whether a program meets its specification, you can supply hints — extra
assertions, loop invariants, or contracts — that let it reach a definite answer.
Some properties, such as the absence of common runtime errors, are checked
without you having to state them.

Under the hood, Laurel discharges its proof obligations using a Satisfiability
Modulo Theories (SMT) solver. For simple obligations the solver finds a proof on
its own. For harder ones it needs guidance, and most of this guide is about the
constructs you use to provide that guidance.

## A first program

A Laurel program is a sequence of declarations. The most important one is the
*procedure*. A procedure has input parameters, optional output parameters
introduced with `returns`, an optional contract, and a body enclosed in braces.
Statements inside the body are separated by semicolons.

```
program Laurel;
procedure addOne(x: int) returns (r: int)
  opaque
  ensures r == x + 1
{
  r := x;
  r++;
  r++
};
```

The `opaque` keyword marks a procedure whose body is hidden from its callers:
callers reason about it only through its contract (`requires` / `ensures` /
`modifies`). This is the standard *modular* style — each procedure is verified
once against its contract, and call sites trust the contract rather than the
body.

# Laurel without verification

TODO, cover all the non-verification language parts

## Primitive types

Laurel provides unbounded mathematical `int` and `real` types, a `bool` type,
`string`, and fixed-width bitvectors. Because `int` is unbounded, arithmetic in
specifications behaves like ordinary mathematics: there is no overflow to reason
around when you are stating what a procedure computes.

## Composites

Laurel models objects with *composite* types. A composite declares mutable
fields and may declare *instance procedures* (methods). Fields are read and
written with the `#` selector, instances are created with `new`, and a method is
invoked with the same `#` syntax.

```
program Laurel;
composite Counter {
  var count: int
  procedure reset(self: Counter)
    opaque
    ensures self#count == 0
    modifies self
  {
    self#count := 0
  };
}

procedure useCounter()
  opaque
{
  var c: Counter := new Counter;
  c#reset();
  assert c#count == 0
};
```

An instance procedure takes its receiver as an explicit `self` parameter and
refers to fields through it. The contract of a method uses the same `requires` /
`ensures` / `modifies` clauses as any other procedure; here `ensures self#count
== 0` is what lets the caller conclude `c#count == 0` after `c#reset()`.

Field selection and method calls chain, so you can reach through one object to
another: `o#inner#x` reads field `x` of the object stored in `o`'s `inner` field,
and `o#inner#isOne()` calls a method on it.

```
program Laurel;
composite Inner { var x: int }
composite Outer { var inner: Inner }

procedure useOuter()
  opaque
{
  var o: Outer := new Outer;
  var v: int := o#inner#x
};
```

# Verification fundamentals

## Assertions

An `assert` states a fact that Laurel must prove holds at that point in the
program. If the solver cannot prove it, verification fails and the failing
`assert` is reported.

```
program Laurel;
procedure checkPositive(x: int)
  requires x > 0
  opaque
{
  assert x > 0;
  assert x >= 1
};
```

The dual of `assert` is `assume`. An `assume` introduces a fact without proof:
from that point on, Laurel reasons as if the assumed expression is true. Assuming
something false makes everything afterwards trivially provable, which is
occasionally useful but should be used with care.

```
program Laurel;
procedure assumeThenProve()
  opaque
{
  assume false;
  assert false  // provable: we assumed a contradiction
};
```

Assertions are the building block behind every other verification feature in
this guide. Preconditions, postconditions, and loop invariants are all
ultimately checked by turning them into assertions at the right program points.

## Loop invariants

Laurel cannot know in advance how many times a loop runs, so it reasons about
loops through a *loop invariant*: a condition that holds every time the loop
guard is evaluated — on first entry and after each execution of the body.

A loop invariant serves two purposes. Inside the loop it tells Laurel what is
true, which is what lets it prove that operations in the body are safe. After the
loop it combines with the negated guard to describe the state on exit.

```
program Laurel;
procedure countUp()
  opaque
{
  var n: int := 5;
  var i: int := 0;
  while (i < n)
    invariant i >= 0
    invariant i <= n
  {
    i := i + 1
  };
  assert i == n
};
```

The two invariants together establish `i == n` after the loop: the loop exits
when `i < n` is false, so `i >= n`, and the second invariant gives `i <= n`.

A loop invariant must hold *on entry* and be *preserved* by the body. If it fails
on entry, Laurel reports the error at the offending invariant. For example,
initializing `i` to `-1` above would break `invariant i >= 0` before the loop
even starts, and that specific invariant is flagged.

## Preconditions

A *precondition*, written with `requires`, states what must be true when a
procedure is called. It has two effects. It restricts callers: every call site
must prove the precondition holds for the arguments it passes. And it gives the
body an assumption to work from when proving its own obligations.

```
program Laurel;
procedure halve(x: int) returns (r: int)
  requires x > 0
  opaque
  ensures r >= 0
{
  r := x / 2
};

procedure caller()
  opaque
{
  var a: int := halve(10);   // ok: 10 > 0
  var b: int := halve(0)     // error: precondition does not hold
};
```

A procedure may have several `requires` clauses; they are conjoined. A call must
satisfy all of them.

```
program Laurel;
procedure addBoth(x: int, y: int) returns (r: int)
  requires x > 0
  requires y > 0
  opaque
  ensures r > 0
{
  r := x + y
};
```

Functions support `requires` clauses too, with the same meaning: each use of the
function must prove the requirement.

## Postconditions

A *postcondition*, written with `ensures`, states what a procedure guarantees
when it returns. Laurel checks the body against every `ensures` clause, and
callers may rely on those clauses without looking at the body. Postconditions are
how you say precisely what a procedure does.

```
program Laurel;
procedure max(x: int, y: int) returns (r: int)
  opaque
  ensures r >= x
  ensures r >= y
  ensures r == x || r == y
{
  if x > y then { r := x }
  else { r := y }
};
```

At a call site, the postcondition is all the caller knows about the result:

```
program Laurel;
procedure useMax()
  opaque
{
  var m: int := max(3, 7);
  assert m >= 3;
  assert m >= 7
  // we cannot assert m == 7 here: the contract only promises r >= x, r >= y,
  // and r == x || r == y, which does not pin m to 7.
};
```

Postconditions and preconditions work together. It is common to need a
precondition in order to be able to prove a postcondition, and adding that
precondition simultaneously rules out the calls for which the procedure would not
behave as specified.

## Quantifier

For specifications that range over many values, Laurel provides *quantifiers*.
A `forall` states that its body holds for every value of the bound variables; an
`exists` states that there is at least one value for which the body holds. Both
take one or more typed binders and a body introduced with `=>`.

```
program Laurel;
procedure quantifiers()
  opaque
{
  assert forall(x: int) => x + 0 == x;
  assert exists(x: int) => x == 42
};
```

The implication operator `==>` is frequently used inside quantifiers to restrict
the range of interest — for instance, to say something about every index of an
array within bounds:

```
program Laurel;
procedure inContract(n: int)
  requires n > 0
  opaque
  ensures forall(i: int) => i >= 0 ==> i < n ==> i < n + 1
{
};
```

Because a `forall` over an infinite domain (such as all integers) cannot be
checked by enumeration, the solver reasons about it logically. To control how it
instantiates a quantifier, you can attach a *trigger* — a pattern in braces that
tells the solver which terms should cause the quantified fact to fire:

```
program Laurel;
function P(x: int): int;
procedure withTrigger()
  opaque
{
  assume forall(i: int) { P(i) } => P(i) == i + 1;
  assert P(1) == 2   // the term P(1) matches the trigger, so the fact fires
};
```

# Verification of object mutation


## Modifies clauses

When a procedure may change the fields of objects on the heap, it must say so
with a `modifies` clause. The clause lists the references the procedure is
allowed to mutate. This *frame* is what callers rely on to know what did *not*
change across a call.

A `modifies` clause is especially important on `opaque` procedures: without it, a
caller would have to assume the call could have changed any heap state. With it,
the caller keeps every fact about objects outside the frame.

```
program Laurel;
composite Container {
  var value: int
}

procedure bump(c: Container)
  opaque
  modifies c
{
  c#value := c#value + 1
};

procedure caller()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  bump(c);
  assert x == d#value   // holds: only c is in bump's modifies clause
};
```

A procedure that writes to a field it has not listed is rejected, and so is a
call that passes more permission than the caller itself holds. You can list
several references by repeating the clause (`modifies c; modifies d`), and the
wildcard `modifies *` permits modifying any object — at the cost of telling
callers that nothing on the heap is preserved.

Objects allocated with `new` *inside* the procedure body are exempt: a freshly
allocated object may be modified freely without appearing in the `modifies`
clause, because no caller could hold any prior knowledge about it.

```
program Laurel;
composite Container { var value: int }

procedure makeOne()
  opaque
{
  var c: Container := new Container;
  c#value := 1   // allowed: c is freshly allocated here
};
```

## Old

In a postcondition you often want to relate the state when the procedure returns
to the state when it was entered. Wrapping an expression in `old(...)` evaluates
that expression in the *pre-state* — the heap as it was on entry. This is the
standard way to specify a procedure that mutates its arguments.

```
program Laurel;
composite Cell {
  var value: int
}

procedure bumpCell(c: Cell)
  opaque
  ensures c#value == old(c#value) + 1
  modifies c
{
  c#value := c#value + 1
};
```

Here `c#value` denotes the value on return and `old(c#value)` the value on entry,
so the postcondition says the field grew by exactly one. Without `old`, the
clause would read `c#value == c#value + 1`, which no implementation can satisfy.

`old` distributes through the structure of an expression, so you can wrap a whole
sub-expression: `old(2 * c#value + 3)` means the same as `2 * old(c#value) + 3`.
It may also appear inside quantifiers and conditionals in a postcondition:

```
program Laurel;
composite Cell { var value: int }

procedure strictBump(c: Cell)
  opaque
  ensures forall(other: Cell) => other == c ==> other#value > old(other#value)
  modifies c
{
  c#value := c#value + 1
};
```

A caller can reproduce the two-state reasoning by snapshotting the pre-state into
a local variable before the call and asserting against it afterwards:

```
program Laurel;
composite Cell { var value: int }

procedure bumpCell(c: Cell)
  opaque
  ensures c#value == old(c#value) + 1
  modifies c
{
  c#value := c#value + 1
};

procedure bumpCellCaller()
  opaque
{
  var c: Cell := new Cell;
  var pre: int := c#value;
  bumpCell(c);
  assert c#value == pre + 1
};
```

An `old(...)` that mentions nothing from the heap has no effect and Laurel warns
about it, since it cannot relate two states. The same warning is issued for a
redundant `old(old(...))`, whose inner `old` is dropped.
