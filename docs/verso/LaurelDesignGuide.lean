/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.ModifiesClauses

open Strata.Laurel

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Laurel Language Design Guide" =>
%%%
shortTitle := "Laurel Design"
%%%

# Design Goals

This guide describes the goals that Laurel is designed with, and the history of the decisions made to get to the language as it is now. When evolving the language, this document must be updated to advocate for the changes.

Laurel is an intermediate verification language designed to serve as a target for popular
garbage-collected languages that include imperative features, such as Java, Python, and
JavaScript, where those languages have been extended to include verification specific constructs.
Laurel tries to include any features that are common to those three languages.

Goals:
1. Enable proving both correctness and incorrectness properties of software, through a combination of:
  1. Property based testing
  2. Symbolic execution (aka verification), both bounded and unbounded
  3. Hybrid concrete and symbolic property checking
  4. Data-flow analysis
2. Reduce code duplication in the analysis of popular languages by being a target for compilation from those languages, and including features common to them. Note that we expect source languages to reuse their existing compilers when possible, so language features that can be compiled away don't need to be considered.
3. Enable modular verification
4. Minimize the amount of user code needed to enable verification.
5. Enable finding proofs through an automated search.
6. Use complete analysis algorithms to reduce the required proof effort.
7. Verification must be erasable. Removing verification code may not affect execution behavior.
8. Have a great user experience

# Correctness checking features

## Property-based testing
To be designed..

## Verification
To achieve goal 1.2, enable proving properties through verification, Laurel has the following features.

### Assertions
An `assert` states a property that must hold at the point where it appears. An assertion is the basic unit of proof: everything else in this section is a way of making the facts an assertion needs available, or of stating such properties more conveniently.

```
procedure abs(x: int) returns (r: int)
{
    if x < 0 then { r := -x } else { r := x };
    assert r >= 0
};
```

Here the assertion holds on both branches, so it is discharged; had a branch left `r` negative, the assertion would report a failure.

### Quantifiers
Laurel supports universal (`forall`) and existential (`exists`) quantifiers in properties, written `forall(x: T) => P(x)` and `exists(x: T) => P(x)`. They let a single property range over unboundedly many values.

```
procedure allNonNegativeSquares()
  opaque
{
    assert forall(x: int) => x * x >= 0
};

procedure someMultipleOf42()
  opaque
{
    assert exists(x: int) => x == 42
};
```

The two quantifiers correspond to the two analysis modes. A universal quantifier is what soundness (correctness) checking needs: to prove a procedure correct, its properties must hold for *all* inputs and *all* reachable states, so proving a `forall` establishes the property for every case. An existential quantifier fits bug finding (incorrectness) mode: exhibiting *some* state that satisfies a property is enough to witness that a situation is reachable, for example a state that violates an intended invariant. Because unrestricted quantifier instantiation is a common cause of slow verification, a `forall` may carry an explicit trigger, written `forall(i: int) { P(i) } => …`, that tells the solver which terms may instantiate it.

### Old
In a postcondition, `old(e)` denotes the value of the expression `e` in the procedure's pre-state, before the body ran. This lets a contract relate the final state to the initial one, which is how mutation is specified. The specification is written in a mutation-free style: `old` and the current value are both just expressions, and comparing them describes the effect of the mutation without the contract itself performing any mutation.

```
procedure increment(counter: Counter)
  opaque
  ensures counter#value == old(counter#value) + 1
  modifies counter
{
  counter#value := counter#value + 1
};
```

The postcondition `counter#value == old(counter#value) + 1` captures the mutation performed by the body, yet it is a pure comparison between two values. A caller learns exactly how the field changed relative to its prior value without the contract mutating anything, keeping verification code erasable (see goal 7).

## Unbounded verification
Bounded symbolic execution unrolls a loop a fixed number of times, so on its own it cannot prove a property for every run of a loop whose iteration count is not statically known. Loop invariants close that gap. A `while` loop may carry one or more `invariant` clauses, each an expression that must hold when the loop is first reached and be preserved by every iteration.

```
procedure countUp()
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

The invariants let Laurel replace the loop with three obligations that stand in for it no matter how many times it runs:
1. the invariants hold on entry to the loop;
2. assuming the invariants and the guard, one iteration of the body re-establishes the invariants;
3. after the loop, the invariants together with the negation of the guard may be assumed.

None of these obligations mentions a concrete iteration count, so an invariant strong enough to imply the property discharges it for an unbounded loop. Each invariant is checked independently and reports a failure against its own source range, so a diagnostic points at the specific invariant that does not hold rather than at the whole loop.

## Hybrid property checking
Laurel allows bypassing the symbolic checking of properties in various ways:
- Assumptions
- Bodyless procedures

By bypassing the symbolic check, a concrete check (property-based testing) can be used instead. How exactly Laurel will guarantee a correct hand-off between concrete and symbolic property checking, is yet to be designed.

## Data-flow analysis

To be designed..

# Prevent duplicate work
To achieve goal (2), reduce code duplication in the analysis of popular languages, Laurel contains many features shared between several languages. The following table shows which features are shared with which input languages.

Legend: the *Laurel* column records Laurel's own status — ✓ implemented, WIP planned but not yet implemented, ✗ not planned. The source-language columns record — ✓ directly supported, ~ partial or library-only (semantics differ, or only available through a standard library rather than the core language), — not present.

:::table +header
 *
   * Feature
   * Laurel
   * Java
   * JavaScript
   * Python
 *
   * Reference (heap) objects
   * ✓
   * ✓
   * ✓
   * ✓
 *
   * Classes with instance methods
   * ✓
   * ✓
   * ✓
   * ✓
 *
   * Multiple supertypes for subtyping (interface conformance)
   * ✓
   * ✓
   * —
   * ✓
 *
   * Multiple implementation inheritance (fields/methods from several parents)
   * ✓
   * —
   * ~
   * ✓
 *
   * Record types (immutable, structural equality)
   * WIP
   * ✓
   * —
   * ~
 *
   * Runtime type test and cast (`is` / `as`)
   * ✓
   * ✓
   * ✓
   * ✓
 *
   * Reference equality
   * ✓
   * ✓
   * ✓
   * ✓
 *
   * Arbitrary-precision integers
   * ✓
   * ~
   * ~
   * ✓
 *
   * IEEE-754 64-bit floats
   * ✓
   * ✓
   * ✓
   * ✓
 *
   * Strings
   * ✓
   * ✓
   * ✓
   * ✓
 *
   * Sets and maps
   * ✓
   * ✓
   * ✓
   * ✓
 *
   * Fixed-width bitvector operations
   * ✓
   * ✓
   * ~
   * ~
 *
   * `while` loops
   * ✓
   * ✓
   * ✓
   * ✓
 *
   * `do`/`while` (post-test) loops
   * ✓
   * ✓
   * ✓
   * —
 *
   * `break` / `continue` (direct statements)
   * WIP
   * ✓
   * ✓
   * ✓
 *
   * `break` / `continue` via labelled block exit (`exit L`)
   * ✓
   * ✓
   * ✓
   * ~
 *
   * Increment / decrement operators (`++` / `--`)
   * ✓
   * ✓
   * ✓
   * —
 *
   * Assignments in expression positions
   * ✓
   * ✓
   * ✓
   * ~
 *
   * Short-circuit boolean operators (`&&` / `||`)
   * ✓
   * ✓
   * ✓
   * ✓
 *
   * Algebraic datatypes / pattern matching
   * ✓
   * ~
   * —
   * ~
 *
   * Try / catch and checked exceptions
   * WIP
   * ✓
   * ~
   * ~
 *
   * Procedure types and procedures as values
   * WIP
   * ✓
   * ✓
   * ✓
 *
   * Parametric polymorphism (generics)
   * WIP
   * ✓
   * —
   * ~
 *
   * Reflection / runtime metaprogramming (dynamic field/method or prototype mutation)
   * ✗
   * ✓
   * ✓
   * ✓
 *
   * `eval` / dynamic code loading
   * ✗
   * ~
   * ✓
   * ✓
 *
   * Shared-memory concurrency (threads, locks, memory model)
   * WIP
   * ✓
   * ~
   * ✓
 *
   * Garbage-collection observability (finalizers, weak references)
   * ✗
   * ✓
   * ✓
   * ✓
:::

Notes on the partial (~) entries:
- *Multiple supertypes for subtyping* — Laurel's `extending` list lets a type declare several supertypes for `is`/`as` and subtyping. Java gets this from implementing multiple interfaces (and Python from its MRO). JavaScript has only a single prototype chain and no interface concept.
- *Multiple implementation inheritance* — this is the stronger form Python needs: inheriting fields and method implementations from several concrete parents, resolved by an MRO. Only Python has it fully; JavaScript relies on ad-hoc mixin patterns, and Java has none (interfaces provide default methods but no fields).
- *Record types* — an immutable aggregate compared by structural equality. Java has `record`s directly. Python has `@dataclass`/`NamedTuple` (~, library/decorator-based). JavaScript has no record type (the Records & Tuples proposal is not shipped).
- *Arbitrary-precision integers* — only Python has them as the default `int`; Java and JavaScript expose them through a library (`BigInteger`, `BigInt`).
- *Fixed-width bitvector operations* — JavaScript's bitwise operators are 32-bit; Python integers are arbitrary width.
- *`do`/`while` loops* — Python has none.
- *`break` / `continue`* — Laurel does not yet have dedicated `break`/`continue` keywords (WIP). It already provides the more general primitive underneath them: a labelled block `{ … } L` and an `exit L` statement that jumps to the end of that block. `break` is an exit of the block wrapping the loop, and `continue` an exit of the block wrapping the loop body, so the one primitive covers both. On the labelled-exit row, Python has `break`/`continue` without labels.
- *Increment / decrement* — Python has no such operators.
- *Assignments in expression positions* — Laurel allows assignments (and other imperative constructs) to appear where an expression is expected, and lifts them out into preceding statements. Java and JavaScript treat assignment as an expression directly. In Python assignments are statements; only the walrus operator `:=` provides a restricted assignment expression.
- *Algebraic datatypes / pattern matching* — Java (sealed types + `switch` patterns) and Python (`match`) support a subset; JavaScript has none.
- *Exceptions* — Java has checked exceptions; JavaScript and Python have exceptions, but unchecked.

Notes on the not-planned (✗) entries. These are features that survive the source language's own compilation (they are not mere syntactic sugar) yet Laurel deliberately does not model, because they cannot be lowered into static Laurel constructs without either embedding a runtime interpreter or losing soundness, and they are fundamentally at odds with modular static verification.
- *Reflection / runtime metaprogramming* — all three source languages allow a program to inspect and rewrite its own structure at runtime: Java through `java.lang.reflect` and dynamic proxies, Python through `getattr`/`setattr`, `__dict__` mutation, metaclasses, and monkey-patching, and JavaScript through `Proxy`/`Reflect` and prototype mutation (`Object.setPrototypeOf`). Laurel's static and flow-based typing, and its inference of composite types from a fixed set of assigned fields, assume the set of fields and methods of a type is known statically, so arbitrary self-modification is out of scope.
- *`eval` / dynamic code loading* — code that does not exist until runtime cannot be verified ahead of time. Python (`eval`/`exec`) and JavaScript (`eval`) have it directly; Java exposes it more indirectly through scripting and dynamic class loading (~).
- *Garbage-collection observability* — finalizers and weak references (Java `finalize`/`WeakReference`, Python `__del__`/`weakref`, JavaScript `WeakRef`/`FinalizationRegistry`) expose the nondeterministic timing of collection. Laurel models the heap abstractly and does not expose when, or whether, an object is collected.

Note on the *shared-memory concurrency* entry (WIP): Java has real shared-memory threads governed by the Java Memory Model (`synchronized`, `volatile`, happens-before); Python has threads under the GIL (✓); JavaScript is single-threaded and only achieves parallelism through workers that communicate by message passing (~). Laurel is currently sequential, and reasoning under a relaxed memory model is a large, separable piece of work, so this is planned rather than available.

# Modular Verification
To achieve goal (3), Laurel has the following features related to modular verification.

## Preconditions
Preconditions enable proving the assertions in a procedure's body without having to consider the callers. This way, each assertion only needs to be proven once, instead of once for each transitive call-site.

## Postconditions and opaque procedures
Laurel allows a procedure to be marked as opaque, which means that callers won't get access to the body of the procedure. Once a procedure is opaque, Laurel allows defining postconditions for it. The postconditions will remain available to the caller. Postcondition and opaque bodies allow encapsulating the body of a procedure, making it easier to reason about by callers.

Laurel does not allow postconditions on procedures with transparent bodies, because a postcondition can only contain information that can also be inferred from the body, and redundant information is bad for verification performance.

For proving properties on top of a procedure's body or postconditions, define a separate procedure that calls the target one.

Since modifies clauses are a type of postcondition, they are also only allowed on opaque procedures.

# Minimize Verification Code
To achieve goal (4), minimize the amount of user code needed to enable verification, Laurel has the following features:

## Transparent procedures
Laurel procedures are transparent by default, meaning that a call can use the body of the callee to prove facts about the result of the call. Laurel aims to allow any procedure to be transparent; some restrictions still remain for now. In particular, Laurel will allow procedures that contain loops or that modify the heap to be transparent as well.

By allowing any procedure to be transparent, Laurel prevents users from having to repeat the body of a procedure in a postcondition. Here's an example that shows an opaque procedure that would have been easier to define as being transparent, without any loss of readability:

```
procedure increment(counter: Counter)
  // In Laurel, the next three lines can be left out and callers will get the same information
  opaque
  modifies counter
  ensures counter#value == old(counter#value) + 1
{
  counter#value := counter#value + 1
};
```

## Heap mutation in contracts
A contract in Laurel may not modify any object that exists outside of that contract, as if the contract has an empty modifies clause. However, new objects may be created and modified inside the contract.

A common design choice in verification-aware programming languages is not to allow creating or modifying objects in contracts. A good reason for this is that objects are more complex to reason about than immutable data, and contracts are intended to contain easy to reason about code. Laurel still allows creating and modifying new objects inside contracts because code might be declared to operate specifically through the use of reference types, and Laurel does not want to restrict users from using such code even in contracts.

A second reason for not allowing any heap modification inside contracts is that this is prone to soundness issues. From outside the contract the heap is assumed not to be modified, so if knowledge of an inside modification escapes the contract, this leads to an inconsistency. Because Laurel does not allow assigning to a variable defined outside the contract, from inside the contract, no modification can escape the contract. The heap used inside a contract is a separate heap variable.

## Invoke on
The postcondition of an opaque procedure is exposed to callers as an axiom: the ensures clause, universally quantified over the procedure's inputs. Left unrestricted, the solver may instantiate such an axiom on any matching term, which is a common cause of slow and unpredictable verification.

An `invokeOn` clause names the SMT trigger for that axiom. It takes an expression over the procedure's inputs, and the axiom is only instantiated when a term matching that expression appears in the proof context.

```
procedure PAndQ(x: int)
  invokeOn P(x)
  opaque
  ensures P(x) && Q(x);
```

This emits the axiom `forall x. {P(x)} P(x) && Q(x)`, triggered on `P(x)`. An obligation that mentions `P(x)` pulls in `P(x) && Q(x)`, so it can establish both `P(x)` and `Q(x)`. An obligation that mentions only `Q(x)` does not match the trigger, so the axiom stays dormant and `Q(x)` is not proved. The trigger controls *when* the fact is instantiated, but not *where*: the axiom is emitted at the top level of the program, so once a matching term appears the fact becomes available to every proof obligation in the program, not just to a particular caller or region.

This global availability is a deliberate simplification for the first version of the feature. It is enough to make an opaque procedure's postcondition usable, but it gives no control over scope: a fact intended for one caller is visible everywhere its trigger matches, which can slow down or perturb unrelated proofs. `invokeOn` is expected to evolve toward finer-grained control over where facts are made available — for example scoping a fact to specific callers, modules, or call sites — so that authors can expose a postcondition exactly where it is useful rather than program-wide.

## Aliasing

Potential aliasing of heap-allocated objects can make verification more complicated. Laurel builds on two related notions to make it easier to specify which references are disjoint. A reference is *allocated* (in a given state) when it already exists in that state's heap; internally this is the condition that the reference predates the state's allocation counter. A reference is *fresh* when it is the negation of that: newly created by the procedure and therefore not allocated in the pre-state.

Today only `fresh` has surface syntax — the `fresh(e)` predicate, which may only target reference (impure composite) types. It is exactly what a caller needs to conclude that a returned reference cannot alias anything that was already allocated.

```
procedure allocate() returns (r: Node)
  opaque
  ensures fresh(r)
{
  return new Node
};

procedure usesAllocate(existing: Node) {
  var created: Node := allocate();
  assert created != existing   // holds: `fresh(r)` tells the caller `created`
                               // is distinct from every object that already existed
};
```

Because `allocate` ensures `fresh(r)`, the caller learns that `created` was newly allocated and therefore cannot alias `existing`, or any other reference that was already allocated before the call, without the caller having to track allocation itself.

An `allocated(e)` predicate is planned as the dual of `fresh`. Where `fresh(e)` asserts a reference is new, `allocated(e)` will assert that a reference already existed in the current state's heap — useful, for example, in a precondition that requires an argument to be a pre-existing object rather than a fresh one. The following sketch (syntax illustrative — `allocated` is not yet implemented) shows the intended shape:

```
// syntax illustrative — `allocated` is planned, not yet implemented
procedure store(container: Container, item: Node)
  requires allocated(item)   // reject fresh items; only pre-existing ones may be stored
  opaque
  modifies container
{
  container#head := item
};
```

# Automated proof search
Goal 5 was enabling the finding of proofs through automated search.

## Reads clauses
Reads clauses are useful to improve verification performance. The facts they provide work well together with the facts provided by modifies clauses, making it easier to prove which procedure values have remained unchanged after objects were modified.

## Frozen types
Frozen types (To be designed). A reads clause specifies that a procedure always returns the same value, if the reads references have the same values and if the explicit input arguments, which excludes the heap, are the same. A procedure that returns a newly created object, which has a reference counter that depends on the counter of the input heap, can thus never satisfy a reads clause. For this purpose Laurel allows erasing the counter from a reference value. A Laurel `Frozen` type takes a regular reference type, and produces a type that is the same except that it does not support reference equality or mutation of its fields. Record types are composite types that are frozen by default.

The following sketch (syntax illustrative — reads clauses, records, and `Frozen` are still being designed) shows why the erasure matters. Each procedure declares an empty reads clause, claiming its result depends on nothing in the heap:

```
record Tuple { var fst: int; var snd: int }
composite MutableTuple { var fst: int; var snd: int }

procedure makeRecord() reads {} returns (r: Tuple)
{ return Tuple(1, 2) };                  // ok: records are frozen, no reference identity

procedure makeFrozen() reads {} returns (r: Frozen<MutableTuple>)
{ ... };                                 // ok: the counter is erased, so the result is heap-independent

procedure makeMutable() reads {} returns (r: MutableTuple)
//                      ^^^^^^^^ fails: the new object's identity depends on the heap counter
{ return new MutableTuple(1, 2) };
```

`makeRecord` and `makeFrozen` satisfy the empty reads clause because neither result carries a heap-dependent reference counter, so calling either twice with the same inputs yields equal results. `makeMutable` returns a fresh `MutableTuple` whose reference identity is drawn from the heap's allocation counter, so its result differs between calls and cannot satisfy an empty reads clause.

# Use complete algorithms to reduce workload
To achieve goal 6, to reduce the verification work through the use of complete algorithms, Laurel has the following features.

## Constrained types
A constrained type refines an existing type with a predicate, so that a fact established once travels through the program as part of the type instead of being re-proved at each use. It is declared with a base type, a `where` predicate, and a `witness` value that shows the constraint is inhabited.

```
constrained nat = x: int where x >= 0 witness 0
```

The property that matters for reducing proof effort is that the fact survives flow through code that knows nothing about it. Consider a polymorphic `identity`, which returns its argument unchanged for any type `T`:

```
// syntax illustrative — generics are still in progress
procedure identity<T>(x: T) returns (r: T) { return x };

procedure usesIdentity() {
  var n: nat := 5;
  var m: nat := identity(n);
  assert m >= 0            // still available: the `nat` constraint survived the round-trip
};
```

`identity` is verified once, generically, with no knowledge of `nat` or its predicate. Yet because the constraint rides along with the type, instantiating `T` with `nat` lets the caller recover `m >= 0` on the result with no extra annotation or proof at the call site. The fact is neither dropped when the value enters the generic procedure nor re-derived when it leaves. That is what lets constrained types cut proof effort across a whole program: a property proved at one point remains available everywhere the constrained value flows, even through procedures that are entirely agnostic to the constraint.

## Type inference

To be designed.. but here is some subject to change content.

Laurel can statically infer the types of variables, which, when the inferred types were otherwise not available in the source program, can enable emitting code that can be verified more efficiently.

Here's an example related to nullable reference types:

Input program:
```
var foo := new Foo;
foo#x := 1;

var bar := foo;
bar := null;
bar#x := 2
```

Without type inference, we cannot judge whether the variable `foo` should have type `Foo` or `Nullable<Foo>`, so we have to pick defensively:
```
datatype Nullable<T> = from_NotNull(as_notNull: T) | from_Null

var foo: Nullable<Foo> := from_NotNull(new Foo);
as_notNull(foo)#x := 1;

var bar: Nullable<Foo> := foo;
bar := null;
as_notNull(bar)#x := 2
```

With type inference, we can infer that `foo` is never nullable:
```
var foo: Foo := new Foo;
foo#x := 1;

var bar: Nullable<Foo> := from_NotNull(foo);
bar := null;
as_notNull(bar)#x := 2
```

Note the coercion `from_NotNull` that was inserted in the assignment to `bar`. Laurel can be given a list of coercions that can be inserted automatically. Laurel can also be given a list of type coercions, which it can use to change the type annotations of variables, from for example `T` to `Nullable<T>`.

## Flow based types

Flow based types allow the type of a variable to change throughout the control-flow of the program, which enables having more precise types which improves verification performance.

Source program:
```
var foo := new Foo;
foo#x := 1;
foo := null;
foo#x := 2;
```

Inferred program:
```
var foo := new Foo;
foo#x := 1;
var foo_2: Nullable<Foo> := from_NotNull(foo);
foo_2 := null;
as_notNull(foo_2)#x := 2;
```

## Inference of composite types

To be designed..

Useful for dynamic languages. Infers composite types based on fields assigned to values.
Composite types perform better than maps because reading from them incurs no domain check.

# Verification code must be erasable

To support goal 7, for verification code not to affect the outcome of executing the program, Laurel has rules for code that exists only for verification purposes.

Rules for contracts:
- Contract code may not modify variables defined outside the contract scope.
- Contract code has an empty modifies clause. Contract code operates on a copy of the heap.
- Contract code must terminate, so removing it does not affect whether execution code is reachable or not.

For example, the body of the procedure below changes `p`, and that effect is declared with `modifies p`; `old(p#x)` in the ensures clause refers to the pre-state:

```
procedure shift(p: Point, dx: int)
  opaque
  ensures p#x == old(p#x) + dx
  modifies p
{
  p#x := p#x + dx
};
```

The ensures expression may read the heap and build temporary values while it is evaluated, but it cannot assign to `p`, to `dx`, or to any variable declared outside it, and it contributes no modifies effect of its own. Even if the postcondition called a helper that allocated and mutated a scratch object, that would run against a copy of the heap and remain invisible to callers, which still see every pre-existing object unchanged across the evaluation of the contract. As a result, adding, strengthening, or removing the ensures clause never changes how the program executes.

## Decreases clauses
To enable proving that contracts terminate, Laurel uses decreases clauses to enable proving the termination of procedure calls.

# Great user experience

## Parameter lists
In Laurel, input and output parameters are defined in a separate list. Inout parameters are defined by repeating the parameter name in both lists. In Core, there is a single parameter list where each parameter defines its kind (in/out/inout).

At the call-site, Laurel requires calls with multiple out parameters to occur inside an assignment, like this:
`assign x, y := multiOutCall(a, b)`
Core uses the argument list to assign the output parameters, like this:
`multiOutCall(a, b, out x, out y)`

In Laurel, an inout parameter only influences the callee's code, since it means there is a single variable that is used as input and output. On the calling side however, there is no concept of inout parameters. This is different from Core, where inout variables affect the calling side. Example of an inout being called in Core, `hasInout(inout x)`.

## Assignments to fresh and existing declarations
In Laurel, assignments can have multiple targets. Each target can be either an existing variable or a local declaration. Example:
```
var x: int;
var z: int;
assign x, var y: int, z := hasThreeOutputs()
```
In Core, when calling a procedure with multiple outputs, each output parameter must be assigned to an existing local variable. Example:
```
var x: int;
var y: int;
var z: int;
hasThreeOutputs(out x, out y, out z);
```
