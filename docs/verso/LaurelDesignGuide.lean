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
  1. property based testing
  2. data-flow analysis
  3. symbolic execution (aka verification), both bounded and unbounded
2. Reduce code duplication in the analysis of popular languages by being a target for compilation from those languages, and including features common to them. Note that we expect source languages to reuse their existing compilers when possible, so language features that can be compiled away don't need to be considered.
3. Have a great user experience
4. Enable modular verification
5. Minimize the amount of user code needed to enable verification.
6. Enable finding proofs through an automated search.
7. Use complete analysis algorithms to reduce the required proof effort.
8. Code used to enable verification may not affect execution behavior.

# Enable Verification
To achieve goal 1.3, enable proving properties through verification, Laurel has the following features.
- Assertions
- Quantifiers
- Old/allocated/fresh
- Decreases clauses
- Assumptions (more about gradual verification)

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
To achieve goal (4), Laurel has the following features related to modular verification.

## Preconditions
Preconditions enable proving the assertions in a procedure's body without having to consider the callers. This way, each assertion only needs to be proven once, instead of once for each transitive call-site.

## Opaque procedures
Laurel allows a procedure to be marked as opaque, which means that callers won't get access to the body of the procedure. Laurel only allows postconditions for opaque procedures. This restriction is because a postcondition can only contain information that can also be inferred from the body, and redundant information is bad for verification performance.

Since modifies clauses are a type of postcondition, they are also only allowed on opaque procedures.

# Minimize Verification Code
To achieve goal (5), minimize the amount of user code needed to enable verification, Laurel has the following features:

## Transparent procedures
Laurel procedures are transparent by default, meaning that a call can use the body of the callee to prove facts about the result of the call. Laurel will allow any procedure to be transparent, although currently there are some restrictions. In particular, Laurel will allow procedures that contain loops or that modify the heap, to be transparent as well.

By allowing any procedure to be transparent, Laurel prevents users from having to repeat the body of a procedure in a postcondition. Here's an example that shows an opaque procedure that would have been easier to define as being transparent, without any loss of readability:

```
procedure increment(counter: Counter) opaque
  // In Laurel, this ensures clause can be left out
  ensures counter.value == old(counter.value) + 1
{
  counter.value := counter.value + 1
};
```

## Heap mutation in contracts
A contract in Laurel may not modify any object that exists outside of that contract, as if the contract has an empty modifies clause. However, new objects may be created and modified inside the contract.

A common design choice in verification-aware programming languages is not to allow creating or modifying objects in contracts. A good reason for this is that objects are more complex to reason about than immutable data, and contracts are intended to contain easy to reason about code. Laurel still allows creating and modifying new objects inside contracts because code might be declared to operate specifically through the use of reference types, and Laurel does not want to restrict users from using such code even in contracts.

A second reason for not allowing any heap modification inside contracts is that this is prone to soundness issues. From outside the contract the heap is assumed not to be modified, so if knowledge of an inside modification escapes the contract, this leads to an inconsistency. Because Laurel does not allow assigning to variable defined outside the contract, from inside the contract, no modification can escape the contract. The heap used inside a contract is a separate heap variable.

## Invoke on

TODO, fill in

# Automated proof search
Goal 6 was enabling the finding of proofs through automated search.

## Loop invariants
These enable unbounded symbolic execution. TODO, say more.

## Reads clauses
Reads clauses are useful to improve verification performance. The facts they prove work well together with the facts provided by modifies clauses, making it easier to prove which procedure values have remained unchanged after objects were modified.

## Frozen types
Frozen types (To be designed). A reads clause specifies that a procedure always returns the same value, if the reads references have the same values and if the explicit input arguments, which excludes the heap, are the same. A procedure that returns a newly created object, which has a reference counter that depends on the counter of the input heap, can thus never satisfy a reads clause. For this purpose Laurel allows erasing the counter from a reference value. A Laurel `Frozen` type takes a regular reference type, and produces a type that is the same except that it does not support reference equality or mutation of its fields. Record types are composite types that are frozen by default.

TODO, add example with a `record Tuple..` and a `composite MutableTuple` and a `Frozen<MutableTuple>` that are all three created in and returned from different procedures that each have an empty reads clause. Returning the `MutableTuple` fails to prove the reads clause.

# Use complete algorithms to reduce workload
To achieve goal 7, to reduce the verification work through the use of complete algorithms, Laurel has the following features.

## Constrained types
Constrained types propagating facts through the type system.

TODO, add example using polymorphic types, like a wrapping Container<T> that takes a `nat` and we still have the `nat` fact on the other side.

## Type inference

To be designed.. but here is some subject to change content.

Laurel can statically infer the types of variables, which, when the inferred types where otherwise not available in the source program, can enable emitting code that can be verified more efficiently.

Here's an example related to nullable reference types:

Input program:
```
var foo := new Foo;
foo.x := 1;

var bar := foo;
bar := null;
bar.x := 2
```

Without type inference, we can not judge whether the variable `foo` should have type `Foo` or `Nullable<Foo>`, so we have to pick defensively:
```
datatype Nullable<T> = from_NotNull(as_notNull: T) | from_Null

var foo: Nullable<Foo> := from_NotNull(new Foo);
as_notNull(foo).x := 1;

var bar: Nullable<Foo> := foo;
bar := null;
as_notNull(bar).x := 2
```

With type inference, we can infer that `foo` is never nullable:
```
var foo: Foo := new Foo;
foo.x := 1;

var bar: Nullable<Foo> := from_NotNull(foo);
bar := null;
as_notNull(bar).x := 2
```

Note the coercion `from_NotNull` that was inserted in the assignment to `bar`. Laurel can be given a list of coercions that can be inserted automatically. Laurel can also be given a list of type coercions, which it can use to change the type annotations of variables, from for example `T` to `Nullable<T>`.

## Flow based types

Flow based types allow the type of a variable to change throughout the control-flow of the program, which enables having more precise types which improves verification performance.

Source program:
```
var foo := new Foo;
foo.x := 1;
foo := null;
foo.x := 2;
```

Inferred program:
```
var foo := new Foo;
foo.x := 1;
var foo_2: Nullable<Foo> := from_NotNull(foo);
foo_2 := null;
as_notNull(foo_2).x := 2;
```

## Inference of composite types

To be designed..

Useful for dynamic languages. Infers composites types based on fields assigned to values.
Composite types perform better than maps because reading from them incurs no domain check.

# Verification without side-effects

To support goal 8, for verification code not to affect the outcome of executing the program, Laurel has rules for code that exists only for verification purposes.

Rules for contracts:
- Contract code may not modify variables defined outside the contract scope.
- Contract code has an empty modifies clause. Contract code operates on a copy of the heap.

TODO, add examples

# Great user experience

## Parameter lists
Parameter lists. In Laurel, input and output parameters are defined in a separate list. Inout parameters are defined by repeating the parameter name in both lists. In Core, there is a single parameter list where each parameter defines its kind (in/out/inout).

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
