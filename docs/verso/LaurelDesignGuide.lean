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
2. Reduce code duplication in the analysis of popular languages by being a target for compilation from those languages, and including features common to them. Note that we expect source languages to reduce their existing compilers when possible, so language features that can be compiled away don't need to be considered.
3. Minimize the amount of user code needed to enable verification.
4. Enable modular verification
5. Use complete analysis algorithms to reduce the required proof effort.
6. Enable finding proofs through an automated search.
7. Code used to enable verification may not affect execution behavior.

# Reduce duplication between source languages
To achieve goal (2), reduce code duplication in the analysis of popular languages, Laurel contains many features shared between several languages. The following table shows which features are shared with which input languages.

TODO, add a table with Laurel features as rows, and a list of languages in columns (Java, Kotlin, C#, JavaScript, Python, GoLang). Split up language feature whenever relevant for the columns.

These features should be in rows but marked as WIP:
- Try/catch and checked exception
- Procedures types and procedures as values
- Parametric polymorphism

# Enable Verification
To achieve goal 1.3, enable proving properties through verification, Laurel has the following features.
- Assertions
- Quantifiers
- Old/allocated/fresh
- Decreases clauses
- Loop invariants (more about automated proof)
- Assumptions (more about gradual verification)

# Modular Verification
To achieve goal (4), Laurel has the following features related to modular verification.

## Preconditions
Preconditions enable proving the assertions in a procedure's body without having to consider the callers. This way, each assertion only needs to be proven once, instead of once for each transitive call-site.

## Encapsulation
Postconditions enable encapsulating the behavior of a procedure through a simpler condition. This simplifies reasoning at the call-site.

Since procedures can mutate references as well, once we add encapsulation through postconditions, we also need modifies clauses to enable encapsulating reference modifying procedures.

Reads clauses are useful to improve verification performance. The facts they prove work well together with the facts provided by modifies clauses, making it easier to prove which procedure values have remained unchanged after objects were modified.

# Reduce verification through complete analysis
To achieve goal 5, Laurel has the following features.

## Constrained types
Constrained types propagating facts through the type system.

TODO, add example using polymorphic types

## Implicit conversions

To be designed..


# Minimize Verification Code
To achieve goal (3), minimize the amount of user code needed to enable verification, Laurel has the following features:

## Transparent procedures
Laurel procedures are transparent by default, meaning that a call can use the body of the callee to prove facts about the result of the call. Laurel will allow any procedure to be transparent, although currently there are some restrictions. In particular, Laurel will allow procedures that contains loops or that modify the heap, to be transparent as well.

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

# Naming choices

# Differences between Laurel and Core

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
