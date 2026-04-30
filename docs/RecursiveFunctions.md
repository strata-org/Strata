# Recursive Functions in Strata

This document describes the recursive function infrastructure in Strata Core.

## Overview

Strata Core supports recursive functions that recurse on algebraic datatypes
(ADTs). At the SMT level, a recursive function is encoded as an **uninterpreted
function (UF)** together with **per-constructor axioms** equipped with
**triggers**.

Both single and mutually recursive functions are supported.

## Syntax

### Single Recursive Functions

Recursive functions are declared with the `rec` keyword. Exactly one parameter
must be annotated with `@[cases]` to indicate the ADT argument being recursed on.
A single recursive function is a `rec` block containing one function, terminated
by `;`:

```
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};
```

The `@[cases]` annotation tells the axiom generator which parameter drives the
per-constructor axiom generation (partial evaluation). Only one `@[cases]`
parameter is allowed per function.

Recursive functions cannot be marked `inline`.

### The `decreases` Clause

An optional `decreases` clause specifies which parameter is used as the
termination measure. It appears after the preconditions and before the body:

```
rec function zipLen (@[cases] xs : IntList, ys : IntList) : int
  decreases ys
{
  if IntList..isNil(xs) then 0
  else if IntList..isNil(ys) then 0
  else 1 + zipLen(IntList..tl(xs), IntList..tl(ys))
};
```

- If `decreases` is omitted, the `@[cases]` parameter is used as the termination
  measure (this is the common case where both coincide).
- If `decreases` is provided, it overrides only the termination check. The
  `@[cases]` parameter still controls per-constructor axiom generation.
- The `decreases` expression must name a parameter whose type is a known ADT.
- `@[cases]` is always required, even when `decreases` is provided.

### Mutually Recursive Functions

Mutually recursive functions are declared as multiple functions within a single
`rec` block. The block starts with `rec`, lists each function (without `rec`
on subsequent functions), and ends with `;`. Each function in the block must
have its own `@[cases]` parameter. All functions in the block can call each
other (and themselves). The functions may operate on different datatypes:

```
datatype RoseTree { Leaf(val: int), Node(children: RoseList) }
datatype RoseList { RNil(), RCons(hd: RoseTree, tl: RoseList) };

rec function treeSize (@[cases] t : RoseTree) : int
{
  if RoseTree..isLeaf(t) then 1 else listSize(RoseTree..children(t))
}
function listSize (@[cases] xs : RoseList) : int
{
  if RoseList..isRNil(xs) then 0 else treeSize(RoseList..hd(xs)) + listSize(RoseList..tl(xs))
};
```

## Verification Pipeline

1. **Parsing & Elaboration (DDM):** The `rec` block is parsed via
   `command_recfndefs` in the grammar. Individual functions within the block
   are parsed as `recfn_decl` nodes. The `@[preRegisterFunctions]` annotation
   on the block triggers two-phase elaboration: Phase 1 extracts all function
   signatures and registers them in the global context, Phase 2 elaborates
   all function bodies with full mutual visibility. The `@[cases]` binding is
   translated to an `inlineIfConstr` attribute recording the parameter index.

2. **Axiom Generation (`RecursiveAxioms.lean`):** For each constructor `C` of
   the ADT at the `@[cases]` parameter, a universally quantified axiom is
   generated:

   ```
   ∀ (params..., fields...). f(..., C(fields...), ...) = PE(f(..., C(fields...), ...))
   ```

   The LHS is left unevaluated and serves as the **trigger pattern** for the SMT
   solver. The RHS is obtained by passing the LHS through the **partial
   evaluator (PE)**, which inlines the function body (since the `@[cases]`
   argument is a constructor application, matching the `inlineIfConstr`
   attribute) and reduces.

   For mutually recursive functions, axioms are generated independently for each
   function in the block.

3. **SMT Encoding (`SMTEncoder.lean`):** Each function is declared as an
   **uninterpreted function**. The per-constructor axioms from step 2 are
   emitted as quantified SMT assertions with `:pattern` annotations.

### SMT Encoding Example

Given a `listLen` function over `IntList = Nil | Cons(hd: int, tl: IntList)`,
the SMT output is:

```smt2
(declare-datatype IntList (
  (Nil)
  (Cons (IntList..hd Int) (IntList..tl IntList))))

; listLen is an uninterpreted function
(declare-fun listLen (IntList) Int)

; Per-constructor axiom for Cons, with trigger
(assert (forall (($__bv0 Int) ($__bv1 IntList))
  (! (= (listLen ((as Cons IntList) $__bv0 $__bv1))
        (+ 1 (listLen $__bv1)))
     :pattern ((listLen ((as Cons IntList) $__bv0 $__bv1))))))
```

There is no axiom for `Nil` because the PE fully reduces `listLen(Nil)` to `0`,
so the encoder emits it as a concrete equality rather than a quantified axiom.

## Termination Checking

Termination checking is always on for all `rec` functions. It verifies that
recursive calls pass a structurally smaller argument by encoding a well-founded
ordering on ADTs using `dtRank` functions (see `docs/TerminationChecking.md`).

For each recursive function, the TermCheck pipeline phase:

1. Generates a `D..dtRank : D → Int` uninterpreted function and per-constructor
   axioms establishing that recursive fields have strictly smaller rank.
2. Generates a `f$$term` verification procedure that asserts
   `dtRank(callArg) < dtRank(callerParam)` at each recursive call site,
   guarded by the path condition through `ite` branches.

A function that fails its termination check will produce an `unknown` or `fail`
result on its `_terminates_` obligations. Non-terminating definitions like
`f(xs) = f(xs)` or `f(xs) = f(Cons(1, xs))` are caught this way.

## Current Limitations

- **ADT recursion only:** The `@[cases]` and `decreases` mechanisms only support
  structural recursion on algebraic datatypes. Recursion on other types
  (e.g., `int`) or non-structural recursion patterns are not yet supported.
  Arbitrary integer measures and lexicographic orderings are planned.
- **Monomorphic SMT encoding only:** Polymorphic recursive functions are not yet
  supported at the SMT encoding level. This applies to both single and mutually
  recursive functions.
- **Top-level only:** Recursive functions must be declared at the program level;
  recursive function statements (local declarations) are not supported.
- **No procedure termination checking:** Self-recursive procedures do not yet
  have termination checking support.
