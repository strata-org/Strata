> **Note:** The canonical reference for recursive function syntax is now the
> [Strata Core Language Definition](verso/LangDefDoc.lean) (Section 4, "Recursive Functions").
> SMT encoding details are in [Transforms and Analysis](verso/TransformsDoc.lean).
> This file is retained for additional detail not yet migrated. It may be removed in the future.

# Recursive Functions in Strata

This document describes the recursive function infrastructure in Strata Core.

## Overview

Strata Core supports two kinds of recursive functions:

1. **Structural recursion** over algebraic datatypes (ADTs), driven by `@[cases]`.
2. **Int-valued recursion** with an integer termination measure (`decreases <int expr>`).

Both single and mutually recursive functions are supported in both modes.

## Syntax

### Single Recursive Functions

Recursive functions are declared with the `rec` keyword. A single recursive
function is a `rec` block containing one function, terminated by `;`:

```
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};
```

For structural recursion, exactly one parameter must be annotated with `@[cases]`
to indicate the ADT argument. The `@[cases]` annotation tells the axiom
generator which parameter drives per-constructor axiom generation (partial
evaluation). For int-valued recursion, `@[cases]` is not required.

Recursive functions cannot be marked `inline`.

### The `decreases` Clause

An optional `decreases` clause specifies the termination measure. It appears
after the preconditions and before the body.

```
rec function zipLen (@[cases] xs : IntList, ys : IntList) : int
  decreases ys
{
  if IntList..isNil(xs) then 0
  else if IntList..isNil(ys) then 0
  else 1 + zipLen(IntList..tl(xs), IntList..tl(ys))
};
```

```
rec function fib (n : int) : int
  decreases n
{
  if n <= 1 then n else fib(n - 1) + fib(n - 2)
};
```

- If `decreases` is omitted, the `@[cases]` parameter is used as the measure.
- If `decreases` names a datatype-typed parameter, structural termination is
  used. The `@[cases]` parameter still controls axiom generation independently.
- If `decreases` is an expression of type `int`, int-valued termination is used.
  `@[cases]` is not required.
- The expression may be compound (e.g., `decreases m + n`).
- If both `@[cases]` and an int-valued `decreases` are present, `@[cases]` is
  used for unfolding in the SMT solver, while `decreases` is used for
  termination checking.

### Mutually Recursive Functions

Mutually recursive functions are declared as multiple functions within a single
`rec` block. The block starts with `rec`, lists each function (without `rec`
on subsequent functions), and ends with `;`. All functions in the block can call
each other (and themselves). Each function must have either a `@[cases]`
parameter or a `decreases` clause. The functions may operate on different
datatypes:

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

2. **Axiom Generation (`RecursiveAxioms.lean`):** For structural recursive
   functions (those with `@[cases]`), per-constructor axioms are generated.
   For each constructor `C` of the ADT at the `@[cases]` parameter, a
   universally quantified axiom is generated:

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
   **uninterpreted function**. For structural recursive functions, the
   per-constructor axioms from step 2 are emitted as quantified SMT assertions
   with `:pattern` annotations. Int-recursive functions have no axioms.

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

Termination checking is always on for all `rec` functions. The TermCheck
pipeline phase generates a `f$$term` verification procedure for each recursive
function, asserting that the termination measure decreases at each recursive
call site, guarded by path conditions through `ite` branches.

### Structural Termination (ADT)

For structural recursion, TermCheck:

1. Generates a `D..adtRank : D → Int` uninterpreted function and per-constructor
   axioms establishing that recursive fields have strictly smaller rank.
2. Generates a `f$$term` procedure that asserts
   `adtRank(callArg) < adtRank(callerParam)` at each recursive call site.

### Int-Valued Termination

For int-valued recursion, TermCheck generates a `f$$term` procedure that asserts
two obligations at each recursive call site:
- `0 <= call_measure` (non-negativity)
- `call_measure < caller_measure` (strict decrease)

Where `call_measure` is the `decreases` expression with formals substituted by
the actual arguments at the call site. No `adtRank` axioms are needed.

### Failure Modes

A function that fails its termination check will produce an `unknown` or `fail`
result on its `_terminates_` obligations. Non-terminating definitions like
`f(xs) = f(xs)` or `f(n) = f(n + 1)` are caught this way.

## Current Limitations

- **Monomorphic SMT encoding only:** Polymorphic recursive functions are not yet
  supported at the SMT encoding level. This applies to both single and mutually
  recursive functions.
- **Top-level only:** Recursive functions must be declared at the program level;
  recursive function statements (local declarations) are not supported.
- **No procedure termination checking:** Self-recursive procedures do not yet
  have termination checking support.
- **No lexicographic measures:** Only single-expression measures are supported.
  Lexicographic tuple measures are planned.
- **No nat type:** Non-negativity of compound int-valued measures involving
  function calls (e.g., `listLen(l1) + listLen(l2)`) may require explicit
  preconditions, since the SMT solver cannot always infer that a function
  returns a non-negative value.
