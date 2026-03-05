# Recursive Functions in Strata

This document describes the recursive function infrastructure in Strata Core.

## Overview

Strata Core supports recursive functions that recurse on algebraic datatypes
(ADTs). At the SMT level, a recursive function is encoded as an **uninterpreted
function (UF)** together with **per-constructor axioms** equipped with
**triggers**.

## Syntax

Recursive functions are declared with the `rec` keyword. Exactly one parameter
must be annotated with `@[cases]` to indicate the ADT argument being recursed on:

```
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
}
```

The `@[cases]` annotation tells the axiom generator which parameter drives the
recursion. Only one `@[cases]` parameter is allowed per function.

Recursive functions cannot be marked `inline`.

## Verification Pipeline

1. **Parsing & Elaboration (DDM):** The `rec function` syntax is parsed via
   `command_recfndef` in the grammar. The `@[scopeSelf]` annotation on the body
   parameter makes the function name available in its own body during
   elaboration, enabling recursive calls. The `@[cases]` binding is translated
   to an `inlineIfConstr` attribute recording the parameter index.

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

3. **SMT Encoding (`SMTEncoder.lean`):** The function is declared as an
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

## Current Limitations

- **ADT recursion only:** The `@[cases]` mechanism only supports structural
  recursion on algebraic datatypes. Recursion on other types (e.g., `int`) or
  non-structural recursion patterns are not supported.
- **No termination checking:** Recursive functions are accepted without verifying
  that they terminate. Unsound axioms can result from non-terminating definitions.
- **Monomorphic SMT encoding only:** Polymorphic recursive functions are not yet
  supported at the SMT encoding level.
- **No mutual recursion:** Mutually recursive functions are not supported.
- **Top-level only:** Recursive functions must be declared at the program level;
  recursive function statements (local declarations) are not supported.
