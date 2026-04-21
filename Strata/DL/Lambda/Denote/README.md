# Lambda's Denotational Semantics

This folder contains a denotational semantics for Lambda, intepreting Lambda terms
as objects in Lean's logic. The basic design is loosely inspired by the semantics
of Why3's logic as presented in Jean-Christophe Filliâtre's 2013 paper
"One Logic to Use Them All" (https://inria.hal.science/hal-00809651v1/document) 
and more concretely by the subsequent Rocq formalization by Cohen and Johnson-Freyd 
(https://dl.acm.org/doi/10.1145/3632902). The main differences
concern variable binding, the mechanics of `Factory` function evaluation,
equality checking reasoning, and the presence of an operational semantics.

Each file's header lists the key theorems and definitions.
The organization of the directory is as follows:
- `LExprAnnotated.lean` - definition of a type system for well-annotated Lambda
terms (i.e. those that are annotated with their inferred types)
- `Assumptions.lean` - typing and annotation-consistency assumptions for
Factory bodies/concrete evaluators, environments, and expressions
- `LExprDenote.lean` - definition of denotation function, equivalence with
relational version, definitions of logical notions (e.g. validity)
- `LExprDenoteProps.lean` - properties of denotations (e.g. invariance under
changes to interpretations and valuations that agree on variables/ops present
in a term, invariance under changes to metadata)
- `LExprDenoteSubst.lean` - proofs about semantics of substitution of bound
variables (`substK`, `subst`) and free variables (`substFvarsLifting`)
- `LExprDenoteTySubst.lean` - proofs about semantics of type substitution 
(`tySubst`)
- `CallOfLFuncDenote.lean` - proofs about semantics of Factory function calls
and `callOfLFunc` more generally
- `LExprDenoteConstrs.lean` - proofs about semantics of datatype constructors
- `LExprDenoteEq.lean` - proof of soundness of equality check `eql`
- `LExprSemanticsConsistent.lean` - proof that operational and denotational 
semantics are consistent (single-step, multi-step, and partial evaluator)

## Trusted Code Base

The TCB of the denotational semantics consists of the following:
1. The typing relation `HasTypeA` in `LExprAnnotated.lean`
2. The definitions of type and term denotations in `LExprDenote.lean` (
`SortDenote`, `TyDenote`, `LExpr.denote`, and its dependencies)
3. The definitions of consistency in `LExprDenote.lean` (especially 
`InterpConsistentBody`, `InterpConsistentEval`, `InterpConsistent`, 
`ConstrInterpConsistent`)
4. The dependencies of these definitions, especially heterogenous lists in 
`HList.lean` and the definition of `substTyVars`.

Notably, the TCB denotational semantics does not include several nontrivial
functions present in the TCB of the operational semantics: `substFvarsLifting`,
`substFvarsFromState`, `Factory.callOfLFunc`, `eql`, etc.

The semantics consistency theorems additionally depend on the assumptions in
`Assumptions.lean`. See below.

## Assumptions

The denotational semantics and its theorems rely on two kinds of assumptions:
1. The definition of validity in the semantics itself requires consistent 
interpretations - those that agree with concrete `Factory` functions and 
declared datatypes.
2. The semantic consistency theorems require various typing and well-formedness
assumptions on the expression in question, `Factory` functions, and the
environment. 

The second set of assumptions are given in `Assumptions.lean` and we will
eventually prove that they are satisfied of well-typed terms.
The first set is much trickier to handle. Implicitly, each concrete function and
datatype definition gives rise to a set of axioms concerning its behavior, and
these assumptions are intended to hold if these axioms are consistent. If the
assumptions do not hold (for instance, if the typing rules are too permissive),
then validity becomes trivial. Proving that consistent interpretations exist
is possible but very difficult with recursive functions.
TODO: Show that consistent interpretations exist for a simple but nontrivial
example.

Note that the semantics does not handle function preconditions at the moment.

## Using the Semantics

The file `StrataTest/DL/Lambda/Denote/Tautologies.lean` shows how to use the
semantics to prove validity of some simple bool-valued formulas 
(e.g. modus ponens). In this file, we provide an alternate kernel-reducing 
version of the consistency conditions that
sidestep the need for most of the dependent type reasoning.
The remaining limitation is the use of HashMaps for a `Factory`; since this
does not reduce in the kernel, lookups are currently handled by a mix of
`native_decide` and `sorry` (for non-decidable values).