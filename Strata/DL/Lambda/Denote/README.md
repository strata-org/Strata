# Lambda's Denotational Semantics

This folder contains a denotational semantics for Lambda, intepreting Lambda terms
as objects in Lean's logic. The basic design is loosely inspired by the semantics
of Why3's logic as presented in Jean-Christophe Filliâtre's 2013 paper
"One Logic to Use Them All" (https://inria.hal.science/hal-00809651v1/document) 
and more concretely by the subsequent Rocq formalization by Cohen and Johnson-Freyd 
(https://dl.acm.org/doi/10.1145/3632902). The main differences
concern variable binding, the mechanics of `Factory` function evaluation, and
equality checking reasoning.

Each file's header lists the key theorems and definitions.
The organization of the directory is as follows:
- `HList.lean` - definition of heterogenous lists
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

