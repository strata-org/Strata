# Hindley-Milner Soundness Experiment

This folder contains an experiment for an alternate, stronger proof of soundness for a Hindley-Milner type system. You can think of it as a self-contained mini-Strata to help give us ideas about how we can structure proofs that will extend to the full system. This version omits some features that cause complications in the full Strata implementation (e.g. type aliases, scopes) and provides explicitly annotated terms.

## The Proof Goal

The particular goal is to prove type soundness via a 2 step approach: first prove that the result of type inference is within a stronger type system (one where all terms are explicitly annotated with their types) and then prove terms well-typed in this stronger type system are also well-typed in Hindley-Milner.

Each of these two parts is complete (`W_well_typed` in `WellTyped.lean` proves the first, and `HasTypeA_implies_HasType` in `Erasure.lean` proves the second). However, the latter theorem requires a condition that the context is "compatible" with the free variable annotations. Proving this last remaining lemma (`W_ctxCompat` in `Soundness.lean`) is quite tricky. In particular, it likely requires lots of reasoning about type substitutions and their relation to each other. It also almost certainly requires results about freshness (e.g. the fact that Algorithm W produces fresh type variables), which so far has not been needed in any proofs. This, in turn, requires reasoning about the state (a `Nat`) used to ensure fresh variables.

Some notes:
1. There will likely be an additional condition we need on `W_ctxCompat` (something about the input context). 
2. It is possible (though unlikely), that `AExpr.ctxCompat` is not exactly the right condition. More broadly, we need a condition that is sufficient to prove `HasTypeA_implies_HasType` and which holds of the result of `W`. However, I believe that this condition is the right one.

## File Structure

The dependencies should be straightforward. Essentially, each file in the list show depend on the ones before it. There are a handful of `List` and `Map` lemmas from `Strata/DL/Util`, other than that, there are no other dependencies:

`Ty.lean` - (polymorphic) types, similar to Lambda
`Expr.lean` - expressions, similar to Lambda
`AExpr.lean` - annotated expressions
`Subst.lean` - defines type substitutions
`Typing.lean` - a Hindley-Milner-style type system (like HasType)
`Unify.lean` - an (incorrect) implementation of unification
`AlgorithmW.lean` - an implementation of Hindley-Milner type inference
`SoundnessLemmas.lean` - various helper lemmas, mostly about type substitutions
`Checker.lean` - the definition of `HasTypeA` (the stronger type system) and a function to check consistency of annotations, plus their equivalence proof
`Erasure.lean` - the proof that `HasTypeA` implies `HasType` 
`WellTyped.lean` - the proof that type inference satisfies `HasTypeA` (well-annotated)
`Soundness.lean` - the (incomplete) proof of `W_ctxCompat` and the overall proof of soundness

Note that there are 2 axioms: 1 about strings (working with strings is annoying in Lean) and the soundness of unification, which is not actually true of the given implementation (but has been proved of the real one). If it is easier, we can axiomatize `unify` completely.