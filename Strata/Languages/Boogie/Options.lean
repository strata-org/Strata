/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/--
Remove irrelevant axioms; this mode is intended only for _deductive verification_,
where it is always sound to remove an axiom. We can use this mode to prune the
goals as a part of a backend portfolio one day to optimize verification
performance.

Soundness has the usual definition: if we report that a formula is valid, then
it is really valid.

For this discussion, we assume that there is no contradiction in the axioms.

## Deductive Verification

Consider a goal `G: P ==> Q`, where `P` contains an axiom/assumption `A`. If `A`
is removed, then we get `G': P' ==> Q`, where `P'` is a weaker version of `P`
that doesn't contain `A` (and of course, `G'` is a stronger version of `G`). For
soundness w.r.t. deductive verification, we want: if `G'` is valid, then `G`
was valid (but not necessarily the converse).

**Case 1: `G'` is valid.**
Since `P' ==> P`, we have `P ==> Q`, i.e., `G` is valid too. Soundness is
preserved.

**Case 2: `G'` is invalid.**
There exists a model `M` for which `G'` is false, i.e., `M ⊨ P'` but `M ⊭ Q`.
This alone doesn't tell us about the validity of `G`:
- If `M ⊨ P` (i.e., `M` also satisfies the removed axiom `A`), then `M` is a
  counterexample for `G` too, so `G` is invalid too. Thus, a counterexample can
  be validated by checking if it satisfies `P`.
- If `M ⊭ P` (i.e., `M` violates the removed axiom `A`), then `M` is not a
  valid counterexample for `G`, and `G` might still be valid.

**Case 3: Validity of `G'` cannot be determined.**
This can be due to various reasons, like solver timeout, problem's complexity,
or incomplete solver theories. `G` could be valid, invalid, or undecidable.

**Soundness guarantee:** Axiom removal does not lead to proofs of
invalid goals, but it may cause valid goals to become unprovable,
resulting in "unknown" results. Moreover, if a counterexample is found for the
weakened goal, it may not be a valid counterexample for the original goal.

Note though that soundness is preserved regardless of the quality of axiom
relevance analysis.
-/
inductive IrrelevantAxiomsMode where
  /--
    Only the functions in the consequent `Q` of a goal `P ==> Q` will be
    taken into account for relevant axiom analysis. This means that axioms
    relevant to some function in `P` (but not in `Q`) may be removed. This is
    sound, but may yield unknown results from the solver.
  -/
  | Aggressive
  /--
   Functions in both `P` and `Q` of a goal `P ==> Q` will be considered for
   relevant axiom analysis.
  -/
  | Precise
  /-- Do not prune any axioms. -/
  | Off
  deriving Repr, DecidableEq, Inhabited

structure Options where
  verbose : Bool
  parseOnly : Bool
  typeCheckOnly : Bool
  checkOnly : Bool
  stopOnFirstError : Bool
  removeIrrelevantAxioms : IrrelevantAxiomsMode
  /-- Solver time limit in seconds -/
  solverTimeout : Nat

def Options.default : Options := {
  verbose := true,
  parseOnly := false,
  typeCheckOnly := false,
  checkOnly := false,
  stopOnFirstError := false,
  removeIrrelevantAxioms := IrrelevantAxiomsMode.Off,
  solverTimeout := 10
}

instance : Inhabited Options where
  default := .default

def Options.quiet : Options :=
  { Options.default with verbose := false }
