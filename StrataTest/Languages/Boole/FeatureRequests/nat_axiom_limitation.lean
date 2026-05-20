/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Discussion: `type nat := int` + auto-generated non-negativity axioms

Abdal's proposed design
───────────────────────
  type nat := int;
  datatype NatList { Nil(), Cons(head: nat, tail: NatList) };
  -- auto-generated:
  axiom (∀ l : NatList :: NatList..isCons(l) ==> NatList..head(l) >= 0)

The auto-axiom lets any procedure that receives a NatList immediately derive
`head(l) >= 0` from `isCons(l)`, without a manual assumes/requires.

────────────────────────────────────────────────────────────────────────────
CASE 1 — WORKS: homogeneous nat-field list
────────────────────────────────────────────────────────────────────────────
NatList has only `nat` fields.  The auto-axiom fires and the postcondition
`head(l) >= 0` is proved without a manual requires.  ✅ intended behaviour.
-/

private def natListCase : Strata.Program :=
#strata
program Boole;

type nat := int;

datatype NatList {
  Nil(),
  Cons(head: nat, tail: NatList)
};

procedure use_nat_list(l: NatList) returns ()
spec {
  requires NatList..isCons(l);
  ensures NatList..head(l) >= 0;
} {
  exit use_nat_list;
};
#end

/-- info:
Obligation: use_nat_list_post_use_nat_list_ensures_1_1512_calls_NatList..head_0
Property: assert
Result: ✅ pass

Obligation: use_nat_list_ensures_1_1512
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" natListCase (options := .quiet)

/-
────────────────────────────────────────────────────────────────────────────
CASE 2 — BROKEN: mixed nat/int fields in the same datatype
────────────────────────────────────────────────────────────────────────────
`Pair` has `first : nat` (gets the auto-axiom) and `second : int` (does not).

The auto-axiom emitted is:
  ∀ x : Pair . Pair..isPair_mk(x) ==> Pair..first(x) >= 0

Problem: the SMT solver (cvc5 1.3.3) can instantiate this forall with the
synthetic term  x := Pair_mk(Pair_second(p), 0).
By the ADT selector axiom,  Pair_first(Pair_mk(Pair_second(p), 0)) = Pair_second(p).
So the axiom instance becomes:  Pair_second(p) >= 0.

This means ANY query that contains both this datatype and a negative `int`
value becomes inconsistent in the SMT model — even when `second` is
completely unrelated to `first`.

Illustration: the procedure below has precondition `second(p) < 0` and
postcondition `second(p) >= 0`, which is logically false.  But it passes (✅)
because the auto-axiom makes the SMT context inconsistent.
This is a soundness hole for the mixed-field case.
-/

private def mixedPairCase : Strata.Program :=
#strata
program Boole;

type nat := int;

datatype Pair {
  Pair_mk(first: nat, second: int)
};

procedure unsound_example(p: Pair) returns ()
spec {
  requires Pair..isPair_mk(p) && Pair..second(p) < 0;
  ensures Pair..second(p) >= 0;
} {
  exit unsound_example;
};
#end

-- ⚠️  This should be ❌ fail but is ✅ pass — the auto-axiom is too strong.
/-- info: [Boole] Warning: constructor `Pair.Pair_mk` has both `nat`- and `int`-typed fields. The auto-generated non-negativity axiom is globally quantified over all SMT terms of type `Pair`, which may be unsound if the solver introduces synthetic terms with negative nat fields.
---
info:
Obligation: unsound_example_pre_unsound_example_requires_0_3451_calls_Pair..second_0
Property: assert
Result: ✅ pass

Obligation: unsound_example_post_unsound_example_ensures_1_3505_calls_Pair..second_0
Property: assert
Result: ✅ pass

Obligation: unsound_example_ensures_1_3505
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" mixedPairCase (options := .quiet)

/-
Why it happens — the minimal SMT formula
─────────────────────────────────────────
The SMT problem sent to cvc5 for `unsound_example_ensures` is:

  (set-logic ALL)
  (declare-datatype Pair ((Pair_mk (Pair..first Int) (Pair..second Int))))
  ; auto-axiom for first : nat
  (assert (forall (($bv0 Pair)) (=> (|is-Pair_mk| $bv0) (>= (Pair..first $bv0) 0))))
  ; precondition
  (assert (and (|is-Pair_mk| p) (< (Pair..second p) 0)))
  ; negated goal (validity check)
  (assert (not (>= (Pair..second p) 0)))
  (check-sat)   ; → unsat  (should be sat)

Manually verified: `cvc5 min.smt2` returns `unsat` with this formula.
Without the forall assert it returns `sat` (correct).

Root cause: the `forall` is a global SMT assertion over ALL Pair terms in
the universe, including synthetic ones.  Instantiating with
  $bv0 := Pair_mk(Pair..second(p), 0)
gives  Pair..first(Pair_mk(Pair..second(p), 0)) >= 0,
which simplifies to  Pair..second(p) >= 0  (by the ADT selector axiom).
This contradicts  Pair..second(p) < 0, making the context inconsistent.

────────────────────────────────────────────────────────────────────────────
DESIGN ALTERNATIVES
────────────────────────────────────────────────────────────────────────────

Option A — Status quo + documented restriction
  Keep the auto-axiom.  Document that `nat` fields must not be mixed with
  unconstrained `int` fields in the same datatype when the `nat` axiom is
  active.  Works for all five dalek-lite benchmarks (B1–B5) since their
  `nat`-like fields are either separate datatypes or all-`nat` constructors.
  Simplest path; no SMT change required.

Option B — Distinct abstract type (existing nat_int_boundary.lean approach)
  Keep `type nat;` as an abstract sort (not a synonym for int).
  Add explicit coercions:
    function nat_to_int(n: nat) : int;
    axiom (∀ n : nat . nat_to_int(n) >= 0);   -- one axiom, no ADT interaction
  `nat` and `int` live in separate SMT sorts — no quantifier instantiation
  issue.  Downside: every use of a `nat` field requires an explicit
  `nat_to_int` call, adding coercion noise to specs.

Option C — Constructor-site preconditions instead of a global axiom
  Don't emit a global forall axiom.  Instead, when a procedure receives a
  datatype value, add a ghost `requires` (or an `assume`) that the `nat`
  fields are non-negative.  This is local and never interacts with unrelated
  `int` values.  Downside: either the user must state it manually, or the
  translator must detect "datatype parameter" inputs and inject the assumes
  automatically — more complex but semantically precise.

Option D — Keep auto-axiom but restrict it to programs with no bare `int` fields
  Only emit the nonneg axiom if ALL non-recursive fields of the datatype are
  `nat` (or other non-negative types).  Mixed nat/int datatypes fall back to
  Option B or C.  Conservative; avoids the soundness hole without any SMT
  change.
-/
