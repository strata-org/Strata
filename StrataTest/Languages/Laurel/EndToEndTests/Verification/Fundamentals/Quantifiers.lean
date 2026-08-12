/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel <|
#strata
program Laurel;
procedure testForall()
  opaque
{
    assert forall(x: int) => x + 0 == x
};

procedure testExists()
  opaque
{
    assert exists(x: int) => x == 42
};

procedure testQuantifierInContract(n: int)
  requires n > 0
  opaque
  ensures forall(i: int) => i >= 0 ==> i < n ==> i < n + 1
{
};

procedure P(x: int): int;
procedure Q(): int;
procedure triggers()
  opaque
{
  assert forall(i: int) { P(i) } => P(i) == i + 1;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  assert forall(i: int) => true;

  assume forall(i: int) { P(i) } => P(i) == i + 1 && Q() == 0;
  assert Q() == 0;
//^^^^^^^^^^^^^^^ error: assertion could not be proved
  assert P(1) == 2
};
#end

/-! ## Quantifier proof procedures

A quantifier body may be a multi-statement block containing `assert`/`assume`
steps. The transparency pass precedes the quantifier with a *proof block*:

```
{ var $proof_0: bool;
  if $proof_0 then { var $havoc_0: T; <body[x := $havoc_0]>; assume false };
  forall(x: T) => <goal> }
```

The nondet-guarded branch havocs the bound variable — under a fresh `$havoc_N`
name, since a declaration reusing the binder's name would shadow an in-scope
local and shadowing does not survive lowering to Core — runs the body's proof
steps, and seals with `assume false` so nothing leaks into the enclosing path
conditions.

The proof block discharges *only* the obligations written inside the body: its
`assert` steps, checked for an arbitrary `x`, with the body's `assume` steps
available as hypotheses. It establishes nothing about the quantifier itself —
no `assume forall(...)` is emitted — so the enclosing `assert`/`assume` still
sees an ordinary quantifier that the solver must discharge on its own merits.
The tests below pin both halves of that contract. -/

-- Proof procedure: the goal holds unconditionally, so the quantifier is
-- provable on its own merits and the body's assume is merely a proof step.
#eval testLaurel <|
#strata
program Laurel;

procedure proofProcedureBasic()
  opaque
{
  assert forall(x: int) => {
    assume x * x >= 0;
    x * x >= 0
  }
};
#end

/-! ### The proof block must not establish the quantifier

No `assume forall(x: T) => <goal>` is emitted after the sealed branch. Such an
assume would be unsound: the goal sits in expression position inside the branch
and generates no obligation, so the branch never proves it, making the assume a
free axiom — and being procedure-scoped, it would also discharge later unrelated
quantified asserts. These tests pin that no such assume exists. -/

-- A goal that is false for some x must not be provable, even though the
-- body's assume constrains x. (x = 11 refutes `x > 100`.)
#eval testLaurel <|
#strata
program Laurel;

procedure proofProcedureGoalNotAssumed()
  opaque
{
  assert forall(x: int) => { assume x > 10; x > 100 }
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A proof procedure must not leak an antecedent-free fact to a later,
-- unrelated quantified assert. (y = 0 refutes `y > 5`.)
#eval testLaurel <|
#strata
program Laurel;

procedure proofProcedureNoAntecedentLeak()
  opaque
{
  assert forall(x: int) => { assume x > 10; x > 5 };
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  assert forall(y: int) => y > 5
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Soundness probe for the seal: `assume false` inside a proof body must not
-- discharge a later procedure-level assert.
#eval testLaurel <|
#strata
program Laurel;

procedure proofProcedureSealSoundness()
  opaque
{
  assert forall(x: int) => {
    assume false;
    x * x >= 0
  };
  assert 1 == 2
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Proof procedure with an intermediate assertion step.
#eval testLaurel <|
#strata
program Laurel;

procedure proofProcedureWithAssert()
  opaque
{
  assert forall(x: int) => {
    assert x * x >= 0;
    x * x >= 0
  }
};
#end

/-! ### An inner assert is a real obligation, not a dropped step

An `assert` inside a quantifier body is checked for an arbitrary `x` rather than
discarded, so a body with a valid goal but a false proof step fails verification.
The failure is reported against the inner assert, not the enclosing quantifier. -/
#eval testLaurel <|
#strata
program Laurel;

procedure proofStepNowChecked()
  opaque
{
  assert forall(x: int) => { assert x > 10; x * x >= 0 }
//                           ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### Proof blocks apply to `exists` too

Because the proof block assumes nothing, it is mode-agnostic: it only *adds* the
body's own obligations, checked under a havoc'd binder, and can never make an
unprovable goal verify. So `.Exists` needs no special-casing — the havoc branch
checks the body's steps (the wellformedness question, which is the same for both
modes), and the stripped `exists` remains the block's value for the solver to
discharge with a witness as usual. The tests below pin that: a true existential
verifies, a false one fails, a false proof step is reported, and the seal holds. -/

-- A true existential with a proof body: `exists x, x > 100` holds (e.g. 101),
-- so this verifies on the quantifier's own merits.
#eval testLaurel <|
#strata
program Laurel;

procedure existsProofProcedure()
  opaque
{
  assert exists(x: int) => { assume x == 999999; x > 100 }
};
#end

-- A false existential must fail even though the body's assume is satisfiable:
-- no x has x * x < 0.
#eval testLaurel <|
#strata
program Laurel;

procedure existsProofProcedureGoalNotAssumed()
  opaque
{
  assert exists(x: int) => { assume x > 10; x * x < 0 }
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A false proof step inside an `exists` body is reported, just as for `forall`.
#eval testLaurel <|
#strata
program Laurel;

procedure existsProofStepFails()
  opaque
{
  assert exists(x: int) => { assert 1 == 2; x == x }
//                           ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The seal applies to `exists` bodies as well.
#eval testLaurel <|
#strata
program Laurel;

procedure existsProofProcedureSealSoundness()
  opaque
{
  assert exists(x: int) => { assume x == 5; x == 5 };
  assert 1 == 2
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### Nested and sibling proof procedures

`rewriteQuantifierBodies` recurses, so a quantifier proof body may itself contain
one. Each proof block declares its own nondet guard, so the guards must have
distinct names — a shared `$proof` fails Core type checking with "Variable $proof
of type bool already in context". The havoc variable likewise gets a fresh
identifier, so a nested body's declaration does not collide with the outer one. -/

-- Nested proof procedures: both goals are valid, so this verifies.
#eval testLaurel <|
#strata
program Laurel;

procedure nestedProofProcedure()
  opaque
{
  assert forall(x: int) => {
    assume forall(y: int) => { assume x + y >= x; x + y >= x };
    x * x >= 0
  }
};
#end

-- A false proof step in the *inner* proof procedure must still be reported.
#eval testLaurel <|
#strata
program Laurel;

procedure nestedProofProcedureInnerStepFails()
  opaque
{
  assert forall(x: int) => {
    assert forall(y: int) => { assert y > 10; y == y };
//                             ^^^^^^^^^^^^^ error: assertion does not hold
    x * x >= 0
  }
};
#end

-- Two proof procedures side by side in one procedure.
#eval testLaurel <|
#strata
program Laurel;

procedure siblingProofProcedures()
  opaque
{
  assert forall(x: int) => { assume x >= 0; x * x >= 0 };
  assert forall(z: int) => { assume z >= 0; z * z >= 0 }
};
#end

/-! ### Directly-nested quantifiers

Where the tests above nest a quantifier inside a *block* (`{ inner; plainBool }`),
here the outer body **is** the inner quantifier. That distinction matters: the
proof-block decision is made on the body as written, before descending, so the
inner rewrite cannot influence it. Deciding after recursion would see the inner's
emitted `assume false` seal, wrap the inner's scaffolding, and leave an
uninitialized `var $proof_N` in the outer's goal — which the schema pass rejects
with "local variables must have initializers in transparent bodies or contracts",
aborting translation on well-formed source. All four mode pairings are covered
because the rewrite is mode-agnostic and each pairing reaches the same code path. -/

-- Both proof step and goal are valid for arbitrary bindings, so this verifies.
#eval testLaurel <|
#strata
program Laurel;

procedure directNestForallForall()
  opaque
{
  assert forall(x: int) => forall(y: int) => { assert x * x >= 0; y * y >= 0 }
};
#end

-- `exists`/`exists` with an `assume` proof step.
#eval testLaurel <|
#strata
program Laurel;

procedure directNestExistsExists()
  opaque
{
  assert exists(x: int) => exists(y: int) => { assume y > 0; y > -1 }
};
#end

-- Mixed pairings: `forall`/`exists` and `exists`/`forall`.
#eval testLaurel <|
#strata
program Laurel;

procedure directNestForallExists()
  opaque
{
  assert forall(x: int) => exists(y: int) => { assert x * x >= 0; y * y >= 0 }
};
#end

#eval testLaurel <|
#strata
program Laurel;

procedure directNestExistsForall()
  opaque
{
  assert exists(x: int) => forall(y: int) => { assume y * y >= 0; y * y >= 0 }
};
#end

-- A false proof step in a directly-nested body is still reported against the
-- step, so the top-down decision does not silence the inner obligation.
#eval testLaurel <|
#strata
program Laurel;

procedure directNestInnerStepFails()
  opaque
{
  assert forall(x: int) => forall(y: int) => { assert 1 == 2; y * y >= 0 }
//                                             ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### A binder whose name matches an in-scope local

The proof block's havoc variable is a fresh `$havoc_N`, not the binder's own name.
Reusing the name would declare it inside the branch while an enclosing local of the
same name is live, and that shadowing does not survive lowering: Core rejects the
re-declaration ("Variable x of type int already in context") and nothing renames
shadowed locals apart on the way there. Since the binder's name is the user's
choice, matching an outer local is ordinary source — it must keep working. -/
#eval testLaurel <|
#strata
program Laurel;

procedure binderShadowsLocal()
  opaque
{
  var x: int := 10;
  assert forall(x: int) => { assume x * x >= 0; x * x >= 0 };
  assert x == 10
};
#end

-- The rename is keyed on `uniqueId`, not text, so a nested quantifier rebinding
-- the same name keeps its own references: only the binder being havoc'd here is
-- redirected, not the inner one that shadows it.
#eval testLaurel <|
#strata
program Laurel;

procedure nestedBindersSameName()
  opaque
{
  assert forall(x: int) => {
    assume forall(x: int) => { assume x * x >= 0; x * x >= 0 };
    x * x >= 0
  }
};
#end

-- A false proof step is still reported when the binder shadows a local, so the
-- rename does not silence real obligations.
#eval testLaurel <|
#strata
program Laurel;

procedure binderShadowsLocalStepFails()
  opaque
{
  var x: int := 10;
  assert forall(x: int) => { assert x > 10; x * x >= 0 };
//                           ^^^^^^^^^^^^^ error: assertion does not hold
  assert x == 10
};
#end

/-! ### A proof body that does not mention the bound variable

The lifting pass hoists a `var` declaration out of a block when a lifted
statement reads it. The `$cndtn_N` temporary for an assert/assume condition is
prepended via `prependList`, which records its reads just as `prepend` does, so
the havoc `var x` moves up along with the statements referencing it instead of
being stranded below them (which would surface as `Resolution failed: 'x' is not
defined` after the pass). `G` is uninterpreted here, so the goal is genuinely
unprovable; the point is that this reports a normal verification failure rather
than an internal error. -/
#eval testLaurel <|
#strata
program Laurel;
procedure G(x: int): int;

procedure proofStepNotMentioningBoundVar()
  opaque
{
  assert forall(x: int) { G(x) } => { assert 1 == 1; G(x) >= 0 }
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

-- Proof procedure with trigger.
#eval testLaurel <|
#strata
program Laurel;
procedure F(x: int): int;

procedure proofProcedureWithTrigger()
  opaque
{
  assume forall(i: int) { F(i) } => F(i) == i * i;
  assert forall(x: int) { F(x) } => {
    assume F(x) == x * x;
    F(x) >= 0
  }
};
#end

-- Quantified postcondition: without a body, cannot be proved.
#eval testLaurel <|
#strata
program Laurel;
procedure F(x: int): int;

procedure quantifiedPostcondition()
  opaque
  ensures forall(x: int) => F(x) >= 0
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition does not hold
{
};
#end

/-! ### A local declaration in a quantifier body stays under the binder

The lifting pass hoists declarations out of expression position, but a quantifier
body is a spec position under a binder, so nothing may be hoisted out of it. A
`var` whose initializer mentions the bound variable is the case that makes this
observable: hoisting it above the quantifier would strand `x` outside its scope
and the program would fail to resolve. It stays inside, where `InlineLocalVariables`
folds it back into the goal.

The first procedure has no proof steps, so it exercises the plain quantifier path;
the second pairs the declaration with an `assert` step so it also runs through the
transparency pass's proof block, where the binder is renamed to `$havoc_N`. -/
#eval testLaurel <|
#strata
program Laurel;

procedure binderLocalNoProof()
  opaque
{
  assert forall(x: int) => { var t: int := x * x; t >= 0 }
};

procedure binderLocalInProofBody()
  opaque
{
  assert forall(x: int) => {
    var t: int := x * x;
    assert t >= 0;
    t >= 0
  }
};

procedure binderLocalInPostcondition()
  opaque
  ensures forall(x: int) => { var t: int := x * x; t >= 0 }
{
};
#end

-- `exists` is the same spec position as `forall`.
#eval testLaurel <|
#strata
program Laurel;

procedure existsBinderLocal()
  opaque
{
  assert exists(x: int) => { var t: int := x * x; t == 4 }
};
#end

-- Nested quantifiers, each with a binder-dependent local: the inner declaration
-- must stay under the inner binder and the outer under the outer.
#eval testLaurel <|
#strata
program Laurel;

procedure nestedBinderLocals()
  opaque
{
  assert forall(x: int) => {
    var t: int := x * x;
    forall(y: int) => { var u: int := y * y; t + u >= 0 }
  }
};
#end

-- An outer local sharing the binder's name must not be substituted inside the
-- quantifier: the binder shadows it, and the outer local still reads 5 after.
#eval testLaurel <|
#strata
program Laurel;

procedure binderShadowsOuterLocal()
  opaque
{
  var t: int := 5;
  assert forall(t: int) => { var u: int := t * t; u >= 0 };
  assert t == 5
};
#end

/-! ### A local declaration inside a quantifier *trigger*

A trigger is `{ <StmtExpr> }`, so it can hold a block with a declaration just as a
body can, and it is the same spec position: nothing is lifted out of it, and what
stays behind must be inlined before Core. Without the trigger arm of
`inlineLocalVariablesInProcedureSpecs` this program is rejected with "local
variables in transparent bodies should have been eliminated by the
InlineLocalVariablesPass". -/
#eval testLaurel <|
#strata
program Laurel;
procedure F(x: int): int;

procedure binderLocalInTrigger()
  opaque
{
  assume forall(i: int) { { var t: int := i; F(t) } } => F(i) >= 0;
  assert F(3) >= 0
};
#end

/-! ### Contract-pass temporaries inside a quantifier body

A `/` in a quantifier body becomes a call to the `requires`-bearing `$div`
wrapper, which the contract pass rewrites into argument temporaries. Those are
left inside the body by the lifting pass and folded back in by
`InlineLocalVariables`, so the division is re-evaluated per instantiation. -/
#eval testLaurel <|
#strata
program Laurel;

procedure divisionInQuantifierBody()
  opaque
{
  assert forall(x: int) => x > 0 ==> (x / x) == 1
};
#end
