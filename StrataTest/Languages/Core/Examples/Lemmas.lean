/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
namespace Strata

/-! # Lemmas and parameterized axioms

An axiom or a lemma may be written with a parameter list and optional
triggers, which stands for a `forall` over the parameters. A lemma is checked
under the axioms, like an assertion, and is not assumed afterwards. `f_big` does
not follow from `f_pos`; with a quantified axiom in scope the solver reports it
as unknown rather than failed.
-/

def lemmaPgm :=
#strata
program Core;

function f(x : int) : int;
axiom [f_pos] (x : int) { f(x) }: int.gt(f(x), 0);

lemma [f_nonneg] (x : int) { f(x) }: int.ge(f(x), 0);
lemma [f_two]: forall x : int, y : int :: int.gt(int.add(f(x), f(y)), 1);
lemma [f_big]: int.gt(f(0), 1);

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: f_nonneg
Property: assert
Assumptions:
f_pos: forall x : int ::  { f(x) }
  int.gt(f(x), 0)
Obligation:
int.ge(f(x@1), 0)

Label: f_two
Property: assert
Assumptions:
f_pos: forall x : int ::  { f(x) }
  int.gt(f(x), 0)
Obligation:
int.gt(int.add(f(x@2), f(y@1)), 1)

Label: f_big
Property: assert
Assumptions:
f_pos: forall x : int ::  { f(x) }
  int.gt(f(x), 0)
Obligation:
int.gt(f(0), 1)

---
info:
Obligation: f_nonneg
Property: assert
Result: ✅ pass

Obligation: f_two
Property: assert
Result: ✅ pass

Obligation: f_big
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify lemmaPgm

/-! A lemma is not assumed: `uses_f_big` fails just like the lemma `f_big`. -/

def lemmaNotAssumedPgm :=
#strata
program Core;

function f(x : int) : int;
lemma [f_big] (x : int): int.gt(f(x), 1);

procedure P()
{
  assert [uses_f_big]: int.gt(f(0), 1);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: f_big
Property: assert
Obligation:
int.gt(f(x@1), 1)

Label: uses_f_big
Property: assert
Obligation:
int.gt(f(0), 1)

---
info:
Obligation: f_big
Property: assert
Result: ❌ fail
Model:
(x@1, 0)

Obligation: uses_f_big
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify lemmaNotAssumedPgm

/-! A lemma may take type parameters. It must hold at every type, so it is
checked with each type parameter replaced by a fresh opaque type. -/

def polyLemmaPgm :=
#strata
program Core;

lemma [select_update] <k, v> (m : Map k v, x : k, y : v): m[x := y][x] == y;

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: select_update
Property: assert
Obligation:
(m@1[x@1:=y@1])[x@1] == y@1

---
info:
Obligation: select_update
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polyLemmaPgm

/-! A lemma with type parameters must hold at every type, so its formula cannot
fix a type parameter to a concrete type: `x == 0` would need `a` to be `int`. -/

def badPolyLemmaPgm :=
#strata
program Core;

lemma [bad] <a> (x : a): x == 0;

#end

/--
error: ❌ Type checking error.
Impossible to unify $__opaque_bad_a_0 with int.
-/
#guard_msgs in
#eval Core.verify badPolyLemmaPgm

/-! Type checking alone rejects it too, rather than fixing `a` to `int`. -/

/-- info: Impossible to unify $__rigid_bad_a with int. -/
#guard_msgs in
#eval match Core.typeCheck .quiet (TransM.run Inhabited.default (translateProgram badPolyLemmaPgm)).fst with
  | .ok _ => IO.println "accepted"
  | .error e => IO.println e.message

/-! A lemma's partial calls get well-formedness lemmas, as an assertion's do:
dividing by zero fails although the lemma itself holds. -/

def lemmaWFPgm :=
#strata
program Core;

lemma [ldiv] (x : int): int.safeDiv(x, 0) == int.safeDiv(x, 0);

#end

/--
info:
Obligation: ldiv_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail

Obligation: ldiv_calls_Int.SafeDiv_1
Property: division by zero check
Result: ❌ fail

Obligation: ldiv
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify lemmaWFPgm (options := .quiet)

/-! Generated lemmas are named away from the program's declarations: an axiom
named like a termination lemma keeps its name, and only that lemma takes a
suffix. -/

def generatedNameClashPgm :=
#strata
program Core;

axiom [f_terminates_0]: true;
rec function f (n : int) : int
  decreases n
{ if int.le(n, 0) then 0 else f(int.sub(n, 1)) };

#end

/--
info:
Obligation: f_terminates_0_1
Property: assert
Result: ✅ pass

Obligation: f_terminates_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify generatedNameClashPgm (options := .quiet)

/-! The same holds for well-formedness lemmas. -/

def wfNameClashPgm :=
#strata
program Core;

function g(x : int) : int
  requires int.gt(x, 0);
{ x }
function h(x : int) : int { g(x) }
axiom [h_body_calls_g_0]: true;

#end

/--
info:
Obligation: h_body_calls_g_0_1
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify wfNameClashPgm (options := .quiet)

/-! A contract's well-formedness lemma reads each precondition in the entry state:
there an in-out parameter stands for its `old` value, so `g_nonzero` guards the
division by `old g` in the postcondition. The postcondition itself fails, since
the empty body does not establish it. -/

def wfOldPgm :=
#strata
program Core;

procedure Q(inout g : int, y : int)
spec {
  requires [g_nonzero]: !(g == 0);
  ensures [uses_old]: int.ge(int.safeDiv(y, old g), 0);
}
{ };

#end

/--
info:
Obligation: Q_post_uses_old_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: uses_old
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify wfOldPgm (options := .quiet)

/-! Each well-formedness check gets its own lemma, named after it, so a failing
division is reported alone, with a counterexample for the function's inputs. -/

def twoDivPgm :=
#strata
program Core;

function twoDiv(x : int, y : int, z : int) : int
  requires !(y == 0);
{ int.add(int.safeDiv(x, y), int.safeDiv(x, z)) }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: twoDiv_body_calls_Int.SafeDiv_0
Property: division by zero check
Obligation:
!(y@1 == 0) ==> !(y@1 == 0)

Label: twoDiv_body_calls_Int.SafeDiv_1
Property: division by zero check
Obligation:
!(y@2 == 0) ==> !(z@2 == 0)

---
info:
Obligation: twoDiv_body_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: twoDiv_body_calls_Int.SafeDiv_1
Property: division by zero check
Result: ❌ fail
Model:
(y@2, int.neg(1)) (z@2, 0)
-/
#guard_msgs in
#eval Core.verify twoDivPgm

/-! Checks from two preconditions share a label, since each condition numbers
its checks from 0. Each still gets a lemma of its own name. -/

def twoPrecondsPgm :=
#strata
program Core;

function f(x : int, y : int, z : int) : int
  requires int.gt(int.safeDiv(x, y), 0);
  requires int.gt(int.safeDiv(x, z), 0);
{ x }

#end

/--
info:
Obligation: f_precond_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail

Obligation: f_precond_calls_Int.SafeDiv_0_1
Property: division by zero check
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify twoPrecondsPgm (options := .quiet)

/-! A lemma's variables are opened under fresh names, so a parameter named like a
global constant does not inherit the constant's axioms. -/

def shadowConstPgm :=
#strata
program Core;

const n : int;
axiom [n_one]: n == 1;
function f(n : int) : int { int.safeDiv(1, n) }

const x : int;
axiom [x_one]: x == 1;
lemma [lx] (x : int): x == 1;

#end

/--
info:
Obligation: f_body_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail

Obligation: lx
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify shadowConstPgm (options := .quiet)

/-! A lemma's hypotheses are partially evaluated, so an `inline` higher-order
function in an earlier precondition is expanded before SMT encoding. -/

def inlineHypPgm :=
#strata
program Core;

inline function apply(f : int -> int, x : int) : int { f(x) }
function g(x : int, y : int) : int
  requires int.gt(apply(fun a : int => int.add(a, 1), y), 1);
  requires int.gt(int.safeDiv(x, y), 0);
{ x }

#end

/--
info:
Obligation: g_precond_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify inlineHypPgm (options := .quiet)

end Strata
