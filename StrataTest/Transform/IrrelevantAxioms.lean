/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Transform.IrrelevantAxioms
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # Goal-directed axiom relevance

A goal about `k1` keeps `n1_def`, `n_alias` and `n2_def` through `k1`'s
body, and never keeps `k2_def`. `Uses`, `Tagged` and `ref_of` are
uninterpreted, so their facts are kept only for goals that reach them. Each
`_m` axiom has the shape of the one before it with the sides swapped, and is
kept or dropped with it. `ref_1_m` is also a definition of `ref_k1b`, so a
goal about `ref_k1b` alone keeps it, and through it `ref_1`. -/

namespace Core.IrrelevantAxioms.Tests

def directedAxiomsPgm : StrataDDM.Program :=
#strata
program Core;
datatype Key { MkKey(size : int) };
function Uses(k : Key, n : int) : bool;
function Tagged(k : Key) : bool;
function imported(s : string) : int;
function pick(k : Key) : string;
function ref_of(k : Key) : string;
function n1() : int;
function n2() : int;
function k1() : Key { MkKey(n1) }
function k2() : Key;
function k1_size() : int;
function ref_k1() : string;
function ref_k1b() : string;
function names() : Sequence string;
function rotation_ok(k : Key) : bool { int.gt(Key..size(k), 0) }
function owns(k : Key) : bool { Uses(k, 0) }
axiom [n1_def]: n1 == 5;
axiom [n_alias]: n1 == n2;
axiom [n2_def]: n2 == imported("x");
axiom [k2_def]: k2 == MkKey(7);
axiom [k1_size_def]: Key..size(k1) == k1_size;
axiom [sel_0]: Sequence.select!(names, 0) == pick(k1);
axiom [sel_1_m]: pick(k1) == Sequence.select!(names, 1);
axiom [names_0]: Sequence.select!(names, 2) == "v";
axiom [names_m]: "v" == Sequence.select!(names, 3);
axiom [k1_uses]: Uses(k1, 0) == true;
axiom [k1_uses_m]: true == Uses(k1, 1);
axiom [k1_tag]: Tagged(k1) == true;
axiom [k1_tag_m]: true == Tagged(k1);
axiom [ref_1]: ref_of(k1) == ref_k1;
axiom [ref_1_m]: ref_k1b == ref_of(k1);
axiom [spec_nonneg]: (forall k : Key :: int.ge(Key..size(k), 0));
procedure P()
{
  assert [rotation]: rotation_ok(k1);
  assert [ownership]: owns(k1);
  assert [alias]: n2 == 5;
  assert [size]: Key..size(k1) == k1_size;
  assert [names]: Sequence.select!(names, 0) == Sequence.select!(names, 1);
  assert [ref]: ref_of(k1) == ref_k1b;
};
#end

/-- The axioms of `pgm` that goal-directed relevance drops for a goal with
    functions `seeds`, one per line. -/
def directedIrrelevant (seeds : List String)
    (pgm : StrataDDM.Program := directedAxiomsPgm) : IO Unit :=
  let (program, _) := Strata.Core.getProgram pgm
  let names := (DirectedIndex.build program).irrelevantAxioms seeds
  IO.println (String.intercalate "\n" names.toList)

/--
info: k2_def
sel_0
sel_1_m
names_0
names_m
k1_uses
k1_uses_m
k1_tag
k1_tag_m
ref_1
ref_1_m
-/
#guard_msgs in
#eval directedIrrelevant ["rotation_ok", "k1"]

/--
info: k2_def
sel_0
sel_1_m
names_0
names_m
k1_tag
k1_tag_m
ref_1
ref_1_m
-/
#guard_msgs in
#eval directedIrrelevant ["owns", "k1"]

/--
info: k2_def
k1_size_def
sel_0
sel_1_m
names_0
names_m
k1_uses
k1_uses_m
k1_tag
k1_tag_m
ref_1
ref_1_m
-/
#guard_msgs in
#eval directedIrrelevant ["n2"]

/--
info: k2_def
sel_0
sel_1_m
names_0
names_m
k1_uses
k1_uses_m
k1_tag
k1_tag_m
ref_1
ref_1_m
-/
#guard_msgs in
#eval directedIrrelevant ["k1", "k1_size"]

/--
info: k2_def
k1_uses
k1_uses_m
k1_tag
k1_tag_m
ref_1
ref_1_m
-/
#guard_msgs in
#eval directedIrrelevant ["names"]

/--
info: k2_def
sel_0
sel_1_m
names_0
names_m
k1_uses
k1_uses_m
k1_tag
k1_tag_m
-/
#guard_msgs in
#eval directedIrrelevant ["ref_of", "k1", "ref_k1b"]

/--
info: k2_def
sel_0
sel_1_m
names_0
names_m
k1_uses
k1_uses_m
k1_tag
k1_tag_m
-/
#guard_msgs in
#eval directedIrrelevant ["ref_k1b"]

/--
info: k2_def
sel_0
sel_1_m
names_0
names_m
k1_uses
k1_uses_m
k1_tag
k1_tag_m
-/
#guard_msgs in
#eval directedIrrelevant ["ref_of", "k1"]

-- `c` is reached only via `c_def`; its body calls `f`, whose body has `e`.
def calledBodyPgm : StrataDDM.Program :=
#strata
program Core;
function g() : int;
function h() : int;
function d() : int;
function e() : int;
function f(x : int) : int { int.add(x, e) }
function c() : int { f(d) }
axiom [c_def]: g == c;
axiom [e_def]: e == 1;
axiom [d_def]: d == 2;
axiom [h_def]: h == 3;
#end

/--
info: h_def
-/
#guard_msgs in
#eval directedIrrelevant ["g"] calledBodyPgm

-- `Uses` is only in the body of `c`, which is reached only via `g_def`.
def bodyUsesPgm : StrataDDM.Program :=
#strata
program Core;
function Uses(x : int, n : int) : bool;
function g() : bool;
function h() : int;
function k() : int;
function c() : bool { Uses(k, 0) }
axiom [g_def]: g == c;
axiom [k_uses]: Uses(k, 0) == true;
axiom [h_uses]: Uses(h, 0) == true;
#end

/--
info: h_uses
-/
#guard_msgs in
#eval directedIrrelevant ["g"] bodyUsesPgm

-- `Uses` and `Tagged` are reached only after `k`, through `k_c` and `c`.
def waitingPgm : StrataDDM.Program :=
#strata
program Core;
function Uses(x : int, n : int) : bool;
function Tagged(x : int) : bool;
function g() : int;
function h() : int;
function k() : int;
function c() : bool { Uses(k, 0) }
axiom [g_k]: g == k;
axiom [k_uses]: Uses(k, 0) == true;
axiom [k_two]: Uses(k, 1) == Tagged(k);
axiom [k_c]: k == (if c then 1 else 0);
axiom [h_uses]: Uses(h, 0) == true;
axiom [h_two]: Uses(h, 1) == Tagged(h);
#end

/--
info: h_uses
h_two
-/
#guard_msgs in
#eval directedIrrelevant ["g"] waitingPgm

-- A goal about `x` keeps `x_def`, which reaches `f` and so keeps `f_y`; a
-- goal about `w` keeps `w_def`, which reaches `d`, whose body has `z`, so it
-- keeps `z_def`.
def keptAxiomFnsPgm : StrataDDM.Program :=
#strata
program Core;
function f(k : int) : int;
function x() : int;
function y() : int;
function w() : int;
function z() : int;
function d(k : int) : int { int.add(k, z) }
axiom [x_def]: x == f(y);
axiom [f_y]: f(y) == 3;
axiom [w_def]: w == d(y);
axiom [y_def]: y == 2;
axiom [z_def]: z == 1;
procedure P()
{
  assert [x_val]: x == 3;
  assert [w_val]: w == 3;
};
#end

/--
info: w_def
z_def
-/
#guard_msgs in
#eval directedIrrelevant ["x"] keptAxiomFnsPgm

/--
info: x_def
f_y
-/
#guard_msgs in
#eval directedIrrelevant ["w"] keptAxiomFnsPgm

/--
info:
Obligation: x_val
Property: assert
Result: ✅ pass

Obligation: w_val
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify keptAxiomFnsPgm
  (options := { Core.VerifyOptions.default with
    verbose := .quiet, removeIrrelevantAxioms := .Directed })

-- `link` has no constants, so it is always kept, and it reaches `g`; `d` is
-- reached the same way, and its body has `z`.
def alwaysKeptPgm : StrataDDM.Program :=
#strata
program Core;
function g(k : int) : int;
function h(k : int) : int;
function c() : int;
function z() : int;
function u() : int;
function d(k : int) : int { int.add(k, z) }
axiom [link]: (forall k : int :: h(k) == g(k));
axiom [link_d]: (forall k : int :: int.ge(d(k), k));
axiom [g_c]: g(c) == 5;
axiom [z_def]: z == 1;
axiom [u_def]: u == 2;
#end

/--
info: u_def
-/
#guard_msgs in
#eval directedIrrelevant ["h", "c"] alwaysKeptPgm

-- `a_def` defines `a`, and `c_def` defines `d + 1`, not `c`.
def leftSidePgm : StrataDDM.Program :=
#strata
program Core;
function a() : int;
function b() : int;
function c() : int;
function d() : int;
axiom [a_def]: a == int.add(b, 1);
axiom [c_def]: int.add(d, 1) == c;
#end

/--
info: c_def
-/
#guard_msgs in
#eval directedIrrelevant ["a", "c"] leftSidePgm

/--
info: a_def
-/
#guard_msgs in
#eval directedIrrelevant ["b", "d"] leftSidePgm

-- `fa` is a fact about `f` that is also followed from `b`; `g_ge` is
-- quantified, so reaching `g` keeps it.
def ufFactsPgm : StrataDDM.Program :=
#strata
program Core;
function f(x : int) : int;
function g(x : int) : int;
function a() : int;
function b() : int;
function c() : int;
function u() : int;
axiom [fa]: f(a) == int.add(b, 1);
axiom [b3]: b == 3;
axiom [g_ge]: (forall x : int :: int.ge(g(x), c));
axiom [c_def]: c == 1;
axiom [u_def]: u == 2;
procedure P()
{
  assert [fa_val]: f(a) == 4;
  assert [g_val]: int.ge(g(3), 1);
};
#end

/--
info: g_ge
c_def
u_def
-/
#guard_msgs in
#eval directedIrrelevant ["f", "a"] ufFactsPgm

/--
info: fa
b3
u_def
-/
#guard_msgs in
#eval directedIrrelevant ["g"] ufFactsPgm

/--
info: g_ge
c_def
u_def
-/
#guard_msgs in
#eval directedIrrelevant ["b"] ufFactsPgm

/--
info:
Obligation: fa_val
Property: assert
Result: ✅ pass

Obligation: g_val
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify ufFactsPgm
  (options := { Core.VerifyOptions.default with
    verbose := .quiet, removeIrrelevantAxioms := .Directed })

/-- Whether adding the functions `extra` to the goal's functions `seeds`
    drops no axiom of `pgm` that `seeds` alone keeps. -/
def dropsNoMore (seeds extra : List String)
    (pgm : StrataDDM.Program := directedAxiomsPgm) : Bool :=
  let (program, _) := Strata.Core.getProgram pgm
  let idx := DirectedIndex.build program
  let fewer := idx.irrelevantAxioms seeds
  (idx.irrelevantAxioms (seeds ++ extra)).all fewer.contains

#guard dropsNoMore ["k1"] ["names"]
#guard dropsNoMore ["n2"] ["ref_of", "k1"]
#guard dropsNoMore ["names"] ["owns", "k1_size"]
#guard dropsNoMore ["a"] ["f"] ufFactsPgm
#guard dropsNoMore ["c"] ["g"] ufFactsPgm

-- Every goal passes with `Directed` pruning.
/--
info:
Obligation: rotation
Property: assert
Result: ✅ pass

Obligation: ownership
Property: assert
Result: ✅ pass

Obligation: alias
Property: assert
Result: ✅ pass

Obligation: size
Property: assert
Result: ✅ pass

Obligation: names
Property: assert
Result: ✅ pass

Obligation: ref
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify directedAxiomsPgm
  (options := { Core.VerifyOptions.default with
    verbose := .quiet, removeIrrelevantAxioms := .Directed })

-- `c_one` reaches only `c`, which `c_def` does not define, so `Directed`
-- drops both axioms, and `c_one` needs them. With one assertion per program,
-- common-subexpression elimination hoists no shared term into a definition on
-- the path; such a definition would make its functions relevant to the goal.
def droppedNeededPgm : StrataDDM.Program :=
#strata
program Core;
function c() : int;
function d() : int;
axiom [c_def]: int.add(d, 1) == c;
axiom [d_def]: d == 0;
procedure P() { assert [c_one]: c == 1; };
#end

/--
info: c_def
d_def
-/
#guard_msgs in
#eval directedIrrelevant ["c"] droppedNeededPgm

/--
info:
Obligation: c_one
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify droppedNeededPgm
  (options := { Core.VerifyOptions.default with verbose := .quiet })

-- The counterexample may violate a dropped axiom, so `c_one` is unknown.
/--
info:
Obligation: c_one
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Core.verify droppedNeededPgm
  (options := { Core.VerifyOptions.default with
    verbose := .quiet, removeIrrelevantAxioms := .Directed })

-- The same holds when obligations are solved in parallel.
/--
info:
Obligation: c_one
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Core.verify droppedNeededPgm
  (options := { Core.VerifyOptions.default with
    verbose := .quiet, removeIrrelevantAxioms := .Directed,
    parallelWorkers := 2 })

-- Bug-finding mode asks whether `c_one` can hold. That `sat` may also
-- violate a dropped axiom, so it reports as unknown too.
/--
info:
Obligation: c_one
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Core.verify droppedNeededPgm
  (options := { Core.VerifyOptions.default with
    verbose := .quiet, removeIrrelevantAxioms := .Directed,
    checkMode := .bugFinding })

-- `c_x` also reaches only `c`, and its counterexample is shown with the
-- unknown result.
def droppedNeededModelPgm : StrataDDM.Program :=
#strata
program Core;
function c() : int;
function d() : int;
axiom [c_def]: int.add(d, 1) == c;
axiom [d_def]: d == 0;
procedure P(x : int) { assume x == 1; assert [c_x]: c == x; };
#end

/--
info:
Obligation: c_x
Property: assert
Result: ❓ unknown
Model:
(x@1, 1)
-/
#guard_msgs in
#eval Strata.Core.verify droppedNeededModelPgm
  (options := { Core.VerifyOptions.models with
    removeIrrelevantAxioms := .Directed })

-- The incremental back end reports the same.
/--
info:
Obligation: c_one
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Core.verify droppedNeededPgm
  (options := { Core.VerifyOptions.default with
    verbose := .quiet, removeIrrelevantAxioms := .Directed,
    incremental := true })

-- `d_one` keeps both axioms and is false, so it fails.
def keptAllPgm : StrataDDM.Program :=
#strata
program Core;
function c() : int;
function d() : int;
axiom [c_def]: int.add(d, 1) == c;
axiom [d_def]: d == 0;
procedure P() { assert [d_one]: d == 1; };
#end

/-- info: -/
#guard_msgs in
#eval directedIrrelevant ["d"] keptAllPgm

/--
info:
Obligation: d_one
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Core.verify keptAllPgm
  (options := { Core.VerifyOptions.default with
    verbose := .quiet, removeIrrelevantAxioms := .Directed })

end Core.IrrelevantAxioms.Tests
end
