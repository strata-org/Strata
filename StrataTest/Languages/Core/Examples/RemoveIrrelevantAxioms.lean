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

def irrelevantAxiomsTestPgm : StrataDDM.Program :=
#strata
program Core;
type StrataHeap;
type StrataRef;
type StrataField (t: Type);

// Constants
const a : bool;
const b : bool;
const c : bool;
const d : bool;

// Functions
function f(x0 : int) : (bool);

// Axioms
axiom [ax_l11c1]: (forall x : int :: (int.ge(x, 0) ==> f(x)));

// Uninterpreted procedures
// Implementations
procedure P()

{
  anon0: {
    assert [a0]: ((a ==> ((b ==> c) ==> d)) <==> (a ==> ((b ==> c) ==> d)));
    assert [a1]: ((a ==> (b ==> c)) <==> ((a ==> b) ==> c));
    assert [a2]: f(23);
    assert [a3]: f(int.neg(5));
  }
  _exit : {}
};

procedure Q0(x : int)

{
  anon0: {
    assert [a4]: (x == 2);
    assert [a5]: (x == 2);
  }
  _exit : {}
};

procedure Q1(x : int)

{
  anon0: {
    assert [a6]: (x == 2);
    assert [a7]: (x == 2);
  }
  _exit : {}
};

procedure Q2(x : int)

{
  anon0: {
    assert [a8]: (x == 2);
    assert [a9]: (x == 2);
  }
  _exit : {}
};

procedure Q3(x : int)

{
  anon0: {
    assert [a10]: (x == 2);
    assert [a1]: (x == 2);
  }
  _exit : {}
};
#end

---------------------------------------------------------------------

def normalizeModelValues (s : String) : String :=
  let lines := s.splitOn "\n"
  let normalized := lines.map fun line =>
    -- Handle multi-variable model lines: normalize each (x@N, val) entry
    if line.contains "(x" && line.contains ", " then
      let entries := line.splitOn "(x" |>.drop 1 |>.map fun entry =>
        match entry.splitOn ", " with
        | [varSuffix, rest] =>
          let val := (rest.splitOn ")").head!.trimAscii
          let val := if val.startsWith "#" then val.drop 1 else val
          match val.toInt? with
          | some v => if v == 2 then s!"(x{varSuffix}, VALUE_WAS_2)"
                      else s!"(x{varSuffix}, model_not_2)"
          | none => s!"(x{varSuffix}, {val})"
        | _ => s!"(x{entry}"
      String.intercalate " " (entries.mergeSort (· ≤ ·))
    else line
  String.intercalate "\n" normalized

/--
info:
Obligation: a0
Property: assert
Result: ✅ pass

Obligation: a1
Property: assert
Result: ❌ fail
Model:
(x@1, model_not_2) (x@2, model_not_2) (x@3, model_not_2) (x@4, model_not_2)

Obligation: a2
Property: assert
Result: ✅ pass

Obligation: a3
Property: assert
Result: ❓ unknown

Obligation: a4
Property: assert
Result: ❌ fail
Model:
(x@1, model_not_2) (x@2, model_not_2) (x@3, model_not_2) (x@4, model_not_2)

Obligation: a5
Property: assert
Result: ❌ fail
Model:
(x@1, model_not_2) (x@2, model_not_2) (x@3, model_not_2) (x@4, model_not_2)

Obligation: a6
Property: assert
Result: ❌ fail
Model:
(x@1, model_not_2) (x@2, model_not_2) (x@3, model_not_2) (x@4, model_not_2)

Obligation: a7
Property: assert
Result: ❌ fail
Model:
(x@1, model_not_2) (x@2, model_not_2) (x@3, model_not_2) (x@4, model_not_2)

Obligation: a8
Property: assert
Result: ❌ fail
Model:
(x@1, model_not_2) (x@2, model_not_2) (x@3, model_not_2) (x@4, model_not_2)

Obligation: a9
Property: assert
Result: ❌ fail
Model:
(x@1, model_not_2) (x@2, model_not_2) (x@3, model_not_2) (x@4, model_not_2)

Obligation: a10
Property: assert
Result: ❌ fail
Model:
(x@1, model_not_2) (x@2, model_not_2) (x@3, model_not_2) (x@4, model_not_2)

Obligation: a1
Property: assert
Result: ❌ fail
Model:
(x@1, model_not_2) (x@2, model_not_2) (x@3, model_not_2) (x@4, model_not_2)
-/
#guard_msgs in
#eval do
  let results ← Core.verify irrelevantAxiomsTestPgm
        (options := {Core.VerifyOptions.models with removeIrrelevantAxioms := .Precise})
  IO.println (normalizeModelValues (toString results))

---------------------------------------------------------------------

/--
info:
Obligation: a0
Property: assert
Result: ✅ pass

Obligation: a1
Property: assert
Result: ❓ unknown

Obligation: a2
Property: assert
Result: ✅ pass

Obligation: a3
Property: assert
Result: ❓ unknown

Obligation: a4
Property: assert
Result: ❓ unknown

Obligation: a5
Property: assert
Result: ❓ unknown

Obligation: a6
Property: assert
Result: ❓ unknown

Obligation: a7
Property: assert
Result: ❓ unknown

Obligation: a8
Property: assert
Result: ❓ unknown

Obligation: a9
Property: assert
Result: ❓ unknown

Obligation: a10
Property: assert
Result: ❓ unknown

Obligation: a1
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify irrelevantAxiomsTestPgm
        (options := {Core.VerifyOptions.models with removeIrrelevantAxioms := .Off})

---------------------------------------------------------------------
/-! ## Monomorphized-function axiom relevance

A polymorphic function `f<a>` with an axiom about it, used at a ground type, is
specialised to `$__mono#f#int` by `MonomorphizeFunctions`.  The obligation the
relevance analysis reads its seeds from is post-monomorphization (so it mentions
`$__mono#f#int`), but the axiom program / call-graph / cache relevance is
computed against is the pre-pipeline one (which names the base `f`).
`preprocessObligation` therefore demangles the seed names before the relevance
query, so both sides agree on `f` and the axiom survives under `.Precise`.

The `monoAxiomControlPgm` monomorphic control is identical in shape but never
mangled, so its axiom survives regardless. -/

def monoAxiomPolyPgm : StrataDDM.Program :=
#strata
program Core;
function f<a>(x : a) : int;
axiom [f_neg]: (forall x : int :: { f(x) } int.lt(f(x), 0));
procedure P(out r : int)
spec {
  ensures int.lt(f(5), 0);
}
{
};
#end

def monoAxiomControlPgm : StrataDDM.Program :=
#strata
program Core;
function g(x : int) : int; // This is not polymorphic in control
axiom [g_neg]: (forall x : int :: { g(x) } int.lt(g(x), 0));
procedure P(out r : int)
spec {
  ensures int.lt(g(5), 0);
}
{
};
#end

-- Baseline: with axiom pruning `.Off` the axiom is kept, so the specialized
-- `f<int>(5) < 0` obligation is discharged.
/--
info:
Obligation: P_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify monoAxiomPolyPgm
        (options := {Core.VerifyOptions.default with verbose := .quiet, removeIrrelevantAxioms := .Off})

-- Thanks to seed demangling in `preprocessObligation` this goal is discharged.
/--
info:
Obligation: P_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify monoAxiomPolyPgm
        (options := {Core.VerifyOptions.default with verbose := .quiet, removeIrrelevantAxioms := .Precise})

-- Monomorphic control: `g` is never mangled, so under `.Precise` its axiom is
-- kept and the same-shaped obligation is discharged.
/--
info:
Obligation: P_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify monoAxiomControlPgm
        (options := {Core.VerifyOptions.default with verbose := .quiet, removeIrrelevantAxioms := .Precise})

end Strata
end
---------------------------------------------------------------------
