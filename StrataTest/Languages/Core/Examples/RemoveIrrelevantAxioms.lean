/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def irrelevantAxiomsTestPgm : Strata.Program :=
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
axiom [ax_l11c1]: (forall x: int :: ((x >= 0) ==> f(x)));

// Uninterpreted procedures
// Implementations
procedure P()

{
  anon0: {
    assert [a0]: ((a ==> ((b ==> c) ==> d)) <==> (a ==> ((b ==> c) ==> d)));
    assert [a1]: ((a ==> (b ==> c)) <==> ((a ==> b) ==> c));
    assert [a2]: f(23);
    assert [a3]: f(-(5));
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
      String.intercalate " " entries
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
(x@4, model_not_2) (x@3, model_not_2) (x@2, model_not_2) (x@1, model_not_2)

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
(x@4, model_not_2) (x@3, model_not_2) (x@2, model_not_2) (x@1, model_not_2)

Obligation: a5
Property: assert
Result: ❌ fail
Model:
(x@4, model_not_2) (x@3, model_not_2) (x@2, model_not_2) (x@1, model_not_2)

Obligation: a6
Property: assert
Result: ❌ fail
Model:
(x@4, model_not_2) (x@3, model_not_2) (x@2, model_not_2) (x@1, model_not_2)

Obligation: a7
Property: assert
Result: ❌ fail
Model:
(x@4, model_not_2) (x@3, model_not_2) (x@2, model_not_2) (x@1, model_not_2)

Obligation: a8
Property: assert
Result: ❌ fail
Model:
(x@4, model_not_2) (x@3, model_not_2) (x@2, model_not_2) (x@1, model_not_2)

Obligation: a9
Property: assert
Result: ❌ fail
Model:
(x@4, model_not_2) (x@3, model_not_2) (x@2, model_not_2) (x@1, model_not_2)

Obligation: a10
Property: assert
Result: ❌ fail
Model:
(x@4, model_not_2) (x@3, model_not_2) (x@2, model_not_2) (x@1, model_not_2)

Obligation: a1
Property: assert
Result: ❌ fail
Model:
(x@4, model_not_2) (x@3, model_not_2) (x@2, model_not_2) (x@1, model_not_2)
-/
#guard_msgs in
#eval do
  let results ← verify irrelevantAxiomsTestPgm
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
#eval verify irrelevantAxiomsTestPgm
        (options := {Core.VerifyOptions.models with removeIrrelevantAxioms := .Off})

---------------------------------------------------------------------
