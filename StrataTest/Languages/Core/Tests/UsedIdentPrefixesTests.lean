/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Transform.CoreTypeCheck
import StrataDDM.Integration.Lean.HashCommands
import StrataTest.Languages.Core.Tests.TestUtil

/-! # The `$__` prefixes a program uses

The type-checking phase records the prefixes of the program's names in the `$__` namespace
(`Program.usedIdentPrefixes`), so that every such name starts with a recorded prefix. A program
that records nothing has its prefixes collected on demand (`Program.knownIdentPrefixes`). A pass
that generates `$__` names adds their prefixes to the record; one that already avoids the
program's names claims its prefixes, and warns and avoids them only when the program may use
them. -/

namespace Strata.UsedIdentPrefixesTests

/-- Variables in the `$__` namespace: one followed by letters, one by a digit and one by an
    underscore. -/
def internalPgm :=
#strata
program Core;
procedure P (x : int)
{
  var $__ndelim_ite$_0 : int := x;
  var $__0 : int := x;
  var $___x : int := x;
  assert [a]: int.ge($__ndelim_ite$_0, int.add($__0, $___x));
};
#end

/-- The same program without them. -/
def plainPgm :=
#strata
program Core;
procedure P (x : int)
{
  assert [a]: int.ge(x, x);
};
#end

/-- The recorded prefixes after the type-checking phase (sorted), whether they cover the
    program's internal names, and whether each prefix of `pfxs` is free. -/
def run (p : Core.Program) (pfxs : List String) : IO Unit := do
  match ← (Core.runTransforms p [Core.typeCheckPipelinePhase .quiet]).toBaseIO with
  | .error e => IO.println e.message
  | .ok (p', _) =>
    IO.println s!"recorded: {p'.usedIdentPrefixes.map (·.mergeSort)}"
    IO.println s!"covered: {p'.identPrefixesCovered}"
    for pfx in pfxs do
      IO.println s!"free {pfx}: {p'.identPrefixesFree [pfx]}"

-- A digit or an underscore after `$__` is kept, so neither name records the bare `$__`, which
-- would overlap every prefix: `$__cse.` stays free.
/--
info: recorded: (some [$__0, $___, $__ndelim])
covered: true
free $__ndelim_ite$: false
free $__cse.: true
-/
#guard_msgs in
#eval run (Core.getProgram internalPgm).fst ["$__ndelim_ite$", "$__cse."]

-- A program without internal names records none, and every prefix is free.
/--
info: recorded: (some [])
covered: true
free $__ndelim_ite$: true
-/
#guard_msgs in
#eval run (Core.getProgram plainPgm).fst ["$__ndelim_ite$"]

-- A program that was not type checked records `none`; its prefixes are collected on demand, so
-- it is not taken as free of `$__ndelim`.
/--
info: recorded: none
known: [$__0, $___, $__ndelim]
free: false
-/
#guard_msgs in
#eval do
  let p := (Core.getProgram internalPgm).fst
  IO.println s!"recorded: {p.usedIdentPrefixes}"
  IO.println s!"known: {p.knownIdentPrefixes.mergeSort}"
  IO.println s!"free: {p.identPrefixesFree ["$__ndelim_ite$"]}"

/-- A nondeterministic `if` and a call to a procedure with a postcondition. -/
def passesPgm :=
#strata
program Core;
procedure g (x : int, out y : int) spec { ensures [g_post]: (y == x); } { y := x; };
procedure P (x : int)
{
  var r : int;
  call g(x, out r);
  if * {
    assert [a]: (r == x);
  }
};
#end

/-- The same program declaring a type named like call elimination's opaque types. -/
def cetyPgm :=
#strata
program Core;
type $__cety0;
procedure g (x : int, out y : int) spec { ensures [g_post]: (y == x); } { y := x; };
procedure P (x : int)
{
  var r : int;
  call g(x, out r);
  if * {
    assert [a]: (r == x);
  }
};
#end

/-- The warnings, then the recorded prefixes (sorted) after type checking, call elimination and
    nondeterminism elimination, and whether they cover the output's internal names. -/
def runPasses (p : Core.Program) : IO Unit := do
  match ← (Core.runTransforms p [Core.typeCheckPipelinePhase .quiet, Core.callElimPipelinePhase,
      Core.NondetElim.nondetElimPipelinePhase]).toBaseIO with
  | .error e => IO.println e.message
  | .ok (p', st) =>
    for w in st.warnings do IO.println s!"[warning] {w.message}"
    IO.println s!"recorded: {p'.usedIdentPrefixes.map (·.mergeSort)}"
    IO.println s!"covered: {p'.identPrefixesCovered}"

-- Each pass adds the prefixes of the names it generates, so they cover the output's internal
-- names. Call elimination's prefixes are free, so it collects no names to avoid and does not
-- warn. It declares no opaque type, so it does not record its type prefix `$__cety`.
/--
info: recorded: (some [$__callElim, $__ndelim_ite$, $__ndelim_loop$])
covered: true
-/
#guard_msgs in
#eval runPasses (Core.getProgram passesPgm).fst

-- The program uses a name with call elimination's type prefix, so call elimination warns and
-- avoids the program's names, as it did before.
/--
info: [warning] callElim: the program uses names starting with '$__cety', which overlaps the prefixes '$__cety' this pass generates; it checks its generated names against the program's (slower).
recorded: (some [$__callElim, $__cety, $__ndelim_ite$, $__ndelim_loop$])
covered: true
-/
#guard_msgs in
#eval runPasses (Core.getProgram cetyPgm).fst

/-- A variable named like the temporary call elimination gives the call's argument. The assertion
    is false: the call does not change the variable. Type checking records `$__callElimTmp`, so
    call elimination warns and draws its temporaries apart from the program's variables. -/
def callTempPgm :=
#strata
program Core;
procedure g(x : int, out y : int) spec { ensures (y == int.add(x, 1)); } { y := int.add(x, 1); };
procedure C(n : int, out r : int) {
  var $__callElimTmp_arg_0 : int := 5;
  call g(7, out r);
  assert [same]: ($__callElimTmp_arg_0 == 7);
};
#end

-- The temporary does not overwrite the variable, so the assertion is not reported as passing: it
-- is `unknown`, as a failure through a call's contract is. (Quiet verification prints no
-- warnings; the `initsOfC` run on `callTempPgm` below shows the warning.)
/--
info:
Obligation: g_ensures_0
Property: assert
Result: ✅ pass

Obligation: same
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Core.verify callTempPgm (options := .quiet)

/-- The warnings and the variables `C` initializes after the phases `phases`. -/
def initsOfC (phases : List Core.PipelinePhase) (p : Core.Program) : IO Unit := do
  match ← (Core.runTransforms p phases).toBaseIO with
  | .error e => IO.println e.message
  | .ok (p', st) =>
    for w in st.warnings do IO.println s!"[warning] {w.message}"
    let inits := p'.decls.flatMap fun d =>
      if d.name.name == "C" then d.statements.filterMap fun
        | .cmd (.cmd (.init x _ _ _)) => some x.name
        | _ => none
      else []
    IO.println s!"inits: {inits}"

-- Call elimination warns and draws its argument temporary apart from the program's variable.
/--
info: [warning] callElim: the program uses names starting with '$__callElimTmp', which overlaps the prefixes '$__callElim' this pass generates; it checks its generated names against the program's (slower).
inits: [$__callElimTmp_arg_0, $__callElimTmp_arg_1, $__callElimTmp_r_2]
-/
#guard_msgs in
#eval initsOfC [Core.typeCheckPipelinePhase .quiet, Core.callElimPipelinePhase]
  (Core.getProgram callTempPgm).fst

/-- A phase that does not maintain the record and lies in it: it returns `q` type checked, whose
    variable `$__callElimTmp_arg_0` is named like call elimination's first temporary, recording
    that `q` uses no `$__` prefix. -/
def staleRecordPhase (q : Core.Program) : Core.PipelinePhase where
  transform _ := do
    let (_, checked) ← (Core.typeCheckPipelinePhase .quiet).transform q
    return (true, { checked with usedIdentPrefixes := some [] })
  phase.name := "staleRecord"

-- The pipeline does not let the phase after one that does not maintain the record trust it
-- (`CoreTransformState.identPrefixesTrusted`), so call elimination collects the prefixes again,
-- finds `$__callElimTmp`, and still avoids the program's variable. If it trusted the record, call
-- elimination would name its argument temporary `$__callElimTmp_arg_0` too.
/--
info: [warning] callElim: the program uses names starting with '$__callElimTmp', which overlaps the prefixes '$__callElim' this pass generates; it checks its generated names against the program's (slower).
inits: [$__callElimTmp_arg_0, $__callElimTmp_arg_1, $__callElimTmp_r_2]
-/
#guard_msgs in
#eval initsOfC [staleRecordPhase (Core.getProgram callTempPgm).fst, Core.callElimPipelinePhase]
  (Core.getProgram callTempPgm).fst

-- The same stale record on the input program itself: `runTransforms` does not let the first
-- phase trust the input's record, so call elimination, run without type checking first, collects
-- the prefixes, finds `$__callElimTmp`, and avoids the program's variable.
/--
info: [warning] callElim: the program uses names starting with '$__callElimTmp', which overlaps the prefixes '$__callElim' this pass generates; it checks its generated names against the program's (slower).
inits: [$__callElimTmp_arg_0, $__callElimTmp_arg_1, $__callElimTmp_r_2]
-/
#guard_msgs in
#eval show IO Unit from do
  let q := (Core.getProgram callTempPgm).fst
  let (_, checked) ← IO.ofExcept ((Core.Transform.run q
    (Core.typeCheckPipelinePhase .quiet).transform).mapError (·.message))
  initsOfC [Core.callElimPipelinePhase] { checked with usedIdentPrefixes := some [] }

/-- `P` calls `h`, which calls `g`. -/
def inlineTwicePgm :=
#strata
program Core;
procedure g(x : int, out y : int) spec { ensures (y == x); } { y := x; };
procedure h(x : int, out y : int) { call g(x, out y); };
procedure P(x : int, out r : int) { call h(x, out r); assert [ok]: (r == x); };
#end

-- Inlining twice: the first run records the prefix of its variables, `$__inline`, but not that of
-- its opaque types, `$__inlty`, since it declares none; the two prefixes do not overlap. So the
-- second run finds its type prefix free and does not warn.
/--
info: recorded: (some [$__inline])
covered: true
-/
#guard_msgs in
#eval show IO Unit from do
  match ← (Core.runTransforms (Core.getProgram inlineTwicePgm).fst
      [Core.typeCheckPipelinePhase .quiet, Core.procedureInliningPipelinePhase {},
       Core.procedureInliningPipelinePhase {}]).toBaseIO with
  | .error e => IO.println e.message
  | .ok (p', _) =>
    IO.println s!"recorded: {p'.usedIdentPrefixes.map (·.mergeSort)}"
    IO.println s!"covered: {p'.identPrefixesCovered}"

/-- The warnings, then the recorded prefixes (sorted), after the phases `phases`. -/
def runPhases (phases : List Core.PipelinePhase) (p : Core.Program) : IO Unit := do
  match ← (Core.runTransforms p phases).toBaseIO with
  | .error e => IO.println e.message
  | .ok (p', st) =>
    for w in st.warnings do IO.println s!"[warning] {w.message}"
    IO.println s!"recorded: {p'.usedIdentPrefixes.map (·.mergeSort)}"

-- Opaque type generation twice on a program with no polymorphic procedure: neither run declares a
-- type, so neither records a prefix and the second run does not warn.
/--
info: recorded: (some [])
-/
#guard_msgs in
#eval runPhases [Core.typeCheckPipelinePhase .quiet, Core.genOpaqueTypeParamsPipelinePhase,
  Core.genOpaqueTypeParamsPipelinePhase] (Core.getProgram inlineTwicePgm).fst

/-- `r` doubled 40 times: symbolic evaluation's output shares the subterm `r` stands for at each
    step, so the assertion is a tree of about 2^41 nodes but only about 40 distinct ones. -/
def doublingPgm :=
#strata
program Core;
procedure D($__x : int, out r : int) {
  r := $__x;
  r := int.add(r, r); r := int.add(r, r); r := int.add(r, r); r := int.add(r, r);
  r := int.add(r, r); r := int.add(r, r); r := int.add(r, r); r := int.add(r, r);
  r := int.add(r, r); r := int.add(r, r); r := int.add(r, r); r := int.add(r, r);
  r := int.add(r, r); r := int.add(r, r); r := int.add(r, r); r := int.add(r, r);
  r := int.add(r, r); r := int.add(r, r); r := int.add(r, r); r := int.add(r, r);
  r := int.add(r, r); r := int.add(r, r); r := int.add(r, r); r := int.add(r, r);
  r := int.add(r, r); r := int.add(r, r); r := int.add(r, r); r := int.add(r, r);
  r := int.add(r, r); r := int.add(r, r); r := int.add(r, r); r := int.add(r, r);
  r := int.add(r, r); r := int.add(r, r); r := int.add(r, r); r := int.add(r, r);
  r := int.add(r, r); r := int.add(r, r); r := int.add(r, r); r := int.add(r, r);
  assert [big]: int.ge(r, $__x);
};
#end

-- Collecting the prefixes after symbolic evaluation gives up the tree walk after
-- `Program.InternalNames.treeWalkFuel` nodes and visits each distinct subterm once
-- (`Program.InternalNames.exprNamesPtrCache`); a walk over the whole tree would not finish.
/--
info: recorded: (some [$__x])
-/
#guard_msgs in
#eval runPhases [Core.typeCheckPipelinePhase .quiet, Core.symbolicEvalPipelinePhase .quiet]
  (Core.getProgram doublingPgm).fst

end Strata.UsedIdentPrefixesTests
