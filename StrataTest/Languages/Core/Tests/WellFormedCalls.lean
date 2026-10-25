/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Transform.CoreTransform
meta import Strata.Transform.CallElim
meta import Strata.Transform.ProcedureInlining
meta import Strata.Transform.FilterProcedures
meta import Strata.Languages.Core.Verifier

/-! # Well-formed calls

A call is well-formed (`WF.WFcallProp`, decided by `callError?`) when it names a
declared procedure, its arguments match that procedure's signature
(`WF.ArgsMatchSignature`: as many input arguments as input formals, as many result
variables as output formals, and an argument of the formal's mode at each position),
and its result variables are distinct. `assertWellFormedCalls`, the first phase of every
registered pipeline, refuses any other call as a user error. Every component that
checks a call refuses it too, with the same explanation. -/

meta section

open Core
open Core.Transform
open Strata

namespace WellFormedCallsTest

private def translate (t : StrataDDM.SourcedProgram) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-- The error message together with the source text it points at. -/
private def located (p : StrataDDM.SourcedProgram) (e : Strata.Message) : String :=
  let r := e.fileRange.range
  let src := String.fromUTF8? (p.source.toUTF8.extract
    (r.start.byteIdx - p.basePos) (r.stop.byteIdx - p.basePos))
  s!"at `{src.getD "?"}`: {e.message}"

/-- `ok`, or the located call-elimination error. -/
private def callElimResult (p : StrataDDM.SourcedProgram) : String :=
  match run (translate p) CallElim.callElim' with
  | .ok _ => "ok"
  | .error e => located p e

/-- `ok`, or the located type-checking error. -/
private def typeCheckResult (p : StrataDDM.SourcedProgram) : String :=
  match Core.typeCheck { Core.VerifyOptions.default with verbose := .quiet } (translate p) with
  | .ok _ => "ok"
  | .error e => located p e

/-- The symbolic evaluator's error, or `ok`. -/
private def symEvalResult (p : StrataDDM.SourcedProgram) : String :=
  match Core.toCoreProofObligationProgram .default (translate p) with
  | .ok _ => "ok"
  | .error e => toString e.message

/-- The concrete interpreter's errors and assertion failures for `caller`. -/
private def interpretResult (p : StrataDDM.SourcedProgram) : String :=
  let prog := translate p
  match Program.Procedure.find? prog ⟨"caller", ()⟩ with
  | none => "no caller"
  | some caller =>
    match Core.Program.interpretEntries prog [caller] 1000 with
    | .error e => toString e.message
    | .ok o => s!"errors={o.errors.toList.map fun (n, e) => s!"{n}: {Std.format e}"} \
                  failures={o.diagnostics.size + o.unmapped.size}"

/-- The verifier's program transforms under `options`: `ok`, or the located error
    and its category. -/
private def pipelineResult (p : StrataDDM.SourcedProgram)
    (options : VerifyOptions := .default) : IO String := do
  match ← (runTransforms (translate p) (transformPipelinePhases options)).toBaseIO with
  | .ok _ => pure "ok"
  | .error e => pure s!"{located p e} ({e.kind})"

/-- The procedure `caller` after call elimination, or the error. -/
private def callElimCaller (p : StrataDDM.SourcedProgram) : String :=
  match run (translate p) CallElim.callElim' with
  | .ok (_, q) => "procedure caller" ++ ((Core.formatProgram q).pretty.splitOn "procedure caller").getLast!
  | .error e => toString e

/-! ## Results must be distinct variables -/

private def twoOuts :=
#strata
program Core;
procedure two(out x : int, out y : int)
spec {
  ensures (x == 1 && y == 2);
};
procedure caller() {
  var x : int;
  call two(out x, out x);
  assert [after_call]: false;
};
#end

/-- info: "at `call two(out x, out x);`: ❌ Ill-formed call: the call to two passes the variable x for more than one out parameter; the results of a call must be distinct variables (userError)" -/
#guard_msgs in
#eval pipelineResult twoOuts

/-- info: "at `call two(out x, out x);`: Call elimination requires every call to be well-formed: the call to two passes the variable x for more than one out parameter; the results of a call must be distinct variables" -/
#guard_msgs in
#eval callElimResult twoOuts

/-- info: "at `call two(out x, out x);`: [call two(out x, out x);]: Ill-formed call: the call to two passes the variable x for more than one out parameter; the results of a call must be distinct variables" -/
#guard_msgs in
#eval typeCheckResult twoOuts

/-- info: "procedure 'caller': [ERROR] Ill-formed call: the call to two passes the variable x for more than one out parameter; the results of a call must be distinct variables" -/
#guard_msgs in
#eval symEvalResult twoOuts

/-- info: "errors=[caller: [ERROR] Ill-formed call: the call to two passes the variable x for more than one out parameter; the results of a call must be distinct variables] failures=0" -/
#guard_msgs in
#eval interpretResult twoOuts

-- An `inout` argument counts as a result too.
private def inoutAndOut :=
#strata
program Core;
procedure p(inout g : int, out r : int)
spec {
  ensures (r == old g);
};
procedure caller() {
  var g : int;
  call p(inout g, out g);
};
#end

/-- info: "at `call p(inout g, out g);`: [call p(inout g, out g);]: Ill-formed call: the call to p passes the inout argument g for more than one inout or out parameter; an inout argument must not alias another result of the call" -/
#guard_msgs in
#eval typeCheckResult inoutAndOut

/-! ## Inout parameters take `inout` arguments -/

-- An input value for an inout parameter with a separate `out` result is refused.
private def splitInout :=
#strata
program Core;
procedure inc(inout y : int)
spec {
  ensures (y == int.add(old y, 1));
}
{
  y := int.add(y, 1);
};
procedure caller() {
  var a : int;
  a := 0;
  call inc(5, out a);
  assert [after_call]: (a == 1);
};
#end

/-- info: "at `call inc(5, out a);`: ❌ Ill-formed call: the call to inc passes an input value for y, which is an inout parameter and must be passed as inout (userError)" -/
#guard_msgs in
#eval pipelineResult splitInout

/-- info: "at `call inc(5, out a);`: Call elimination requires every call to be well-formed: the call to inc passes an input value for y, which is an inout parameter and must be passed as inout" -/
#guard_msgs in
#eval callElimResult splitInout

/-- info: "at `call inc(5, out a);`: [call inc(5, out a);]: Ill-formed call: the call to inc passes an input value for y, which is an inout parameter and must be passed as inout" -/
#guard_msgs in
#eval typeCheckResult splitInout

/-- info: "procedure 'caller': [ERROR] Ill-formed call: the call to inc passes an input value for y, which is an inout parameter and must be passed as inout" -/
#guard_msgs in
#eval symEvalResult splitInout

/-- info: "errors=[caller: [ERROR] Ill-formed call: the call to inc passes an input value for y, which is an inout parameter and must be passed as inout] failures=0" -/
#guard_msgs in
#eval interpretResult splitInout

-- Passed as `inout`, the call is accepted, and call elimination snapshots `old y`
-- from `a`.
private def inoutArg :=
#strata
program Core;
procedure inc(inout y : int)
spec {
  ensures (y == int.add(old y, 1));
}
{
  y := int.add(y, 1);
};
procedure caller() {
  var a : int;
  a := 0;
  call inc(inout a);
  assert [a_is_1]: (a == 1);
};
#end

/-- info: "ok" -/
#guard_msgs in
#eval pipelineResult inoutArg

/--
info: procedure caller ()
{
  var a : int;
  a := 0;
  var tmp_arg_0 : int := a;
  var tmp_a_1 : int := a;
  var old_a_2 : int := a;
  havoc a;
  assume [callElimAssume_inc_ensures_0_3]: a == int.add(old_a_2, 1);
  assert [a_is_1]: a == 1;
};
-/
#guard_msgs in
#eval IO.println (callElimCaller inoutArg)

/-- info: "ok" -/
#guard_msgs in
#eval typeCheckResult inoutArg

/-- info: "errors=[] failures=0" -/
#guard_msgs in
#eval interpretResult inoutArg

/-! ## The other conditions

Every component reports these through `callError?`, so the type checker stands for
all of them. -/

private def undeclared :=
#strata
program Core;
procedure caller() {
  var x : int;
  call missing(out x);
};
#end

/-- info: "at `call missing(out x);`: [call missing(out x);]: Ill-formed call: no procedure named missing is declared" -/
#guard_msgs in
#eval typeCheckResult undeclared

private def tooFewInputs :=
#strata
program Core;
procedure addTo(inout y : int, d : int)
spec {
  ensures (y == int.add(old y, d));
};
procedure caller() {
  var a : int;
  call addTo(inout a);
};
#end

/-- info: "at `call addTo(inout a);`: [call addTo(inout a);]: Ill-formed call: the call to addTo passes 1 input argument, but addTo has 2 input parameters (y, d)" -/
#guard_msgs in
#eval typeCheckResult tooFewInputs

-- Arguments match parameters by position, and the mode written on each argument
-- must agree with its parameter's. Here `5` lands on the inout parameter `y` and
-- `inout a` on the input parameter `d`, though every count matches.
private def modeMismatch :=
#strata
program Core;
procedure addTo(inout y : int, d : int)
spec {
  ensures (y == int.add(old y, d));
};
procedure caller() {
  var a : int;
  call addTo(5, inout a);
};
#end

/-- info: "at `call addTo(5, inout a);`: [call addTo(5, inout a);]: Ill-formed call: the call to addTo passes an input value for y, which is an inout parameter and must be passed as inout" -/
#guard_msgs in
#eval typeCheckResult modeMismatch

-- The inout and out arguments follow the order of the callee's outputs, so here
-- the result of `y` goes to `w` rather than to its `inout` argument `a`.
private def inoutOutOfOrder :=
#strata
program Core;
procedure split(inout y : int, out z : int)
spec {
  ensures (z == old y);
};
procedure caller() {
  var a : int;
  var w : int;
  call split(out w, inout a);
};
#end

/-- info: "at `call split(out w, inout a);`: [call split(out w, inout a);]: Ill-formed call: the call to split passes inout a for y, but the result of y goes to w; the inout and out arguments must follow the order of split's outputs" -/
#guard_msgs in
#eval typeCheckResult inoutOutOfOrder

private def tooFewResults :=
#strata
program Core;
procedure two(out x : int, out y : int)
spec {
  ensures (x == 1 && y == 2);
};
procedure caller() {
  var x : int;
  call two(out x);
};
#end

/-- info: "at `call two(out x);`: [call two(out x);]: Ill-formed call: the call to two passes 1 result variable, but two has 2 output parameters (x, y)" -/
#guard_msgs in
#eval typeCheckResult tooFewResults

-- The result arguments are checked against the output formals in order, before
-- the results' distinctness, so a variable passed twice can also land an `out`
-- argument on an inout formal or an `inout` argument on an output-only one.
private def outForInout :=
#strata
program Core;
procedure p(inout y : int, out z : int)
spec {
  ensures (z == old y);
};
procedure caller() {
  var a : int;
  call p(out a, inout a);
};
#end

/-- info: "at `call p(out a, inout a);`: [call p(out a, inout a);]: Ill-formed call: the call to p passes out a for y, which is an inout parameter and must be passed as inout" -/
#guard_msgs in
#eval typeCheckResult outForInout

private def inoutForOutputOnly :=
#strata
program Core;
procedure p(out z : int, inout y : int)
spec {
  ensures (z == old y);
};
procedure caller() {
  var a : int;
  call p(inout a, out a);
};
#end

/-- info: "at `call p(inout a, out a);`: [call p(inout a, out a);]: Ill-formed call: the call to p passes inout a for z, which is an output-only parameter and must be passed as out" -/
#guard_msgs in
#eval typeCheckResult inoutForOutputOnly

/-! ## The phase checks every procedure

`assertWellFormedCalls` runs before the procedure filter, so a procedure that
`--procedures` leaves out is checked too. -/

private def excludedIllFormed :=
#strata
program Core;
procedure two(out x : int, out y : int)
spec {
  ensures (x == 1 && y == 2);
};
procedure caller() {
  assert [fine]: true;
};
procedure other() {
  var x : int;
  call two(out x, out x);
};
#end

/-- info: "at `call two(out x, out x);`: ❌ Ill-formed call: the call to two passes the variable x for more than one out parameter; the results of a call must be distinct variables (userError)" -/
#guard_msgs in
#eval pipelineResult excludedIllFormed
  { VerifyOptions.default with proceduresToVerify := some ["caller"] }

/-! ## Phases that claim to preserve the fact keep it -/

private def wellFormed :=
#strata
program Core;
procedure inc(inout y : int)
spec {
  ensures (y == int.add(old y, 1));
}
{
  y := int.add(y, 1);
};
procedure twice(inout y : int)
spec {
  ensures (y == int.add(old y, 2));
}
{
  call inc(inout y);
  call inc(inout y);
};
procedure caller() {
  var a : int;
  a := 0;
  call twice(inout a);
};
#end

/-- Whether `phase` succeeds on `wellFormed` and its output has well-formed calls. -/
private def keepsWellFormedCalls (phase : PipelinePhase) : Bool :=
  match run (translate wellFormed) phase.transform with
  | .ok (_, q) => illFormedCalls q == []
  | .error _ => false

#guard illFormedCalls (translate wellFormed) == []
#guard keepsWellFormedCalls callElimPipelinePhase
#guard keepsWellFormedCalls procedureInliningPipelinePhase
#guard keepsWellFormedCalls (filterProceduresPipelinePhase ["caller"])

end WellFormedCallsTest

end
