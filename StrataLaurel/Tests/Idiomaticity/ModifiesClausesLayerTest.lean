/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
`ModifiesClausesTransform` on the program and model the pipeline hands it: every case runs source
through `runPassesBefore`, then the pass once. The pass's input refers to `$heap`, which source
cannot declare, so the shared `runPassForIdiomaticity` driver, which runs one pass on `resolve`'s
output, cannot produce it.

1. *Group disposition.* An empty-target group is the opaque default "nothing
   changes" frame and must be KEPT; a wildcard-target group claims nothing and
   must be DROPPED; zero groups mean unframed, and a procedure that writes no heap
   has nothing to frame. A mutation that treats empty groups like wildcards would
   silently unframe every defaulted opaque procedure — the e2e suites only catch
   that incidentally. A lifted instance procedure is framed only if the pass gets
   the pipeline's model: the first resolve's model does not record its fresh id as
   a heap writer.

2. *The enumerated-frame split under a guard.* With the optimization on, a
   group whose targets are individual references, in a procedure that cannot
   allocate, lowers to the assume/assert pair (callers get the quantifier-free
   enumerated frame, the body checks the quantified one) — for unguarded AND
   guarded groups alike, both halves under the group's guard. Gating the split
   on unguarded groups would silently make every lowered throwing procedure's
   normal frame quantified for callers, a precision/perf regression invisible
   to soundness-only tests.

3. *The plain form's mode.* Checked with a body, assumed without one.

4. *The frame itself*, as the program either side of the pass.

5. *A concrete run gets none of these frames.* It executes callee bodies
   rather than assuming their frames, and checking a frame at the exit would
   halt it.

6. *A set-valued target*, which no source program produces, so its entry is
   built directly: the frame excludes the set's members through an existential.
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.ModifiesClauses
import StrataLaurel.Implementation.MapStmtExpr
import StrataLaurel.Implementation.Grammar.AbstractToConcreteTreeTranslator

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- The procedure `p`, which every fixture declares, named `C$p` once lifted out of `C`. -/
private def theP (program : Program) : IO Procedure := do
  let .Unordered prog := program
    | throw (IO.userError s!"expected an Unordered program, got {program.kind}")
  match prog.staticProcedures.filter (["p", "C$p"].contains ·.name.text) with
  | [proc] => pure proc
  | procs => throw (IO.userError s!"expected one 'p', got {procs.length}")

/-- `p` as `ModifiesClausesTransform` receives it and as it returns it. -/
private def aroundPass (opts : LaurelTranslateOptions) (program : StrataDDM.Program) :
    IO (Procedure × Procedure) := do
  let (input, model, diags) ←
    runPassesBefore modifiesClausesTransformPass opts (← translateLaurel program)
  let (output, passDiags, _) := modifiesClausesTransformPass.run opts input model
  let diags := diags ++ passDiags
  if diags.any (·.kind != .warning) then
    throw (IO.userError s!"Diagnostics: {diags.map (·.message)}")
  pure (← theP input, ← theP output)

private def modeName : ConditionMode → String
  | .Assert => "Assert"
  | .Assume => "Assume"
  | .Both   => "Both"

private def containsQuantifier (e : StmtExprMd) : Bool :=
  anyStmtExpr (fun n => match n.val with | .Quantifier .. => true | _ => false) e

private def isImpliesWrapped (e : StmtExprMd) : Bool :=
  match e.val with
  | .StaticCall n (_ :: _ :: _) _ => n.text == Operation.Implies.procName
  | _ => false

/-- One line per condition: mode, whether the group's guard survived as an
    implication wrapper, and whether the frame is the quantified form. -/
private def describe (cs : List Condition) : String :=
  if cs.isEmpty then "(no conditions)"
  else "\n".intercalate (cs.map fun c =>
    s!"{modeName c.mode}, guarded={isImpliesWrapped c.condition}, quantified={containsQuantifier c.condition}")

private def posts (proc : Procedure) : List Condition :=
  match proc.body with
  | .Opaque posts _ _ => posts
  | _                 => []

/-- The postconditions `ModifiesClausesTransform` appends to `p`, found by dropping those its input
    already has. This needs no knowledge of how a frame is worded, and leaves out the free
    postconditions heap parameterization adds. -/
private def framesAdded (opts : LaurelTranslateOptions) (program : StrataDDM.Program) :
    IO String := do
  let (before, after) ← aroundPass opts program
  pure (describe ((posts after).drop (posts before).length))

/-- How `p` reaches `ModifiesClausesTransform`: opaque with how many modifies groups, or not
    opaque. -/
private def groupsInto (program : StrataDDM.Program) : IO String := do
  match (← aroundPass {} program).1.body with
  | .Opaque _ _ groups => pure s!"opaque, {groups.length} groups"
  | _                  => pure "not opaque"

/-! ## Fixtures -/

/-- Opaque, writes the heap, no `modifies` clause: the defaulted group. -/
private def noModifies : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite C { var n: int }
procedure p(b: C) opaque { b#n := 5 };
#end

/-- `modifies *`, which claims nothing. -/
private def wildcard : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite C { var n: int }
procedure p(b: C) opaque modifies * { b#n := 5 };
#end

/-- A wildcard beside a named target: the wildcard still governs. -/
private def wildcardBesideNamed : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite C { var n: int }
procedure p(b: C) opaque modifies * modifies b { b#n := 5 };
#end

/-- One named individual reference: the shape the enumerated split applies to. -/
private def namedTarget : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite C { var n: int }
procedure p(b: C) opaque modifies b { b#n := 5 };
#end

/-- The named target in a procedure that allocates, which therefore gets no split. -/
private def allocating : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite C { var n: int }
procedure p(b: C) opaque modifies b { var u: C := new C; b#n := 5 };
#end

/-- A throwing procedure: `EliminateExceptions` guards its `modifies b` on the normal exit. -/
private def guardedTarget : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite C { var n: int }
procedure p(b: C) throws (e: int) opaque modifies b { b#n := 5 };
#end

/-- The named target with no body, so the frame is assumed rather than checked. -/
private def bodiless : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite C { var n: int }
procedure p(b: C) opaque modifies b;
#end

/-- A transparent procedure that writes a constrained global, which `ConstrainedTypeElim` makes
    opaque to carry the global's constraint, with no modifies group at all. -/
private def zeroGroups : StrataDDM.SourcedProgram :=
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
var count: nat := 0
composite C { var n: int }
procedure p(b: C) { count := 1; b#n := 5 };
#end

/-- Opaque with a body that writes no heap, so the pass has nothing to frame. -/
private def noHeap : StrataDDM.SourcedProgram :=
#strata
program Laurel;
procedure p(x: int) opaque { var y: int := x + 1 };
#end

/-- An instance procedure, which `LiftInstanceProcedures` lifts to `C$p`. -/
private def instanceProcedure : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite C {
  var n: int
  procedure p(self: C) opaque modifies self { self#n := 5 };
}
#end

private def enumerated : LaurelTranslateOptions := { enumeratedModifiesClauses := true }

private def executing : LaurelTranslateOptions := { analysisMode := .Execute }

/-! ## 1. Group disposition: the default kept, a wildcard dropped, no groups unframed -/

/--
info: defaulted group: Both, guarded=false, quantified=true
zero groups (opaque, 0 groups): (no conditions)
wildcard: (no conditions)
wildcard + named: (no conditions)
no heap: (no conditions)
lifted instance procedure: Both, guarded=false, quantified=true
-/
#guard_msgs in
#eval do
  IO.println s!"defaulted group: {← framesAdded {} noModifies}"
  IO.println s!"zero groups ({← groupsInto zeroGroups}): {← framesAdded {} zeroGroups}"
  IO.println s!"wildcard: {← framesAdded {} wildcard}"
  IO.println s!"wildcard + named: {← framesAdded {} wildcardBesideNamed}"
  IO.println s!"no heap: {← framesAdded {} noHeap}"
  IO.println s!"lifted instance procedure: {← framesAdded {} instanceProcedure}"

/-! ## 2. The enumerated split applies under a guard -/

/--
info: named, plain: Both, guarded=false, quantified=true
named, enumerated:
Assume, guarded=false, quantified=false
Assert, guarded=false, quantified=true
allocating, enumerated: Both, guarded=false, quantified=true
defaulted, enumerated: Both, guarded=false, quantified=true
guarded, plain: Both, guarded=true, quantified=true
guarded, enumerated:
Assume, guarded=true, quantified=false
Assert, guarded=true, quantified=true
-/
#guard_msgs in
#eval do
  IO.println s!"named, plain: {← framesAdded {} namedTarget}"
  IO.println s!"named, enumerated:\n{← framesAdded enumerated namedTarget}"
  IO.println s!"allocating, enumerated: {← framesAdded enumerated allocating}"
  IO.println s!"defaulted, enumerated: {← framesAdded enumerated noModifies}"
  IO.println s!"guarded, plain: {← framesAdded {} guardedTarget}"
  IO.println s!"guarded, enumerated:\n{← framesAdded enumerated guardedTarget}"

/-! ## 3. The plain form's mode: checked with a body, assumed without one -/

/--
info: with body: Both, guarded=false, quantified=true
bodiless: Assume, guarded=false, quantified=true
-/
#guard_msgs in
#eval do
  IO.println s!"with body: {← framesAdded {} namedTarget}"
  IO.println s!"bodiless: {← framesAdded {} bodiless}"

/-! ## 4. The frame itself

`namedTarget`'s `p` before and after the pass. The two differ in one line: `modifies b` becomes the
quantified frame. -/

/--
info: -- before ModifiesClauses:
procedure p(b: Composite)
  free requires Composite..ref!(b) < Heap..nextReference!($heap) summary "input is allocated on the heap"
  free requires C$constraint(b)
  opaque
  free ensures old(Heap..nextReference!($heap)) <= Heap..nextReference!($heap) summary "monotonic heap pointer"
  modifies b
  writes $heap
{
  var $writeValue0: int := 5;
  $heap := updateField($heap, Composite..ref!(b), C.n(), BoxInt($writeValue0))
};
-- after ModifiesClauses:
procedure p(b: Composite)
  free requires Composite..ref!(b) < Heap..nextReference!($heap) summary "input is allocated on the heap"
  free requires C$constraint(b)
  opaque
  free ensures old(Heap..nextReference!($heap)) <= Heap..nextReference!($heap) summary "monotonic heap pointer"
  ensures forall($modifies_obj: int) => forall($modifies_fld: Field){readField($heap, $modifies_obj, $modifies_fld)} => $modifies_obj < Heap..nextReference!(old($heap)) & $modifies_obj != Composite..ref!(b) ==> readField(old($heap), $modifies_obj, $modifies_fld) == readField($heap, $modifies_obj, $modifies_fld) summary "modifies clause"
  writes $heap
{
  var $writeValue0: int := 5;
  $heap := updateField($heap, Composite..ref!(b), C.n(), BoxInt($writeValue0))
};
-/
#guard_msgs in
#eval do
  let (before, after) ← aroundPass {} namedTarget
  IO.println s!"-- before ModifiesClauses:\n{Std.Format.pretty (Std.ToFormat.format before)}"
  IO.println s!"-- after ModifiesClauses:\n{Std.Format.pretty (Std.ToFormat.format after)}"

/-! ## 5. A concrete run gets none of these frames -/

/--
info: defaulted group: (no conditions)
named, enumerated: (no conditions)
guarded: (no conditions)
bodiless: (no conditions)
-/
#guard_msgs in
#eval do
  let executingEnumerated := { executing with enumeratedModifiesClauses := true }
  IO.println s!"defaulted group: {← framesAdded executing noModifies}"
  IO.println s!"named, enumerated: {← framesAdded executingEnumerated namedTarget}"
  IO.println s!"guarded: {← framesAdded executing guardedTarget}"
  IO.println s!"bodiless: {← framesAdded executing bodiless}"

/-! ## 6. A set-valued target -/

private def setNotModified : StmtExprMd :=
  buildNotModifiedForEntry ⟨.Var (.Local (mkId "$modifies_obj")), .unknown⟩
    ⟨.Var (.Local (mkId "$modifies_fld")), .unknown⟩
    (.set ⟨.Var (.Local (mkId "s")), .unknown⟩) .unknown

/--
info: !exists($modifies_member: Composite) => select(s, $modifies_member) & Composite..ref!($modifies_member) == $modifies_obj
-/
#guard_msgs in
#eval IO.println (formatStmtExpr setNotModified)

end Strata.Laurel
