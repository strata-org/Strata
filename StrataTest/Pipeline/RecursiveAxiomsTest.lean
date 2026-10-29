/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Transform.RecursiveFunctionAxioms
import StrataDDM.Integration.Lean.HashCommands

/-! # Recursive-function axioms without symbolic evaluation

A pipeline that runs `simplify` in place of symbolic evaluation must still give the
solver the per-constructor axioms of a recursive `@[cases]` function, which symbolic
evaluation would have generated. Without them, an assertion about the function on a
symbolic argument fails with a spurious counterexample. -/

meta section

namespace Strata.RecursiveAxiomsTest

private def recPgm :=
#strata
program Core;
datatype IntList () { Nil(), Cons(hd: int, tl: IntList) };
rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};
procedure L2 (xs : IntList)
{
  assume IntList..isCons(xs);
  assert [l2]: listLen(xs) == int.add(1, listLen(IntList..tl(xs)));
};
#end

/-- The pipeline a front end uses when every body is already in obligation form:
    `simplify` where the default order runs symbolic evaluation, optionally followed by
    `recursiveAxioms`. -/
private def withoutSymbolicEval (axioms : Bool)
    (axiomOptions : Core.VerifyOptions := Core.VerifyOptions.default) :
    Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) := do
  let ho ← Core.assertPhaseFor (Core.assertPhaseName .hasObligationForm)
  let pc ← Core.assertPhaseFor (Core.assertPhaseName .noProcedureContracts)
  let entry ← [.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment, .noNondetGuards].mapM
    (fun f => Core.assertPhaseFor (Core.assertPhaseName f))
  (Core.validatePipeline
    (entry ++ [Core.passTermCheck, Core.passPrecondElim, Core.passGenOpaqueTypeParams,
      Core.passTypeCheck .quiet, Core.passMonomorphizeFunctions, Core.passSimplify] ++
     (if axioms then [Core.passRecursiveAxioms axiomOptions] else []) ++
     [ho, pc, Core.passFunctionInlining, Core.passBetaReduce])).toOption

/-- The phase names of `withoutSymbolicEval axioms`, or why it does not compose. -/
private def phaseNames (axioms : Bool) : String :=
  match withoutSymbolicEval axioms with
  | some vp => ", ".intercalate (vp.phases.map (·.phase.name))
  | none => "does not compose"

/-- info: "assertNoCFGBodies, assertNoCalls, assertNoLoops, assertStaticSingleAssignment, assertNoNondetGuards, termCheck, precondElim, genOpaqueTypeParams, typeCheck, monomorphizeFunctions, simplify, recursiveAxioms, assertHasObligationForm, assertNoProcedureContracts, functionInlining, betaReduce" -/
#guard_msgs in
#eval phaseNames true

/-- info: "assertNoCFGBodies, assertNoCalls, assertNoLoops, assertStaticSingleAssignment, assertNoNondetGuards, termCheck, precondElim, genOpaqueTypeParams, typeCheck, monomorphizeFunctions, simplify, assertHasObligationForm, assertNoProcedureContracts, functionInlining, betaReduce" -/
#guard_msgs in
#eval phaseNames false

/-! Without the axioms, the solver sees `listLen` as an uninterpreted function and finds a
counterexample. -/

/--
info:
Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: assert_l2_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: l2
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify recPgm (options := Core.VerifyOptions.quiet)
  (pipeline := withoutSymbolicEval false)

/-! With them, the assertion passes, as it does under the default order. -/

/--
info:
Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: assert_l2_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: l2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify recPgm (options := Core.VerifyOptions.quiet)
  (pipeline := withoutSymbolicEval true)

/-! The phase reads the options `Core.verify` runs with, not those it was built with. Built
for `recursiveFnsAsDefineFunRec` but run without it, it still generates the axioms, so the
solver is never left with neither the axioms nor a `define-fun-rec` definition. -/

/--
info:
Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: assert_l2_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: l2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify recPgm (options := Core.VerifyOptions.quiet)
  (pipeline := withoutSymbolicEval true
    { Core.VerifyOptions.quiet with recursiveFnsAsDefineFunRec := true })

/-! By default the phase gives `listLen` one axiom per constructor of `IntList`, two in all.
With `recursiveFnsAsDefineFunRec`, the back end emits `listLen`'s definition itself, so the
phase generates none, as symbolic evaluation also generates none. -/

/-- The number of axioms `recursiveAxioms` attaches to `recPgm`'s functions under `options`. -/
private def axiomCount (options : Core.VerifyOptions) : String :=
  let prog := (TransM.run Inhabited.default (translateProgram recPgm)).fst
  match Core.Transform.run prog (Core.RecursiveAxioms.run options)
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
  | .error e => s!"error: {e}"
  | .ok (_, q) => toString <| q.decls.foldl (init := 0) fun n d =>
      match d with
      | .recFuncBlock fs _ => n + (fs.map (·.axioms.length)).sum
      | _ => n

/-- info: "2" -/
#guard_msgs in
#eval axiomCount .quiet

/-- info: "0" -/
#guard_msgs in
#eval axiomCount { Core.VerifyOptions.quiet with recursiveFnsAsDefineFunRec := true }

/-! Symbolic evaluation generates the axioms too, through the same function, which leaves
a function that already carries them alone. Running the phase first therefore adds no
duplicate: `listLen` still carries two axioms after both. -/

/-- The axiom count of `recPgm`'s functions after `recursiveAxioms` and then symbolic
    evaluation's generation step. -/
private def axiomCountTwice : Except String Nat :=
  let prog := (TransM.run Inhabited.default (translateProgram recPgm)).fst
  match Core.Transform.run prog (Core.RecursiveAxioms.run .quiet)
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
  | .error e => .error (toString e)
  | .ok (_, q) =>
    let tf : @Lambda.TypeFactory Core.CoreLParams.IDMeta := (q.decls.filterMap fun
      | .type (.data d) _ => some d
      | _ => none).toArray
    q.decls.foldlM (init := 0) fun n d =>
      match d with
      | .recFuncBlock fs _ => fs.foldlM (init := n) fun n f =>
          match Core.generateRecursiveAxioms tf id f.toLFunc with
          | .ok lf => .ok (n + lf.axioms.length)
          | .error e => .error (toString e)
      | _ => .ok n

/-- info: Except.ok 2 -/
#guard_msgs in
#eval axiomCountTwice

end Strata.RecursiveAxiomsTest

end
