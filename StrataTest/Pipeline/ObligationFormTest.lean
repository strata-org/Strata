/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! # Symbolic evaluation's output satisfies `hasObligationForm`

Runs the default pipeline on programs with zero, one and several obligations
and checks the output. -/

meta section

namespace Strata

/-- Three obligations: one `assert` on each branch of an `if`, and the
    postcondition. -/
private def multiObligationPgm :=
#strata
program Core;
procedure P(x : int, out y : int)
spec {
  ensures (int.ge(y, 0));
}
{
  if (int.ge(x, 0)) {
    y := x;
    assert (int.ge(y, 0));
  } else {
    y := int.neg(x);
    assert (int.gt(y, 0));
  }
};
#end

/-- The default pipeline followed by the assert phase for `fact`. -/
private def withAssert (fact : Core.ProgramFact) :
    Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) := do
  let a ← Core.assertPhaseFor (Core.assertPhaseName fact)
  (Core.ValidatedPipeline.ofList
    (Core.corePipelinePhases Core.VerifyOptions.quiet ++ [a])).toOption

/-! Both pipelines build, so neither test below falls back to the default order. -/

#guard (withAssert .hasObligationForm).isSome
#guard (withAssert .noNondetGuards).isSome

/-! `hasObligationForm` holds of the output. -/

/--
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: assert_1
Property: assert
Result: ✅ pass

Obligation: P_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify multiObligationPgm (options := Core.VerifyOptions.quiet)
  (pipeline := withAssert .hasObligationForm)

/-! `noNondetGuards` does not: the obligations are separated by `ite *`. -/

/-- error: ❌ Expected noNondetGuards, but the program does not satisfy it. -/
#guard_msgs in
#eval Core.verify multiObligationPgm (options := Core.VerifyOptions.quiet)
  (pipeline := withAssert .noNondetGuards)

/-- Run the default pipeline on `env` and print the output program and whether
    it satisfies `hasObligationForm`. -/
private def runDefault (env : StrataDDM.Program) : IO Unit := do
  let (prog, _) := Core.getProgram env
  let step (p : Core.Program) (ph : Core.PipelinePhase) :
      Core.Transform.CoreTransformM Core.Program := do
    let (_, out) ← ph.transform p
    return out
  match ((Core.corePipelinePhases Core.VerifyOptions.quiet).foldlM step prog).run .emp with
  | (.ok out, _) =>
    IO.println (Std.format out)
    IO.println s!"hasObligationForm: \
      {Core.Program.allStatements Core.Statements.hasObligationForm out}"
  | (.error e, _) => IO.println s!"error: {e.message}"

/-! With no obligations the body is empty. -/

private def noObligationPgm :=
#strata
program Core;
procedure P(x : int, out y : int)
{
  y := x;
};
#end

/-- info: program Core;

procedure P ()
{

};

hasObligationForm: true -/
#guard_msgs (whitespace := lax) in
#eval runDefault noObligationPgm

/-! With one obligation the body is its `assume`s and `assert`, with no `ite *`.
The `block` around the `assert` does not appear in the output. -/

private def oneObligationPgm :=
#strata
program Core;
procedure P(x : int, out y : int)
spec {
  requires (int.ge(x, 0));
}
{
  b: {
    assert (int.ge(x, 0));
  }
};
#end

/-- info: program Core;

procedure P ()
{
  var $__cse.0 : bool := int.ge(x@1, 0);
  assume [P_requires_0]: $__cse.0;
  assert [assert_0]: $__cse.0;
};

hasObligationForm: true -/
#guard_msgs in
#eval runDefault oneObligationPgm

end Strata

end -- meta section
