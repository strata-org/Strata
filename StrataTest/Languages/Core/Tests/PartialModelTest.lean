/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.IncrementalSolve
meta import Strata.Languages.Core.SarifOutput
import StrataDDM.Integration.Lean.HashCommands

/-! # A counterexample model with no value for some requested variable is printed as partial -/

meta section

namespace Strata.PartialModelTest

open Strata

private def parse (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- An assertion over the two parameters `x` and `y`. -/
private def twoVars :=
#strata
program Core;
procedure p (x : int, y : int) {
  assert [sum]: int.gt(int.add(x, y), 0);
};
#end

/-- A discharge that refutes every obligation with a model holding a value for the first
    requested variable only. -/
private def firstVarOnly : Core.MkDischargeFn := fun _ _ _ vars _ _ _ _ _ =>
  fun _ _ _ _ _ _ _ =>
    let model := (vars.take 1).map fun (v, _) => (v, Strata.SMT.Term.prim (.int 7))
    pure (.ok (.unknown, .sat model, Strata.SMT.EncoderState.init))

/-- Print each obligation's result, its model included. -/
private def report (p : StrataDDM.Program) (mk : Core.MkDischargeFn) : IO Unit := do
  match ← (Strata.Core.verifyProgram (parse p)
      { Core.VerifyOptions.default with solver := "not-a-local-solver", verbose := .models }
      (mkDischarge := mk)).toBaseIO with
  | .ok results => for r in results do IO.println (toString (Std.format r))
  | .error e => IO.println s!"error: {e}"

/--
info: Obligation: sum
Property: assert
Result: ❌ fail
Model: (partial; no value for y@1)
(x@1, 7)
-/
#guard_msgs in
#eval report twoVars firstVarOnly

/-- A discharge that refutes every obligation with a model holding a value for every
    requested variable. -/
private def everyVar : Core.MkDischargeFn := fun _ _ _ vars _ _ _ _ _ =>
  fun _ _ _ _ _ _ _ =>
    let model := vars.map fun (v, _) => (v, Strata.SMT.Term.prim (.int 7))
    pure (.ok (.unknown, .sat model, Strata.SMT.EncoderState.init))

/--
info: Obligation: sum
Property: assert
Result: ❌ fail
Model:
(x@1, 7) (y@1, 7)
-/
#guard_msgs in
#eval report twoVars everyVar

/-! The SARIF message of a result with a partial model carries the same marker. -/

/-- Print the SARIF message of each obligation's result. -/
private def reportSarif (p : StrataDDM.Program) (mk : Core.MkDischargeFn) : IO Unit := do
  match ← (Strata.Core.verifyProgram (parse p)
      { Core.VerifyOptions.default with solver := "not-a-local-solver", verbose := .models }
      (mkDischarge := mk)).toBaseIO with
  | .ok results => for r in results do
      IO.println (Core.Sarif.vcResultToSarifResult .deductive {} r).message.text
  | .error e => IO.println s!"error: {e}"

/-- info: Can be false and is reachable, unknown if always false with counterexample: (x@1, 7) (partial; no value for y@1) -/
#guard_msgs in
#eval reportSarif twoVars firstVarOnly

/-- info: Can be false and is reachable, unknown if always false with counterexample: (x@1, 7) (y@1, 7) -/
#guard_msgs in
#eval reportSarif twoVars everyVar

/-- A cover over the two parameters `x` and `y`. -/
private def twoVarsCover :=
#strata
program Core;
procedure p (x : int, y : int) {
  cover [sum]: int.gt(int.add(x, y), 0);
};
#end

/-- A discharge that satisfies every obligation with a model holding a value for the first
    requested variable only. -/
private def firstVarOnlySat : Core.MkDischargeFn := fun _ _ _ vars _ _ _ _ _ =>
  fun _ _ _ _ _ _ _ =>
    let model := (vars.take 1).map fun (v, _) => (v, Strata.SMT.Term.prim (.int 7))
    pure (.ok (.sat model, .unsat, Strata.SMT.EncoderState.init))

/-! The SARIF message of a passing cover prints no model, so it carries no marker, although
    the satisfying model is partial. -/

/-- info: Can be true, unknown if always true -/
#guard_msgs in
#eval reportSarif twoVarsCover firstVarOnlySat

/-! A message that prints both the true and the false model marks each partial one. -/

/-- A discharge whose satisfiability model has a value for the first requested variable only
    and whose validity model has a value for every requested variable but the first. -/
private def splitModels : Core.MkDischargeFn := fun _ _ _ vars _ _ _ _ _ =>
  fun _ _ _ _ _ _ _ =>
    let value := fun (vs : List _) => vs.map fun (v, _) => (v, Strata.SMT.Term.prim (.int 7))
    pure (.ok (.sat (value (vars.take 1)), .sat (value (vars.drop 1)),
      Strata.SMT.EncoderState.init))

/-- Print the SARIF message of each obligation's result under both checks. -/
private def reportSarifFull (p : StrataDDM.Program) (mk : Core.MkDischargeFn) : IO Unit := do
  match ← (Strata.Core.verifyProgram (parse p)
      { Core.VerifyOptions.default with
          solver := "not-a-local-solver", verbose := .models, checkLevel := .full }
      (mkDischarge := mk)).toBaseIO with
  | .ok results => for r in results do
      IO.println (Core.Sarif.vcResultToSarifResult .deductive {} r).message.text
  | .error e => IO.println s!"error: {e}"

/-- info: True or false depending on inputs (true: (x@1, 7), false: (y@1, 7)) (partial; the true model has no value for y@1; the false model has no value for x@1) -/
#guard_msgs in
#eval reportSarifFull twoVars splitModels

/-! The incremental back end prints a partial model the same way. -/

/-- An assertion over two variables the procedure declares, in the form the incremental back
    end takes. -/
private def twoLocals :=
#strata
program Core;
procedure p () {
  var x : int;
  var y : int;
  assert [sum]: int.gt(int.add(x, y), 0);
};
#end

/-- A solver that, asked for the values of several variables, answers for the first one only. -/
private def firstValueOnly (s : Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType IO) :
    Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType IO :=
  { s with getModelText := fun ts => s.getModelText (ts.take 1) }

/-- Print each obligation's result from the incremental back end, its model included. -/
private def reportIncremental (p : StrataDDM.Program) : IO Unit := do
  match ← Core.IncrementalSolve.verifyProgram (parse p) 1
      { Core.VerifyOptions.quiet with verbose := .models } (wrapSolver := firstValueOnly) with
  | .ok (results, _, _) => for r in results do IO.println (toString (Std.format r))
  | .error e => IO.println s!"error: {e}"

/--
info: Obligation: sum
Property: assert
Result: ❌ fail
Model: (partial; no value for y)
(x, 0)
-/
#guard_msgs in
#eval reportIncremental twoLocals

/-! The SARIF message prints a model value converted to a Core expression, as the command line
    prints it: the solver's real value `(- (/ 5.0 2.0))` is printed `real.neg(2.5)`. -/

/-- An assertion over the real parameter `r`. -/
private def realVar :=
#strata
program Core;
procedure q (r : real) {
  assert [a2]: real.ge(r, real.neg(1.5));
};
#end

/-- A discharge that refutes every obligation with the model `r = -(5/2)`, read from the
    solver response `((r (- (/ 5.0 2.0))))`. -/
private def negRational : Core.MkDischargeFn := fun _ _ _ vars _ _ _ _ _ =>
  fun _ _ _ _ _ _ _ => do
    let pairs ← Imperative.SMT.parseModelDDM "((r (- (/ 5.0 2.0))))"
    let model := (vars.take 1).flatMap fun (v, _) => pairs.map fun (_, t) => (v, t)
    pure (.ok (.unknown, .sat model, Strata.SMT.EncoderState.init))

/-- info: Can be false and is reachable, unknown if always false with counterexample: (r@1, real.neg(2.5)) -/
#guard_msgs in
#eval reportSarif realVar negRational

end Strata.PartialModelTest

end -- meta section
