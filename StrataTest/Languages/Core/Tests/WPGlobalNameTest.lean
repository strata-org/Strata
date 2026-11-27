/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core
import Strata.MetaVerifier
import StrataTest.Languages.Core.Tests.WPTestUtils

/-! # Parameters named like global functions and constants

A variable of an obligation and a function of the program are both encoded as SMT
constants under their own names, so an obligation variable named like a 0-ary function or
a constant would denote it, constrained by its axioms. The SSA phase gives every
parameter a fresh entry name, as symbolic evaluation does, so a read-only parameter `c` never
denotes a global `c`. Each assertion below holds only of the global `c` (axiom `c0`), not of an
arbitrary parameter `c`, so it must not be proved, in symbolic mode and in
`--vcgen wp` alike.

The same programs, written as type-annotated ASTs, are then run through the phases that follow
the type check, supplied with a proof that the facts the type check establishes hold. -/

namespace Strata.WPGlobalNameTest

open Strata.WPTestUtils

/-- A read-only parameter named like a 0-ary function. -/
def functionPgm :=
#strata
program Core;

function c() : int;
axiom [c0]: c == 0;

procedure P(c : int, out r : int)
{
  assert [pc]: c == 0;
};

#end

/-- A read-only parameter named like a constant. -/
def constPgm :=
#strata
program Core;

const c : int;
axiom [c0]: c == 0;

procedure P(c : int, out r : int)
{
  assert [pc]: c == 0;
};

#end

/-- An output parameter assigned from the read-only parameter named like a 0-ary function. -/
def assignPgm :=
#strata
program Core;

function c() : int;
axiom [c0]: c == 0;

procedure P(c : int, out r : int)
{
  r := c;
  assert [pr]: r == 0;
};

#end

/--
info: symbolic pc: refuted
wp pc: refuted
-/
#guard_msgs in
#eval printModesProved functionPgm

/--
info: symbolic pc: refuted
wp pc: refuted
-/
#guard_msgs in
#eval printModesProved constPgm

/--
info: symbolic pr: refuted
wp pr: refuted
-/
#guard_msgs in
#eval printModesProved assignPgm

/-- An in-out parameter named like a constant, its starting value read as `old(c)` in the
    contract. The contract is about the parameter, and its `old` value, so it is proved; the
    assertion holds only of the global `c`. -/
def inoutPgm :=
#strata
program Core;

const c : int;
axiom [c0]: c == 0;

procedure P(inout c : int)
spec {
  ensures [inc]: c == int.add(old(c), 1);
}
{
  assert [pc]: c == 0;
  c := int.add(c, 1);
};

#end

/--
info: symbolic pc: refuted
symbolic inc: proved
wp pc: refuted
wp inc: proved
-/
#guard_msgs in
#eval printModesProved inoutPgm

/-! A pipeline that does not end with `separateVarNames` is accepted, and its program reaches
the back end with a variable named like the constant; each back end renames it apart itself
before it extracts, so the verdicts are those above, on the per-obligation and the incremental
back end alike. -/

/-- `printProved` on `pgm` for each of the two `modes`, through the default order without its
    last phase, `separateVarNames`, on the per-obligation back end and on the incremental one. -/
private def printWithoutSeparation (pgm : StrataDDM.SourcedProgram) : IO Unit := do
  for (mode, opts) in modes do
    for (backEnd, incremental) in [("per-obligation", false), ("incremental", true)] do
      let opts := { opts with incremental }
      let phases := (Core.corePipelinePhases opts).filter (Core.phaseName · != "separateVarNames")
      match Core.validatePipeline phases with
      | .error e => IO.println s!"{mode} {backEnd}: rejected: {e}"
      | .ok vp => printProved pgm opts (pipeline := some vp) (pre := s!"{mode} {backEnd} ")

/--
info: symbolic per-obligation pc: refuted
symbolic per-obligation inc: proved
symbolic incremental pc: refuted
symbolic incremental inc: proved
wp per-obligation pc: refuted
wp per-obligation inc: proved
wp incremental pc: refuted
wp incremental inc: proved
-/
#guard_msgs in
#eval printWithoutSeparation inoutPgm

/-- A function-typed parameter named like a global function and applied: the application is
    of the parameter, so the assertion, true of the global `g`, is not proved. -/
def appliedParamPgm :=
#strata
program Core;

function g(x : int) : int { x }

procedure P(g : int -> int)
{
  assert [paramApplied]: g(1) == 1;
};

#end

/--
info: symbolic paramApplied: refuted
wp paramApplied: refuted
-/
#guard_msgs in
#eval printModesProved appliedParamPgm

/-- A constant used before a local of its name is declared: the first assertion reads the
    constant, the second the local. -/
def globalBeforeLocalPgm :=
#strata
program Core;

const c : int;
axiom [c0]: c == 0;

procedure P()
{
  assert [globalBefore]: c == 0;
  var c : int;
  assert [localAfter]: c == 0;
};

#end

/--
info: symbolic globalBefore: proved
symbolic localAfter: refuted
wp globalBefore: proved
wp localAfter: refuted
-/
#guard_msgs in
#eval printModesProved globalBeforeLocalPgm

/-! The incremental back end keeps them apart too. -/

/--
info: globalBefore: proved
localAfter: refuted
-/
#guard_msgs in
#eval printProved globalBeforeLocalPgm { Core.VerifyOptions.quiet with incremental := true }

/-- An output parameter named like a constant, assigned twice, beside a variable already named
    `c@1`: the versions symbolic evaluation gives the parameter avoid `c@1`, and neither is the
    global `c`. The counterexample shows the parameter's last version under `c@…`. -/
def renamedBesideVersionsPgm :=
#strata
program Core;

const c : int;
axiom [c0]: c == 0;

procedure P(|c@1| : int, out c : int)
{
  c := |c@1|;
  c := int.add(c, 1);
  assert [renamedNotGlobal]: c == 1;
  assert [versionsApart]: c == int.add(|c@1|, 1);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: renamedNotGlobal
Property: assert
Assumptions:
c0: c == 0
Obligation:
int.add(c@2, 1) == 1

Label: versionsApart
Property: assert
Assumptions:
c0: c == 0
Obligation:
true

---
info:
Obligation: renamedNotGlobal
Property: assert
Result: ❌ fail
Model:
(c@2, int.neg(1))

Obligation: versionsApart
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify renamedBesideVersionsPgm

/-! ### The phases after the type check, on type-annotated ASTs -/

/-- The global `c`, of type `int`. -/
private def cGlobal : Core.Expression.Expr := .op Core.coreLoc "c" (some .int)

/-- A variable of type `int`. -/
private def intVar (x : String) : Core.Expression.Expr := .fvar Core.coreLoc ⟨x, ()⟩ (some .int)

/-- The axiom `c0 : c == 0`. -/
private def c0Axiom : Core.Decl := .ax
    { name := "c0", e := .eq Core.coreLoc cGlobal (.intConst Core.coreLoc 0) } .empty

/-- The procedure `P(c : int, out r : int)` with the body `body`. -/
private def procP (body : List Core.Statement) : Core.Decl :=
  .proc { header := { name := "P", typeArgs := [], inputs := [("c", .int)],
                      outputs := [("r", .int)] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured body false } .empty

/-- The body `assert [pc]: c == 0`. -/
private def assertPc : List Core.Statement :=
  [.cmd (.cmd (.assert "pc" (.eq Core.coreLoc (intVar "c") (.intConst Core.coreLoc 0)) .empty))]

/-- `functionPgm` as an AST. -/
private def functionAst : Core.Program :=
  { decls := [.func { name := "c", inputs := [], output := .int } .empty, c0Axiom,
              procP assertPc] }

/-- `constPgm` as an AST. -/
private def constAst : Core.Program :=
  { decls := [.func (Core.Function.const "c" .int) .empty, c0Axiom, procP assertPc] }

/-- `assignPgm` as an AST. -/
private def assignAst : Core.Program :=
  { decls := [.func { name := "c", inputs := [], output := .int } .empty, c0Axiom,
              procP [.cmd (.cmd (.set "r" (.det (intVar "c")) .empty)),
                     .cmd (.cmd (.assert "pr" (.eq Core.coreLoc (intVar "r")
                                               (.intConst Core.coreLoc 0)) .empty))]] }

/-- The facts the type check establishes. -/
private def checkedFacts : Core.ProgramFactSet :=
  Core.ProgramFactSet.ofList [.wellFormedCalls, .typeAnnotated, .exitsCovered]

/-- A program whose calls are well formed, whose expressions are all annotated, and whose exits
    all target an enclosing block has the facts the type check establishes. -/
private theorem checkedFacts_holds {p : Core.Program}
    (hcalls : (Core.illFormedCalls p).isEmpty = true)
    (hann : Core.Program.allExprs Lambda.LExpr.fullyAnnotated p = true)
    (hexits : Core.Program.allStatements (Imperative.Block.checkExitsCoveredByBlocks []) p = true) :
    checkedFacts.holds p := by
  intro f hf
  cases f
  all_goals first
    | exact absurd hf (by decide)
    | exact (Core.ProgramFact.holds_iff_check rfl p).mpr hcalls
    | exact hann
    | exact (Core.ProgramFact.holds_iff_check rfl p).mpr hexits

/-- Every expression of `functionAst`, `constAst` and `assignAst` carries its type annotation. -/
private theorem asts_annotated :
    [functionAst, constAst, assignAst].all (Core.Program.allExprs Lambda.LExpr.fullyAnnotated)
      = true := by
  decide

/-- `functionAst` has the facts the type check establishes. -/
private theorem functionAst_facts : checkedFacts.holds functionAst :=
  checkedFacts_holds (by decide) (List.all_eq_true.mp asts_annotated _ List.mem_cons_self)
    (by decide)

/-- `constAst` has the facts the type check establishes. -/
private theorem constAst_facts : checkedFacts.holds constAst :=
  checkedFacts_holds (by decide)
    (List.all_eq_true.mp asts_annotated _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (by decide)

/-- `assignAst` has the facts the type check establishes. -/
private theorem assignAst_facts : checkedFacts.holds assignAst :=
  checkedFacts_holds (by decide)
    (List.all_eq_true.mp asts_annotated _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (by decide)

/-- Prints, for each of the two `modes`, one line per obligation of `p` as `printModesProved`
    does, running only the phases of that mode that follow the type check. -/
private def printModesProvedAfterCheck (p : Core.Program) (hp : checkedFacts.holds p) :
    IO Unit := do
  for (mode, opts) in modes do
    let afterCheck := (Core.corePipelinePhases opts).drop 1
    match Core.ValidatedPipeline.ofListFrom checkedFacts afterCheck with
    | .error e => IO.println e
    | .ok vp =>
      match ← (Strata.Core.verifyProgram p opts (entryFacts := checkedFacts)
          (pipeline := some vp) (entryFactsHold := hp)).toBaseIO with
      | .ok rs => for r in rs do IO.println (provedLine s!"{mode} " r)
      | .error e => IO.println s!"error: {e}"

/--
info: symbolic pc: refuted
wp pc: refuted
-/
#guard_msgs in
#eval printModesProvedAfterCheck functionAst functionAst_facts

/--
info: symbolic pc: refuted
wp pc: refuted
-/
#guard_msgs in
#eval printModesProvedAfterCheck constAst constAst_facts

/--
info: symbolic pr: refuted
wp pr: refuted
-/
#guard_msgs in
#eval printModesProvedAfterCheck assignAst assignAst_facts

/-! Common-subexpression elimination prepends its definitions to a body, so it requires a
body that declares no variable (`noInits`), which symbolic evaluation establishes and the
SSA phase does not. A pipeline that runs it after the WP, SSA and dead-definition phases is
rejected. -/

/-- The phase names of the `--vcgen wp` order, with `commonSubexprElim` at the end. -/
private def wpThenCSE : List String :=
  (Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .wp }).map
    Core.phaseName ++ ["commonSubexprElim"]

/-- `validatePipeline` on the phases named `names`: `accepted`, or its diagnostic. -/
private def validation (names : List String) : Except String String := do
  let phases ← Core.resolvePhases (Core.nameablePhases Core.VerifyOptions.quiet) names
  match Core.validatePipeline phases with
  | .ok _ => pure "accepted"
  | .error e => pure e

/--
info: Except.ok "phase #20 `commonSubexprElim` requires `noInits` but preceding phases only guarantee `noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noLambdas, noPrecondsFromFuncs, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated, exitsCovered, armsHaveObligations, varsNotFunctions`"
-/
#guard_msgs in
#eval validation wpThenCSE

/-! The phases a caller may name do not depend on `--vcgen`: resolved against the phases
nameable under `--vcgen wp`, the same list is rejected with the same diagnostic. -/

/--
info: Except.ok "phase #20 `commonSubexprElim` requires `noInits` but preceding phases only guarantee `noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noLambdas, noPrecondsFromFuncs, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated, exitsCovered, armsHaveObligations, varsNotFunctions`"
-/
#guard_msgs in
#eval show Except String String from do
  let opts := { Core.VerifyOptions.quiet with vcgen := .wp }
  let phases ← Core.resolvePhases (Core.nameablePhases opts) wpThenCSE
  match Core.validatePipeline phases with
  | .ok _ => pure "accepted"
  | .error e => pure e

/-- info: Except.ok "accepted" -/
#guard_msgs in
#eval validation ((Core.corePipelinePhases Core.VerifyOptions.quiet).map Core.phaseName)

/-! The rewrite loop reduces the redexes of procedure bodies only, so it does not establish
`noBetaRedexes`, which the back end requires: the default order of `--vcgen wp`, which ends with
`betaReduce`, `lambdaLift` and `separateVarNames`, is accepted, and the same order without
`betaReduce` and `lambdaLift` is rejected. -/

/-- The phase names of the `--vcgen wp` order. -/
private def wpOrder : List String :=
  (Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .wp }).map Core.phaseName

/-- info: Except.ok "accepted" -/
#guard_msgs in
#eval validation wpOrder

/--
info: Except.ok "phase #18 `the verification back end` requires:\n  • `noBetaRedexes`: preceding phases only guarantee `noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated, exitsCovered, armsHaveObligations, varsNotFunctions`\n  • `noLambdas`: preceding phases only guarantee `noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated, exitsCovered, armsHaveObligations, varsNotFunctions`"
-/
#guard_msgs in
#eval validation (wpOrder.filter (fun n => n != "betaReduce" && n != "lambdaLift"))

end Strata.WPGlobalNameTest
