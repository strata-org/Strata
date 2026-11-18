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

The type checker rejects a parameter named like a function or a constant, so `Core.verify`
rejects each program. The same programs, written as type-annotated ASTs, are then run through
the phases that follow the type check, supplied with a proof that the facts the type check
establishes hold. -/

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
error: ❌ Type checking error.
Procedure 'P': parameter 'c' collides with a function or constant of the same name
-/
#guard_msgs in
#eval printModesProved functionPgm

/--
error: ❌ Type checking error.
Procedure 'P': parameter 'c' collides with a function or constant of the same name
-/
#guard_msgs in
#eval printModesProved constPgm

/--
error: ❌ Type checking error.
Procedure 'P': parameter 'c' collides with a function or constant of the same name
-/
#guard_msgs in
#eval printModesProved assignPgm

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
          body := .structured body } .empty

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
info: symbolic pc: not proved
wp pc: not proved
-/
#guard_msgs in
#eval printModesProvedAfterCheck functionAst functionAst_facts

/--
info: symbolic pc: not proved
wp pc: not proved
-/
#guard_msgs in
#eval printModesProvedAfterCheck constAst constAst_facts

/--
info: symbolic pr: not proved
wp pr: not proved
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
info: Except.ok "phase #18 `commonSubexprElim` requires `noInits` but preceding phases only guarantee `noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated, exitsCovered, armsHaveObligations`"
-/
#guard_msgs in
#eval validation wpThenCSE

/-! The phases a caller may name do not depend on `--vcgen`: resolved against the phases
nameable under `--vcgen wp`, the same list is rejected with the same diagnostic. -/

/--
info: Except.ok "phase #18 `commonSubexprElim` requires `noInits` but preceding phases only guarantee `noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated, exitsCovered, armsHaveObligations`"
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

end Strata.WPGlobalNameTest
