/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
import StrataDDM.Integration.Lean.HashCommands
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.ObligationExtraction
meta import Strata.Languages.Core.Analysis.DeductiveVerification

meta section

open Strata

/-! # The entries of a Core program

Deductive verification over a base factory (`DeductiveVerificationOnCoreWith`) has two kinds
of entries. These tests pin what they are on small programs.

- A procedure entry is one of mainline's (`IsCoreEntry`): its factory is
  `Program.factoryBeforeProcedure`, Core's factory with the functions declared before the
  procedure. A procedure declared after a datatype is found, and the factory its entries
  must have is that one, but it has none of the functions generated for the datatype. A
  body that evaluates the datatype's constructors or testers gets stuck there, so deductive
  verification says nothing about the assertions after it. Follow-up work adds those
  functions.
- The declarations entry walks the declarations in order (`declsLang`), assuming each axiom
  and `distinct` declaration and asserting each lemma. Obligation extraction walks them the
  same way.
-/

namespace Strata.CoreEntriesTests

private def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-- A datatype declared before a procedure. -/
private def dtBeforeProc :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
procedure P() spec { ensures true; } { assert [a]: true; };
#end

-- `P` is found, and the only declaration before it is the datatype.
#guard ((translate dtBeforeProc).findProcByString? "P").map (·.header.name.name) == some "P"
#guard ((translate dtBeforeProc).declsBeforeProcedure "P").length == 1

-- The factory a procedure entry of `P` must have (`factoryBeforeProcedure`) has no function
-- generated for the datatype; the runtime factory over Core's has them.
#guard !(((translate dtBeforeProc).factoryBeforeProcedure "P").toArray.any
  (·.name.name == "Some"))
#guard (Core.Specification.Analysis.runtimeFactoryOf Core.Factory
  ((translate dtBeforeProc).declsBeforeProcedure "P")).toArray.any (·.name.name == "Some")

/-- The constant `n`, as an operator. -/
private def cst (n : String) : Core.Expression.Expr := .op Core.coreLoc ⟨n, ()⟩ none

/-- An axiom, a `distinct` declaration and two lemmas:
    `axiom [ax1]: c == 1; distinct [dist]: [c, d]; lemma [l1]: c == 1; lemma [l2]: d == d`. -/
private def declsProg : Core.Program :=
  { decls := [
      .ax { name := "ax1", e := .eq Core.coreLoc (cst "c") (.intConst Core.valueLoc 1) } .empty,
      .distinct ⟨"dist", ()⟩ [cst "c", cst "d"] .empty,
      .lemma { name := "l1", e := .eq Core.coreLoc (cst "c") (.intConst Core.valueLoc 1) } .empty,
      .lemma { name := "l2", e := .eq Core.coreLoc (cst "d") (cst "d") } .empty] }

/-- The declarations entry's walk, read off `declAssumes`: for each declaration in order,
    the labels of the conditions it assumes (`false`), or, for a lemma, its name as an
    assertion (`true`). `declEvents` asserts a lemma only when its formula has a value, which
    depends on the model, so the lemma case is the one written by hand. -/
private def declsWalk (ρ : Imperative.Env Core.Expression) (p : Core.Program) :
    List (Bool × String) :=
  p.decls.flatMap fun d =>
    match d with
    | .lemma l _ => [(true, l.name)]
    | d => (Core.Specification.Analysis.declAssumes ρ d).map fun c => (false, c.label)

/-- Obligation extraction's walk: for each obligation, in order, the labels of the global
    facts it assumes, in the order they were declared, then its own label. -/
private def extractedWalk (p : Core.Program) : List (List String × String) :=
  match Core.ObligationExtraction.extractObligations p with
  | .ok obs => obs.toList.map fun ob =>
      (ob.assumptions.flatten.map
        (Imperative.PathConditionEntry.name (P := Core.Expression)), ob.label)
  | .error _ => []

-- In every environment, the declarations entry assumes the axiom and the `distinct` pair, then
-- asserts `l1` and `l2`, never assuming a lemma afterwards.
example (ρ : Imperative.Env Core.Expression) : declsWalk ρ declsProg =
    [(false, "ax1"), (false, "dist"), (true, "l1"), (true, "l2")] := rfl

-- Obligation extraction asserts the same lemmas, in the same order, each under the axiom and
-- the `distinct` declaration only, never under an earlier lemma.
#guard extractedWalk declsProg == [(["ax1", "dist"], "l1"), (["ax1", "dist"], "l2")]

/-- A `distinct` declaration over an `int` and a `bool`. -/
private def mixedDistinctPgm :=
#strata
program Core;
const c : int;
const b : bool;
distinct [mix]: [c, b];
lemma [after]: c == c;
#end

/-- The elaboration of `mixedDistinctPgm` by type checking, if any. -/
private def mixedDistinctElab : Option Core.Program :=
  (Core.typeCheck .quiet (translate mixedDistinctPgm)).toOption

-- Type checking accepts an ill-sorted `distinct` declaration today, and `declFormulasTyped`
-- rejects it, so `TypeCheckDeclFormulasTyped` is false. Once type checking requires one type
-- for a `distinct` declaration's expressions, this program is rejected and the first check
-- flips.
#guard mixedDistinctElab.isSome
#guard mixedDistinctElab.all fun p => !Core.Specification.Analysis.Program.formulasTypedB p
#guard mixedDistinctElab.all fun p => p.decls.any fun d =>
  match d with
  | .distinct .. => !Core.Specification.Analysis.declFormulasTyped d
  | _ => false

/-- A lemma before the `distinct` declaration it needs. -/
private def distinctAfterLemmaPgm :=
#strata
program Core;
const c : int;
const d : int;
lemma [early]: !(c == d);
distinct [dist]: [c, d];
#end

/-- The same lemma after the `distinct` declaration. -/
private def distinctBeforeLemmaPgm :=
#strata
program Core;
const c : int;
const d : int;
distinct [dist]: [c, d];
lemma [late]: !(c == d);
#end

-- The premise theorems take: it fails on the first program and holds on the second.
#guard !Core.Specification.Analysis.Program.distinctsBeforeLemmasB (translate distinctAfterLemmaPgm)
#guard Core.Specification.Analysis.Program.distinctsBeforeLemmasB (translate distinctBeforeLemmaPgm)

/-- `Core.verify`'s verdict on each obligation of `p`. -/
private def verdicts (p : StrataDDM.Program) : IO Unit := do
  let results ← Strata.Core.verify p (options := .quiet)
  for r in results do
    IO.println s!"{r.obligation.label}: {if r.isSuccess then "pass" else "not proved"}"

-- A KNOWN WRONG verdict: `Core.verify` hoists the later `distinct` into `early`'s obligation
-- and reports it proved, although the language reference checks a lemma only under the
-- declarations before it, and a model with `c = d` falsifies `early` there. When
-- `Core.verify` scopes `distinct` declarations by position, this becomes `not proved`.
/-- info: early: pass -/
#guard_msgs in
#eval verdicts distinctAfterLemmaPgm

-- With the `distinct` first, the lemma is proved, as the reference says.
/-- info: late: pass -/
#guard_msgs in
#eval verdicts distinctBeforeLemmaPgm

end Strata.CoreEntriesTests
