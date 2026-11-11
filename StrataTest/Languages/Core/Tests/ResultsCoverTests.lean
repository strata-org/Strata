/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
import StrataDDM.Integration.Lean.HashCommands
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.Analysis.DeductiveVerification
meta import Strata.Transform.PrecondElim
meta import Strata.Transform.TerminationCheck

meta section

open Strata

/-! # Exactly one result per lemma

Deductive verification over a base factory (`DeductiveVerificationOnCoreWith`) asks for
exactly one result for each lemma of the program (`ResultsCover`). These tests pin it on the
program `lemma l1: true; lemma l2: false`. A pipeline that drops `l2` produces a program
whose only lemma is `l1`, and the back end proves it: the results show nothing about `l2`,
whose verdict is `unknown`, so without `ResultsCover` they would be accepted for the
program. With it, they are not deductive verification of the program, and the phase that
dropped `l2` does not keep the names of the lemmas (`LemmaLabelsKept`).
-/

namespace Strata.ResultsCoverTests

open Core.Specification.Analysis

private def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-- The program `lemma l1: true; lemma l2: false`. -/
private def twoLemmas :=
#strata
program Core;
lemma [l1]: true;
lemma [l2]: false;
#end

/-- `twoLemmas` with `l2` dropped. -/
private def dropL2 (p : Core.Program) : Core.Program :=
  { decls := p.decls.filter fun
      | .lemma l _ => l.name != "l2"
      | _ => true }

/-- A passing result for an obligation labeled `label`, with metadata `md`. -/
private def pass (label : String) (md : Imperative.MetaData Core.Expression := {}) :
    Core.VCResult :=
  { obligation := { label, property := .assert, assumptions := [],
                    obligation := .boolConst () true, metadata := md },
    outcome := .ok { satisfiabilityProperty := .unknown, validityProperty := .unsat } }

/-- A passing result for the lemma of `p` named `name`, with its metadata. -/
private def lem (p : Core.Program) (name : String) : Core.VCResult :=
  pass name (((lemmaIds p.decls).find? (·.1 == name)).map (·.2) |>.getD {})

/-- A passing result for each lemma of `p`. -/
private def lems (p : Core.Program) : Core.VCResults :=
  (lemmaIds p.decls).toArray.map fun (n, md) => pass n md

-- The program has the two lemmas, and dropping `l2` leaves `l1`.
#guard lemmaLabels (translate twoLemmas).decls == ["l1", "l2"]
#guard lemmaLabels (dropL2 (translate twoLemmas)).decls == ["l1"]

-- One passing result for `l1` covers the program with `l2` dropped.
#guard decide (ResultsCover (dropL2 (translate twoLemmas)) #[lem (translate twoLemmas) "l1"])

-- It does not cover the program: `l2` has no result. Its verdict is `unknown`, which the
-- verdicts alone do not tell apart from a lemma the back end could not prove.
#guard !decide (ResultsCover (translate twoLemmas) #[lem (translate twoLemmas) "l1"])
#guard (vcResultsVerdict (Entry := Unit) #[pass "l1"] ⟨"l2", {}⟩ matches .unknown _)

-- Dropping `l2` does not keep the names of the lemmas, so no phase that does it meets
-- `PhaseKeepsLemmaLabels`.
#guard !decide (LemmaLabelsKept (translate twoLemmas).decls (dropL2 (translate twoLemmas)).decls)
#guard decide (LemmaLabelsKept (translate twoLemmas).decls (translate twoLemmas).decls)

-- Exactly one: two results for `l1` do not cover it.
#guard !decide (ResultsCover (dropL2 (translate twoLemmas))
  #[lem (translate twoLemmas) "l1", lem (translate twoLemmas) "l1"])

-- Two lemmas with one name are not covered, even with one result for the name: one result
-- would stand for both. Dropping one of them keeps the name once, but not the lemma.
private def sameName : Core.Program :=
  { decls := [
      .lemma { name := "l", e := .boolConst () true } .empty,
      .lemma { name := "l", e := .boolConst () false } .empty] }
private def sameNameDropped : Core.Program := { decls := sameName.decls.take 1 }
#guard decide (ResultsCover sameNameDropped #[pass "l"])
#guard !decide (ResultsCover sameName #[pass "l"])
#guard !decide (LemmaLabelsKept sameName.decls sameNameDropped.decls)

-- Type checking rejects two lemmas of one name, so a type-checked program has distinct
-- lemma names.
#guard (_root_.Core.typeCheck .quiet sameName) matches .error _

-- Results under other labels, such as those of procedure assertions, are allowed.
#guard decide (ResultsCover (translate twoLemmas)
  (lems (translate twoLemmas) |>.push (pass "P_ensures_0")))

/-- The program `lemma l1: true; lemma l2: false`, built directly, so that the kernel can
    evaluate its lemma names. -/
private def twoLemmasDirect : Core.Program :=
  { decls := [
      .lemma { name := "l1", e := .boolConst () true } .empty,
      .lemma { name := "l2", e := .boolConst () false } .empty] }

#guard lemmaLabels twoLemmasDirect.decls == lemmaLabels (translate twoLemmas).decls

/-- **The results of the program with `l2` dropped are not deductive verification of the
    program**, over any base factory and for any entry points. -/
example (base : Lambda.Factory Core.CoreLParams) (entryPoints : List String) :
    ¬ DeductiveVerificationOnCoreWith base ⟨entryPoints, twoLemmasDirect⟩ #[pass "l1"] :=
  fun h => by
    have := (h.1 (show NoProcedures twoLemmasDirect by decide)).2 ("l2", .empty)
      (by simp [lemmaIds, twoLemmasDirect])
    simp [Core.VCResult.isForLemma, pass] at this

/-! ## Results for lemmas the back end did not get

Results for the program the back end verifies are each for one of its lemmas
(`ResultsWithin`); a result under a label the program has no lemma for is not. -/

#guard decide (ResultsWithin (translate twoLemmas) #[pass "l1", pass "l2"])
#guard !decide (ResultsWithin (translate twoLemmas) #[pass "l1", pass "l2", pass "l3"])

/-! ## The lemmas of the repaired program

Termination checking and precondition elimination add lemmas, named after the function
they check, and those are lemmas of the repaired program: each needs its own result. A
program may already declare a lemma with such a name. The added lemma then gets another
name (`Strata.Name.freshName`), so the repaired program's lemmas still have distinct
names, and exactly one result for each can be met. -/

/-- A recursive function, whose termination lemma and well-formedness lemma would be named
    `listLen_terminates_0` and `listLen_body_calls_IntList..tl_0`, next to user lemmas with
    those names. -/
private def generatedNames :=
#strata
program Core;
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};
lemma [listLen_terminates_0]: true;
lemma [listLen_body_calls_IntList..tl_0]: true;
#end

/-- The program repaired by termination checking and precondition elimination, in the order
    `Core.verify`'s pipeline runs them. -/
private def repaired : Except String Core.Program := do
  let s : Core.Transform.CoreTransformState :=
    { Core.Transform.CoreTransformState.emp with factory := Core.Factory }
  let (r1, s1) := Core.Transform.runWith (translate generatedNames) Core.TermCheck.termCheck s
  let (_, p1) ← r1.mapError fun _ => "termination checking failed"
  let (r2, _) := Core.Transform.runWith p1 Core.PrecondElim.precondElim s1
  let (_, p2) ← r2.mapError fun _ => "precondition elimination failed"
  return p2

private def generatedNamesLabels : Except String (List String) :=
  repaired.map (lemmaLabels ·.decls)

-- Both phases added a lemma to the repaired program, the user's lemmas keep their names, and
-- no two lemmas share one.
#guard match generatedNamesLabels with
  | .ok ls => ls.length == 4 && ls.contains "listLen_terminates_0" &&
      ls.contains "listLen_body_calls_IntList..tl_0" && ls.eraseDups.length == ls.length
  | .error _ => false
#guard lemmaLabels (translate generatedNames).decls ==
  ["listLen_terminates_0", "listLen_body_calls_IntList..tl_0"]

-- The source's lemma names are each the name of exactly one lemma of the repaired program.
#guard match repaired with
  | .ok q => decide (LemmaLabelsKept (translate generatedNames).decls q.decls)
  | .error _ => false

-- The termination lemma the repair adds needs a result: results for the user's lemmas alone
-- do not cover the repaired program, and one result for each of its lemmas does.
#guard match repaired with
  | .ok q => !decide (ResultsCover q #[lem q "listLen_terminates_0",
      lem q "listLen_body_calls_IntList..tl_0"]) &&
    decide (ResultsCover q (lems q)) && decide (ResultsWithin q (lems q))
  | .error _ => false

/-! ## Programs with procedures

Lemma coverage is claimed only for programs without procedures. In a program with a
procedure, a procedure obligation may have a lemma's name and metadata, so its result could
stand in for the lemma's own; `ResultsCover` then claims nothing about the lemmas. -/

private def assertNamedLikeLemma :=
#strata
program Core;
lemma [l1]: true;
procedure P() spec { ensures true; } { assert [l1]: true; };
#end

/-- `assertNamedLikeLemma` as a program built without locations would have it: the lemma
    and the assertion `l1` both have no metadata. -/
private def assertLikeLemmaNoLocations : Core.Program :=
  { decls := (translate assertNamedLikeLemma).decls.map fun
      | .lemma l _ => .lemma l .empty
      | .proc p md =>
        let body : List Core.Statement := [.cmd (.cmd (.assert "l1" (.boolConst () true) .empty))]
        .proc { p with body := .structured body } md
      | d => d }

-- With only the assertion's result, that result is the one result matching the lemma, and
-- no coverage is claimed: `ResultsCover` holds of any results, even none.
#guard #[pass "l1"].countP (·.isForLemma "l1" .empty) == 1
#guard decide (ResultsCover assertLikeLemmaNoLocations #[pass "l1"])
#guard decide (ResultsCover assertLikeLemmaNoLocations #[])
#guard decide (ResultsCover (translate assertNamedLikeLemma) #[])

-- Without a procedure, the only obligations are the lemmas'. A second result with `l1`'s
-- name and metadata beside `l1`'s own leaves the program uncovered, and so does `l1`'s
-- result missing.
#guard !decide (ResultsCover twoLemmasDirect #[pass "l1", pass "l1", pass "l2"])
#guard !decide (ResultsCover twoLemmasDirect #[pass "l2"])

/-! ## Lemmas whose metadata changes

A phase must keep a lemma's metadata as well as its name: the lemma's result is found by
both. A phase that changes only a lemma's metadata does not keep it. -/

/-- `twoLemmasDirect` with the metadata of `l1` changed. -/
private def retagged : Core.Program :=
  { decls := twoLemmasDirect.decls.map fun
      | .lemma l md => if l.name == "l1" then .lemma l (md.pushElem (.label "tag") (.msg "x"))
          else .lemma l md
      | d => d }

#guard !decide (LemmaLabelsKept twoLemmasDirect.decls retagged.decls)
#guard decide (LemmaLabelsKept twoLemmasDirect.decls twoLemmasDirect.decls)

/-! ## `Core.verify`'s own results

The results `Core.verify` returns cover the program it was given, read as
`DeductiveVerificationOnElaborated` reads it: after type checking. -/

/-- Whether `Core.verify`'s results on `t` cover the type-checked program. -/
private def coveredByVerify (t : StrataDDM.Program) : IO Unit := do
  let results ← Strata.Core.verify t (options := .quiet)
  match _root_.Core.typeCheck .quiet (translate t) with
  | .ok p => IO.println s!"{decide (ResultsCover p results)}"
  | .error e => IO.println s!"type checking failed: {e}"

/-- info: true -/
#guard_msgs in
#eval coveredByVerify assertNamedLikeLemma

/-- info: true -/
#guard_msgs in
#eval coveredByVerify generatedNames

end Strata.ResultsCoverTests

end -- meta section
