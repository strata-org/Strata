/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! # The SMT encoder reads only real copies as the functions they copy

`MonomorphizeFunctions` names its copy of a factory function `f` at an instantiation
`$__mono#f#…`, marks the copy's factory entry as a copy of `f`, and the SMT encoder
encodes a marked function as `f`. A user function can carry a name of that shape, for
instance when a pipeline skips monomorphization (here by checking `noPolymorphicFunctions`
in its place). It is not marked, so it is encoded from its own declaration. Here it is
named like the copy of integer addition, with a body of its own.
-/

meta section
namespace Strata

/-- `f(2, 3)` is `6` under the user's definition, so `r == 5` is false; it would hold if
    `f` were read as integer addition. -/
private def copyNamedPgm :=
#strata
program Core;
function |$__mono#Int.Add#int|(a : int, b : int) : int { int.add(int.add(a, b), 1) }
procedure P(out r : int)
spec { ensures [falseUnderUser]: r == 5; }
{ r := |$__mono#Int.Add#int|(2, 3); };
#end

/-- The same function with the postcondition its definition gives. -/
private def copyNamedTruePgm :=
#strata
program Core;
function |$__mono#Int.Add#int|(a : int, b : int) : int { int.add(int.add(a, b), 1) }
procedure P(out r : int)
spec { ensures [trueUnderUser]: r == 6; }
{ r := |$__mono#Int.Add#int|(2, 3); };
#end

private def toCore (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- `phases` with the monomorphization phase replaced by `q`. -/
private def replaceMono (phases : List Core.PipelinePhase) (q : Core.PipelinePhase) :
    List Core.PipelinePhase :=
  phases.map fun p => if p.phase.name == "monomorphizeFunctions" then q else p

/-- The check that no function is polymorphic, which these programs pass. It establishes the
    fact monomorphization would, so a pipeline with it in place of monomorphization validates
    without entry facts. -/
private def assertNoPoly : Core.PipelinePhase := Core.ProgramFact.assertPhase .noPolymorphicFunctions

/-- The default order with monomorphization replaced by `assertNoPoly`. -/
private def withoutMono : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) :=
  (Core.validatePipeline
    (replaceMono (Core.corePipelinePhases Core.VerifyOptions.quiet) assertNoPoly)).toOption

-- `none` would verify with the default order, so the pipeline has to validate.
#guard withoutMono.isSome

/-- Verify `p` with `pipeline`, or with the default order. -/
private def runVerify (p : StrataDDM.Program)
    (pipeline : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) := none) : IO Unit := do
  match ← (Core.verifyProgram (toCore p) (options := .quiet) (pipeline := pipeline)).toBaseIO with
  | .error e => IO.println s!"verify error: {e}"
  | .ok rs => for r in rs do IO.println s!"{r.obligation.label}: {r.formatOutcome}"

/-- The functions `p` declares, with their attributes. -/
private def declaredAttrs (p : Core.Program) : List (String × Array Strata.DL.Util.FuncAttr) :=
  p.decls.flatMap fun
    | .func f _ => [(f.name.name, f.attr)]
    | .recFuncBlock fs _ => fs.map fun f => (f.name.name, f.attr)
    | _ => []

/-! ## Only monomorphization marks a copy

The translation from Core's syntax gives a function only the attributes its syntax can state
(inlining), so the user's function named exactly like the copy of integer addition carries no
copy mark, and the encoder reads no function of the program as a copy. -/

#guard (declaredAttrs (toCore copyNamedPgm)).map (·.1) == ["$__mono#Int.Add#int"]
#guard (declaredAttrs (toCore copyNamedPgm)).all fun (_, a) =>
  (Strata.DL.Util.FuncAttr.findMonoCopyOf a).isNone

/-- info: falseUnderUser: ❌ fail -/
#guard_msgs in
#eval runVerify copyNamedPgm withoutMono

/-! ## A mark set by hand on a program function is dropped

A program built through the API can put the copy mark on a function it declares. A program's
functions are never copies of factory functions, so the mark is dropped when the function is
registered for encoding, and the false postcondition still fails. -/

/-- `copyNamedPgm` with its function marked as a copy of integer addition. -/
private def handMarkedPgm : Core.Program :=
  let p := toCore copyNamedPgm
  { p with decls := p.decls.map fun
      | .func f md => .func { f with attr := f.attr.push (.monoCopyOf "Int.Add") } md
      | d => d }

#guard (declaredAttrs handMarkedPgm).any fun (_, a) =>
  Strata.DL.Util.FuncAttr.findMonoCopyOf a == some "Int.Add"

/-- info: falseUnderUser: ❌ fail -/
#guard_msgs in
#eval show IO Unit from do
  match ← (Core.verifyProgram handMarkedPgm (options := .quiet) (pipeline := withoutMono)).toBaseIO with
  | .error e => IO.println s!"verify error: {e}"
  | .ok rs => for r in rs do IO.println s!"{r.obligation.label}: {r.formatOutcome}"

/-- info: trueUnderUser: ✅ pass -/
#guard_msgs in
#eval runVerify copyNamedTruePgm withoutMono

/-! ## The default order verifies the user's function

Monomorphization keeps the user's name and names its own copies apart from it
(`NameMangling.choosePrefix`), and the user's function carries no copy mark, so the default
order encodes it from its own declaration: the postcondition that is false under the user's
body fails. -/

/-- info: falseUnderUser: ❌ fail -/
#guard_msgs in
#eval runVerify copyNamedPgm

/-! ## A phase only named like monomorphization does not turn decoding on

Whether a function is read as a copy depends on its factory entry, not on the phases that ran,
so a pipeline whose phase in that place is `assertNoPoly` renamed `monomorphizeFunctions`
still encodes the user's function from its own declaration. -/

/-- `assertNoPoly` under the name of monomorphization. -/
private def fakeMono : Core.PipelinePhase :=
  { assertNoPoly with phase := { assertNoPoly.phase with name := "monomorphizeFunctions" } }

private def withFakeMono : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) :=
  (Core.validatePipeline
    (replaceMono (Core.corePipelinePhases Core.VerifyOptions.quiet) fakeMono)).toOption

#guard withFakeMono.isSome

/-- info: falseUnderUser: ❌ fail -/
#guard_msgs in
#eval runVerify copyNamedPgm withFakeMono

/-! ## A variable named like a copy

The encoder reads only functions as copies and encodes a variable under its own name.
Monomorphization does not check variable names, so the default order verifies a procedure whose
parameter is named like the copy of integer addition; the postcondition, false for most values
of the parameter, is not proved. -/

private def copyNamedVarPgm :=
#strata
program Core;
procedure P(|$__mono#Int.Add#int| : int, out r : int)
spec { ensures [varLike]: r == 5; }
{ r := int.add(|$__mono#Int.Add#int|, 1); };
#end

/-- info: varLike: ❌ fail -/
#guard_msgs in
#eval runVerify copyNamedVarPgm

/-! ## Real copies are still read as their base functions

The default pipeline copies the polymorphic `update` and `select` to `$__mono#update#…` and
`$__mono#select#…`. By default `Map` is an uninterpreted sort and each copy is encoded as an
uninterpreted function with its own axioms, so the copy's name never matters. With the array
theory (`useArrayTheory`), the encoder sends the marked copies to SMT's `store` and `select`:
the queries mention no copy, and the postcondition is proved. -/

private def realCopyPgm :=
#strata
program Core;
procedure P(m : Map int int, k : int, j : int, out r : int)
spec { ensures [copyAtInt]: j == k || r == m[j]; }
{ r := m[k := 1][j]; };
#end

/-- info: copyAtInt: ✅ pass -/
#guard_msgs in
#eval runVerify realCopyPgm

/-- Verify `p` with the array theory, keeping the SMT queries, then print each verdict and
    whether a query names a copy of `select` or `update` rather than the theory operation. -/
private def runArrayTheory (p : StrataDDM.Program) : IO Unit :=
  IO.FS.withTempDir fun dir => do
    let options := { Core.VerifyOptions.quiet with useArrayTheory := true, vcDirectory := some dir }
    match ← (Core.verifyProgram (toCore p) (options := options)).toBaseIO with
    | .error e => IO.println s!"verify error: {e}"
    | .ok rs =>
      for r in rs do IO.println s!"{r.obligation.label}: {r.formatOutcome}"
      let mut queries := ""
      for f in ← dir.readDir do
        queries := queries ++ (← IO.FS.readFile f.path)
      let has (t : String) : Bool := (queries.splitOn t).length > 1
      IO.println s!"names a copy: {has "$__mono#select" || has "$__mono#update"}, \
        uses select: {has "(select "}, uses store: {has "(store "}"

/--
info: copyAtInt: ✅ pass
names a copy: false, uses select: true, uses store: true
-/
#guard_msgs in
#eval runArrayTheory realCopyPgm

/-! ## Unrolling bounded quantifiers

`UnrollBoundedQuantifiers` reads a sequence selector through name mangling. The user's
function below is named like the copy of `Sequence.select!` at `int`, and is constantly `7`,
so the assertion is false of a sequence whose elements are not `7`. With monomorphization
the name is rejected; without it, the polymorphic sequence operations cannot be encoded, so
the program is not verified either way. -/

private def copyNamedSelectPgm :=
#strata
program Core;
const s : Sequence int;
function |$__mono#Sequence.select!#int|(t : Sequence int, i : int) : int { 7 }
procedure P()
{
  assume [len]: Sequence.length(s) == 2;
  assert [selectLike]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==>
    |$__mono#Sequence.select!#int|(s, i) == Sequence.select!(s, i);
};
#end

/-- The default order without monomorphization, then unrolling, as the unrolling tests run it. -/
private def unrollingWithoutMono : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) :=
  (Core.ValidatedPipeline.ofList
    (replaceMono ((Core.corePipelinePhases Core.VerifyOptions.quiet).filter
        fun p => p.phase.name != "commonSubexprElim") assertNoPoly
      ++ [Core.passFunctionInlining, Core.passBetaReduce, Core.passUnrollBoundedQuantifiers,
          Core.passLambdaLift])
    ).toOption

#guard unrollingWithoutMono.isSome

/--
info: selectLike: 🚨 SMT Encoding Error! SMT encoding: unexpected type variable 'a' — the input to SMTEncoder should be fully monomorphic.
-/
#guard_msgs in
#eval runVerify copyNamedSelectPgm unrollingWithoutMono

end Strata
end
