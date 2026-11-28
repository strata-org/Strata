/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Transform.TerminationCheckPhase
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

/-! # Facts across `termCheck`

`termCheck` preserves `typeAnnotated`, as its contract declares. It does not preserve
`noPolymorphicFunctions`: its rank functions are generic in their datatype's type parameters,
and `monomorphizeFunctions`, which runs after it in every shipped order, specializes them. The
tests type check a program, run `termCheck` and then `monomorphizeFunctions` on the result, and
report both facts after each. An annotation that does not instantiate its callee's signature
is refused. The shipped orders that run `termCheck`
all validate. A caller's order that runs `monomorphizeFunctions` before `termCheck` and not after
it validates with `monomorphizeFunctions` inserted after `termCheck`, and a warning. -/

namespace Strata.TermCheckContractTest

/-- Type check `pgm`, run `termCheck` and then `monomorphizeFunctions`, and print both facts
    after each. -/
def report (pgm : Program) : IO Unit := do
  let p := (TransM.run Inhabited.default (translateProgram pgm)).fst
  let facts (q : Core.Program) : String :=
    s!"noPolymorphicFunctions={Core.Program.noPolymorphicFunctions q}, \
       typeAnnotated={Core.Program.allExprs Lambda.LExpr.fullyAnnotated q}"
  match ← (Core.runTransforms p [Core.typeCheckPipelinePhase]).toBaseIO with
  | .error e => IO.println s!"typeCheck error: {e.message}"
  | .ok (checked, _) =>
    IO.println s!"after typeCheck: {facts checked}"
    match ← (Core.runTransforms checked [Core.termCheckPipelinePhase]).toBaseIO with
    | .error e => IO.println s!"termCheck error: {e.message}"
    | .ok (out, _) =>
      IO.println s!"after termCheck: {facts out}"
      match ← (Core.runTransforms out [Strata.Core.passMonomorphizeFunctions]).toBaseIO with
      | .error e => IO.println s!"monomorphizeFunctions error: {e.message}"
      | .ok (mono, _) => IO.println s!"after monomorphizeFunctions: {facts mono}"

/-- A polymorphic datatype and a monomorphic function recursing structurally on it. -/
def monoFnPolyDatatype : Program :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function ilen (@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0 else int.add(1, ilen(MyList..tl(xs)))
};
#end

/--
info: [Strata.Core] Type checking succeeded.

after typeCheck: noPolymorphicFunctions=true, typeAnnotated=true
after termCheck: noPolymorphicFunctions=false, typeAnnotated=true
after monomorphizeFunctions: noPolymorphicFunctions=true, typeAnnotated=true
-/
#guard_msgs (whitespace := lax) in
#eval report monoFnPolyDatatype

/-- A polymorphic function recursing structurally on a polymorphic datatype. -/
def polyFnPolyDatatype : Program :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function plen<a> (@[cases] xs : MyList a) : int
{
  if MyList..isNil(xs) then 0 else int.add(1, plen(MyList..tl(xs)))
};
#end

/--
info: [Strata.Core] Type checking succeeded.

after typeCheck: noPolymorphicFunctions=false, typeAnnotated=true
after termCheck: noPolymorphicFunctions=false, typeAnnotated=true
after monomorphizeFunctions: noPolymorphicFunctions=true, typeAnnotated=true
-/
#guard_msgs (whitespace := lax) in
#eval report polyFnPolyDatatype

/-- A datatype declared after a first recursive function, used at a second instance by a
    later one: the rank function is specialized at `MyList int` and at `MyList Foo`. -/
def laterInstance : Program :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function ilen (@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0 else int.add(1, ilen(MyList..tl(xs)))
};

datatype Foo { FA(), FB(n: int) };

rec function flen (@[cases] xs : MyList Foo) : int
{
  if MyList..isNil(xs) then 0 else int.add(1, flen(MyList..tl(xs)))
};
#end

/-- Verify `pgm` with the default pipeline and print each obligation's verdict. -/
def verifyDefault (pgm : Program) : IO Unit := do
  let p := (TransM.run Inhabited.default (translateProgram pgm)).fst
  match ← (Strata.Core.verifyProgram p Core.VerifyOptions.quiet).toBaseIO with
  | .error e => IO.println s!"error: {e}"
  | .ok rs => for r in rs do
      let v := if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"
      IO.println s!"{r.obligation.label}: {v}"

/--
info: ilen_terminates_0: pass
ilen_body_calls_MyList..tl_0: pass
flen_terminates_0: pass
flen_body_calls_MyList..tl_0: pass
-/
#guard_msgs in
#eval verifyDefault laterInstance

/-- A field named `adtRank_int`: its destructor `MyList..adtRank_int` is a generated function
    named like the rank function of `MyList` with a suffix, and the program still verifies. -/
def rankNamedField : Program :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, adtRank_int: int, tl: MyList a) };

rec function ilen (@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0 else int.add(1, ilen(MyList..tl(xs)))
};
#end

/--
info: ilen_terminates_0: pass
ilen_body_calls_MyList..tl_0: pass
-/
#guard_msgs in
#eval verifyDefault rankNamedField

/-- `e` with every reference to `plen` annotated `bool → int`, a type that does not instantiate
    `plen`'s signature: the annotations are all present, but one is wrong. -/
partial def misannotate : Core.Expression.Expr → Core.Expression.Expr
  | .op m o ty => .op m o (if o.name == "plen" then some (.arrow .bool .int) else ty)
  | .app m f a => .app m (misannotate f) (misannotate a)
  | .abs m n ty e => .abs m n ty (misannotate e)
  | .quant m k n ty tr e => .quant m k n ty (misannotate tr) (misannotate e)
  | .ite m c t e => .ite m (misannotate c) (misannotate t) (misannotate e)
  | .eq m a b => .eq m (misannotate a) (misannotate b)
  | e => e

/-- `termCheck` alone on the type-checked `polyFnPolyDatatype` with `plen`'s annotations
    replaced by `misannotate`: its input is fully annotated, and `termCheck` refuses the call
    whose annotation does not instantiate `plen`'s signature rather than give its measure a
    type the lemma does not bind. -/
def reportMisannotated : IO Unit := do
  let p := (TransM.run Inhabited.default (translateProgram polyFnPolyDatatype)).fst
  match ← (Core.runTransforms p [Core.typeCheckPipelinePhase]).toBaseIO with
  | .error e => IO.println s!"typeCheck error: {e.message}"
  | .ok (checked, _) =>
    let bad : Core.Program := { decls := checked.decls.map fun
      | .recFuncBlock fs md =>
        .recFuncBlock (fs.map fun f => { f with body := f.body.map misannotate }) md
      | d => d }
    IO.println s!"input typeAnnotated={Core.Program.allExprs Lambda.LExpr.fullyAnnotated bad}"
    match ← (Core.runTransforms bad [Core.termCheckPipelinePhase]).toBaseIO with
    | .error e => IO.println s!"termCheck error: {e.message}"
    | .ok (out, _) =>
      IO.println s!"output typeAnnotated={Core.Program.allExprs Lambda.LExpr.fullyAnnotated out}"

/--
info: [Strata.Core] Type checking succeeded.

input typeAnnotated=true
termCheck error: termination checking 'plen': the type annotation of its call to 'plen' does not instantiate the signature of 'plen'
-/
#guard_msgs (whitespace := lax) in
#eval reportMisannotated

/-! ## The shipped orders that run `termCheck`

Each order is validated as its runner validates it. Dropping a fact from `termCheck`'s
`preserves` would make an order that relies on it be refused here. -/

/-- `ok`, or the reason validation refuses. -/
def verdict {σ : Core.ProgramFactSet} (r : Except String (Core.ValidatedPipeline σ)) : String :=
  match r with
  | .ok _ => "ok"
  | .error e => s!"refused: {e}"

/-- The default order under each verification-condition generator, MetaVerifier's order, and
    two production orders written out, one that runs `simplify` where the default order runs
    symbolic evaluation and one that runs symbolic evaluation, each validated from the entry
    facts it assumes. -/
def shippedOrderVerdicts : List (String × String) :=
  let q := Core.VerifyOptions.quiet
  let defaults := [("default", q), ("default wp", { q with vcgen := .wp }),
    ("default symexec never", { q with symExec := some .never }),
    ("default symexec always", { q with symExec := some .always }),
    ("default symexec pathsAbove 4", { q with symExec := some (.pathsAbove 4) })]
  let defaultVerdicts := defaults.map fun (n, o) =>
    (n, verdict (Core.validatePipeline (Core.corePipelinePhases o)))
  let metaOrder := [_root_.Core.typeCheckPipelinePhase q, _root_.Core.termCheckPipelinePhase,
    Strata.Core.passPrecondElim, Strata.Core.passInsertLoopInvariantAsserts,
    Strata.Core.passLoopElim] ++ _root_.Core.preSymbolicEvalPipelinePhases
  let simplifyOrder := [Strata.Core.passTypeCheck, Strata.Core.passTermCheck,
    Strata.Core.passPrecondElim,
    Strata.Core.passGenOpaqueTypeParams, Strata.Core.passMonomorphizeFunctions,
    Strata.Core.passSimplify, Strata.Core.passRecursiveAxioms,
    Core.ProgramFact.assertPhase .hasObligationForm,
    Core.ProgramFact.assertPhase .noProcedureContracts, Strata.Core.passFunctionInlining,
    Strata.Core.passBetaReduce, Strata.Core.passUnrollBoundedQuantifiers,
    Strata.Core.passFoldAxioms, Strata.Core.passEqualitySimplification, Strata.Core.passLambdaLift]
  let symEvalOrder := [Strata.Core.passTypeCheck, Strata.Core.passTermCheck,
    Strata.Core.passPrecondElim,
    Strata.Core.passGenOpaqueTypeParams, Strata.Core.passMonomorphizeFunctions,
    Strata.Core.passSymbolicEval, Strata.Core.passFunctionInlining, Strata.Core.passBetaReduce,
    Strata.Core.passUnrollBoundedQuantifiers, Strata.Core.passLambdaLift]
  defaultVerdicts ++
    [("MetaVerifier", verdict (Core.ValidatedPipeline.ofListFrom
        (factSet![.noCFGBodies, .noCalls]) metaOrder)),
     ("production order with simplify", verdict (Core.validatePipelineFrom
        (factSet![.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment, .noNondetGuards])
        simplifyOrder)),
     ("production order with symbolic evaluation", verdict (Core.validatePipelineFrom
        (factSet![.noCFGBodies, .noCalls, .noLoops, .noNondetGuards]) symEvalOrder))]

/-- A caller's order that monomorphizes before `termCheck`, and makes procedures monomorphic
    again after it. Nothing re-establishes `noPolymorphicFunctions` after `termCheck`, which
    `lambdaLift` requires. -/
def monoBeforeTermCheck : List Core.PipelinePhase :=
  [Strata.Core.passTypeCheck, Strata.Core.passGenOpaqueTypeParams,
    Strata.Core.passMonomorphizeFunctions, Strata.Core.passTermCheck, Strata.Core.passPrecondElim,
    Strata.Core.passGenOpaqueTypeParams, Strata.Core.passSimplify,
    Core.ProgramFact.assertPhase .hasObligationForm,
    Core.ProgramFact.assertPhase .noProcedureContracts, Strata.Core.passFunctionInlining,
    Strata.Core.passBetaReduce, Strata.Core.passLambdaLift]

/-- The entry facts the orders above assume. -/
def entryFacts : Core.ProgramFactSet :=
  factSet![.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment, .noNondetGuards]

/-- Print the warnings and the phases of `phases` as `validatePipelineFromRepairing` validates
    it from `σ`, or why it refuses. -/
def printRepaired (σ : Core.ProgramFactSet) (phases : List Core.PipelinePhase) : IO Unit :=
  match Core.validatePipelineFromRepairing σ phases with
  | .error e => IO.println s!"repaired: refused: {e}"
  | .ok (vp, notes) => do
    notes.forM IO.println
    IO.println s!"repaired: {",".intercalate (vp.phases.map Strata.Core.phaseName)}"

/-- `validatePipelineFromExact` refuses the order as given; `validatePipelineFromRepairing` runs
    `monomorphizeFunctions` again after `termCheck`, and warns. -/
def repairVerdicts : IO Unit := do
  let exact := Core.validatePipelineFromExact entryFacts monoBeforeTermCheck
  IO.println s!"as given: {verdict exact}"
  printRepaired entryFacts monoBeforeTermCheck

/--
info: as given: refused: phase #12 `lambdaLift` requires `noPolymorphicFunctions`, guaranteed by phase #3 `monomorphizeFunctions` but phase #4 `termCheck` afterwards does not preserve it
Warning: inserted phase `monomorphizeFunctions` after `genOpaqueTypeParams`: `termCheck` declares polymorphic rank functions, which a later phase needs specialized.
repaired: typeCheck,genOpaqueTypeParams,monomorphizeFunctions,termCheck,precondElim,genOpaqueTypeParams,monomorphizeFunctions,simplify,assertHasObligationForm,assertNoProcedureContracts,functionInlining,betaReduce,lambdaLift
-/
#guard_msgs (whitespace := lax) in
#eval repairVerdicts

/-- `monoBeforeTermCheck` with its first `monomorphizeFunctions` taken out, its
    `noPolymorphicFunctions` coming first from the entry facts, then from an `assert` phase. -/
def otherSources : IO Unit := do
  let noMono := monoBeforeTermCheck.filter
    (Strata.Core.phaseName · != Strata.Core.phaseName Strata.Core.passMonomorphizeFunctions)
  printRepaired (factSet![.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment,
    .noNondetGuards, .noPolymorphicFunctions]) noMono
  printRepaired entryFacts (noMono.take 2 ++
    Core.ProgramFact.assertPhase .noPolymorphicFunctions :: noMono.drop 2)

/--
info: Warning: inserted phase `monomorphizeFunctions` after `genOpaqueTypeParams`: `termCheck` declares polymorphic rank functions, which a later phase needs specialized.
repaired: typeCheck,genOpaqueTypeParams,termCheck,precondElim,genOpaqueTypeParams,monomorphizeFunctions,simplify,assertHasObligationForm,assertNoProcedureContracts,functionInlining,betaReduce,lambdaLift
Warning: inserted phase `monomorphizeFunctions` after `genOpaqueTypeParams`: `termCheck` declares polymorphic rank functions, which a later phase needs specialized.
repaired: typeCheck,genOpaqueTypeParams,assertNoPolymorphicFunctions,termCheck,precondElim,genOpaqueTypeParams,monomorphizeFunctions,simplify,assertHasObligationForm,assertNoProcedureContracts,functionInlining,betaReduce,lambdaLift
-/
#guard_msgs (whitespace := lax) in
#eval otherSources


/--
info: default: ok
default wp: ok
default symexec never: ok
default symexec always: ok
default symexec pathsAbove 4: ok
MetaVerifier: ok
production order with simplify: ok
production order with symbolic evaluation: ok
-/
#guard_msgs in
#eval shippedOrderVerdicts.forM fun (n, v) => IO.println s!"{n}: {v}"

/-- Verify `monoFnPolyDatatype` with `phases`, repaired, its entry facts checked by `assert`
    phases, and print the warnings and each obligation's verdict, or why the order or the run
    fails. -/
def verifyWith (phases : List Core.PipelinePhase) : IO Unit := do
  let entry := [Core.ProgramFact.assertPhase .noCFGBodies, Core.ProgramFact.assertPhase .noCalls,
    Core.ProgramFact.assertPhase .noLoops, Core.ProgramFact.assertPhase .staticSingleAssignment,
    Core.ProgramFact.assertPhase .noNondetGuards]
  match Core.validatePipelineRepairing (entry ++ phases) with
  | .error e => IO.println s!"refused: {e}"
  | .ok (vp, notes) =>
    notes.forM IO.println
    let p := (TransM.run Inhabited.default (translateProgram monoFnPolyDatatype)).fst
    match ← (Strata.Core.verifyProgram p Core.VerifyOptions.quiet
        (pipeline := some vp)).toBaseIO with
    | .error e => IO.println s!"error: {e}"
    | .ok rs => for r in rs do
        let v := if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"
        IO.println s!"{r.obligation.label}: {v}"

/-- `monoBeforeTermCheck` with `monomorphizeFunctions` written after the second
    `genOpaqueTypeParams`, where the repair puts it: it validates as given. -/
def monoAfterTermCheck : List Core.PipelinePhase :=
  [Strata.Core.passTypeCheck, Strata.Core.passGenOpaqueTypeParams,
    Strata.Core.passMonomorphizeFunctions, Strata.Core.passTermCheck, Strata.Core.passPrecondElim,
    Strata.Core.passGenOpaqueTypeParams, Strata.Core.passMonomorphizeFunctions,
    Strata.Core.passSimplify, Core.ProgramFact.assertPhase .hasObligationForm,
    Core.ProgramFact.assertPhase .noProcedureContracts, Strata.Core.passFunctionInlining,
    Strata.Core.passBetaReduce, Strata.Core.passLambdaLift]

-- The repaired order warns, and gives the verdicts of `monoAfterTermCheck`, which needs no
-- repair.
/--
info: Warning: inserted phase `monomorphizeFunctions` after `genOpaqueTypeParams`: `termCheck` declares polymorphic rank functions, which a later phase needs specialized.
[Strata.Core] Type checking succeeded.

ilen_terminates_0: pass
ilen_body_calls_MyList..tl_0: pass
-/
#guard_msgs (whitespace := lax) in
#eval verifyWith monoBeforeTermCheck

/--
info: [Strata.Core] Type checking succeeded.

ilen_terminates_0: pass
ilen_body_calls_MyList..tl_0: pass
-/
#guard_msgs (whitespace := lax) in
#eval verifyWith monoAfterTermCheck

/-- `validatePipelineFromExact` returns the phases it is given: here `monoAfterTermCheck`, which
    needs no repair. `validatePipelineFrom` repairs `monoBeforeTermCheck` into the same order. -/
def exactPhases : String :=
  let names (r : Except String (Core.ValidatedPipeline entryFacts)) : List String :=
    match r with
    | .ok vp => vp.phases.map Strata.Core.phaseName
    | .error _ => []
  let given := monoAfterTermCheck.map Strata.Core.phaseName
  s!"exact keeps the order: {names (Core.validatePipelineFromExact entryFacts monoAfterTermCheck)
    == given}, repaired order is it: {names (Core.validatePipelineFrom entryFacts
    monoBeforeTermCheck) == given}"

/-- info: exact keeps the order: true, repaired order is it: true -/
#guard_msgs in
#eval IO.println exactPhases

end Strata.TermCheckContractTest

end
