/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import all Strata.Transform.UnrollBoundedQuantifiers
import StrataDDM.Integration.Lean
import StrataDDM.Integration.Lean.HashCommands

/-! # Soundness of `unrollBoundedQuantifiers` with respect to declaration order

A lemma or a procedure is checked under the axioms declared before it. Goals that only
axioms declared after them prove are verified with the phases of a pipeline for
programs whose checks are top-level declarations, with and without unrolling.
Unrolling must not prove them. -/

meta section
namespace Strata

private def opts : Core.VerifyOptions := Core.VerifyOptions.quiet

/-- The phases of a pipeline for programs whose checks are top-level lemmas, with or
    without unrolling. The entry facts the later phases require are asserted first. -/
private def lemmaPhases (unroll : Bool) : List Core.PipelinePhase :=
  [Core.assertPhase .noCFGBodies, Core.assertPhase .noCalls, Core.assertPhase .noLoops,
   Core.assertPhase .staticSingleAssignment, Core.assertPhase .noNondetGuards,
   Core.assertPhase .wellFormedCalls, Core.passTermCheck, Core.passPrecondElim,
   Core.passGenOpaqueTypeParams, Core.passTypeCheck opts, Core.passMonomorphizeFunctions,
   Core.passSimplify, Core.passRecursiveAxioms opts, Core.assertPhase .hasObligationForm,
   Core.assertPhase .noProcedureContracts, Core.passFunctionInlining, Core.passBetaReduce]
  ++ (if unroll then [Core.passUnrollBoundedQuantifiers] else [])
  ++ [Core.passFoldAxioms, Core.passEqualitySimplification]

private def lemmaPipeline (unroll : Bool) :
    Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) :=
  (Core.ValidatedPipeline.ofList (lemmaPhases unroll)).toOption

#guard (lemmaPipeline true).isSome && (lemmaPipeline false).isSome

private def toCore (pgm : StrataDDM.Program) : Core.Program :=
  TransM.run Inhabited.default (translateProgram pgm) |>.fst

private def initState : Core.Transform.CoreTransformState :=
  { Core.Transform.CoreTransformState.emp with factory := Core.Factory }

/-- Run the phases through unrolling and print the declarations `render` renders. -/
private def printUnrolled (pgm : StrataDDM.Program) (render : Core.Decl → Option String) :
    IO Unit := do
  let name := Core.unrollBoundedQuantifiersPipelinePhase.phase.name
  let phases := (lemmaPhases true).take
    ((lemmaPhases true).findIdx (fun p => p.phase.name == name) + 1)
  match ← (Core.runTransforms (toCore pgm) phases (initState := initState)).toBaseIO with
  | .error e => IO.println s!"{e}"
  | .ok (p, _) =>
    for d in p.stripMetaData.decls do
      if let some str := render d then IO.println str

/-- The lemmas after the phases through unrolling. -/
private def unrolledLemmas (pgm : StrataDDM.Program) : IO Unit :=
  printUnrolled pgm fun
    | .lemma l _ => some s!"{l.name}: {Std.format l.e}"
    | _ => none

/-! ## A lemma is checked under the axioms before it

The axioms pinning the count come after the lemma, so its quantifier stays. -/

def laterAxiomPgm :=
#strata
program Core;

const s : Sequence int;
lemma [l]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> Sequence.select!(s, i) == 1;
axiom [len]: Sequence.length(s) == 1;
axiom [e0]: Sequence.select!(s, 0) == 1;
#end

/-- info: l: forall i : int :: int.le(0, i) && int.lt(i, Sequence.length(s)) ==> Sequence.select!(s, i) == 1 -/
#guard_msgs in
#eval unrolledLemmas laterAxiomPgm

/--
info:
Obligation: l
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify laterAxiomPgm (options := opts) (pipeline := lemmaPipeline false)

/--
info:
Obligation: l
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify laterAxiomPgm (options := opts) (pipeline := lemmaPipeline true)

/-! ## A procedure is checked under the axioms before it

The axioms pinning the count and the element come after the procedure, so its goal
keeps its quantifier and does not verify. -/

def procLaterAxiomPgm :=
#strata
program Core;

const s : Sequence int;
procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> Sequence.select!(s, i) == 1;
};
axiom [len]: Sequence.length(s) == 1;
axiom [e0]: Sequence.select!(s, 0) == 1;
#end

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify procLaterAxiomPgm (options := opts) (pipeline := lemmaPipeline false)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify procLaterAxiomPgm (options := opts) (pipeline := lemmaPipeline true)

/-! The same goal with the axioms before the procedure unrolls and verifies, so a
procedure goal still sees the axioms declared before it. -/

def procEarlierAxiomPgm :=
#strata
program Core;

const s : Sequence int;
axiom [len]: Sequence.length(s) == 1;
axiom [e0]: Sequence.select!(s, 0) == 1;
procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> Sequence.select!(s, i) == 1;
};
#end

/-- The `assert` and `cover` conditions of a procedure body, as `label: condition`. -/
private partial def goalLines : List Core.Statement → List String
  | [] => []
  | s :: rest =>
    let here := match s with
      | .cmd (.cmd (.assert l e _)) | .cmd (.cmd (.cover l e _)) => [s!"{l}: {Std.format e}"]
      | .block _ ss _ => goalLines ss
      | .ite _ tss ess _ => goalLines tss ++ goalLines ess
      | _ => []
    here ++ goalLines rest

/-- The procedures' goals after the phases through unrolling. -/
private def unrolledProcs (pgm : StrataDDM.Program) : IO Unit :=
  printUnrolled pgm fun
    | .proc q _ => match q.body with
      | .structured ss => some ("\n".intercalate (goalLines ss))
      | .cfg _ => none
    | _ => none

/-- info: a: true -/
#guard_msgs in
#eval unrolledProcs procEarlierAxiomPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify procEarlierAxiomPgm (options := opts) (pipeline := lemmaPipeline true)

/-! ## A program's datatype declared before the goal

The tester reduces only with the datatype's functions in the factory, which the pass
adds for the datatypes declared before the goal, so the goal unrolls to `true`. A goal
cannot mention a datatype declared after it: the parser rejects the undeclared type. -/

def datatypeBeforePgm :=
#strata
program Core;

datatype Color { Red(), Green() };
const s : Sequence Color;
axiom [len]: Sequence.length(s) == 1;
axiom [e0]: Sequence.select!(s, 0) == Red();
procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> Color..isRed(Sequence.select!(s, i));
};
#end

/-- info: a: true -/
#guard_msgs in
#eval unrolledProcs datatypeBeforePgm

/-! ## Element facts from later axioms

The length axiom comes before the procedure and the element axiom after it, so the
count resolves and the element does not: the goal unrolls to one instance that keeps
`Sequence.select!(s, 0)`, and does not verify. -/

def splitAxiomPgm :=
#strata
program Core;

const s : Sequence int;
axiom [len]: Sequence.length(s) == 1;
procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> Sequence.select!(s, i) == 1;
};
axiom [e0]: Sequence.select!(s, 0) == 1;
#end

/-- info: a: int.lt(0, Sequence.length(s)) ==> Sequence.select!(s, 0) == 1 -/
#guard_msgs in
#eval unrolledProcs splitAxiomPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify splitAxiomPgm (options := opts) (pipeline := lemmaPipeline true)

/-! An assumption in the body gives the count, and the element axiom comes after the
procedure, so the element stays unresolved. -/

def assumeAndLaterAxiomPgm :=
#strata
program Core;

const s : Sequence int;
procedure P()
{
  assume [len]: Sequence.length(s) == 1;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> Sequence.select!(s, i) == 1;
};
axiom [e0]: Sequence.select!(s, 0) == 1;
#end

/-- info: a: int.lt(0, Sequence.length(s)) ==> Sequence.select!(s, 0) == 1 -/
#guard_msgs in
#eval unrolledProcs assumeAndLaterAxiomPgm

/-! A `cover` before the axioms that would make it reachable keeps its quantifier. -/

def coverLaterAxiomPgm :=
#strata
program Core;

const s : Sequence int;
procedure P()
{
  cover [c]: exists i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) && Sequence.select!(s, i) == 1;
};
axiom [len]: Sequence.length(s) == 1;
axiom [e0]: Sequence.select!(s, 0) == 1;
#end

/-- info: c: exists i : int :: int.le(0, i) && int.lt(i, Sequence.length(s)) && Sequence.select!(s, i) == 1 -/
#guard_msgs in
#eval unrolledProcs coverLaterAxiomPgm

/-! A builtin fact outranks a program axiom naming the same term: the factory states
`length(empty()) == 0`, so the count is 0 and the goal holds vacuously, despite the
program's contradicting axiom. -/

def builtinPrecedencePgm :=
#strata
program Core;

axiom [bad]: Sequence.length(Sequence.empty<int>()) == 3;
procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(Sequence.empty<int>()))) ==> int.lt(i, 0);
};
#end

/-- info: a: true -/
#guard_msgs in
#eval unrolledProcs builtinPrecedencePgm

/-! ## The WP pipeline

With `--vcgen wp`, procedures and the top-level axioms after them reach the pass in
declaration order, so this is the path where a later axiom sits next to a goal. -/

private def wpOpts : Core.VerifyOptions := { opts with vcgen := .wp }

private def wpPipeline (unroll : Bool) :
    Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) :=
  (Core.validatePipeline (Core.corePipelinePhases wpOpts
    ++ (if unroll then [Core.passUnrollBoundedQuantifiers] else []))).toOption

#guard (wpPipeline true).isSome && (wpPipeline false).isSome

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify procLaterAxiomPgm (options := wpOpts) (pipeline := wpPipeline false)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify procLaterAxiomPgm (options := wpOpts) (pipeline := wpPipeline true)

/-! ## A bound that mentions an outer bound variable

The inner bound `(λx. 2)(m)` mentions the outer binder `m`. Normalizing it would give 2,
but normalization substitutes without lifting bound variables, so the pass leaves such
a bound unresolved and the obligation as it arrived. The term is built directly, since
beta reduction before the pass would remove the redex. -/

private def lcAtProbe : String :=
  let int : Lambda.LMonoTy := .int
  let bin (f : Lambda.LExpr Core.CoreLParams.mono) (a b : Lambda.LExpr Core.CoreLParams.mono) :=
    Lambda.LExpr.app () (.app () f a) b
  let le := (Lambda.intLeFunc (T := Core.CoreLParams)).opExpr
  let lt := (Lambda.intLtFunc (T := Core.CoreLParams)).opExpr
  let andOp := (Lambda.boolAndFunc (T := Core.CoreLParams)).opExpr
  let impl := (Lambda.boolImpliesFunc (T := Core.CoreLParams)).opExpr
  let zero : Lambda.LExpr Core.CoreLParams.mono := .const () (.intConst 0)
  let i : Lambda.LExpr Core.CoreLParams.mono := .bvar () 0
  let bound : Lambda.LExpr Core.CoreLParams.mono :=
    .app () (.abs () "x" (some int) (.const () (.intConst 2))) (.bvar () 1)
  let inner := Lambda.LExpr.all () "i" (some int)
    (bin impl (bin andOp (bin le zero i) (bin lt i bound)) (bin lt i (.const () (.intConst 5))))
  let goal := Lambda.LExpr.exist () "m" (some int) inner
  let env : Core.UnrollBoundedQuantifiers.UEnv := ⟨[], [], Core.Factory⟩
  let (goal', c) := Core.UnrollBoundedQuantifiers.processExpr env goal
  s!"unchanged: {goal' == goal}, unrolled: {c.get .unrolled}, unresolved: {c.get .unresolved}"

/-- info: unchanged: true, unrolled: 0, unresolved: 1 -/
#guard_msgs in
#eval IO.println lcAtProbe

/-! ## A fact resolves only the selector it states

`Sequence.select` and `Sequence.select!` are separate functions of Core's factory,
whose axioms do not relate them. A fact about `select` therefore leaves an occurrence
of `select!` in place, in range and out of range, and these goals are unknown. A
factory axiom relating the two selectors would make them provable; these tests then
change with it. -/

def crossSelectorInRangePgm :=
#strata
program Core;

const s : Sequence int;
axiom [len]: Sequence.length(s) == 1;
axiom [e0]: Sequence.select(s, 0) == 1;
procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> Sequence.select!(s, i) == 1;
};
#end

/-- info: a: int.lt(0, Sequence.length(s)) ==> Sequence.select!(s, 0) == 1 -/
#guard_msgs in
#eval unrolledProcs crossSelectorInRangePgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify crossSelectorInRangePgm (options := opts) (pipeline := lemmaPipeline true)

/-! The fact names an index past the length. Precondition elimination does not check
an axiom's calls, so no obligation reports the out-of-range `select(s, 5)`. -/

def crossSelectorOutOfRangePgm :=
#strata
program Core;

const s : Sequence int;
axiom [len]: Sequence.length(s) == 1;
axiom [e5]: Sequence.select(s, 5) == 1;
procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.le(i, 5)) ==> (i == 5 ==> Sequence.select!(s, i) == 1);
};
#end

/-- info: a: Sequence.select!(s, 5) == 1 -/
#guard_msgs in
#eval unrolledProcs crossSelectorOutOfRangePgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify crossSelectorOutOfRangePgm (options := opts) (pipeline := lemmaPipeline true)

/-! The reverse direction out of range, as a lemma: a fact about `select!` at index 5
leaves the lemma's `select(s, 5)` in place, and its bounds check stays unknown. -/

def crossSelectorBangOutOfRangePgm :=
#strata
program Core;

const s : Sequence int;
axiom [len]: Sequence.length(s) == 2;
axiom [e5]: Sequence.select!(s, 5) == 1;
lemma [l]: forall i : int :: (int.le(0, i) && int.le(i, 5)) ==> (i == 5 ==> Sequence.select(s, i) == 1);
#end

/--
info: l_calls_Sequence.select_0: int.lt(5, Sequence.length(s))
l: Sequence.select(s, 5) == 1
-/
#guard_msgs in
#eval unrolledLemmas crossSelectorBangOutOfRangePgm

/--
info:
Obligation: l_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: l
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify crossSelectorBangOutOfRangePgm (options := opts) (pipeline := lemmaPipeline true)

end Strata
