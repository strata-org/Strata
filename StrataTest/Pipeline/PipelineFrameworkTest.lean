/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.ProgramFactSet
import Strata.Languages.Core.ProgramFactSetProps
import Strata.Languages.Core.PipelinePhaseProps
import Strata.Languages.Core
-- The `#eval`s below run the validator on production phases, which needs the
-- compiled code of the modules those phases are defined in.
meta import Strata.Languages.Core
meta import Strata.Languages.Core.PipelinePhase
meta import Strata.Languages.Core.Verifier
meta import Strata.Transform.CallElim
meta import Strata.Transform.LoopElim
meta import Strata.Transform.InsertLoopInvariantAsserts
meta import Strata.Transform.FilterProcedures
meta import Strata.Transform.PrecondElim
meta import Strata.Transform.ProcedureInlining
meta import Strata.Transform.TerminationCheck
meta import Strata.Transform.CommonSubexprElim
meta import Strata.Transform.FunctionInlining
meta import Strata.Transform.UnrollBoundedQuantifiers
import Strata.Languages.Core.Verifier
import Strata.Transform.CallElim
import Strata.Transform.LoopElim
import Strata.Transform.InsertLoopInvariantAsserts
import Strata.Transform.FilterProcedures
import Strata.Transform.PrecondElim
import Strata.Transform.ProcedureInlining
import Strata.Transform.TerminationCheck
import Strata.Transform.CommonSubexprElim
import Strata.Transform.FunctionInlining
import Strata.Transform.UnrollBoundedQuantifiers
import Strata.Transform.MonomorphizeProcedures
import Strata.Languages.Core.ObligationExtraction

/-! ## Pipeline framework tests

Verifies that `ValidatedPipeline.ofList` accepts well-composed pipelines,
rejects ill-composed ones, and explains the rejection. Each `#guard_msgs`
block fails the build if its pinned message diverges. -/

open Core
open Strata.Pipeline (applyPhase)

/-! ### Fact sets are canonical by construction -/

/-- Extensionally equal fact sets are *equal*. Pipeline validation does not
    need this, only inclusion; it is what makes equations between fact sets
    provable. -/
example (σ₁ σ₂ : ProgramFactSet) (h : ∀ f, f ∈ σ₁ ↔ f ∈ σ₂) : σ₁ = σ₂ :=
  ProgramFactSet.ext_of_mem_iff h

/-- Fact sets are duplicate-free, whichever constructor built them. -/
example (σ : ProgramFactSet) : σ.facts.Nodup := σ.nodup

/-- The two constructors agree wherever both apply. -/
example (σ : ProgramFactSet) : ProgramFactSet.ofList σ.facts = σ :=
  Strata.Pipeline.factSetOfList_factsOf σ

/--
error: fact set lists a fact more than once; fact sets must be written in `ProgramFact.all` declaration order without duplicates. Write factSet![.noCFGBodies] instead. For a list that is only known at runtime, use `ofList`, which sorts it and produces the proof.
-/
#guard_msgs in
def duplicatedFacts : ProgramFactSet := factSet![.noCFGBodies, .noCFGBodies]

/--
error: fact set lists facts out of order; fact sets must be written in `ProgramFact.all` declaration order without duplicates. Write factSet![.noCFGBodies, .noLoops] instead. For a list that is only known at runtime, use `ofList`, which sorts it and produces the proof.
-/
#guard_msgs in
def misorderedFacts : ProgramFactSet := factSet![.noLoops, .noCFGBodies]

/--
error: could not synthesize default value for field 'canonical' of 'Strata.Pipeline.CanonicalFactList' using tactics
---
error: fact set is not statically known, so `canon_facts` cannot check that it is in canonical order. Use `ofList`, which sorts the list at runtime and produces the proof, or write a concrete literal here.
-/
#guard_msgs in
def dynamicFacts (l : List ProgramFact) : ProgramFactSet := { facts := l }

/-- info: [Core.ProgramFact.noCFGBodies, Core.ProgramFact.noLoops] -/
#guard_msgs in
#eval (ProgramFactSet.ofList [.noLoops, .noCFGBodies, .noLoops]).facts

/-- Dropping an unpreserved fact yields the empty set, not a stale one.
    Closed by `rfl`, so this also pins that the fact index reduces. -/
example : applyPhase (factSet![] : ProgramFactSet) factSet![] factSet![.noCFGBodies]
    = factSet![] := by rfl

/-! ### What the facts mean on a program -/

private def trueExpr : Expression.Expr := Transform.createFvar "b"

private def intTy : Expression.Ty := Imperative.HasInt.intTy

/-- The facts of a fact set on one line, so an expectation stays readable as
    the fact list grows. -/
private def factNames (σ : ProgramFactSet) : String :=
  if σ.facts.isEmpty then "(none)" else ", ".intercalate (σ.facts.map (·.name))

/-! The three set operations walk the vocabulary and the two sets together
rather than testing membership per fact. These pin that the walks agree with the
specification they replace: a union holds the facts of either set in canonical
order, an intersection those of both, and inclusion is decided by the sublist
walk. -/

/-- info: noCFGBodies, noLoops, noBetaRedexes -/
#guard_msgs in
#eval IO.println (factNames (Strata.Pipeline.factSetUnion factSet![.noCFGBodies, .noBetaRedexes]
                                          factSet![.noLoops, .noBetaRedexes]))

/-- info: noBetaRedexes -/
#guard_msgs in
#eval IO.println (factNames (Strata.Pipeline.factSetInter factSet![.noCFGBodies, .noBetaRedexes]
                                          factSet![.noLoops, .noBetaRedexes]))

/-- info: true, false -/
#guard_msgs in
#eval IO.println s!"{decide (factSet![.noCalls, .noLoops] ⊑ ProgramFactSet.all)}, \
{decide (ProgramFactSet.all ⊑ factSet![.noCalls])}"

/-- The facts whose check accepts `p`. A fact with no check cannot appear,
    which is the honest report: nothing here can decide it. The framework
    itself has no such function — a fact is a `Prop` there — so the tests
    assemble it from `ProgramFact.all`. -/
private def ofProgramFacts (p : Program) : ProgramFactSet :=
  ProgramFactSet.ofList (ProgramFact.all.filter fun f =>
    match f.check? with
    | some c => c p
    | none => false)

/-! A polymorphic procedure and a polymorphic function each drop their fact,
whether the function is declared at top level or inside a body — which is what
makes lifting neutral for `noPolymorphicFunctions`. -/

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts { decls :=
  [.proc { (default : Procedure) with
             header := { (default : Procedure.Header) with typeArgs := ["a"] },
             body := .structured [] } default] }))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts { decls :=
  [.func { (default : Function) with typeArgs := ["a"] } default] }))

/-- Wrap `body` as the single procedure of a program. -/
private def progOf (body : List Statement) : Program :=
  { decls := [.proc { (default : Procedure) with body := .structured body } default] }

/-- A loop carrying both an invariant and a measure, with a call nested two
    levels down inside its body. -/
private def loadedProgram : Program :=
  progOf [.loop .nondet (some trueExpr) [("inv", trueExpr)]
    [.block "b" [.ite .nondet [Statement.call "f" [] {}] [] {}] {}] {}]

/-- info: noCFGBodies, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts loadedProgram))

/-- info: noCFGBodies, noCalls, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (progOf [.loop .nondet none [] [] {}])))

/-! A loop nested anywhere drops the fact: inside another loop's body, inside a
block, or inside either branch of an `ite`. -/

/-- info: noCFGBodies, noCalls, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (progOf
  [.loop (.det trueExpr) none [] [.block "b" [.loop (.det trueExpr) none [] [] {}] {}] {}])))

/-- info: noCFGBodies, noCalls, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (progOf
  [.ite (.det trueExpr) [] [.loop (.det trueExpr) none [] [] {}] {}])))

/-- info: noCFGBodies, noCalls, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (progOf
  [.ite (.det trueExpr) [.loop (.det trueExpr) none [] [] {}] [] {}])))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts { decls := [] }))

/-- info: noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts { decls := [.proc { (default : Procedure) with body := .cfg { entry := "entry", blocks := [("entry", { cmds := [.call "f" [] {}], transfer := .finish {} })] } } default] }))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (progOf [Statement.set "x" trueExpr {}])))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (progOf [Statement.havoc "x" {}])))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (progOf [Statement.init "x" intTy .nondet {}])))

/-- info: noCFGBodies, noCalls, noLoopInvariants, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts (progOf [.loop (.det trueExpr) (some trueExpr) [] [] {}])))
private def redexExpr : Expression.Expr :=
  .app () (.abs () "x" none (.bvar () 0)) trueExpr

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (progOf [Statement.assume "a" redexExpr {}])))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts { decls := [.distinct "d" [redexExpr] default] }))
/-- A local function whose body is `e` and which is otherwise trivial. -/
private def localFuncDecl (e : Expression.Expr) : Statement :=
  .funcDecl { name := "f", inputs := .empty, output := intTy,
              body := some e } {}

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (progOf [localFuncDecl redexExpr])))

/-! `noPolymorphicFunctions` counts a function declared inside a procedure body,
not only a top-level one. -/

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noPolymorphicProcedures -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (progOf
  [.funcDecl { name := "f", typeArgs := ["a"], inputs := .empty, output := intTy,
               body := some trueExpr } {}])))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts (progOf [.funcDecl { name := "f", inputs := .empty, output := intTy, body := some trueExpr, measure := some redexExpr } {}])))
#guard
  let f : Statement :=
    .funcDecl { name := "f", inputs := .empty, output := intTy,
                body := some (Transform.createFvar "body"),
                axioms := [Transform.createFvar "ax"],
                preconditions := [{ expr := Transform.createFvar "pre", md := default }],
                measure := some (Transform.createFvar "meas") } {}
  Statements.allExprs [f] ==
    [Transform.createFvar "body", Transform.createFvar "ax",
     Transform.createFvar "pre", Transform.createFvar "meas"]

/-- info: noCFGBodies, noCalls, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts (progOf [.loop (.det trueExpr) none [] [localFuncDecl redexExpr] {}])))

/-- info: noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts { decls := [.proc { (default : Procedure) with body := .cfg { entry := "entry", blocks := [("entry", { cmds := [], transfer := .condGoto redexExpr "t" "f" {} })] } } default] }))

/-! A CFG block's commands are reached as well as its transfer: `Body.statements`
flattens the blocks, so an expression inside a command is seen by the same walk
that sees a structured body's. -/

/-- info: noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts { decls := [.proc { (default : Procedure) with body := .cfg { entry := "entry", blocks := [("entry", { cmds := [.cmd (.assert "a" redexExpr {})], transfer := .finish {} })] } } default] }))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noNondetGuards, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts (progOf [.funcDecl { name := "f", inputs := .empty, output := intTy, body := some trueExpr, preconditions := [{ expr := trueExpr, md := default }] } {}])))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts { decls := [.proc { (default : Procedure) with spec := { preconditions := .empty, postconditions := .ofList [("post", { expr := redexExpr })] } } default] }))
/-- A program whose single statement assumes `e`. -/
private def assumeProg (e : Expression.Expr) : Program :=
  progOf [Statement.assume "a" e {}]

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (assumeProg (.ite () trueExpr redexExpr trueExpr))))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts (assumeProg (.app () (Transform.createFvar "f") redexExpr))))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts (assumeProg (.app () (.app () (Transform.createFvar "f") redexExpr) trueExpr))))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts (assumeProg (.quant () .all "x" none trueExpr redexExpr))))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts (assumeProg (.quant () .exist "x" none redexExpr trueExpr))))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (assumeProg (.abs () "x" none redexExpr))))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (factNames (ofProgramFacts (assumeProg (.eq () trueExpr redexExpr))))

/-- info: noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions -/
#guard_msgs in
#eval IO.println
  (factNames (ofProgramFacts (assumeProg (.abs () "x" none (.app () (Transform.createFvar "f") trueExpr)))))
example (f : ProgramFact) (c : Program → Bool) (hc : f.check? = some c) (p : Program)
    (h : c p = true) : f.holds p := (ProgramFact.holds_iff_check hc p).mpr h

example (f : ProgramFact) (c : Program → Bool) (hc : f.check? = some c) (p : Program)
    (h : f.holds p) : c p = true := (ProgramFact.holds_iff_check hc p).mp h

example : ProgramFact.noCFGBodies.check?.isSome = true := by decide

/-! ### What the back end needs at exit -/

/-- info: noCFGBodies, noCalls, noLoops, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated -/
#guard_msgs in
#eval IO.println (factNames backEndRequiredFacts)

/-- info: delivered -/
#guard_msgs in
#eval IO.println (match coreValidatedPipeline with | .ok _ => "delivered" | .error e => e)

/-! ### Proofs, deferred -/

/-- Nothing is owed today: a deferred obligation is satisfiable even for a
    claim that is false. This is the cost of `proveAllPhaseContracts` being
    `false`, stated as a test rather than as a comment. -/
example : PhaseContractObligation false False := PhaseContractObligation.deferred (by decide)

/-- A phase that claims its contract cannot cheat the same way. -/
example : PhaseContractObligation true False → False := by
  simp [PhaseContractObligation, proveAllPhaseContracts]

/-- And it can discharge the obligation from a proof of the claim. -/
example (P : Prop) (h : P) : PhaseContractObligation true P := PhaseContractObligation.intro h

/-! ### Validation and diagnostics -/

private def testNoop : PipelinePhase where
  transform := fun p => return (false, p)
  phase := { name := "testNoop" }

private def testRequirer : PipelinePhase where
  transform := fun p => return (false, p)
  phase := { name := "testRequirer" }
  requires := factSet![.noCFGBodies]

/-- Requires two facts, so the diagnostic has to report one per line rather
    than in the single-fact phrasing. -/
private def testMultiRequirer : PipelinePhase where
  transform := fun p => return (false, p)
  phase := { name := "testMultiRequirer" }
  requires := factSet![.noCFGBodies, .noLoops]

/-- A phase that genuinely establishes `noCFGBodies`, by replacing the
    program with an empty one — a program with no declarations vacuously
    has no CFG bodies. Useless as a transform, but it is a phase whose
    `establishes_ok` obligation is discharged honestly rather than
    deferred, which is what lets the established-then-invalidated
    diagnostics be tested. -/
private def testEstablisher : PipelinePhase where
  transform := fun _ => return (true, { decls := [] })
  phase := { name := "testEstablisher" }
  establishes := factSet![.noCFGBodies]
  provesContract := true
  establishes_ok := PhaseContractObligation.intro (by
    intro p s b p' s' h f hf
    simp [ExceptT.run, ExceptT.pure, ExceptT.mk, StateT.pure, Pure.pure] at h
    injection h with hok _
    injection hok with hbp
    injection hbp with _ hp'
    subst hp'
    have hf' : f = ProgramFact.noCFGBodies := List.mem_singleton.mp hf
    subst hf'
    exact (ProgramFact.holds_iff_check (c := Program.allStructured) rfl _).mpr (by decide))
  preserves_ok := PhaseContractObligation.intro (by intro f hf; cases hf)

/-- A phase that carries `noCFGBodies` through, so a fact established
    upstream is still available to a requirer downstream of it. -/
private def testPreserver : PipelinePhase where
  transform := fun p => return (false, p)
  phase := { name := "testPreserver" }
  preserves := factSet![.noCFGBodies]
  provesContract := true
  establishes_ok := PhaseContractObligation.intro (by
    intro _ _ _ _ _ _ f hf; cases hf)
  preserves_ok := PhaseContractObligation.intro (by
    intro f _ p s hp b p' s' hrun
    simp [ExceptT.run, ExceptT.pure, ExceptT.mk, StateT.pure, Pure.pure] at hrun
    injection hrun with hok _
    injection hok with hbp
    injection hbp with _ hp'
    subst hp'
    exact hp)

/-- Render a validation outcome compactly for `#guard_msgs`. -/
private def describe {σ₀ : ProgramFactSet}
    (r : Except String (ValidatedPipeline σ₀)) : String :=
  match r with
  | .ok vp =>
      s!"accepted; phases {vp.phases.map (·.phase.name)}; exit {factNames vp.establishes}"
  | .error e => s!"rejected: {e}"

/-- Print a validation outcome. -/
private def report {σ₀ : ProgramFactSet}
    (r : Except String (ValidatedPipeline σ₀)) : IO Unit :=
  IO.println (describe r)

/-- Validate `phases` on a program nothing is known about, and print the
    outcome. -/
private def check (phases : List PipelinePhase) : IO Unit :=
  report (ValidatedPipeline.ofList phases)

/-- Validate `phases` against facts known on entry, and print the outcome. -/
private def checkFrom (σ : ProgramFactSet) (phases : List PipelinePhase) : IO Unit :=
  report (ValidatedPipeline.ofListFrom σ phases)

/-- Validate `phases`, and that they deliver what `consumer` needs, and print
    the outcome. -/
private def checkDelivering (consumer : String) (needed : ProgramFactSet)
    (phases : List PipelinePhase) : IO Unit :=
  report (ValidatedPipeline.ofListDelivering consumer needed phases)

/-- info: rejected: phase #2 `the SMT conversion` requires `noBetaRedexes` but no preceding phase guarantees it -/
#guard_msgs in
#eval checkDelivering "the SMT conversion" factSet![.noBetaRedexes] [testNoop]

/-- info: rejected: phase #3 `the SMT conversion` requires `noCFGBodies`, guaranteed by phase #1 `testEstablisher` but phase #2 `testNoop` afterwards does not preserve it -/
#guard_msgs in
#eval checkDelivering "the SMT conversion" factSet![.noCFGBodies] [testEstablisher, testNoop]

/-- info: accepted; phases [testEstablisher]; exit noCFGBodies -/
#guard_msgs in
#eval checkDelivering "the SMT conversion" factSet![.noCFGBodies] [testEstablisher]

/-- info: accepted; phases []; exit (none) -/
#guard_msgs in
#eval check []

/-- info: accepted; phases [testEstablisher]; exit noCFGBodies -/
#guard_msgs in
#eval check [testEstablisher]

/-- info: accepted; phases [testRequirer]; exit (none) -/
#guard_msgs in
#eval checkFrom factSet![.noCFGBodies] [testRequirer]

/-- info: accepted; phases [testEstablisher, testRequirer]; exit (none) -/
#guard_msgs in
#eval check [testEstablisher, testRequirer]

/-- info: accepted; phases [testRequirer, testNoop, testNoop]; exit (none) -/
#guard_msgs in
#eval checkFrom factSet![.noCFGBodies] [testRequirer, testNoop, testNoop]

/-- info: accepted; phases [testEstablisher, testPreserver, testRequirer]; exit (none) -/
#guard_msgs in
#eval check [testEstablisher, testPreserver, testRequirer]

/-! #### Diagnostics -/

/-- info: rejected: phase #1 `testRequirer` requires `noCFGBodies` but no preceding phase guarantees it -/
#guard_msgs in
#eval check [testRequirer]

/-- info: rejected: phase #2 `testMultiRequirer` requires `noLoops` but preceding phases only guarantee `noCFGBodies` -/
#guard_msgs in
#eval check [testEstablisher, testMultiRequirer]

/-- info: rejected: phase #2 `testRequirer` requires `noCFGBodies`, guaranteed on entry but phase #1 `testNoop` afterwards does not preserve it -/
#guard_msgs in
#eval checkFrom factSet![.noCFGBodies] [testNoop, testRequirer]

/-- info: rejected: phase #3 `testRequirer` requires `noCFGBodies`, guaranteed by phase #1 `testEstablisher` but phase #2 `testNoop` afterwards does not preserve it -/
#guard_msgs in
#eval check [testEstablisher, testNoop, testRequirer]

/-- info: rejected: phase #4 `testRequirer` requires `noCFGBodies`, guaranteed by phase #1 `testEstablisher` but phase #2 `testNoop` afterwards does not preserve it -/
#guard_msgs in
#eval check [testEstablisher, testNoop, testNoop, testRequirer]

/--
info: rejected: phase #2 `testMultiRequirer` requires:
  • `noCFGBodies`: guaranteed on entry but phase #1 `testNoop` afterwards does not preserve it
  • `noLoops`: guaranteed on entry but phase #1 `testNoop` afterwards does not preserve it
-/
#guard_msgs in
#eval checkFrom factSet![.noCFGBodies, .noLoops] [testNoop, testMultiRequirer]

/-- info: rejected: phase #1 `testRequirer` requires `noCFGBodies` but no preceding phase guarantees it — phase #2 `testEstablisher` later in this pipeline establishes it, so it may be ordered too late -/
#guard_msgs in
#eval check [testRequirer, testEstablisher]

/-! ### Production pipeline -/

/-- Facts a phase lists as both established and preserved. Establishing a fact
    already guarantees it, so the contract should name it once. A phase that
    returns its input is exempt: it preserves everything by construction. -/
private def redundantlyPreserved (p : PipelinePhase) : List ProgramFact :=
  if p.preserves.facts == ProgramFact.all then []
  else p.establishes.facts.filter (· ∈ p.preserves)

/-- Facts a phase both requires and establishes. A phase that refuses to run
    without a fact is carrying it, not creating it, so the claim belongs in
    `preserves`: `establishes` says the output has the fact whatever the input
    was, which is not what a phase that rejects the input can offer. -/
private def requiredAndEstablished (p : PipelinePhase) : List ProgramFact :=
  p.requires.facts.filter (· ∈ p.establishes)

/-- Facts a phase requires and then drops: neither established nor preserved,
    so no later phase can rely on what this one insisted on. -/
private def requiredThenDropped (p : PipelinePhase) : List ProgramFact :=
  p.requires.facts.filter fun f => f ∉ p.establishes && f ∉ p.preserves

/-- One `phase: facts` line per phase with something to report. -/
private def findings (title : String) (phases : List PipelinePhase)
    (of : PipelinePhase → List ProgramFact) : List String :=
  let rows := phases.filterMap fun p =>
    match of p with
    | [] => none
    | fs => some s!"  {p.phase.name}: {", ".intercalate (fs.map (·.name))}"
  if rows.isEmpty then [s!"{title}: none"] else s!"{title}:" :: rows

/-- The contract table produced by the production renderer `Core.phaseTable`,
    with the back end as the consumer row, followed by the contract-hygiene
    findings the CLI does not print but a phase author wants. -/
private def contractTable (phases : List PipelinePhase) : String :=
  phaseTable phases (consumer := some ("the backend", backEndRequiredFacts)) ++ "\n\n" ++
  "\n".intercalate (
    findings "established and preserved, name it once" phases redundantlyPreserved ++
    findings "required and established, that is a preserve" phases requiredAndEstablished ++
    findings "required then dropped" phases requiredThenDropped)

/-- info: V starts holding here   | holds, and is carried on   + required here, and holds
: not holding, but would be carried   (blank) not holding, and would not be carried
CF: noCFGBodies   Ca: noCalls   Lo: noLoops   LI: noLoopInvariants
LM: noLoopMeasures   SS: staticSingleAssignment   BR: noBetaRedexes   PF: noPrecondsFromFuncs   NG: noNondetGuards   IF: noInternalFuncDecl   PP: noPolymorphicProcedures   PoF: noPolymorphicFunctions   TA: typeAnnotated

                              CF  Lo  LM  BR  NG  PP  TA
phase                           Ca  LI  SS  PF  IF  PoF
 1 assertNoCFGBodies          V : : : : : : : : : : : :
 2 liftInternalFuncDecls      | : : : : : : : : V :
 3 callElim                   + V : : :     : : | : :
 4 termCheck                  + | : : : :   : : |   : :
 5 precondElim                + | : : : :   V : |   : :
 6 insertLoopInvariantAsserts + | : V V : : | : | : : :
 7 loopElim                   + | V + +   : | : | : : :
 8 monomorphizeProcedures     + + | | | : : | : | V : :
 9 typeCheck                  | | | | | : : | : | | : V
10 monomorphizeFunctions      | | | | | : : | : + + V |
11 nondetElim                 + | | | |   : | V | | | |
12 symbolicEval               + V + | | V   | + | | | |
13 betaReduce                 | | | | | | V | | | | | |
14 commonSubexprElim          + | | | | + | | | | | | |
   the backend                + + +     + + +   + + + +

established and preserved, name it once: none
required and established, that is a preserve: none
required then dropped: none -/
#guard_msgs in
#eval IO.println (contractTable corePipelinePhases)

/-! The two cells that report trouble, on a deliberately broken list:
`testNoop` neither establishes nor preserves the fact `testEstablisher` just
established, so that fact is dropped (`'`), and `testRequirer` then asks for it
where it does not hold (`#`). The walk carries on past the unmet requirement
rather than stopping at it, which is what shows both cells at once. -/

/--
info: # required here, and does not hold   V starts holding here   ' was holding, and is dropped here
(blank) not holding, and would not be carried
CF: noCFGBodies   Ca: noCalls   Lo: noLoops   LI: noLoopInvariants
LM: noLoopMeasures   SS: staticSingleAssignment   BR: noBetaRedexes   PF: noPrecondsFromFuncs   NG: noNondetGuards   IF: noInternalFuncDecl   PP: noPolymorphicProcedures   PoF: noPolymorphicFunctions   TA: typeAnnotated

                   CF  Lo  LM  BR  NG  PP  TA
phase                Ca  LI  SS  PF  IF  PoF
 1 testEstablisher V
 2 testNoop        '
 3 testRequirer    #
-/
#guard_msgs in
#eval IO.println (phaseTable [testEstablisher, testNoop, testRequirer])

/-- info: assertNoCFGBodies establishes noCFGBodies, proved: true, preserves all: true -/
#guard_msgs in
#eval IO.println s!"{assertNoCFGBodiesPhase.phase.name} establishes \
{factNames assertNoCFGBodiesPhase.establishes}, \
proved: {assertNoCFGBodiesPhase.provesContract}, \
preserves all: {assertNoCFGBodiesPhase.preserves.facts == ProgramFact.all}"

/-- info: accepted; phases [assertNoCFGBodies, liftInternalFuncDecls, callElim, termCheck, precondElim, insertLoopInvariantAsserts, loopElim, monomorphizeProcedures, typeCheck, monomorphizeFunctions, nondetElim, symbolicEval, betaReduce, commonSubexprElim]; exit noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated -/
#guard_msgs in
#eval report coreValidatedPipeline

/-- info: accepted; phases [filterProcedures, assertNoCFGBodies, liftInternalFuncDecls, callElim, termCheck, precondElim, filterProcedures, insertLoopInvariantAsserts, loopElim, monomorphizeProcedures, typeCheck, monomorphizeFunctions, nondetElim, symbolicEval, betaReduce, commonSubexprElim]; exit noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated -/
#guard_msgs in
#eval report (coreValidatedPipeline
  (options := { Core.VerifyOptions.default with proceduresToVerify := some ["main"] }))

/-! A phase list assembled by hand is validated the same way. `splicePhasesAfter`
places procedure inlining just after the entry assertion, where it composes
because the assertion has established the structured bodies it requires. -/

/-- info: accepted; phases [assertNoCFGBodies, inlineProcedures, liftInternalFuncDecls, callElim, termCheck, precondElim, insertLoopInvariantAsserts, loopElim, monomorphizeProcedures, typeCheck, monomorphizeFunctions, nondetElim, symbolicEval, betaReduce, commonSubexprElim]; exit noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated -/
#guard_msgs in
#eval report (do
  let phases ← Strata.Core.splicePhasesAfter "assertNoCFGBodies"
    [procedureInliningPipelinePhase] corePipelinePhases
  Strata.Core.validatePipeline phases)

/-! An anchor that is not in the list is refused, rather than the phases landing
somewhere the caller did not ask for. -/

/-- info: rejected: Cannot splice after phase 'noSuchPhase': no phase of that name is in the list. -/
#guard_msgs in
#eval report (do
  let phases ← Strata.Core.splicePhasesAfter "noSuchPhase"
    [procedureInliningPipelinePhase] corePipelinePhases
  Strata.Core.validatePipeline phases)

/-! Anchoring on the last phase is the boundary where nothing follows it, so the
spliced phases end the list. -/

/-- info: [assertNoCFGBodies, liftInternalFuncDecls, callElim, termCheck, precondElim, insertLoopInvariantAsserts, loopElim, monomorphizeProcedures, typeCheck, monomorphizeFunctions, nondetElim, symbolicEval, betaReduce, commonSubexprElim, inlineProcedures] -/
#guard_msgs in
#eval IO.println (match Strata.Core.splicePhasesAfter "commonSubexprElim"
    [procedureInliningPipelinePhase] corePipelinePhases with
  | .ok ps => toString (ps.map Strata.Core.phaseName)
  | .error e => e)

/-! The `functionInlining` and `unrollBoundedQuantifiers` options each insert phases
after `symbolicEval`, independently of one another; unrolling brings its own
`betaReduce` ahead of itself. -/

private def inliningOnly : VerifyOptions :=
  { VerifyOptions.default with functionInlining := true }

private def unrollingOnly : VerifyOptions :=
  { VerifyOptions.default with unrollBoundedQuantifiers := true }

private def inliningAndUnrolling : VerifyOptions :=
  { VerifyOptions.default with functionInlining := true, unrollBoundedQuantifiers := true }

/-- info: accepted; phases [assertNoCFGBodies, liftInternalFuncDecls, callElim, termCheck, precondElim, insertLoopInvariantAsserts, loopElim, monomorphizeProcedures, typeCheck, monomorphizeFunctions, nondetElim, symbolicEval, functionInlining, betaReduce, commonSubexprElim]; exit noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated -/
#guard_msgs in
#eval report (coreValidatedPipeline (options := inliningOnly))

/-- info: accepted; phases [assertNoCFGBodies, liftInternalFuncDecls, callElim, termCheck, precondElim, insertLoopInvariantAsserts, loopElim, monomorphizeProcedures, typeCheck, monomorphizeFunctions, nondetElim, symbolicEval, betaReduce, unrollBoundedQuantifiers, betaReduce, commonSubexprElim]; exit noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated -/
#guard_msgs in
#eval report (coreValidatedPipeline (options := unrollingOnly))

/-- info: accepted; phases [assertNoCFGBodies, liftInternalFuncDecls, callElim, termCheck, precondElim, insertLoopInvariantAsserts, loopElim, monomorphizeProcedures, typeCheck, monomorphizeFunctions, nondetElim, symbolicEval, functionInlining, betaReduce, unrollBoundedQuantifiers, betaReduce, commonSubexprElim]; exit noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated -/
#guard_msgs in
#eval report (coreValidatedPipeline (options := inliningAndUnrolling))

/-! Unrolling on its own, with nothing established about the program, is refused. -/

/-- info: rejected: phase #1 `unrollBoundedQuantifiers` requires:
  • `noCFGBodies`: no preceding phase guarantees it
  • `noLoops`: no preceding phase guarantees it
  • `staticSingleAssignment`: no preceding phase guarantees it -/
#guard_msgs in
#eval check [unrollBoundedQuantifiersPipelinePhase]

/-! Every fact either phase requires it also preserves. -/

#guard requiredThenDropped unrollBoundedQuantifiersPipelinePhase == []

#guard requiredThenDropped functionInliningPipelinePhase == []

/-- info: rejected: phase #2 `functionInlining` requires `noPrecondsFromFuncs` but preceding phases only guarantee `noCFGBodies` — phase #6 `precondElim` later in this pipeline establishes it, so it may be ordered too late -/
#guard_msgs in
#eval report (Strata.Core.validatePipeline
  (match Strata.Core.splicePhasesAfter "assertNoCFGBodies" [functionInliningPipelinePhase]
           corePipelinePhases with
   | .ok phases => phases
   | .error _ => []))

/-! Naming procedures to verify drops the others before the entry assertion
looks at the program, so a CFG body the caller did not ask about cannot refuse
the run. Asking about the CFG-bodied procedure itself still fails. -/

private def namedMixedProgram : Program :=
  { decls :=
      [.proc { (default : Procedure) with
                header := { (default : Procedure.Header) with name := "structured" },
                body := .structured [] } default,
       .proc { (default : Procedure) with
                header := { (default : Procedure.Header) with name := "cfgHelper" },
                body := .cfg { entry := "entry", blocks := [] } } default] }

private def runPhases (phases : List PipelinePhase) (p : Program) : String :=
  let step (prog : Program) (ph : PipelinePhase) : Transform.CoreTransformM Program := do
    let (_, out) ← ph.transform prog
    return out
  match (phases.foldlM step p).run .emp with
  | (.ok _, _)    => "accepted"
  | (.error e, _) => s!"rejected: {e.message}"

/-- info: accepted -/
#guard_msgs in
#eval IO.println (runPhases (transformPipelinePhases
    { Core.VerifyOptions.default with proceduresToVerify := some ["structured"] }) namedMixedProgram)

/-- info: rejected: ❌ Expected every procedure body to be structured, but at least one is a CFG. -/
#guard_msgs in
#eval IO.println (runPhases (transformPipelinePhases
    { Core.VerifyOptions.default with proceduresToVerify := some ["cfgHelper"] }) namedMixedProgram)

private def cfgBodiedProgram : Program :=
  { decls := [.proc
      { (default : Procedure) with body := .cfg { entry := "entry", blocks := [] } }
      default] }

/-! ### Configuring a pipeline by name

`--phases` resolves names against the option-derived phase list plus the extra
phases a user may name, and accepts an `assert<Fact>` form for every fact that
has an executable check. These pin that resolution, and that the resulting list
is validated the same way the default one is. The helpers live in the curated
`Strata.Core` API surface, so they are named in full here. -/

/-- info: [assertNoCFGBodies, liftInternalFuncDecls, inlineProcedures] -/
#guard_msgs in
#eval IO.println (match Strata.Core.resolvePhases
    (corePipelinePhases ++ [Strata.Core.passInlineAll])
    ["assertNoCFGBodies", "liftInternalFuncDecls", "inlineProcedures"] with
  | .ok ps => toString (ps.map Strata.Core.phaseName)
  | .error e => e)

/-! An unknown name is a user error naming the flag that lists the choices. -/

/-- info: Unknown phase name 'noSuchPhase'. Use --display-phases to see the available phases. -/
#guard_msgs in
#eval IO.println (match Strata.Core.resolvePhases corePipelinePhases ["noSuchPhase"] with
  | .ok ps => toString (ps.map Strata.Core.phaseName)
  | .error e => e)

/-! Every fact with a check has an assert form; `typeAnnotated`, which has none,
does not, so `typeCheck` stays its only source. -/

/-- info: assertNoCFGBodies, assertNoCalls, assertNoLoops, assertNoLoopInvariants, assertNoLoopMeasures, assertStaticSingleAssignment, assertNoBetaRedexes, assertNoPrecondsFromFuncs, assertNoNondetGuards, assertNoInternalFuncDecl, assertNoPolymorphicProcedures, assertNoPolymorphicFunctions -/
#guard_msgs in
#eval IO.println (", ".intercalate (ProgramFact.all.filterMap fun f =>
  let nm := Strata.Core.assertPhaseName f
  (Strata.Core.assertPhaseFor nm).map (fun _ => nm)))

/-! An assert phase establishes just the fact it names and carries everything
else, which is what lets it stand in for the transform that established it. -/

/-- info: assertNoLoops establishes noLoops, preserves all: true -/
#guard_msgs in
#eval IO.println (match Strata.Core.assertPhaseFor "assertNoLoops" with
  | some p => s!"{Strata.Core.phaseName p} establishes {factNames p.establishes}, \
                 preserves all: {p.preserves.facts == ProgramFact.all}"
  | none => "no such assert phase")

/-! An all-assert pipeline is what a front end emitting already-passive Core
runs: type checking plus one assert per remaining fact the back end requires
composes, transforms nothing, and checks everything. -/

private def allAssertNames : List String :=
  "typeCheck" :: (backEndRequiredFacts.facts.filterMap fun f =>
    let nm := Strata.Core.assertPhaseName f
    (Strata.Core.assertPhaseFor nm).map (fun _ => nm))

/-- info: accepted; phases [typeCheck, assertNoCFGBodies, assertNoCalls, assertNoLoops, assertStaticSingleAssignment, assertNoBetaRedexes, assertNoPrecondsFromFuncs, assertNoInternalFuncDecl, assertNoPolymorphicProcedures, assertNoPolymorphicFunctions]; exit noCFGBodies, noCalls, noLoops, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated -/
#guard_msgs in
#eval report (match Strata.Core.resolvePhases
                     (corePipelinePhases ++ [Strata.Core.passInlineAll])
                     allAssertNames with
  | .ok ps => Strata.Core.validatePipeline ps
  | .error e => .error e)

/-! An empty name list resolves to an empty pipeline. `ofList` accepts it — no
phase requires anything, so nothing can be violated — while `validatePipeline`
rejects it, since it checks delivery to the back end as well. -/

/-- info: resolves to [] -/
#guard_msgs in
#eval IO.println (match Strata.Core.resolvePhases corePipelinePhases [] with
  | .ok ps => s!"resolves to {ps.map Strata.Core.phaseName}"
  | .error e => s!"unexpected: {e}")

/-- info: accepted; phases []; exit (none) -/
#guard_msgs in
#eval check []

/--
info: rejected: phase #1 `the verification back end` requires:
  • `noCFGBodies`: no preceding phase guarantees it
  • `noCalls`: no preceding phase guarantees it
  • `noLoops`: no preceding phase guarantees it
  • `staticSingleAssignment`: no preceding phase guarantees it
  • `noBetaRedexes`: no preceding phase guarantees it
  • `noPrecondsFromFuncs`: no preceding phase guarantees it
  • `noInternalFuncDecl`: no preceding phase guarantees it
  • `noPolymorphicProcedures`: no preceding phase guarantees it
  • `noPolymorphicFunctions`: no preceding phase guarantees it
  • `typeAnnotated`: no preceding phase guarantees it
-/
#guard_msgs in
#eval report (Strata.Core.validatePipeline [])

/-! A caller that can prove facts of its own output assumes them at entry
instead, and the phases they made unnecessary can go. Here `noLoops` assumed at
entry lets both loop phases drop out, and the result still delivers what the
back end needs. -/

/-- info: accepted; phases [assertNoCFGBodies, liftInternalFuncDecls, callElim, termCheck, precondElim, monomorphizeProcedures, typeCheck, monomorphizeFunctions, nondetElim, symbolicEval, betaReduce, commonSubexprElim]; exit noCFGBodies, noCalls, noLoops, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated -/
#guard_msgs in
#eval report (Strata.Core.validatePipelineFrom factSet![.noLoops]
  (corePipelinePhases.filter fun p =>
    Strata.Core.phaseName p ∉ ["loopElim", "insertLoopInvariantAsserts"]))

/-! Dropping those two phases without assuming the fact is rejected, naming the
phase that needed it. -/

/-- info: rejected: phase #10 `symbolicEval` requires `noLoops` but preceding phases only guarantee `noCFGBodies, noCalls, noPrecondsFromFuncs, noNondetGuards, noInternalFuncDecl, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated` -/
#guard_msgs in
#eval report (Strata.Core.validatePipeline
  (corePipelinePhases.filter fun p =>
    Strata.Core.phaseName p ∉ ["loopElim", "insertLoopInvariantAsserts"]))

/-! The `--display-phases` text: the default order as a pasteable argument, then
the phases that exist but are not in it. -/

/--
info: To run the phases in the default order:

  --phases assertNoCFGBodies,liftInternalFuncDecls,callElim,termCheck,precondElim,insertLoopInvariantAsserts,loopElim,monomorphizeProcedures,typeCheck,monomorphizeFunctions,nondetElim,symbolicEval,betaReduce,commonSubexprElim

You can change this order. Give it back to --phases with no input file and
Strata reports whether it composes without verifying anything.
To see the declared dependencies between phases, use --display-phase-contracts.

Available, not in the default order:

  inlineProcedures
-/
#guard_msgs in
#eval IO.println (Strata.Core.displayPhasesText corePipelinePhases
  (extras := [Strata.Core.passInlineAll]))

/-! Feeding `--display-phases`' output back through `--phases` reproduces the
default pipeline, which is the round-trip the two flags promise. -/

/-- info: true -/
#guard_msgs in
#eval IO.println (toString (match Strata.Core.resolvePhases
    (corePipelinePhases ++ [Strata.Core.passInlineAll])
    (corePipelinePhases.map Strata.Core.phaseName) with
  | .ok ps => ps.map Strata.Core.phaseName == corePipelinePhases.map Strata.Core.phaseName
  | .error _ => false))

private def runAsserter (phase : PipelinePhase) (p : Program) : String :=
  match (phase.transform p).run .emp with
  | (.ok _, _)    => "accepted"
  | (.error e, _) => s!"rejected: {e.message}"

/-- info: rejected: ❌ Expected every procedure body to be structured, but at least one is a CFG. -/
#guard_msgs in
#eval IO.println (runAsserter assertNoCFGBodiesPhase cfgBodiedProgram)

/-- info: accepted -/
#guard_msgs in
#eval IO.println (runAsserter assertNoCFGBodiesPhase { decls := [] })

/-! ### Requirements are enforced on the program, not only on the contracts

A phase rejects a program that fails a fact it requires, where its own walk meets
the offending construct. A caller invoking a phase directly, or a broken
`establishes` claim upstream, therefore gets an error naming the phase and the
construct. -/

/-- info: rejected: ❌ PrecondElim: procedure _ has a CFG body; preconditions can only be eliminated from structured bodies. -/
#guard_msgs in
#eval IO.println (runAsserter precondElimPipelinePhase cfgBodiedProgram)

/-- info: rejected: ❌ CommonSubexprElim: procedure _ has a CFG body; common subexpressions can only be eliminated from structured bodies. -/
#guard_msgs in
#eval IO.println (runAsserter commonSubexprElimPhase cfgBodiedProgram)

/-- info: rejected: ❌ TerminationCheck: procedure _ has a CFG body; termination is only checked on structured bodies. -/
#guard_msgs in
#eval IO.println (runAsserter termCheckPipelinePhase cfgBodiedProgram)

/-! A non-polymorphic procedure with a CFG body is passed through unchanged:
    there is nothing to monomorphize, so structural checks are skipped. -/
/-- info: accepted -/
#guard_msgs in
#eval IO.println (runAsserter monomorphizeProceduresPipelinePhase cfgBodiedProgram)

/-! For a *polymorphic* procedure the CFG-body and noCalls checks still fire,
    because the substitution cannot be applied without a structured body, and
    monomorphization per procedure is only sound once calls are gone. -/

private def polyProgOf (typeArgs : List String) (body : Procedure.Body) : Program :=
  { decls := [.proc { (default : Procedure) with header.typeArgs := typeArgs, body := body }
      default] }

/-- info: rejected: ❌ MonomorphizeProcedures: procedure _ has a CFG body; monomorphization only handles structured bodies. -/
#guard_msgs in
#eval IO.println (runAsserter monomorphizeProceduresPipelinePhase
  (polyProgOf ["T"] (.cfg { entry := "entry", blocks := [] })))

/-- info: rejected: ❌ MonomorphizeProcedures: procedure _ still contains a call; eliminate calls before monomorphizing. -/
#guard_msgs in
#eval IO.println (runAsserter monomorphizeProceduresPipelinePhase
  (polyProgOf ["T"] (.structured [Statement.call "f" [] {}])))

/-! A non-polymorphic procedure with a call is similarly accepted:
    monomorphization is a no-op, so the noCalls precondition does not apply. -/
/-- info: accepted -/
#guard_msgs in
#eval IO.println (runAsserter monomorphizeProceduresPipelinePhase
  (progOf [Statement.call "f" [] {}]))

/-! Symbolic evaluation reports a `loop` and a CFG body through the evaluator's
error channel. -/

/-- A loop with a deterministic guard: a nondeterministic one is refused earlier,
    by the check that `nondetElim` has run, so it would not reach the loop case. -/
private def loopProgram : Program :=
  progOf [.loop (.det trueExpr) none [] [] {}]

/--
info: rejected: ❌ Symbolic evaluation error.
procedure '_': [ERROR] cannot evaluate a `loop` statement: eliminate loops before symbolic evaluation
-/
#guard_msgs in
#eval IO.println (runAsserter (symbolicEvalPipelinePhase) loopProgram)

/-- info: rejected: ❌ Symbolic evaluation error.
procedure '_': [ERROR] CFG bodies not supported yet -/
#guard_msgs in
#eval IO.println (runAsserter (symbolicEvalPipelinePhase) cfgBodiedProgram)

/-! The back end enforces its own requirements the same way. A CFG body would
otherwise yield no obligations at all, leaving a procedure's assertions unchecked
and unreported, and a function precondition surviving `precondElim` is an
obligation nothing generates while the encoder emits total safe arithmetic on the
strength of it having been checked. -/

/-- Render an extraction outcome. -/
private def runExtraction (p : Program) : String :=
  match Core.ObligationExtraction.extractObligations p with
  | .ok obs => s!"extracted {obs.size}"
  | .error e => s!"rejected: {e}"

/-- info: rejected: ObligationExtraction: procedure '_' has a CFG body; obligations can only be extracted from structured bodies -/
#guard_msgs in
#eval IO.println (runExtraction cfgBodiedProgram)

/-- info: rejected: ObligationExtraction: function 'f' still carries a precondition; run precondition elimination before extracting obligations -/
#guard_msgs in
#eval IO.println (runExtraction
  { decls := [.func { name := "f", inputs := .empty, output := Lambda.LMonoTy.tcons "int" [],
                      preconditions := [{ expr := trueExpr, md := default }] } default] })

/-! A precondition can survive on a recursive-function block as well as on a
plain function, and `Program.noFuncPreconditions` inspects both, so extraction
rejects both. -/

/-- info: rejected: ObligationExtraction: function 'f' still carries a precondition; run precondition elimination before extracting obligations -/
#guard_msgs in
#eval IO.println (runExtraction
  { decls := [.recFuncBlock
      [{ name := "f", inputs := .empty, output := Lambda.LMonoTy.tcons "int" [],
         preconditions := [{ expr := trueExpr, md := default }] }] default] })

/-! A block whose functions carry no precondition is accepted, so the guard
rejects the precondition rather than the declaration kind. -/

/-- info: extracted 0 -/
#guard_msgs in
#eval IO.println (runExtraction
  { decls := [.recFuncBlock
      [{ name := "f", inputs := .empty, output := Lambda.LMonoTy.tcons "int" [],
         body := some trueExpr }] default] })

/-! An unevaluable procedure stops the run rather than being skipped: a program
where a good procedure and a bad one sit side by side would otherwise verify the
good one and report nothing about the other, whose assertions were never
checked. -/

private def mixedProgram : Program :=
  { decls :=
      [.proc { (default : Procedure) with body := .structured [] } default,
       .proc { (default : Procedure) with body := .cfg { entry := "entry", blocks := [] } } default] }

/-- info: rejected: ❌ Symbolic evaluation error.
procedure '_': [ERROR] CFG bodies not supported yet -/
#guard_msgs in
#eval IO.println (runAsserter (symbolicEvalPipelinePhase) mixedProgram)

