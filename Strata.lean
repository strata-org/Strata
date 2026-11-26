/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- This module serves as the root of the `Strata` library.
-- In each category, imports are sorted by alphabetical order.
module
/- DDM -/
import StrataDDM.Integration.Lean
import StrataDDM.Ion

/- Dialect Library -/
import Strata.DL.SMT
import Strata.DL.Lambda
import Strata.DL.Imperative
import Strata.DL.Str
import Strata.DL.Util.StringGenProps
import Strata.Languages.Core.NameManglingProps

/- Utilities -/
import Strata.Util.NameProofs
import Strata.Util.OrderedSetProps
import Strata.Util.RealProps
import Strata.Util.IonDeserializer
import Strata.Util.Sarif
import Strata.Util.Worklist
import Strata.Util.WorklistProps

/- Strata Languages -/
import Strata.Languages.Core.BitVecEvalProps
import Strata.Languages.Core.IntEvalProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Languages.Core.InstExprTyping
import Strata.Languages.Core.FactoryWF
import Strata.Languages.Core.FactoryInterp
import Strata.Languages.Core.SeqModel
import Strata.Languages.Core.SMTEncoderProps
import Strata.Languages.Core.SMTEmitter
import Strata.Languages.Core.StatementProps
import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.SarifOutput
import Strata.Languages.Core.WFProps
import Strata.DL.Imperative.StmtExtendCallBridge
import Strata.Languages.Core.StmtExtendCallBridgeProps
/- Code Transforms -/
import Strata.Transform.CallElimCorrect
import Strata.Transform.CFGLoopElimProps
import Strata.Transform.CommonSubexprElimCorrect
import Strata.Transform.CommonSubexprElimProps
import Strata.Transform.CoreSpecification
import Strata.Transform.CoreSpecificationProps
import Strata.Languages.Core.Analysis.ProcedureCorrectness
import Strata.Languages.Core.Analysis.ProcedureCorrectnessProps
import Strata.Languages.Core.Analysis.ProcedureCorrectnessHoareConnection
import Strata.Languages.Core.Analysis.DeductiveVerification
import Strata.Languages.Core.Analysis.DeductiveVerificationProps
import Strata.Languages.Core.Analysis.FragmentFactory
import Strata.DL.Lambda.LFuncEvalSound
import Strata.DL.Lambda.LExprRenameOps
import Strata.Transform.MonomorphizeFunctionsProps
import Strata.Transform.MonomorphizeFunctionsCorrect
import Strata.Languages.Core.ProcedureProps
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core.NameSetsProps
import Strata.Transform.CoreTransformProps
import Strata.Transform.DetToKleeneCorrect
import Strata.Transform.FunctionInlining
import Strata.Transform.FunctionInliningProps
import Strata.Transform.LambdaLiftCorrect
import Strata.Transform.UnrollBoundedQuantifiersProps
import Strata.Transform.LoopInitHoist
import Strata.Transform.LoopInitHoistProps
import Strata.Transform.LoopInitHoistCorrect
import Strata.Transform.LoopInitHoistCoreCorrect
import Strata.Transform.NondetElim
import Strata.Transform.NondetElimCorrect
import Strata.Transform.NondetElimCoreCorrect
import Strata.Transform.NondetElimProps
import Strata.Transform.ProcBodyVerifyCorrect
import Strata.Transform.Simplify
import Strata.Transform.Simplify.Expr
import Strata.Transform.Simplify.LiveSweep
import Strata.Transform.Simplify.StmtShape
import Strata.Transform.Simplify.DeadDefsShape
import Strata.Transform.Simplify.Entry
import Strata.Transform.Simplify.Precondition
import Strata.Transform.Simplify.FoldFactory
import Strata.Transform.Simplify.ExprCorrect
import Strata.Transform.Simplify.StmtSim
import Strata.Transform.Simplify.SimpRun
import Strata.Transform.Simplify.SweepRun
import Strata.Transform.Simplify.Compose
import Strata.Transform.Simplify.SimpWF
import Strata.Transform.Simplify.OutputGate
import Strata.Transform.Simplify.EvalSoundFold
import Strata.Transform.SimplifyCorrect
import Strata.Transform.RecursiveFunctionAxioms
import Strata.Transform.SpecHoareConnection
import Strata.Transform.CoreSpecHoareConnection
import Strata.Transform.StructuredToUnstructured
import Strata.Transform.StructuredToUnstructuredProps
import Strata.Transform.StructuredToUnstructuredCorrect
import Strata.Transform.StructuredToUnstructuredCoreCorrect
import Strata.Transform.StructuredToUnstructuredPipeline
import Strata.Transform.StructuredToUnstructuredPipelineCorrect
import Strata.Transform.StructuredToUnstructuredPipelineProps
import Strata.Transform.StructuredToUnstructuredPipelineCoreCorrect

/- Program Logics -/
import Strata.DL.Imperative.Logic.HoareTemplate
import Strata.DL.Imperative.Logic.HoareTotalTemplate
import Strata.Languages.Core.Logic.LangDefProps
import Strata.Languages.Core.Logic.TraceInterpUsingDenote
import Strata.Languages.Core.Logic.TraceInterpUsingDenoteProps
import Strata.Languages.Core.Logic.Hoare
import Strata.Languages.Core.Logic.HoareTotal
import Strata.Languages.Core.Logic.HoareCall
import Strata.Languages.Core.Logic.ContractToHoareTriple
import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.Languages.Core.Logic.InterpreterHoareRelation

/- Strata Languages — additional -/
import Strata.Languages.Cortex
import Strata.Languages.Cortex.InterpreterSound
import Strata.Languages.Core.EntryPoint
import Strata.Languages.Core.IncrementalSolve
import Strata.Languages.Core.IncrementalSolveCorrect
import Strata.Languages.Core.DeclFormulas
import Strata.Languages.Core.ObligationExtractionProps
import Strata.Languages.Core.ProgramFact
import Strata.Languages.Core.ProgramFactProps
import Strata.Languages.Core.ProgramFactSet
import Strata.Languages.Core.ProgramFactSetProps
import Strata.Languages.Core.PipelinePhaseProps
import Strata.Languages.Core.VerifierProofs
import Strata.Languages.Core.EvaluatorResultsProps
import Strata.Languages.Core.CoreGenProps
import Strata.Languages.Core.VerifierSlicingProofs
import Strata.Languages.Core.WPRewritePipelineProofs
import Strata.DL.Imperative.PathConditionHoldsProps
import Strata.Languages.GOTO

/- DDM -/
import StrataDDM

/- Backends -/
import Strata.Backends.CBMC

/- Dialect Library — additional (can't go in aggregates due to cycles) -/
import Strata.DL.SMT.Denote
import Strata.DL.SMT.DenoteDatatypes
import Strata.DL.SMT.DenoteProps
import Strata.DL.SMT.FactoryCorrect
import Strata.DL.SMT.Translate
import Strata.DL.SMT.DenoteTyped
import Strata.DL.SMT.DenoteTypedProps
import Strata.DL.SMT.DenoteSemanticsEquiv
import Strata.DL.SMT.DenoteTypedSMTQuery
import Strata.DL.SMT.Lean.QueryCorrect
import Strata.DL.SMT.SymbolProps
import Strata.DL.SMT.VerdictReaderProps
import Strata.DL.SMT.RegexMatchProps

/- Other -/
import Strata.MetaVerifier

/- Pipeline -/
import Strata.Pipeline.Diagnostic
import Strata.Pipeline.FactSet
import Strata.Pipeline.FactSetProps
import Strata.Pipeline.PhaseContract
import Strata.Pipeline.PhaseContractProps

/- Simple API -/
import Strata.SimpleAPI

/- CLI -/
import Strata.Cli.CoreCommands
import Strata.Cli.DialectCommands
import Strata.Cli.Framework
import Strata.Cli.VerifyOptions

-- Dead-definition elimination: its over-approximation proofs.
import Strata.Transform.DeadDefElimCoreCorrect
-- Loop elimination: its over-approximation and assertion-validity proofs.
import Strata.Transform.LoopElimCoreCorrect
-- Inserting loop invariant checks: its over-approximation, assertion-validity and Hoare-triple
-- proofs.
import Strata.Transform.InsertLoopInvariantAssertsCoreCorrect
-- Guard forwarding: its over-approximation proofs and their composition with the SSA phase and
-- dead-definition elimination.
import Strata.Transform.GuardFwdCoreCorrect
-- Guard propagation: its over-approximation proof.
import Strata.Transform.GuardPropCoreCorrect
import Strata.Transform.GuardPropTyping
-- The constructor fold: its over-approximation proof.
import Strata.Transform.CtorFold
import Strata.Transform.CtorFoldCoreCorrect
import Strata.Transform.DefInlineCoreCorrect
import Strata.Transform.NormLawTyped
import Strata.Transform.DefInlineRewrite
import Strata.Transform.DefInlineRewriteCorrect
import Strata.Transform.WPLoop
import Strata.Transform.WPRewriteLoop
import Strata.Transform.WPLoopCorrect
import Strata.Transform.WPRewriteLoopCorrect
-- The WP and SSA phases: their properties, the failure preservation of the SSA phase, and
-- the properties of their Core instance.
import Strata.Transform.SSA.SSAEval
import Strata.Transform.SSA.SSAOver
import Strata.Transform.SSA.SSATyping
import Strata.Transform.SSA.SSAUnassignedCorrect
import Strata.Transform.WP.WPProps
import Strata.Util.RopeProps
import Strata.Util.LeftistHeapProps
import Strata.Transform.Passive.CoreProgram
import Strata.Transform.Passive.CoreProgramProps
import Strata.Transform.Passive.WPFactoryProps
import Strata.Transform.Passive.DeclObligationsCoreCorrect
import Strata.Transform.Passive.CoreWPSSA
import Strata.Transform.Passive.CoreWPSSAProps
import Strata.Transform.Passive.CoreTyped
import Strata.Transform.Passive.WellTypedProps
import Strata.Transform.BetaReduceTyping
import Strata.Transform.BetaReduceCorrect
import Strata.Transform.GuardFwdTyping
import Strata.Languages.Core.ObligationExtractionTyping
import Strata.Transform.WP.WPCoreProgram
import Strata.Transform.WP.WPCoreProgramProps
import Strata.Transform.WP.WPCoreCorrect
import Strata.Transform.SSA.SSACoreProgram
import Strata.Transform.SSA.SSACoreProgramProps
import Strata.Transform.SSA.SSACoreCorrect
import Strata.Transform.Passive.Over
import Strata.Transform.WP.WPRestrict
import Strata.Transform.WP.WPCoreDefs
import Strata.Transform.WP.WPEvalIface
import Strata.Transform.WP.WPOutDecls
import Strata.Transform.WP.WPOutOps
import Strata.Transform.WP.WPOutSyntax
import Strata.Transform.WP.WPOutTypes
import Strata.Transform.WP.WPOutTyping
import Strata.Transform.WP.WPOutTypingWalk
import Strata.Transform.WP.WPReplay
import Strata.Transform.WP.WPCoreGate
import Strata.Transform.WP.WPCoreTyping
import Strata.Transform.WP.WPCoreOps
import Strata.Transform.WP.WPCorePrefix

-- Equality simplification: failures are kept, given its expression-level steps are sound.
import Strata.Transform.EqualitySimplificationCorrect
import Strata.Transform.FoldAxiomsEntry

-- Contextual rewriting: rewrites each goal under the facts on its path.
import Strata.Transform.ContextualRewrite

/- The monadic interpreter: the monad-generic engine, its soundness and completeness against
   the reference event semantics, Core's instantiation, the `EvalM`
   instance and its soundness and completeness, counterexample replay, and symbolic execution
   on it -/
import Strata.DL.Imperative.InterpreterFuelMono
import Strata.DL.Imperative.InterpreterTowerProps
import Strata.Languages.Core.ConfigWF
import Strata.Languages.Core.EnvProps
import Strata.Languages.Core.ReplayWF
import Strata.Languages.Core.Interpreter
import Strata.Languages.Core.InterpreterDomainProps
import Strata.Languages.Core.InterpreterEvalSound
import Strata.Languages.Core.FactoryEvalSoundWF
import Strata.Languages.Core.InterpreterBridgeStatements
-- Counterexample lifting (CEL): levels (c) model, (b) valuation, (a) run, and back-links
-- (translations of runs across program transformations)
import Strata.Languages.Core.Counterexample.Run
import Strata.Languages.Core.Counterexample.BackLink
import Strata.Languages.Core.Counterexample.ValuationToRun
import Strata.Languages.Core.Counterexample.RunProps
import Strata.Languages.Core.Counterexample.BackLinkChainReplayProps
import Strata.DL.Imperative.Counterexample.RunProps
import Strata.DL.Imperative.Counterexample.BackLinkProps
import Strata.Languages.Core.Counterexample.ModelToValuation
import Strata.Languages.Core.Counterexample.ModelToValuationProps
import Strata.Languages.Core.Counterexample.ModelProps
import Strata.Languages.Core.Counterexample.ModelAnonymousProps
import Strata.Languages.Core.Counterexample.BackLinkRelSim
import Strata.Languages.Core.Counterexample.BackLinkRelSimProps
import Strata.Languages.Core.Counterexample.BackLinkExactProps
import Strata.Languages.Core.Counterexample.BackLinkExact
import Strata.Languages.Core.InterpreterCallComplete
import Strata.Languages.Core.InterpreterCallSound
import Strata.Languages.Core.InterpreterComplete
import Strata.Languages.Core.InterpreterCFG
import Strata.Languages.Core.InterpreterCFGProps
import Strata.Languages.Core.InterpreterEval
import Strata.Languages.Core.InterpreterEvalProps
import Strata.Languages.Core.InterpreterKleene
import Strata.Languages.Core.InterpreterKleeneProps
import Strata.Languages.Core.InterpreterReach
import Strata.Languages.Core.InterpreterReachBridge
import Strata.Languages.Core.InterpreterReachBuiltins
import Strata.Languages.Core.InterpreterReachCheck
import Strata.Languages.Core.InterpreterReachProps
import Strata.Languages.Core.InterpreterObs
import Strata.Languages.Core.InterpreterObsProps
import Strata.Languages.Core.InterpreterSound
import Strata.Languages.Core.JoinValueNames
import Strata.Languages.Core.SymExec
import Strata.Languages.Core.PathExplorer
import Strata.Languages.Core.PathExplorerProps
import Strata.Languages.Core.SymExecProps
import Strata.Languages.Core.SymExecReplay
import Strata.Languages.Core.SymExecReplayProps
import Strata.Languages.Core.SymExecTree
import Strata.Languages.Core.StmtCallFree

 -- deletion candidates: nothing imports these modules:

-- noimport:
import Strata.DL.Lambda.Denote.Assumptions
import Strata.DL.Lambda.Denote.CallOfLFuncDenote
import Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LExprDenoteCompute
import Strata.DL.Lambda.Denote.LExprDenoteConstrs
import Strata.DL.Lambda.Denote.LExprDenoteConsts
import Strata.DL.Lambda.Denote.LExprDenoteEq
import Strata.DL.Lambda.LExprDenoteEval
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LExprDenoteBeta
import Strata.DL.Lambda.LExprEvalFully
import Strata.DL.Lambda.LExprEvalFuelProps
import Strata.DL.Lambda.LExprEvalAnnotateProps
import Strata.DL.Lambda.LExprDenoteEvalSubst
import Strata.DL.Lambda.LExprDenoteEvalCongr
import Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.DL.Lambda.Denote.LExprDenoteSubst
import Strata.DL.Lambda.Denote.LExprDenoteTySubst
import Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import Strata.DL.Lambda.LExprTEraseProps
import Strata.DL.Lambda.LExprTProps
import Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.LExprTraversal
import Strata.DL.Lambda.LExprTraversalProps
import Strata.DL.Lambda.LTyMatchProps
import Strata.DL.Lambda.NamePrefixesProps
import Strata.DL.Lambda.Reflect
import Strata.DL.Lambda.OperationalSemantics
import Strata.DL.Lambda.OperationalSemanticsProps
import Strata.DL.Lambda.LExprEvalSound
import Strata.DL.Lambda.TypeFactoryWF
import Strata.DL.Lambda.LExprTypeEnvProps
import Strata.DL.Lambda.DatatypeFactoryWFProps
import Strata.DL.Lambda.KnownTypesProps
import Strata.Util.HListProps
import Strata.Util.HMapsProps
import Strata.Languages.Core.ProgramWF
import Strata.Languages.Core.StatementWF
import Strata.DL.Lambda.DatatypeWF
import Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.WrittenTyVarScope
import Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec
import Strata.Languages.Core.ProcedureTypeProps
import Strata.Transform.CFGLoopElimProps
import Strata.Transform.CFGLoopElimReplay
import Strata.Languages.Core.Typing.Spec.DatatypeTypeSpec
import Strata.Languages.Core.Typing.Spec.ProgramTypeSpec
import Strata.Languages.Core.Typing.Spec.NamesWF
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.Languages.Core.Typing.Spec.TypingSpec
import Strata.Languages.Core.Typing.Spec.ConfigTyping
import Strata.Languages.Core.FactoryProps
import Strata.Languages.Core.Typing.Props.CmdTypeProps
import Strata.Languages.Core.Typing.Props.DatatypeTypeProps
import Strata.Languages.Core.Typing.Props.ExprEraseProps
import Strata.Languages.Core.Typing.Props.FactoryRegistrationProps
import Strata.Languages.Core.Typing.Props.FunctionTypeProps
import Strata.Languages.Core.Typing.Props.NamesWFProps
import Strata.Languages.Core.Typing.Props.ProcSigAgreementProps
import Strata.Languages.Core.Typing.Props.ProcedureTypeProps
import Strata.Languages.Core.Typing.Props.ProgramTypeProps
import Strata.Languages.Core.Typing.Props.SkolemScopeProps
import Strata.Languages.Core.Typing.Props.SkolemizerProps
import Strata.Languages.Core.Typing.Props.SourceExprResolveProps
import Strata.Languages.Core.Typing.Props.StatementEraseProps
import Strata.Languages.Core.Typing.Props.StatementTypeProps
import Strata.Languages.Core.Typing.Props.TypeSkolemProps
import Strata.Languages.Core.Typing.Props.TypingSpecProps
import Strata.Languages.Core.Typing.Props.WrittenTyVarScopeProps
import Strata.Languages.Core.Typing.Preservation.SmallStep
import Strata.Languages.Core.Typing.Preservation.Progress
import Strata.Languages.Core.Typing.Soundness
import Strata.Util.Random

import Strata.Examples.Embedded
import Strata.Examples.EmbeddedData
import Strata.Languages.Core.InterpreterReplayTactics

-- noimport: Strata.Util.IOTests (used for tests)
-- noimport: Strata.Util.Tests (used for tests)
-- noimport: Strata.CodeGen.TypeShape (meta module, used by the code generators)
-- noimport: Strata.Java.Gen (meta module, used by laurelJavaGen executable)
-- noimport: Strata.Go.Gen (meta module, used by laurelGoGen executable)
-- noimport: Strata.Go.GoIonRuntime (embedded Go support templates, used by Strata.Go.Gen)
