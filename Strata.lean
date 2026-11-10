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

/- Utilities -/
import Strata.Util.NameProofs
import Strata.Util.OrderedSetProps
import Strata.Util.RealProps
import Strata.Util.IonDeserializer
import Strata.Util.Sarif
import Strata.Util.Worklist

/- Strata Languages -/
import Strata.Languages.Core.BitVecEvalProps
import Strata.Languages.Core.IntEvalProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Languages.Core.InstExprTyping
import Strata.Languages.Core.FactoryWF
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
import Strata.Transform.CoreSpecification
import Strata.Transform.CoreSpecificationProps
import Strata.Languages.Core.Analysis.ProcedureCorrectness
import Strata.Languages.Core.Analysis.ProcedureCorrectnessProps
import Strata.Languages.Core.Analysis.DeductiveVerification
import Strata.Languages.Core.Analysis.DeductiveVerificationProps
import Strata.Languages.Core.Analysis.FragmentFactory
import Strata.DL.Lambda.LFuncEvalSound
import Strata.DL.Lambda.LExprRenameOps
import Strata.Transform.MonomorphizeBasics
import Strata.Transform.MonomorphizeWorklist
import Strata.Transform.MonomorphizeInstances
import Strata.Transform.MonomorphizeFunctionsCorrect
import Strata.Languages.Core.ProcedureProps
import Strata.Languages.Core.ProgramProps
import Strata.Transform.CoreTransformProps
import Strata.Transform.DetToKleeneCorrect
import Strata.Transform.FunctionInlining
import Strata.Transform.FunctionInliningProps
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
import Strata.Transform.RecursiveFunctionAxioms
import Strata.Transform.SpecHoareConnection
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
import Strata.Languages.Core.Logic.LangDefProps
import Strata.Languages.Core.Logic.FactoryInterp
import Strata.Languages.Core.Logic.TraceInterpUsingDenote
import Strata.Languages.Core.Logic.Hoare
import Strata.Languages.Core.Logic.HoareCall
import Strata.Languages.Core.Logic.ContractToHoareTriple
import Strata.Languages.Core.Logic.ContractToHoareTripleProps

/- Strata Languages — additional -/
import Strata.Languages.B3
import Strata.Languages.Cortex
import Strata.Languages.Core.EntryPoint
import Strata.Languages.Core.IncrementalSolve
import Strata.Languages.Core.IncrementalSolveCorrect
import Strata.Languages.Core.DeclFormulas
import Strata.Languages.Core.ProgramFact
import Strata.Languages.Core.ProgramFactProps
import Strata.Languages.Core.ProgramFactSet
import Strata.Languages.Core.ProgramFactSetProps
import Strata.Languages.Core.PipelinePhaseProps
import Strata.Languages.Core.VerifierProofs
import Strata.Languages.GOTO

/- DDM -/
import StrataDDM

/- Backends -/
import Strata.Backends.CBMC

/- Dialect Library — additional (can't go in aggregates due to cycles) -/
import Strata.DL.SMT.Denote
import Strata.DL.SMT.DenoteProps
import Strata.DL.SMT.FactoryCorrect
import Strata.DL.SMT.Translate
import Strata.DL.SMT.DenoteTyped
import Strata.DL.SMT.DenoteTypedProps
import Strata.DL.SMT.DenoteSemanticsEquiv
import Strata.DL.SMT.DenoteTypedSMTQuery
import Strata.DL.SMT.SymbolProps
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
-- The WP and SSA phases: their properties, the failure preservation of the SSA phase, and
-- the properties of their Core instance.
import Strata.Transform.SSA.SSAEval
import Strata.Transform.SSA.SSAOver
import Strata.Transform.WP.WPProps
import Strata.Util.RopeProps
import Strata.Util.LeftistHeapProps
import Strata.Transform.Passive.CoreProgram
import Strata.Transform.Passive.CoreProgramProps
import Strata.Transform.Passive.DeclObligationsCoreCorrect
import Strata.Transform.Passive.CoreWPSSA
import Strata.Transform.Passive.CoreWPSSAProps
import Strata.Transform.Passive.CoreTyped
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

/- The monadic interpreter: the monad-generic engine, its soundness and completeness against
   the reference event semantics, Core's instantiation, the `EvalM`
   instance and its soundness and completeness, and counterexample replay -/
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
import Strata.Languages.Core.InterpreterObs
import Strata.Languages.Core.InterpreterObsProps
import Strata.Languages.Core.InterpreterSound
import Strata.Languages.Core.StmtCallFree

 -- deletion candidates: nothing imports these modules:

-- noimport:
import Strata.DL.Lambda.Denote.Assumptions
import Strata.DL.Lambda.Denote.CallOfLFuncDenote
import Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LExprDenoteCompute
import Strata.DL.Lambda.Denote.LExprDenoteConstrs
import Strata.DL.Lambda.Denote.LExprDenoteEq
import Strata.DL.Lambda.LExprDenoteEval
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LExprEvalFully
import Strata.DL.Lambda.LExprEvalFuelProps
import Strata.DL.Lambda.LExprEvalAnnotateProps
import Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.DL.Lambda.Denote.LExprDenoteSubst
import Strata.DL.Lambda.Denote.LExprDenoteTySubst
import Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import Strata.DL.Lambda.LExprTProps
import Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.LExprTraversal
import Strata.DL.Lambda.LExprTraversalProps
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
import Strata.Languages.Core.ProcedureTypeSpec
import Strata.Languages.Core.ProcedureTypeProps
import Strata.Languages.Core.DatatypeTypeSpec
import Strata.Languages.Core.DatatypeTypeSpecProps
import Strata.Languages.Core.ProgramTypeSpec
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.Languages.Core.Typing.Spec.TypingSpec
import Strata.Languages.Core.FactoryProps
import Strata.Languages.Core.Typing.Props.FactoryRegistrationProps
import Strata.Languages.Core.Typing.Props.ProcSigAgreementProps
import Strata.Languages.Core.Typing.Props.TypingSpecProps
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
