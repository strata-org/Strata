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
import Strata.Util.Sarif
import Strata.Util.Worklist

/- Strata Languages -/
import Strata.Languages.Core.FactoryWF
import Strata.Languages.Core.SeqModel
import Strata.Languages.Core.SMTEncoderProps
import Strata.Languages.Core.SMTEmitter
import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.SarifOutput
import Strata.Languages.Core.WFProps

import Strata.Languages.Laurel
import Strata.Languages.Laurel.CliOptions
import Strata.Languages.Laurel.Grammar
import Strata.Languages.Laurel.Interpreter
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.Laurel.LaurelASTProps
import Strata.Languages.Laurel.ResolutionProps

/- Code Transforms -/
import Strata.Transform.CallElimCorrect
import Strata.Transform.CoreSpecification
import Strata.Languages.Core.ProcedureProps
import Strata.Transform.CoreTransformProps
import Strata.Transform.DetToKleeneCorrect
import Strata.Transform.FunctionInlining
import Strata.Transform.FunctionInliningProps
import Strata.Transform.LiftInternalFuncDecls
import Strata.Transform.LiftInternalFuncDeclsCorrect
import Strata.Transform.LoopInitHoist
import Strata.Transform.LoopInitHoistCorrect
import Strata.Transform.NondetElim
import Strata.Transform.NondetElimCorrect
import Strata.Transform.NondetElimProps
import Strata.Transform.ProcBodyVerifyCorrect
import Strata.Transform.SpecHoareConnection
import Strata.Transform.StructuredToUnstructured
import Strata.Transform.StructuredToUnstructuredCorrect
import Strata.Transform.StructuredToUnstructuredPipeline
import Strata.Transform.StructuredToUnstructuredPipelineCorrect

/- Program Logics -/
import Strata.DL.Imperative.Logic.HoareTemplate
import Strata.Languages.Core.Logic.LangDefProps
import Strata.Languages.Core.Logic.Hoare
import Strata.Languages.Core.Logic.ContractToHoareTriple
import Strata.Languages.Core.Logic.ContractToHoareTripleProps

/- Strata Languages — additional -/
import Strata.Languages.B3
import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify
import Strata.Languages.Core.EntryPoint
import Strata.Languages.Core.ProgramFact
import Strata.Languages.Core.ProgramFactProps
import Strata.Languages.Core.ProgramFactSet
import Strata.Languages.Core.ProgramFactSetProps
import Strata.Languages.Core.PipelinePhaseProps
import Strata.Languages.Core.VerifierProofs
import Strata.Languages.Dyn.Dyn
import Strata.Languages.Dyn.Verify
import Strata.Languages.GOTO
import Strata.Languages.Laurel.FilterPrelude
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslatorProps

/- DDM -/
import StrataDDM

/- Backends -/
import Strata.Backends.CBMC

/- Dialect Library — additional (can't go in aggregates due to cycles) -/
import Strata.DL.SMT.Denote
import Strata.DL.SMT.FactoryCorrect
import Strata.DL.SMT.Translate
import Strata.DL.SMT.DenoteTyped
import Strata.DL.SMT.DenoteTypedProps
import Strata.DL.SMT.DenoteSemanticsEquiv
import Strata.DL.SMT.DenoteTypedSMTQuery

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
import Strata.Cli.Framework
import Strata.Cli.VerifyOptions

 -- deletion candidates: nothing imports these modules:

-- noimport:
import Strata.DL.Imperative.CFGSemantics
import Strata.DL.Imperative.CFGSemanticsProps
import Strata.DL.Lambda.Denote.Assumptions
import Strata.DL.Lambda.Denote.CallOfLFuncDenote
import Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LExprDenoteConstrs
import Strata.DL.Lambda.Denote.LExprDenoteEq
import Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.DL.Lambda.Denote.LExprDenoteSubst
import Strata.DL.Lambda.Denote.LExprDenoteTySubst
import Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import Strata.DL.Lambda.LExprTProps
import Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.LExprTraversal
import Strata.DL.Lambda.LExprTraversalProps
import Strata.DL.Lambda.Reflect
import Strata.DL.Lambda.Semantics
import Strata.DL.Lambda.TypeFactoryWF
import Strata.Util.HListProps
import Strata.Languages.Core.ProgramWF
import Strata.Languages.Core.StatementWF
import Strata.DL.Lambda.DatatypeWF
import Strata.Languages.Core.ProcedureTypeSpec
import Strata.Languages.Core.DatatypeTypeSpec
import Strata.Languages.Core.ProgramTypeSpec
import Strata.Languages.Dyn.DDMTransform.Parse
import Strata.Languages.Dyn.DDMTransform.Translate
import Strata.Util.Random


import Strata.Examples.Embedded
import Strata.Examples.EmbeddedData

-- noimport: Strata.Util.IOTests (used for tests)
-- noimport: Strata.Java.Gen (meta module, used by laurelJavaGen executable)

import Strata.DL.SMT.DenoteTypedFactoryCorrect
import Strata.Languages.Core.VerifiedSMTGen.SMTEncoder
import Strata.Languages.Core.VerifiedSMTGen.ProofObligation
import Strata.Languages.Core.VerifiedSMTGen.SharedWF
import Strata.Languages.Core.VerifiedSMTGen.TranslateSound
import Strata.Languages.Core.VerifiedSMTGen.CollectSound
import Strata.Languages.Core.VerifiedSMTGen.EncoderSound
