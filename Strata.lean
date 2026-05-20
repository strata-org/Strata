/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- This module serves as the root of the `Strata` library.
-- In each category, imports are sorted by alphabetical order.
module
/- DDM -/
import Strata.DDM.Integration.Lean
import Strata.DDM.Ion

/- Dialect Library -/
import Strata.DL.SMT.SMT
import Strata.DL.Lambda.Lambda
import Strata.DL.Imperative.Imperative

/- Utilities -/
import Strata.Util.NameProofs
import Strata.Util.Sarif

/- Strata Languages -/
import Strata.Languages.Core.FactoryWF
import Strata.Languages.Core.SeqModel
import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.SarifOutput
import Strata.Languages.Laurel.LaurelCompilationPipeline

/- Code Transforms -/
import Strata.Transform.CallElimCorrect
import Strata.Transform.CoreSpecification
import Strata.Transform.DetToKleeneCorrect
import Strata.Transform.ProcBodyVerifyCorrect
import Strata.Transform.Specification

/- Strata Languages — additional -/
import Strata.Languages.B3
import Strata.Languages.Boole.Boole
import Strata.Languages.Boole.Verify
import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify
import Strata.Languages.Core.EntryPoint
import Strata.Languages.Core.VerifierProofs
import Strata.Languages.Dyn.Dyn
import Strata.Languages.Dyn.Verify
import Strata.Languages.Python.Python

/- DDM -/
import Strata.DDM

/- Backends -/
import Strata.Backends.CBMC

/- Dialect Library — additional (can't go in aggregates due to cycles) -/
import Strata.DL.Imperative.CFGToCProverGOTO
import Strata.DL.Imperative.ToCProverGOTO
import Strata.DL.SMT.Denote
import Strata.DL.SMT.FactoryCorrect
import Strata.DL.SMT.Translate

/- Code Transforms — additional -/
import Strata.Transform.StructuredToUnstructured

/- Other -/
import Strata.MetaVerifier

/- Simple API -/
import Strata.SimpleAPI

/- Pipeline -/
import Strata.Pipeline.PyAnalyzeLaurel

 -- deletion candidates: nothing imports these modules:

-- noimport: Strata.DL.Imperative.CFGSemantics
-- noimport: Strata.DL.Imperative.SemanticsProps
-- noimport: Strata.DL.Lambda.Denote.Assumptions
-- noimport: Strata.DL.Lambda.Denote.CallOfLFuncDenote
-- noimport: Strata.DL.Lambda.Denote.LExprDenote
-- noimport: Strata.DL.Lambda.Denote.LExprDenoteConstrs
-- noimport: Strata.DL.Lambda.Denote.LExprDenoteEq
-- noimport: Strata.DL.Lambda.Denote.LExprDenoteProps
-- noimport: Strata.DL.Lambda.Denote.LExprDenoteSubst
-- noimport: Strata.DL.Lambda.Denote.LExprDenoteTySubst
-- noimport: Strata.DL.Lambda.Denote.LExprSemanticsConsistent
-- noimport: Strata.DL.Lambda.LExprType
-- noimport: Strata.DL.Lambda.LExprTypeSpec
-- noimport: Strata.DL.Lambda.MetaData
-- noimport: Strata.DL.Lambda.Reflect
-- noimport: Strata.DL.Lambda.Semantics
-- noimport: Strata.DL.Lambda.TypeFactoryWF
-- noimport: Strata.DL.Util.HList
-- noimport: Strata.Languages.Core.ProgramWF
-- noimport: Strata.Languages.Core.StatementWF
-- noimport: Strata.Languages.Dyn.DDMTransform.Parse
-- noimport: Strata.Languages.Dyn.DDMTransform.Translate
-- noimport: Strata.Util.Random
