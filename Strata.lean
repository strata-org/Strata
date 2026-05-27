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
import Strata.DL.Lambda.Lambda
import Strata.DL.Imperative

/- Utilities -/
import Strata.Util.NameProofs
import Strata.Util.Sarif

/- Strata Languages -/
import Strata.Languages.Core.FactoryWF
import Strata.Languages.Core.SeqModel
import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.SarifOutput

import Strata.Languages.Laurel.Grammar
import Strata.Languages.Laurel.LaurelCompilationPipeline

/- Code Transforms -/
import Strata.Transform.CallElimCorrect
import Strata.Transform.CoreSpecification
import Strata.Transform.DetToKleeneCorrect
import Strata.Transform.ProcBodyVerifyCorrect
import Strata.Transform.Specification

/- Strata Languages — additional -/
import Strata.Languages.B3
import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify
import Strata.Languages.Core.EntryPoint
import Strata.Languages.Core.VerifierProofs
import Strata.Languages.Dyn.Dyn
import Strata.Languages.Dyn.Verify
import Strata.Languages.Python.Python

/- DDM -/
import StrataDDM

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

-- noimport:
import Strata.DL.Imperative.CFGSemantics
import Strata.DL.Imperative.SemanticsProps
import Strata.DL.Lambda.Denote.Assumptions
import Strata.DL.Lambda.Denote.CallOfLFuncDenote
import Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LExprDenoteConstrs
import Strata.DL.Lambda.Denote.LExprDenoteEq
import Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.DL.Lambda.Denote.LExprDenoteSubst
import Strata.DL.Lambda.Denote.LExprDenoteTySubst
import Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.MetaData
import Strata.DL.Lambda.Reflect
import Strata.DL.Lambda.Semantics
import Strata.DL.Lambda.TypeFactoryWF
import Strata.DL.Util.HList
import Strata.Languages.Core.ProgramWF
import Strata.Languages.Core.StatementWF
import Strata.Languages.Dyn.DDMTransform.Parse
import Strata.Languages.Dyn.DDMTransform.Translate
import Strata.Util.Random
