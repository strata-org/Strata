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
import Strata.DL.SMT.Translate

/- Code Transforms — additional -/
import Strata.Transform.StructuredToUnstructured

/- Other -/
import Strata.MetaVerifier

/- Simple API -/
import Strata.SimpleAPI

-- noimport: Strata.Util.Random -- deletion candidate: nothing imports this module
