/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.BuiltinDialects
public import Strata.Languages.Boole.Boole
public import Strata.Languages.Core.DDMTransform.Grammar
public import Strata.Languages.Dyn.DDMTransform.Parse
public import Strata.Languages.B3.DDMTransform.DefinitionAST
public import Strata.Languages.B3.DDMTransform.ParseCST
public import Strata.Languages.Laurel.Grammar.LaurelGrammar
public import Strata.Languages.Python.PythonDialect
public import Strata.Languages.Python.Specs.DDM
public import Strata.DL.SMT.DDMTransform.Parse

/-! All dialects bundled with the `strata` binary.  Both the `strata`
CLI and the `productivityCheck` script load dialects from this list so
that they stay in sync. -/

public section

namespace Strata

/-- Dialects shipped with the binary, in dependency order (each dialect
appears after all of its imports). -/
def bundledDialects : Array Dialect := #[
  initDialect,
  headerDialect,
  StrataDDL,
  smtReservedKeywordsDialect,
  SMTCore,
  SMT,
  SMTResponse,
  Core,
  Boole,
  Dyn,
  Python.Python,
  Python.Specs.DDM.PythonSpecs,
  B3AST,
  B3CST,
  Laurel.Laurel
]

end Strata

end
