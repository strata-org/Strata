import Strata.DDM.Elab
import Strata.DDM.AST

import Strata.Languages.Boogie.DDMTransform.Parse

import Strata.Languages.Boogie.Boogie
import Strata.Languages.Python.PythonDialect
import StrataTest.Internal.FunctionSignatures

namespace Strata

def pythonASTToBoogie (pgm: Strata.Program): Boogie.Program :=
  {decls := []}

end Strata
