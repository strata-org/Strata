import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Python.PythonToBoogie
import Strata.Languages.Boogie.DDMTransform.Parse
import StrataTest.Internal.BoogiePrelude

namespace Strata

private def f : Strata.Program := boogiePrelude

def pythonVerify (pgm: Strata.Program) : String :=
  let boogiePgm :=pythonToBoogie pgm
  "Python program:\n" ++ (toString pgm) ++ "\n" ++ "Boogie program\n" ++ (toString boogiePgm) ++ "\n"


end Strata
