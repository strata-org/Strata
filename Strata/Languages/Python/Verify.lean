import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Python.PythonToDyn

namespace Strata

def pythonVerify (pgm: Strata.Program) : String :=
  "Python program:\n" ++ (toString pgm) ++ "\n" ++ "Dyn program\n" ++ (toString (pythonToDyn pgm)) ++ "\n"


end Strata
