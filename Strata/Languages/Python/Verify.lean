import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Python.PythonToBoogie

namespace Strata

def pythonVerify (pgm: Strata.Program) : String :=
  let boogiePgm :=pythonToBoogie pgm
  dbg_trace s!"Num decls: {boogiePgm.decls.length}"
  "Python program:\n" ++ (toString pgm) ++ "\n" ++ "Boogie program\n" ++ (toString boogiePgm) ++ "\n"


end Strata
