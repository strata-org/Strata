import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Python.PythonToBoogie
import Strata.Languages.Boogie.DDMTransform.Parse
import StrataTest.Internal.BoogiePrelude
import Strata.Languages.Boogie.Verifier

namespace Strata

private def f : Strata.Program := boogiePrelude

def pythonVerify (pgm: Strata.Program) : IO String := do
  let boogiePgm := pythonSSAToBoogie pgm
  --dbg_trace f!"Python program:\n" ++ (toString pgm) ++ "\n" ++ "Boogie program\n" ++ (toString boogiePgm) ++ "\n"
  let vcResults ← EIO.toIO (fun f => IO.Error.userError (toString f))
                        (Boogie.verify "z3" boogiePgm Options.default)
  let mut s := ""
  for vcResult in vcResults do
    s := s ++ s!"\n{vcResult.obligation.label}: {Std.format vcResult.result}\n"
  return s

end Strata
