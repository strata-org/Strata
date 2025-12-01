
import Strata.Languages.Boogie.Program
import Strata.Languages.Boogie.Verifier
import Strata.Languages.Laurel.Laurel

namespace Laurel

open Boogie (VCResult VCResults)

mutual
def verify (smtsolver : String) (program : Program)
    (options : Options := Options.default) : IO VCResults := do
  let boogieProgram := translate program
  EIO.toIO (fun f => IO.Error.userError (toString f))
      (Boogie.verify smtsolver boogieProgram options)

def translate (program : Program) : Boogie.Program := sorry

end
