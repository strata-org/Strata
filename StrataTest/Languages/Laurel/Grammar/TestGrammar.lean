-- Test the minimal Laurel grammar
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import StrataTest.DDM.TestGrammar
import Strata.DDM.BuiltinDialects.Init

open Strata
open StrataTest.DDM

namespace Laurel

-- Test parsing the AssertFalse example
def testAssertFalse : IO Bool := do
  -- Create LoadedDialects with the Init and Laurel dialects
  let laurelDialect: Strata.Dialect := Laurel
  let loader := Elab.LoadedDialects.ofDialects! #[initDialect, laurelDialect]

  -- Test the file
  let filePath := "Strata/Languages/Laurel/Examples/AssertFalse.lr.st"
  let result ← testGrammarFile loader "Laurel" filePath

  pure result.normalizedMatch

#eval do
  let success ← testAssertFalse
  if !success then
    throw (IO.userError "Test failed: formatted output does not match input")
