-- Test the minimal Laurel grammar
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import StrataTest.DDM.TestGrammar
import Strata.DDM.BuiltinDialects.Init

open Strata
open StrataTest.DDM

namespace Laurel

-- Test parsing the AssertFalse example
def testAssertFalse : IO Unit := do
  -- Create LoadedDialects with the Init and Laurel dialects
  let laurelDialect: Strata.Dialect := Laurel
  let loader := Elab.LoadedDialects.ofDialects! #[initDialect, laurelDialect]

  -- Test the file
  let result ← testGrammarFile loader "Laurel" "Strata/Languages/Laurel/Examples/AssertFalse.lr.st"

  -- Print results
  printTestResult "AssertFalse.lr.st" result (showFormatted := true)

#eval testAssertFalse
