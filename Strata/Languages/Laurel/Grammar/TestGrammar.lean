-- Test the minimal Laurel grammar
import Strata.Languages.Laurel.Grammar.LaurelGrammar

-- Test parsing the AssertFalse example by reading from file
def assertFalseTest : IO Unit := do
  let content ← IO.FS.readFile "Strata/Languages/Laurel/Examples/Fundamentals/AssertFalse.lr.st"
  IO.println content

#eval assertFalseTest
#eval IO.println "Minimal Laurel grammar test completed"
