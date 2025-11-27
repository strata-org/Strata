-- Test the minimal Laurel grammar
import Strata.Languages.Laurel.Grammar.LaurelGrammar

-- Test parsing the AssertFalse example
def assertFalseTest := #strata
program LaurelMinimal;

val foo = procedure() {
  assert true;
  assert false;
  assert false;
}

val bar = procedure() {
  assume false;
  assert true;
}

#end

#eval IO.println assertFalseTest
#eval IO.println "Minimal Laurel grammar test completed"
