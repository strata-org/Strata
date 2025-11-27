-- Test the minimal Laurel grammar
import Strata.Languages.Laurel.Grammar.LaurelGrammar

-- Test parsing the AssertFalse example
def assertFalseTest := #strata
program LaurelMinimal;

procedure foo() {
  assert true;
  assert false;
  assert false;
}

procedure bar() {
  assume false;
  assert true;
}

#end

#eval IO.println assertFalseTest
#eval IO.println "Minimal Laurel grammar test completed"
