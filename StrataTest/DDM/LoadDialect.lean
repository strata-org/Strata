/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Test the #load_dialect command and also validate example dialects parse.
-/

import Strata.DDM.Integration.Lean

namespace Strata.Test

/--
error: Could not find file INVALID!
-/
#guard_msgs in
#load_dialect "INVALID!"

-- This tests that dialects must be loaded in order.

/--
error: 1 error(s) in ../../Examples/dialects/Arith.dialect.st:
  2:7: Unknown dialect Bool
-/
#guard_msgs in
#load_dialect "../../Examples/dialects/Arith.dialect.st"

#load_dialect "../../Examples/dialects/Bool.dialect.st"

namespace Bool
#strata_gen Bool

-- Test that boolLit has the expected signature
/--
info: Strata.Test.Bool.Expr.boolLit {α : Type} : α → (b : Ann _root_.Bool α) → Expr α
-/
#guard_msgs in
#check Expr.boolLit

end Bool

#load_dialect "../../Examples/dialects/Arith.dialect.st"

namespace Arith
#strata_gen Arith
end Arith

-- Test pipe-delimited identifiers (SMT-LIB/Boogie syntax)
#load_dialect "../../Examples/dialects/PipeIdent.dialect.st"

namespace PipeIdent
#strata_gen PipeIdent

-- Test that pipe-delimited identifiers can be parsed
def testPipeIdent := #strata
program PipeIdent;
|special-name| := 42;
|name with spaces| := 10;
result := |special-name| + |name with spaces|;
#end

/--
info: "program PipeIdent;\n(|special-name|) := 42;(|name with spaces|) := 10;(result) := |special-name| + |name with spaces|;"
-/
#guard_msgs in
#eval toString testPipeIdent.format

-- Test that || operator is not confused with pipe-delimited identifiers
def testOrOperator := #strata
program PipeIdent;
x := a || b;
y := |pipe-id| || |another-pipe|;
#end

/--
info: "program PipeIdent;\n(x) := a || b;(y) := |pipe-id| || |another-pipe|;"
-/
#guard_msgs in
#eval toString testOrOperator.format

end PipeIdent
