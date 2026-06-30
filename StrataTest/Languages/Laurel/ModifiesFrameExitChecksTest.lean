/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
`insertFrameChecks` asserts the frame before every procedure exit (a `return` or an
`exit` of the body block) and at the fall-through tail, but not before an `exit` of
another label. Each wrap plus the tail adds one `assert`, so the counts pin which
exits are instrumented, including the `exit bodyLabel` arm no frontend reaches.
-/

import Strata.Languages.Laurel.ModifiesClauses

open Strata.Laurel

namespace StrataTest.Laurel.ModifiesFrameExitChecks

private def frame : StmtExprMd := { val := .LiteralBool true, source := none }
private def node (e : StmtExpr) : StmtExprMd := { val := e, source := none }
private def assertCount (e : StmtExprMd) : Nat :=
  (reprStr e |>.splitOn "assert").length - 1

#guard assertCount (insertFrameChecks default frame (node (.Return none))) == 2
#guard assertCount (insertFrameChecks default frame (node (.Exit bodyLabel))) == 2
#guard assertCount (insertFrameChecks default frame (node (.Exit "loop"))) == 1
#guard assertCount
  (insertFrameChecks default frame
    (node (.Block [node (.Exit bodyLabel), node (.Exit "loop")] none))) == 2

end StrataTest.Laurel.ModifiesFrameExitChecks
