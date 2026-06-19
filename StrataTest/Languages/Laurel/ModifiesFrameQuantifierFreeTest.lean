/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Structural check, independent of the solver: the enumerated modifies frame
(`buildEnumeratedFrame`) must contain no quantifier, so there is nothing for the
solver to instantiate. The `∀`-based frame it replaces (`buildPointwiseFrame`)
does contain one; asserting both pins the property and shows the check
discriminates between the two encodings.
-/

import Strata.Languages.Laurel.ModifiesClauses

open Strata.Laurel

namespace StrataTest.Laurel.ModifiesFrameQuantifierFree

private def selfRef : StmtExprMd := { val := .Var (.Local "self"), source := none }
private def heapIn  : StmtExprMd := { val := .Var (.Local "$heap_in"), source := none }
private def heapOut : StmtExprMd := { val := .Var (.Local "$heap"), source := none }
private def singleRefModifies : List ModifiesEntry := [.single selfRef]

/-- Whether the (pretty-printed) frame mentions a quantifier. -/
private def hasQuantifier (e : StmtExprMd) : Bool :=
  let s := reprStr e
  (s.splitOn "forall").length > 1 || (s.splitOn "exists").length > 1

#guard !hasQuantifier (buildEnumeratedFrame default singleRefModifies heapIn heapOut)
#guard  hasQuantifier (buildPointwiseFrame   default singleRefModifies heapIn heapOut)

end StrataTest.Laurel.ModifiesFrameQuantifierFree
