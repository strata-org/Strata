/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.Statement
open Boogie Lambda Imperative

namespace Names

def initVarValue (id : BoogieIdent) (suffix : String) : Expression.Expr :=
  .fvar ("init_" ++ id.2 ++ suffix) none

end Names
