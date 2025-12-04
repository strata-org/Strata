/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST

import Strata.Languages.Boogie.DDMTransform.Parse

namespace Strata



namespace Python
#load_dialect "../../../Tools/Python/test_results/dialects/Python.dialect.st.ion"
#strata_gen Python

/--
Return the annotation associated with an expression

FIXME. #strata_gen should eventually generate a more optimized version of this automatically.
-/
def expr.ann {α} [Inhabited α] (expr : Python.expr α) : α := expr.toAst |>.ann


end Python


end Strata
