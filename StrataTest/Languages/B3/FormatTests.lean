/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Expression
import Strata.Languages.B3.Stmt

namespace B3

open Std (Format)

section ExpressionFormatTests

instance : Std.ToFormat defaultExprParams.Metadata where
   format _ := f!""

instance : Std.ToFormat defaultExprParams.Identifier where
   format id := f!"{id.name}"

instance : Coe String defaultExprParams.Identifier
 where
  coe s := B3Ident.mk s









end ExpressionFormatTests

section StatementFormatTests

















end StatementFormatTests

end B3
