/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.Conversion

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------

/- Basic tests for CoreCST ↔ CoreAST conversion -/

-- Test simple expression conversion
#check CoreCSTDDM.Expression.nat_lit
#check CoreCSTDDM.Expression.bool_true
#check CoreCSTDDM.Expression.var_ref

-- Test simple statement conversion  
#check CoreCSTDDM.Statement.var_decl
#check CoreCSTDDM.Statement.assign_stmt

-- Test conversion functions exist
#check convertExprCSTToAST
#check convertExprASTToCST
#check convertStmtCSTToAST
#check convertStmtASTToCST

-- Test main conversion functions
#check cstToAST
#check astToCST
#check roundTripCST

---------------------------------------------------------------------

end Strata
