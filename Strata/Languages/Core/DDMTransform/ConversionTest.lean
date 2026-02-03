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
#check CoreCSTDDM.Expression.nat_lit 42
#check CoreCSTDDM.Expression.bool_true
#check CoreCSTDDM.Expression.var_ref ⟨"x"⟩

-- Test simple statement conversion  
#check CoreCSTDDM.Statement.var_decl ⟨"x"⟩ (.builtin "int")
#check CoreCSTDDM.Statement.assign_stmt ⟨"x"⟩ (.nat_lit 42)

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
