/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement

/-! # Call-free Core statements

`StmtCallFree` / `StmtsCallFree` decide syntactically that a statement (list) contains
no procedure `.call` at any position, recursively. -/

namespace Core

public section
noncomputable section

mutual
/-- No procedure `.call` at *this* statement's own positions, recursively. -/
@[expose] def StmtCallFree : Statement → Bool
  | .cmd (.cmd _) => true
  | .cmd (.call _ _ _) => false
  | .block _ b _ => StmtsCallFree b
  | .ite _ t e _ => StmtsCallFree t && StmtsCallFree e
  | .loop _ _ _ body _ => StmtsCallFree body
  | .exit _ _ => true
  | .typeDecl _ _ => true
/-- `StmtCallFree` over a statement list. -/
@[expose] def StmtsCallFree : List Statement → Bool
  | [] => true
  | s :: rest => StmtCallFree s && StmtsCallFree rest
end

end -- noncomputable section
end -- public section

end Core
