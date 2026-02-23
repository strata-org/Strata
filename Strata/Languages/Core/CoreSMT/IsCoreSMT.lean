/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Statement

/-!
# isCoreSMT Predicate

Defines predicates that characterize the subset of Strata Core that maps
directly to SMT-LIB constructs. Statements and expressions outside this subset
require alternative verification approaches (e.g., symbolic execution, loop
elimination).
-/

namespace Strata.Core.CoreSMT

open Imperative
open Lambda

/-- Predicate for expressions that map to SMT terms.
    Abstractions are supported only when immediately applied (translates to SMT let). -/
def isCoreSMTExpr : Core.Expression.Expr → Bool
  | .const _ _        => true
  | .fvar _ _ _       => true
  | .bvar _ _         => true
  | .op _ _ _         => true
  | .eq _ e1 e2       => isCoreSMTExpr e1 && isCoreSMTExpr e2
  | .ite _ c t e      => isCoreSMTExpr c && isCoreSMTExpr t && isCoreSMTExpr e
  | .quant _ _ _ tr b => isCoreSMTExpr tr && isCoreSMTExpr b
  | .app _ (.abs _ _ body) arg =>
      -- Immediately applied abstraction → SMT let
      isCoreSMTExpr body && isCoreSMTExpr arg
  | .app _ fn arg     => isCoreSMTExpr fn && isCoreSMTExpr arg
  | .abs _ _ _        => false  -- Standalone abstractions not supported

/-- Predicate for commands that map directly to SMT-LIB constructs. -/
def isCoreSMTCmd : Core.Command → Bool
  | .cmd (.assume _ e _)  => isCoreSMTExpr e
  | .cmd (.assert _ e _)  => isCoreSMTExpr e
  | .cmd (.cover _ e _)   => isCoreSMTExpr e
  | .cmd (.init _ _ e _)  => e.all isCoreSMTExpr
  | .cmd (.havoc _ _)     => false  -- Havoc not in CoreSMT subset
  | .cmd (.set _ _ _)     => false  -- Assignment requires symbolic execution
  | .call _ _ _ _         => false  -- Procedure calls not in CoreSMT subset

mutual
/-- Predicate for statements that map directly to SMT-LIB constructs. -/
def isCoreSMTStmt : Core.Statement → Bool
  | .cmd c              => isCoreSMTCmd c
  | .block _ stmts _    => isCoreSMTStmts stmts
  | .funcDecl _ _       => true
  | .ite _ _ _ _        => false
  | .loop _ _ _ _ _     => false
  | .goto _ _           => false

/-- Check all statements in a list are CoreSMT -/
def isCoreSMTStmts : Core.Statements → Bool
  | []      => true
  | s :: ss => isCoreSMTStmt s && isCoreSMTStmts ss
end

end Strata.Core.CoreSMT
