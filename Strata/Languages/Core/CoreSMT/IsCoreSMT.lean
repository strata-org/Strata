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

Each predicate returns `Except String` where the error case provides a
human-readable reason why the construct is not in the CoreSMT subset.
-/

namespace Strata.Core.CoreSMT

open Imperative
open Lambda

/-- Check if a monomorphic type is SMT-native (int, bool, real, string, bitvec, Map, arrow). -/
def isCoreSMTMonoTy : LMonoTy → Except String Unit
  | .tcons "int" []      => .ok ()
  | .tcons "bool" []     => .ok ()
  | .tcons "real" []     => .ok ()
  | .tcons "string" []   => .ok ()
  | .bitvec _            => .ok ()
  | .tcons "Map" [k, v]  => do isCoreSMTMonoTy k; isCoreSMTMonoTy v
  | .tcons "arrow" [a, b] => do isCoreSMTMonoTy a; isCoreSMTMonoTy b
  | .ftvar _              => .ok ()  -- type variables are allowed (polymorphic)
  | ty                   => .error s!"type '{repr ty}' is not an SMT-native type"

/-- Check if a type scheme is SMT-native. -/
def isCoreSMTTy : LTy → Except String Unit
  | .forAll _ mty => isCoreSMTMonoTy mty

/-- Predicate for expressions that map to SMT terms.
    Abstractions are supported only when immediately applied (translates to SMT let). -/
def checkCoreSMTExpr : Core.Expression.Expr → Except String Unit
  | .const _ _        => .ok ()
  | .fvar _ _ _       => .ok ()
  | .bvar _ _         => .ok ()
  | .op _ _ _         => .ok ()
  | .eq _ e1 e2       => do checkCoreSMTExpr e1; checkCoreSMTExpr e2
  | .ite _ c t e      => do checkCoreSMTExpr c; checkCoreSMTExpr t; checkCoreSMTExpr e
  | .quant _ _ _ _ tr b => do checkCoreSMTExpr tr; checkCoreSMTExpr b
  | .app _ (.abs _ _ _ body) arg => do checkCoreSMTExpr body; checkCoreSMTExpr arg
  | .app _ fn arg     => do checkCoreSMTExpr fn; checkCoreSMTExpr arg
  | .abs _ _ _ _        => .error "standalone abstraction is not supported in CoreSMT"

/-- Boolean version for backward compatibility -/
def isCoreSMTExpr (e : Core.Expression.Expr) : Bool :=
  (checkCoreSMTExpr e).isOk

/-- Check a command is in the CoreSMT subset. -/
def checkCoreSMTCmd : Core.Command → Except String Unit
  | .cmd (.assume _ e _)       => checkCoreSMTExpr e
  | .cmd (.assert _ e _)       => checkCoreSMTExpr e
  | .cmd (.cover _ e _)        => checkCoreSMTExpr e
  | .cmd (.init _ ty eOpt _)   => do
      isCoreSMTTy ty
      match eOpt with
      | .det e => checkCoreSMTExpr e
      | .nondet => .ok ()
  | .cmd (.set _ .nondet _)    => .ok ()  -- havoc (nondet set) is ok
  | .cmd (.set _ (.det _) _)   => .error "assignment (set) is not in the CoreSMT subset"
  | .call _ _ _              => .error "procedure call is not in the CoreSMT subset"

/-- Boolean version for backward compatibility -/
def isCoreSMTCmd (c : Core.Command) : Bool :=
  (checkCoreSMTCmd c).isOk

mutual
/-- Check a statement is in the CoreSMT subset. -/
def checkCoreSMTStmt : Core.Statement → Except String Unit
  | .cmd c              => checkCoreSMTCmd c
  | .block _ _ _        => .error "block statement is not in the CoreSMT subset; use .ite .nondet for push/pop semantics"
  | .funcDecl _ _       => .ok ()
  | .typeDecl _ _       => .ok ()
  | .ite .nondet thenB elseB _ => do checkCoreSMTStmts thenB; checkCoreSMTStmts elseB
  | .ite (.det _) _ _ _ => .error "deterministic if-then-else statement is not in the CoreSMT subset"
  | .loop _ _ _ _ _     => .error "loop statement is not in the CoreSMT subset"
  | .exit _ _           => .error "exit statement is not in the CoreSMT subset"

/-- Check all statements in a list are CoreSMT -/
def checkCoreSMTStmts : Core.Statements → Except String Unit
  | []      => .ok ()
  | s :: ss => do checkCoreSMTStmt s; checkCoreSMTStmts ss
end

/-- Boolean version for backward compatibility -/
def isCoreSMTStmt (s : Core.Statement) : Bool :=
  (checkCoreSMTStmt s).isOk

/-- Boolean version for backward compatibility -/
def isCoreSMTStmts (ss : Core.Statements) : Bool :=
  (checkCoreSMTStmts ss).isOk

end Strata.Core.CoreSMT
