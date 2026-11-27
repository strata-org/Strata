/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement

/-! # The obligations of a statement list and of a program

The `assert`/`cover` ids (label and metadata) of a statement list, at any depth, and of a
program's structured procedure bodies, in program order.  The back-links of the phases that
keep labels find the statement an obligation id stands for among them (`sameId`).

Key definitions: `stmtsObls`, `programObls`, `sameId`. -/

namespace Core
namespace ObligationIds

open Imperative

public section

/-- Does `i` identify the same `assert`/`cover` as `a`: the same label and metadata? -/
@[expose] def sameId (a i : AssertId Expression) : Bool :=
  i.label == a.label && decide (i.md = a.md)

mutual
/-- The `assert`/`cover` ids of a statement list, in order. -/
@[expose] def stmtsObls : Statements → List (AssertId Expression)
  | [] => []
  | s :: rest => stmtObls s ++ stmtsObls rest
/-- The `assert`/`cover` ids of a statement, in order. -/
@[expose] def stmtObls : Statement → List (AssertId Expression)
  | .cmd (.cmd (.assert l _ md)) | .cmd (.cmd (.cover l _ md)) => [{ label := l, md := md }]
  | .block _ ss _ => stmtsObls ss
  | .ite _ tss ess _ => stmtsObls tss ++ stmtsObls ess
  | .loop _ _ _ body _ => stmtsObls body
  | _ => []
end

/-- The `assert`/`cover` ids of a program's structured procedure bodies, in order. -/
@[expose] def programObls (p : Program) : List (AssertId Expression) :=
  p.decls.flatMap fun d =>
    match d with
    | .proc proc _ =>
      match proc.body with
      | .structured ss _ => stmtsObls ss
      | .cfg _ _ | .abstract => []
    | _ => []

end -- public section

end ObligationIds
end Core
