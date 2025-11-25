/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.B3.DDMFormatTests
import Strata.Languages.B3.DDMTransform.B3ToDDM
import Strata.Languages.B3.DDMTransform.DDMToB3

namespace B3

open Std (Format)
open Strata
open Strata.B3DDM

-- Helper to strip SourceRange annotations from Statement DDM and replace with Unit
mutual
  partial def stripStmtAnnotations : B3DDM.Statement SourceRange → B3DDM.Statement Unit
    | .var_decl_full _ name ty autoinv init =>
        .var_decl_full () ⟨(), name.val⟩ ⟨(), ty.val⟩ (stripAnnotations autoinv) (stripAnnotations init)
    | .var_decl_with_autoinv _ name ty autoinv =>
        .var_decl_with_autoinv () ⟨(), name.val⟩ ⟨(), ty.val⟩ (stripAnnotations autoinv)
    | .var_decl_with_init _ name ty init =>
        .var_decl_with_init () ⟨(), name.val⟩ ⟨(), ty.val⟩ (stripAnnotations init)
    | .var_decl_typed _ name ty =>
        .var_decl_typed () ⟨(), name.val⟩ ⟨(), ty.val⟩
    | .var_decl_inferred _ name init =>
        .var_decl_inferred () ⟨(), name.val⟩ (stripAnnotations init)
    | .val_decl _ name ty init =>
        .val_decl () ⟨(), name.val⟩ ⟨(), ty.val⟩ (stripAnnotations init)
    | .val_decl_inferred _ name init =>
        .val_decl_inferred () ⟨(), name.val⟩ (stripAnnotations init)
    | .assign _ lhs rhs =>
        .assign () ⟨(), lhs.val⟩ (stripAnnotations rhs)
    | .check _ expr =>
        .check () (stripAnnotations expr)
    | .assume _ expr =>
        .assume () (stripAnnotations expr)
    | .reach _ expr =>
        .reach () (stripAnnotations expr)
    | .assert _ expr =>
        .assert () (stripAnnotations expr)
    | .return_statement _ =>
        .return_statement ()
    | .block _ stmts =>
        .block () ⟨(), stmts.val.map stripStmtAnnotations⟩
    | .if_statement _ cond thenB elseB =>
        .if_statement () (stripAnnotations cond) (stripStmtAnnotations thenB) (stripElseAnnotations elseB)
    | .loop_statement _ invs body =>
        .loop_statement () ⟨(), invs.val.map stripInvariantAnnotations⟩ (stripStmtAnnotations body)
    | .exit_statement _ label =>
        .exit_statement () ⟨(), label.val.map (fun l => ⟨(), l.val⟩)⟩
    | .labeled_statement _ label stmt =>
        .labeled_statement () ⟨(), label.val⟩ (stripStmtAnnotations stmt)
    | .probe _ label =>
        .probe () ⟨(), label.val⟩
    | .aForall_statement _ var ty body =>
        .aForall_statement () ⟨(), var.val⟩ ⟨(), ty.val⟩ (stripStmtAnnotations body)
    | .choose_statement _ branches =>
        .choose_statement () (stripChoiceBranchesAnnotations branches)
    | .if_case_statement _ cases =>
        .if_case_statement () ⟨(), cases.val.map stripIfCaseBranchAnnotations⟩
    | .call_statement _ procName args =>
        .call_statement () ⟨(), procName.val⟩ ⟨(), args.val.map stripCallArgAnnotations⟩

  partial def stripElseAnnotations : B3DDM.Else SourceRange → B3DDM.Else Unit
    | .else_none _ => .else_none ()
    | .else_some _ stmt => .else_some () (stripStmtAnnotations stmt)

  partial def stripInvariantAnnotations : B3DDM.Invariant SourceRange → B3DDM.Invariant Unit
    | .invariant _ expr => .invariant () (stripAnnotations expr)

  partial def stripChoiceBranchesAnnotations : B3DDM.ChoiceBranches SourceRange → B3DDM.ChoiceBranches Unit
    | .choiceAtom _ branch => .choiceAtom () (stripChoiceBranchAnnotations branch)
    | .choicePush _ branches branch => .choicePush () (stripChoiceBranchesAnnotations branches) (stripChoiceBranchAnnotations branch)

  partial def stripChoiceBranchAnnotations : B3DDM.ChoiceBranch SourceRange → B3DDM.ChoiceBranch Unit
    | .choice_branch _ stmt => .choice_branch () (stripStmtAnnotations stmt)

  partial def stripIfCaseBranchAnnotations : B3DDM.IfCaseBranch SourceRange → B3DDM.IfCaseBranch Unit
    | .if_case_branch _ cond stmt => .if_case_branch () (stripAnnotations cond) (stripStmtAnnotations stmt)

  partial def stripCallArgAnnotations : B3DDM.CallArg SourceRange → B3DDM.CallArg Unit
    | .call_arg_expr _ expr => .call_arg_expr () (stripAnnotations expr)
    | .call_arg_out _ id => .call_arg_out () ⟨(), id.val⟩
    | .call_arg_inout _ id => .call_arg_inout () ⟨(), id.val⟩
end

-- Helper to perform the round-trip transformation for statements
-- DDM OperationF → B3 Stmt → DDM → formatted output
def doRoundtripStmt (stmt : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) : Format :=
  match B3DDM.Statement.ofAst stmt with
  | .ok ddmStmt =>
      let ddmStmtUnit := stripStmtAnnotations ddmStmt
      let b3Stmt := Stmt.fromDDM ddmStmtUnit
      dbg_trace f!"B3: {repr b3Stmt}"
      let ddmStmt' := b3Stmt.toDDM
      let ddmAst := ddmStmt'.toAst
      let ddmAstSR := argFUnitToSourceRange (ArgF.op ddmAst)
      cformat ddmAstSR ctx state
  | .error msg => s!"Parse error: {msg}"

-- Helper to extract statement from a program and apply round-trip transformation
def roundtripStmt (p : Program) : Format :=
  let ctx := p.formatContext {}
  let state := p.formatState
  match p.commands.toList with
  | [op] =>
    if op.name.name == "command_stmt" then
      match op.args.toList with
      | [ArgF.op stmt] => doRoundtripStmt stmt ctx state
      | _ => "Error: expected statement op"
    else s!"Error: expected command_stmt, got {op.name.name}"
  | _ => "Error: expected single command"

section StatementRoundtripTests

/--
info: B3: .assign () x (.literal () (Lambda.LConst.intConst 42))
---
info: x := 42
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; x := 42 #end

/--
info: B3: .check () (.binaryOp () .gt (.literal () (Lambda.LConst.intConst 5)) (.literal () (Lambda.LConst.intConst 0)))
---
info: check 5 > 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; check 5 > 0 #end

/--
info: B3: .assume () (.binaryOp () .ge (.literal () (Lambda.LConst.intConst 10)) (.literal () (Lambda.LConst.intConst 0)))
---
info: assume 10 >= 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; assume 10 >= 0 #end

/--
info: B3: .assert () (.binaryOp () .gt (.literal () (Lambda.LConst.intConst 5)) (.literal () (Lambda.LConst.intConst 0)))
---
info: assert 5 > 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; assert 5 > 0 #end

/--
info: B3: .reach () (.binaryOp () .eq (.literal () (Lambda.LConst.intConst 5)) (.literal () (Lambda.LConst.intConst 5)))
---
info: reach 5 == 5
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; reach 5 == 5 #end

/--
info: B3: .returnStmt ()
---
info: return
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; return #end

/--
info: B3: .blockStmt () [.assign () x (.literal () (Lambda.LConst.intConst 1)), .assign () y (.literal () (Lambda.LConst.intConst 2))]
---
info: {
  x := 1
  y := 2
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; { x := 1 y := 2 } #end

/--
info: B3: .ifStmt () (.id () flag) (.assign () x (.literal () (Lambda.LConst.intConst 1))) (some (.blockStmt () [.assign () x (.literal () (Lambda.LConst.intConst 0))]))
---
info: if flag ⏎
  x := 1
else ⏎
  {
    x := 0
  }
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; if flag x := 1 else { x := 0 } #end

/--
info: B3: .loop () [] (.blockStmt () [.assign () i (.binaryOp () .add (.id () i) (.literal () (Lambda.LConst.intConst 1)))])
---
info: loop ⏎
{
  i := i + 1
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; loop { i := i + 1 } #end

/--
info: B3: .loop () [.binaryOp () .ge (.id () i) (.literal () (Lambda.LConst.intConst 0)), .binaryOp () .le (.id () i) (.id () n)] (.blockStmt () [.assign () i (.binaryOp () .add (.id () i) (.literal () (Lambda.LConst.intConst 1)))])
---
info: loop
  invariant i >= 0
  invariant i <= n ⏎
{
  i := i + 1
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; loop invariant i >= 0 invariant i <= n { i := i + 1 } #end

/--
info: B3: .exit () (some "loop_start")
---
info: exit loop_start
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; exit loop_start #end

/--
info: B3: .labeledStmt () "loop_start" (.assign () x (.literal () (Lambda.LConst.intConst 0)))
---
info: loop_start: ⏎
x := 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; loop_start: x := 0 #end

/--
info: B3: .probe () "debug_point"
---
info: probe debug_point
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; probe debug_point #end

/--
info: B3: .varDecl () x (some "int") none none
---
info: var x : int
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; var x : int #end

/--
info: B3: .varDecl () x (some "bool") none (some (.literal () (Lambda.LConst.boolConst true)))
---
info: var x : bool := true
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; val x : bool := true #end

/--
info: B3: .varDecl () y (some "bool") none (some (.literal () (Lambda.LConst.boolConst true)))
---
info: var y : bool := true
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; var y : bool := true #end

/--
info: B3: .varDecl () z (some "int") (some (.binaryOp () .ge (.id () z) (.literal () (Lambda.LConst.intConst 0)))) none
---
info: var z : int autoinv z >= 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; var z : int autoinv z >= 0 #end

/--
info: B3: .aForall () x "int" (.blockStmt () [.check () (.binaryOp () .ge (.id () x) (.literal () (Lambda.LConst.intConst 0)))])
---
info: forall x : int ⏎
{
  check x >= 0
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; forall x : int { check x >= 0 } #end

/--
info: B3: .choose () [.blockStmt () [.assign () x (.literal () (Lambda.LConst.intConst 1))], .blockStmt () [.assign () x (.literal () (Lambda.LConst.intConst 2))]]
---
info: choose ⏎
{
  x := 2
} or ⏎
{
  x := 1
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; choose { x := 1 } or { x := 2 } #end

/--
info: B3: .ifCase () [(.binaryOp () .eq (.id () x) (.literal () (Lambda.LConst.intConst 1)), .blockStmt () [.assign () y (.literal () (Lambda.LConst.intConst 10))]), (.binaryOp () .eq (.id () x) (.literal () (Lambda.LConst.intConst 2)), .blockStmt () [.assign () y (.literal () (Lambda.LConst.intConst 20))])]
---
info: if
case x == 1 ⏎
{
  y := 10
}
case x == 2 ⏎
{
  y := 20
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; if case x == 1 { y := 10 } case x == 2 { y := 20 } #end

/--
info: B3: .call () "compute" [.out result, .expr (.id () a), .expr (.id () b)]
---
info:
compute(out result, a, b)
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; compute(out result, a, b) #end

/--
info: B3: .call () "modify" [.inout x, .out y]
---
info:
modify(inout x, out y)
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3; modify(inout x, out y) #end

end StatementRoundtripTests

end B3
