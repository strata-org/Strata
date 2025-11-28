/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.B3.DDMFormatTests
import Strata.Languages.B3.DDMConversion

namespace B3

open Std (Format)
open Strata
open Strata.B3CST

-- Helper to strip SourceRange annotations from Statement DDM and replace with Unit
mutual
  partial def stripStmtAnnotations : B3CST.Statement SourceRange → B3CST.Statement Unit
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
    | .reinit_statement _ v =>
        .reinit_statement () ⟨(), v.val⟩
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

  partial def stripElseAnnotations : B3CST.Else SourceRange → B3CST.Else Unit
    | .else_none _ => .else_none ()
    | .else_some _ stmt => .else_some () (stripStmtAnnotations stmt)

  partial def stripInvariantAnnotations : B3CST.Invariant SourceRange → B3CST.Invariant Unit
    | .invariant _ expr => .invariant () (stripAnnotations expr)

  partial def stripChoiceBranchesAnnotations : B3CST.ChoiceBranches SourceRange → B3CST.ChoiceBranches Unit
    | .choiceAtom _ branch => .choiceAtom () (stripChoiceBranchAnnotations branch)
    | .choicePush _ branches branch => .choicePush () (stripChoiceBranchesAnnotations branches) (stripChoiceBranchAnnotations branch)

  partial def stripChoiceBranchAnnotations : B3CST.ChoiceBranch SourceRange → B3CST.ChoiceBranch Unit
    | .choice_branch _ stmt => .choice_branch () (stripStmtAnnotations stmt)

  partial def stripIfCaseBranchAnnotations : B3CST.IfCaseBranch SourceRange → B3CST.IfCaseBranch Unit
    | .if_case_branch _ cond stmt => .if_case_branch () (stripAnnotations cond) (stripStmtAnnotations stmt)

  partial def stripCallArgAnnotations : B3CST.CallArg SourceRange → B3CST.CallArg Unit
    | .call_arg_expr _ expr => .call_arg_expr () (stripAnnotations expr)
    | .call_arg_out _ id => .call_arg_out () ⟨(), id.val⟩
    | .call_arg_inout _ id => .call_arg_inout () ⟨(), id.val⟩
end

-- Helper to perform the round-trip transformation for statements
-- DDM OperationF → B3 Stmt → DDM → formatted output
def doRoundtripStmt (stmt : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) : Format :=
  match B3CST.Statement.ofAst stmt with
  | .ok cstStmt =>
      let cstStmtUnit := stripStmtAnnotations cstStmt
      let b3Stmt := Stmt.fromDDM cstStmtUnit
      let reprStr := (repr b3Stmt).pretty.replace "Strata.B3AST.Statement." "."
      let reprStr := reprStr.replace "Strata.B3AST.Expression." "."
      let reprStr := reprStr.replace "Strata.B3AST.Literal." "."
      let reprStr := reprStr.replace "Strata.B3AST.UnaryOp." "."
      let reprStr := reprStr.replace "Strata.B3AST.BinaryOp." "."
      let reprStr := reprStr.replace "Strata.B3AST.Pattern." "."
      let reprStr := reprStr.replace "Strata.B3AST.CallArg." "."
      let reprStr := reprStr.replace "Strata.B3AST.OneIfCase." "."
      dbg_trace f!"B3: {reprStr}"
      let cstStmt' := b3Stmt.toDDM
      let cstAst := cstStmt'.toAst
      let cstAstSR := argFUnitToSourceRange (ArgF.op cstAst)
      cformat cstAstSR ctx state
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
info: B3: .blockStmt
  ()
  { ann := (),
    val := #[.varDecl
               ()
               { ann := (), val := "x" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .assign
               ()
               { ann := (), val := 0 }
               (.literal () (.intLit () { ann := (), val := 42 }))] }
---
info:
{
  var x : int
  x := 42
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; {var x: int x := 42} #end

/--
info: B3: .check
  ()
  (.binaryOp
    ()
    (.gt ())
    (.literal () (.intLit () { ann := (), val := 5 }))
    (.literal () (.intLit () { ann := (), val := 0 })))
---
info:
check 5 > 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; check 5 > 0 #end

/--
info: B3: .assume
  ()
  (.binaryOp
    ()
    (.ge ())
    (.literal () (.intLit () { ann := (), val := 10 }))
    (.literal () (.intLit () { ann := (), val := 0 })))
---
info:
assume 10 >= 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; assume 10 >= 0 #end

/--
info: B3: .assert
  ()
  (.binaryOp
    ()
    (.gt ())
    (.literal () (.intLit () { ann := (), val := 5 }))
    (.literal () (.intLit () { ann := (), val := 0 })))
---
info:
assert 5 > 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; assert 5 > 0 #end

/--
info: B3: .reach
  ()
  (.binaryOp
    ()
    (.eq ())
    (.literal () (.intLit () { ann := (), val := 5 }))
    (.literal () (.intLit () { ann := (), val := 5 })))
---
info:
reach 5 == 5
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; reach 5 == 5 #end

/--
info: B3: .returnStmt ()
---
info:
return
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; return #end

/--
info: B3: .blockStmt
  ()
  { ann := (),
    val := #[.varDecl
               ()
               { ann := (), val := "x" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .varDecl
               ()
               { ann := (), val := "y" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .blockStmt
               ()
               { ann := (),
                 val := #[.assign
                            ()
                            { ann := (), val := 1 }
                            (.literal
                              ()
                              (.intLit () { ann := (), val := 1 })),
                          .assign
                            ()
                            { ann := (), val := 0 }
                            (.literal
                              ()
                              (.intLit () { ann := (), val := 2 }))] }] }
---
info:
{
  var x : int
  var y : int
  {
    x := 1
    y := 2
  }
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var x: int var y: int { x := 1 y := 2 } } #end

/--
info: B3: .blockStmt
  ()
  { ann := (),
    val := #[.varDecl
               ()
               { ann := (), val := "flag" }
               { ann := (), val := some { ann := (), val := "bool" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .varDecl
               ()
               { ann := (), val := "x" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .ifStmt
               ()
               (.id () { ann := (), val := 1 })
               (.assign
                 ()
                 { ann := (), val := 0 }
                 (.literal () (.intLit () { ann := (), val := 1 })))
               { ann := (),
                 val := some (.blockStmt
                          ()
                          { ann := (),
                            val := #[.assign
                                       ()
                                       { ann := (), val := 0 }
                                       (.literal
                                         ()
                                         (.intLit () { ann := (), val := 0 }))] }) }] }
---
info:
{
  var flag : bool
  var x : int
  if flag ⏎
    x := 1
  else ⏎
    {
      x := 0
    }
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST;{ var flag: bool var x: int if flag x := 1 else { x := 0 } } #end

/--
info: B3: .blockStmt
  ()
  { ann := (),
    val := #[.varDecl
               ()
               { ann := (), val := "i" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .loop
               ()
               { ann := (), val := #[] }
               (.blockStmt
                 ()
                 { ann := (),
                   val := #[.assign
                              ()
                              { ann := (), val := 0 }
                              (.binaryOp
                                ()
                                (.add ())
                                (.id () { ann := (), val := 0 })
                                (.literal
                                  ()
                                  (.intLit () { ann := (), val := 1 })))] })] }
---
info:
{
  var i : int
  loop ⏎
  {
    i := i + 1
  }
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var i: int loop { i := i + 1 } } #end

/--
info: B3: .blockStmt
  ()
  { ann := (),
    val := #[.varDecl
               ()
               { ann := (), val := "i" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .varDecl
               ()
               { ann := (), val := "n" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .loop
               ()
               { ann := (),
                 val := #[.binaryOp
                            ()
                            (.ge ())
                            (.id () { ann := (), val := 1 })
                            (.literal
                              ()
                              (.intLit () { ann := (), val := 0 })),
                          .binaryOp
                            ()
                            (.le ())
                            (.id () { ann := (), val := 1 })
                            (.id () { ann := (), val := 0 })] }
               (.blockStmt
                 ()
                 { ann := (),
                   val := #[.assign
                              ()
                              { ann := (), val := 1 }
                              (.binaryOp
                                ()
                                (.add ())
                                (.id () { ann := (), val := 1 })
                                (.literal
                                  ()
                                  (.intLit () { ann := (), val := 1 })))] })] }
---
info:
{
  var i : int
  var n : int
  loop
    invariant i >= 0
    invariant i <= n ⏎
  {
    i := i + 1
  }
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var i: int var n: int loop invariant i >= 0 invariant i <= n { i := i + 1 } } #end

/--
info: B3: .exit () { ann := (), val := some { ann := (), val := "loop_start" } }
---
info:
exit loop_start
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; exit loop_start #end

/--
info: B3: .labeledStmt
  ()
  { ann := (), val := "labeled_block" }
  (.blockStmt
    ()
    { ann := (),
      val := #[.varDecl
                 ()
                 { ann := (), val := "x" }
                 { ann := (), val := some { ann := (), val := "int" } }
                 { ann := (), val := none }
                 { ann := (), val := none },
               .assign
                 ()
                 { ann := (), val := 0 }
                 (.literal () (.intLit () { ann := (), val := 0 }))] })
---
info: labeled_block: ⏎
{
  var x : int
  x := 0
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; labeled_block: {var x: int x := 0} #end

/--
info: B3: .probe () { ann := (), val := "debug_point" }
---
info:
probe debug_point
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; probe debug_point #end

/--
info: B3: .varDecl
  ()
  { ann := (), val := "x" }
  { ann := (), val := some { ann := (), val := "int" } }
  { ann := (), val := none }
  { ann := (), val := none }
---
info:
var x : int
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; var x : int #end

/--
info: B3: .varDecl
  ()
  { ann := (), val := "x" }
  { ann := (), val := some { ann := (), val := "bool" } }
  { ann := (), val := none }
  { ann := (),
    val := some (.literal () (.boolLit () { ann := (), val := true })) }
---
info:
var x : bool := true
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; val x : bool := true #end

/--
info: B3: .varDecl
  ()
  { ann := (), val := "y" }
  { ann := (), val := some { ann := (), val := "bool" } }
  { ann := (), val := none }
  { ann := (),
    val := some (.literal () (.boolLit () { ann := (), val := true })) }
---
info:
var y : bool := true
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; var y : bool := true #end

/--
info: B3: .varDecl
  ()
  { ann := (), val := "z" }
  { ann := (), val := some { ann := (), val := "int" } }
  { ann := (),
    val := some (.binaryOp
             ()
             (.ge ())
             (.id () { ann := (), val := 0 })
             (.literal () (.intLit () { ann := (), val := 0 }))) }
  { ann := (), val := none }
---
info:
var z : int autoinv @0 >= 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; var z : int autoinv z >= 0 #end

/--
info: B3: .aForall
  ()
  { ann := (), val := "x" }
  { ann := (), val := "int" }
  (.blockStmt
    ()
    { ann := (),
      val := #[.check
                 ()
                 (.binaryOp
                   ()
                   (.ge ())
                   (.id () { ann := (), val := 0 })
                   (.literal () (.intLit () { ann := (), val := 0 })))] })
---
info:
forall x : int ⏎
{
  check x >= 0
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; forall x : int { check x >= 0 } #end

/--
info: B3: .choose
  ()
  { ann := (),
    val := #[.blockStmt
               ()
               { ann := (),
                 val := #[.assign
                            ()
                            { ann := (), val := 0 }
                            (.literal
                              ()
                              (.intLit () { ann := (), val := 2 }))] },
             .blockStmt
               ()
               { ann := (),
                 val := #[.assign
                            ()
                            { ann := (), val := 0 }
                            (.literal
                              ()
                              (.intLit () { ann := (), val := 1 }))] }] }
---
info:
choose ⏎
{
  @0 := 1
} or ⏎
{
  @0 := 2
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; choose { x := 1 } or { x := 2 } #end

/--
info: B3: .blockStmt
  ()
  { ann := (),
    val := #[.varDecl
               ()
               { ann := (), val := "x" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .varDecl
               ()
               { ann := (), val := "y" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .ifCase
               ()
               { ann := (),
                 val := #[.oneIfCase
                            ()
                            (.binaryOp
                              ()
                              (.eq ())
                              (.id () { ann := (), val := 1 })
                              (.literal
                                ()
                                (.intLit () { ann := (), val := 1 })))
                            (.blockStmt
                              ()
                              { ann := (),
                                val := #[.assign
                                           ()
                                           { ann := (), val := 0 }
                                           (.literal
                                             ()
                                             (.intLit () { ann := (), val := 10 }))] }),
                          .oneIfCase
                            ()
                            (.binaryOp
                              ()
                              (.eq ())
                              (.id () { ann := (), val := 1 })
                              (.literal
                                ()
                                (.intLit () { ann := (), val := 2 })))
                            (.blockStmt
                              ()
                              { ann := (),
                                val := #[.assign
                                           ()
                                           { ann := (), val := 0 }
                                           (.literal
                                             ()
                                             (.intLit () { ann := (), val := 20 }))] })] }] }
---
info:
{
  var x : int
  var y : int
  if
  case x == 1 ⏎
  {
    y := 10
  }
  case x == 2 ⏎
  {
    y := 20
  }
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var x: int var y: int if case x == 1 { y := 10 } case x == 2 { y := 20 } } #end

/--
info: B3: .blockStmt
  ()
  { ann := (),
    val := #[.varDecl
               ()
               { ann := (), val := "a" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .varDecl
               ()
               { ann := (), val := "b" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .call
               ()
               { ann := (), val := "compute" }
               { ann := (),
                 val := #[.callArgOut () { ann := (), val := "result" },
                          .callArgExpr () (.id () { ann := (), val := 1 }),
                          .callArgExpr
                            ()
                            (.id () { ann := (), val := 0 })] }] }
---
info:
{
  var a : int
  var b : int
  compute(out result, a, b)
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var a: int var b: int compute(out result, a, b) } #end

/--
info: B3: .blockStmt
  ()
  { ann := (),
    val := #[.varDecl
               ()
               { ann := (), val := "x" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .varDecl
               ()
               { ann := (), val := "y" }
               { ann := (), val := some { ann := (), val := "int" } }
               { ann := (), val := none }
               { ann := (), val := none },
             .call
               ()
               { ann := (), val := "modify" }
               { ann := (),
                 val := #[.callArgInout () { ann := (), val := "x" },
                          .callArgOut () { ann := (), val := "y" }] }] }
---
info:
{
  var x : int
  var y : int
  modify(inout x, out y)
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var x: int var y: int modify(inout x, out y) } #end

end StatementRoundtripTests

end B3
