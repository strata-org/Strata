/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.B3.DDMFormatTests
import Strata.Languages.B3.DDMTransform.Conversion

namespace B3

open Std (Format)
open Strata
open Strata.B3CST

-- Helper to perform the round-trip transformation and format
-- DDM OperationF → B3 AST → DDM → formatted output
partial def doRoundtrip (e : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) : Format :=
  match B3CST.Expression.ofAst e with
  | .ok cstExpr =>
      let b3Expr := Expression.toAST cstExpr
      let b3ExprUnit := b3Expr.toUnit
      let reprStr := (repr b3ExprUnit).pretty
      let reprStr := cleanupExprRepr reprStr
      let reprStr := cleanupUnitRepr reprStr
      dbg_trace f!"B3: {reprStr}"
      let cstExpr' := Expression.toCST b3Expr
      let cstAst := cstExpr'.toAst
      cformat (ArgF.op cstAst) ctx state
  | .error msg => s!"Parse error: {msg}"

-- Helper to extract expression from a program and apply round-trip transformation
def roundtripExpr (p : Program) : Format :=
  let ctx := p.formatContext {}
  let state := p.formatState
  match p.commands.toList with
  | [op] =>
    if op.name.name == "command_stmt" then
      match op.args.toList with
      | [ArgF.op stmt] =>
        if stmt.name.name == "check" then
          match stmt.args.toList with
          | [ArgF.op e] => doRoundtrip e ctx state
          | _ => s!"Error: expected op in check, got {repr stmt.args.toList}"
        else s!"Error: expected check statement, got {stmt.name.name}"
      | _ => "Error: expected statement op"
    else if op.name.name == "command_decl" then
       match op.args.toList with
      | [ArgF.op decl] =>
        if decl.name.name == "axiom_decl" then
          match decl.args.toList with
          | [ArgF.op body] =>
            if body.name.name == "axiom" then
              match body.args.toList with
              | [ArgF.op e] => doRoundtrip e ctx state
              | _ => s!"Error: expected op in axiom body, got {repr body.args.toList}"
            else if body.name.name == "explain_axiom" then
              match body.args.toList with
              | [_, ArgF.op e] => doRoundtrip e ctx state
              | _ => s!"Error: expected names and op in explain_axiom, got {repr body.args.toList}"
            else s!"Error: expected axiom or explain_axiom body, got {body.name.name}"
          | _ => s!"Error: expected AxiomBody in axiom_decl, got {repr decl.args.toList}"
        else s!"Error: expected axiom declaration, got {decl.name.name}"
      | _ => "Error: expected axiom op"
    else
      s!"Error: expected command_stmt or command_decl, got {op.name.name}"
  | _ => "Error: expected single command"

section ExpressionRoundtripTests

-- We are loosing the context so this is why it's printing that way.
/--
info: B3: .id () 0
---
info: @0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check x #end

/--
info: B3: .binaryOp
  ()
  (.add ())
  (.literal () (.intLit () 5))
  (.literal () (.intLit () 3))
---
info: 5 + 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 5 + 3 #end

/--
info: B3: .literal () (.boolLit () true)
---
info: true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check true #end

/--
info: B3: .literal () (.boolLit () false)
---
info: false
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check false #end

/--
info: B3: .unaryOp
  ()
  (.not ())
  (.literal () (.boolLit () true))
---
info: !true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check !true #end

/--
info: B3: .binaryOp
  ()
  (.sub ())
  (.literal () (.intLit () 10))
  (.literal () (.intLit () 3))
---
info: 10 - 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 10 - 3 #end

/--
info: B3: .binaryOp
  ()
  (.mul ())
  (.literal () (.intLit () 4))
  (.literal () (.intLit () 5))
---
info: 4 * 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 4 * 5 #end

/--
info: B3: .binaryOp
  ()
  (.div ())
  (.literal () (.intLit () 20))
  (.literal () (.intLit () 4))
---
info: 20 div 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 20 div 4 #end

/--
info: B3: .binaryOp
  ()
  (.mod ())
  (.literal () (.intLit () 17))
  (.literal () (.intLit () 5))
---
info: 17 mod 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 17 mod 5 #end

/--
info: B3: .binaryOp
  ()
  (.eq ())
  (.literal () (.intLit () 5))
  (.literal () (.intLit () 5))
---
info: 5 == 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 5 == 5 #end

/--
info: B3: .binaryOp
  ()
  (.neq ())
  (.literal () (.intLit () 3))
  (.literal () (.intLit () 7))
---
info: 3 != 7
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 3 != 7 #end

/--
info: B3: .binaryOp
  ()
  (.le ())
  (.literal () (.intLit () 3))
  (.literal () (.intLit () 5))
---
info: 3 <= 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 3 <= 5 #end

/--
info: B3: .binaryOp
  ()
  (.lt ())
  (.literal () (.intLit () 2))
  (.literal () (.intLit () 8))
---
info: 2 < 8
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 2 < 8 #end

/--
info: B3: .binaryOp
  ()
  (.ge ())
  (.literal () (.intLit () 10))
  (.literal () (.intLit () 5))
---
info: 10 >= 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 10 >= 5 #end

/--
info: B3: .binaryOp
  ()
  (.gt ())
  (.literal () (.intLit () 15))
  (.literal () (.intLit () 3))
---
info: 15 > 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 15 > 3 #end

/--
info: B3: .binaryOp
  ()
  (.add ())
  (.literal () (.intLit () 2))
  (.binaryOp
    ()
    (.mul ())
    (.literal () (.intLit () 3))
    (.literal () (.intLit () 4)))
---
info: 2 + 3 * 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 2 + 3 * 4 #end

/--
info: B3: .binaryOp
  ()
  (.mul ())
  (.binaryOp
    ()
    (.add ())
    (.literal () (.intLit () 2))
    (.literal () (.intLit () 3)))
  (.literal () (.intLit () 4))
---
info: (2 + 3) * 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check (2 + 3) * 4 #end

/--
info: B3: .binaryOp
  ()
  (.add ())
  (.binaryOp
    ()
    (.add ())
    (.literal () (.intLit () 1))
    (.literal () (.intLit () 2)))
  (.literal () (.intLit () 3))
---
info: 1 + 2 + 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 1 + 2 + 3 #end

/--
info: B3: .binaryOp
  ()
  (.lt ())
  (.binaryOp
    ()
    (.add ())
    (.literal () (.intLit () 1))
    (.literal () (.intLit () 2)))
  (.literal () (.intLit () 5))
---
info: 1 + 2 < 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 1 + 2 < 5 #end

/--
info: B3: .binaryOp
  ()
  (.add ())
  (.binaryOp
    ()
    (.sub ())
    (.literal () (.intLit () 10))
    (.literal () (.intLit () 3)))
  (.literal () (.intLit () 2))
---
info: 10 - 3 + 2
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 10 - 3 + 2 #end

/--
info: B3: .binaryOp
  ()
  (.mul ())
  (.binaryOp
    ()
    (.div ())
    (.literal () (.intLit () 20))
    (.literal () (.intLit () 4)))
  (.literal () (.intLit () 3))
---
info: 20 div 4 * 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 20 div 4 * 3 #end

/--
info: B3: .binaryOp
  ()
  (.lt ())
  (.literal () (.intLit () 1))
  (.binaryOp
    ()
    (.add ())
    (.binaryOp
      ()
      (.mul ())
      (.literal () (.intLit () 2))
      (.literal () (.intLit () 3)))
    (.literal () (.intLit () 4)))
---
info: 1 < 2 * 3 + 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 1 < 2 * 3 + 4 #end

/--
info: B3: .ite
  ()
  (.literal () (.boolLit () true))
  (.literal () (.intLit () 1))
  (.literal () (.intLit () 0))
---
info: if true then 1 else 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check if true then 1 else 0 #end

/--
info: B3: .quantifierExpr
  ()
  (.forall ())
  u "i"
  u "int"
  u #[]
  (.binaryOp
    ()
    (.ge ())
    (.id () 0)
    (.literal () (.intLit () 0)))
---
info: forall i : int i >= 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check forall i : int i >= 0 #end

/--
info: B3: .quantifierExpr
  ()
  (.exists ())
  u "y"
  u "bool"
  u #[]
  (.binaryOp
    ()
    (.or ())
    (.id () 0)
    (.unaryOp () (.not ()) (.id () 0)))
---
info: exists y : bool y || !y
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check exists y : bool y || !y #end

/--
info: B3: .quantifierExpr
  ()
  (.forall ())
  u "x"
  u "int"
  u #[.pattern
    ()
    u #[.functionCall
      ()
      u "f"
      u #[.id () 0],
    .functionCall
      ()
      u "f"
      u #[.id () 0]]]
  (.binaryOp
    ()
    (.gt ())
    (.functionCall
      ()
      u "f"
      u #[.id () 0])
    (.literal () (.intLit () 0)))
---
info: forall x : int pattern f(x), f(x) f(x) > 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check forall x : int pattern f(x), f(x) f(x) > 0 #end

/--
info: B3: .quantifierExpr
  ()
  (.exists ())
  u "y"
  u "bool"
  u #[.pattern
    ()
    u #[.unaryOp
      ()
      (.not ())
      (.id () 0)],
  .pattern () u #[.id () 0]]
  (.binaryOp
    ()
    (.or ())
    (.id () 0)
    (.unaryOp () (.not ()) (.id () 0)))
---
info: exists y : bool pattern y pattern !y y || !y
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check exists y : bool pattern y pattern !y y || !y #end

/--
info: B3: .quantifierExpr
  ()
  (.forall ())
  u "z"
  u "int"
  u #[.pattern
    ()
    u #[.binaryOp
      ()
      (.mul ())
      (.id () 0)
      (.literal () (.intLit () 2))],
  .pattern
    ()
    u #[.binaryOp
      ()
      (.add ())
      (.id () 0)
      (.literal () (.intLit () 1))],
  .pattern () u #[.id () 0]]
  (.binaryOp
    ()
    (.gt ())
    (.id () 0)
    (.literal () (.intLit () 0)))
---
info: forall z : int pattern z pattern z + 1 pattern z * 2 z > 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check forall z : int pattern z pattern z + 1 pattern z * 2 z > 0 #end

end ExpressionRoundtripTests

end B3
