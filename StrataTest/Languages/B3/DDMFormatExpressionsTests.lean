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

-- Helper to perform the round-trip transformation and format
-- DDM OperationF → B3 AST → DDM → formatted output
partial def doRoundtrip (e : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) : Format :=
  match B3CST.Expression.ofAst e with
  | .ok cstExpr =>
      let b3Expr := Expression.toAST cstExpr
      let b3ExprUnit := b3Expr.toUnit
      let reprStr := (repr b3ExprUnit).pretty.replace "Strata.B3AST.Expression." "."
      let reprStr := reprStr.replace "Strata.B3AST.Literal." "."
      let reprStr := reprStr.replace "Strata.B3AST.UnaryOp." "."
      let reprStr := reprStr.replace "Strata.B3AST.BinaryOp." "."
      let reprStr := reprStr.replace "Strata.B3AST.Pattern." "."
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
info: B3: .id () { ann := (), val := 0 }
---
info: @0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check x #end

/--
info: B3: .binaryOp
  ()
  (.add ())
  (.literal () (.intLit () { ann := (), val := 5 }))
  (.literal () (.intLit () { ann := (), val := 3 }))
---
info: 5 + 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 5 + 3 #end

/--
info: B3: .literal () (.boolLit () { ann := (), val := true })
---
info: true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check true #end

/--
info: B3: .literal () (.boolLit () { ann := (), val := false })
---
info: false
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check false #end

/--
info: B3: .unaryOp
  ()
  (.not ())
  (.literal () (.boolLit () { ann := (), val := true }))
---
info: !true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check !true #end

/--
info: B3: .binaryOp
  ()
  (.sub ())
  (.literal () (.intLit () { ann := (), val := 10 }))
  (.literal () (.intLit () { ann := (), val := 3 }))
---
info: 10 - 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 10 - 3 #end

/--
info: B3: .binaryOp
  ()
  (.mul ())
  (.literal () (.intLit () { ann := (), val := 4 }))
  (.literal () (.intLit () { ann := (), val := 5 }))
---
info: 4 * 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 4 * 5 #end

/--
info: B3: .binaryOp
  ()
  (.div ())
  (.literal () (.intLit () { ann := (), val := 20 }))
  (.literal () (.intLit () { ann := (), val := 4 }))
---
info: 20 div 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 20 div 4 #end

/--
info: B3: .binaryOp
  ()
  (.mod ())
  (.literal () (.intLit () { ann := (), val := 17 }))
  (.literal () (.intLit () { ann := (), val := 5 }))
---
info: 17 mod 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 17 mod 5 #end

/--
info: B3: .binaryOp
  ()
  (.eq ())
  (.literal () (.intLit () { ann := (), val := 5 }))
  (.literal () (.intLit () { ann := (), val := 5 }))
---
info: 5 == 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 5 == 5 #end

/--
info: B3: .binaryOp
  ()
  (.neq ())
  (.literal () (.intLit () { ann := (), val := 3 }))
  (.literal () (.intLit () { ann := (), val := 7 }))
---
info: 3 != 7
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 3 != 7 #end

/--
info: B3: .binaryOp
  ()
  (.le ())
  (.literal () (.intLit () { ann := (), val := 3 }))
  (.literal () (.intLit () { ann := (), val := 5 }))
---
info: 3 <= 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 3 <= 5 #end

/--
info: B3: .binaryOp
  ()
  (.lt ())
  (.literal () (.intLit () { ann := (), val := 2 }))
  (.literal () (.intLit () { ann := (), val := 8 }))
---
info: 2 < 8
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 2 < 8 #end

/--
info: B3: .binaryOp
  ()
  (.ge ())
  (.literal () (.intLit () { ann := (), val := 10 }))
  (.literal () (.intLit () { ann := (), val := 5 }))
---
info: 10 >= 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 10 >= 5 #end

/--
info: B3: .binaryOp
  ()
  (.gt ())
  (.literal () (.intLit () { ann := (), val := 15 }))
  (.literal () (.intLit () { ann := (), val := 3 }))
---
info: 15 > 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 15 > 3 #end

/--
info: B3: .binaryOp
  ()
  (.add ())
  (.literal () (.intLit () { ann := (), val := 2 }))
  (.binaryOp
    ()
    (.mul ())
    (.literal () (.intLit () { ann := (), val := 3 }))
    (.literal () (.intLit () { ann := (), val := 4 })))
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
    (.literal () (.intLit () { ann := (), val := 2 }))
    (.literal () (.intLit () { ann := (), val := 3 })))
  (.literal () (.intLit () { ann := (), val := 4 }))
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
    (.literal () (.intLit () { ann := (), val := 1 }))
    (.literal () (.intLit () { ann := (), val := 2 })))
  (.literal () (.intLit () { ann := (), val := 3 }))
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
    (.literal () (.intLit () { ann := (), val := 1 }))
    (.literal () (.intLit () { ann := (), val := 2 })))
  (.literal () (.intLit () { ann := (), val := 5 }))
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
    (.literal () (.intLit () { ann := (), val := 10 }))
    (.literal () (.intLit () { ann := (), val := 3 })))
  (.literal () (.intLit () { ann := (), val := 2 }))
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
    (.literal () (.intLit () { ann := (), val := 20 }))
    (.literal () (.intLit () { ann := (), val := 4 })))
  (.literal () (.intLit () { ann := (), val := 3 }))
---
info: 20 div 4 * 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 20 div 4 * 3 #end

/--
info: B3: .binaryOp
  ()
  (.lt ())
  (.literal () (.intLit () { ann := (), val := 1 }))
  (.binaryOp
    ()
    (.add ())
    (.binaryOp
      ()
      (.mul ())
      (.literal () (.intLit () { ann := (), val := 2 }))
      (.literal () (.intLit () { ann := (), val := 3 })))
    (.literal () (.intLit () { ann := (), val := 4 })))
---
info: 1 < 2 * 3 + 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 1 < 2 * 3 + 4 #end

/--
info: B3: .ite
  ()
  (.literal () (.boolLit () { ann := (), val := true }))
  (.literal () (.intLit () { ann := (), val := 1 }))
  (.literal () (.intLit () { ann := (), val := 0 }))
---
info: if true then 1 else 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check if true then 1 else 0 #end

/--
info: B3: .quantifierExpr
  ()
  (Strata.B3AST.QuantifierKind.forall ())
  { ann := (), val := "i" }
  { ann := (), val := "int" }
  { ann := (), val := #[] }
  (.binaryOp
    ()
    (.ge ())
    (.id () { ann := (), val := 0 })
    (.literal () (.intLit () { ann := (), val := 0 })))
---
info: forall i : int i >= 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check forall i : int i >= 0 #end

/--
info: B3: .quantifierExpr
  ()
  (Strata.B3AST.QuantifierKind.exists ())
  { ann := (), val := "y" }
  { ann := (), val := "bool" }
  { ann := (), val := #[] }
  (.binaryOp
    ()
    (.or ())
    (.id () { ann := (), val := 0 })
    (.unaryOp
      ()
      (.not ())
      (.id () { ann := (), val := 0 })))
---
info: exists y : bool y || !y
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check exists y : bool y || !y #end

/--
info: B3: .quantifierExpr
  ()
  (Strata.B3AST.QuantifierKind.forall ())
  { ann := (), val := "x" }
  { ann := (), val := "int" }
  { ann := (),
    val := #[.pattern
               ()
               { ann := (),
                 val := #[.functionCall
                            ()
                            { ann := (), val := "f" }
                            { ann := (), val := #[.id () { ann := (), val := 0 }] }] }] }
  (.binaryOp
    ()
    (.gt ())
    (.functionCall
      ()
      { ann := (), val := "f" }
      { ann := (), val := #[.id () { ann := (), val := 0 }] })
    (.literal () (.intLit () { ann := (), val := 0 })))
---
info: forall x : int pattern f(x), f(x) > 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check forall x : int pattern f(x), f(x) > 0 #end

/--
info: B3: .quantifierExpr
  ()
  (Strata.B3AST.QuantifierKind.exists ())
  { ann := (), val := "y" }
  { ann := (), val := "bool" }
  { ann := (),
    val := #[.pattern
               ()
               { ann := (),
                 val := #[.unaryOp
                            ()
                            (.not ())
                            (.id () { ann := (), val := 0 })] },
             .pattern
               ()
               { ann := (), val := #[.id () { ann := (), val := 0 }] }] }
  (.binaryOp
    ()
    (.or ())
    (.id () { ann := (), val := 0 })
    (.unaryOp
      ()
      (.not ())
      (.id () { ann := (), val := 0 })))
---
info: exists y : bool pattern y, pattern !y, y || !y
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check exists y : bool pattern y, pattern !y, y || !y #end

/--
info: B3: .quantifierExpr
  ()
  (Strata.B3AST.QuantifierKind.forall ())
  { ann := (), val := "z" }
  { ann := (), val := "int" }
  { ann := (),
    val := #[.pattern
               ()
               { ann := (),
                 val := #[.binaryOp
                            ()
                            (.mul ())
                            (.id () { ann := (), val := 0 })
                            (.literal
                              ()
                              (.intLit () { ann := (), val := 2 }))] },
             .pattern
               ()
               { ann := (),
                 val := #[.binaryOp
                            ()
                            (.add ())
                            (.id () { ann := (), val := 0 })
                            (.literal
                              ()
                              (.intLit () { ann := (), val := 1 }))] },
             .pattern
               ()
               { ann := (), val := #[.id () { ann := (), val := 0 }] }] }
  (.binaryOp
    ()
    (.gt ())
    (.id () { ann := (), val := 0 })
    (.literal () (.intLit () { ann := (), val := 0 })))
---
info: forall z : int pattern z, pattern z + 1, pattern z * 2, z > 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check forall z : int pattern z, pattern z + 1, pattern z * 2, z > 0 #end

end ExpressionRoundtripTests

end B3
