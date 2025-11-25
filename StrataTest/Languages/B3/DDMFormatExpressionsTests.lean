/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.B3.DDMFormatTests

namespace B3

open Std (Format)
open Strata
open Strata.B3DDM

-- Helper to perform the round-trip transformation and format
-- DDM OperationF → B3 AST → DDM → formatted output
def doRoundtrip (e : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) : Format :=
  match B3DDM.Expression.ofAst e with
  | .ok ddmExpr =>
      let ddmExprUnit := stripAnnotations ddmExpr
      let b3Expr := Expression.fromDDM ddmExprUnit
      dbg_trace f!"B3: {repr b3Expr}"
      let ddmExpr' := b3Expr.toDDM
      let ddmAst := ddmExpr'.toAst
      let ddmAstSR := argFUnitToSourceRange (ArgF.op ddmAst)
      cformat ddmAstSR ctx state
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

/--
info: B3: .id () x
---
info: x
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check x #end

/--
info: B3: .binaryOp () .add (.literal () (Lambda.LConst.intConst 5)) (.literal () (Lambda.LConst.intConst 3))
---
info: 5 + 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 5 + 3 #end

/--
info: B3: .literal () (Lambda.LConst.boolConst true)
---
info: true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check true #end

/--
info: B3: .literal () (Lambda.LConst.boolConst false)
---
info: false
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check false #end

/--
info: B3: .unaryOp () .not (.literal () (Lambda.LConst.boolConst true))
---
info: !true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check !true #end

/--
info: B3: .binaryOp () .sub (.literal () (Lambda.LConst.intConst 10)) (.literal () (Lambda.LConst.intConst 3))
---
info: 10 - 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 10 - 3 #end

/--
info: B3: .binaryOp () .mul (.literal () (Lambda.LConst.intConst 4)) (.literal () (Lambda.LConst.intConst 5))
---
info: 4 * 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 4 * 5 #end

/--
info: B3: .binaryOp () .div (.literal () (Lambda.LConst.intConst 20)) (.literal () (Lambda.LConst.intConst 4))
---
info: 20 div 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 20 div 4 #end

/--
info: B3: .binaryOp () .mod (.literal () (Lambda.LConst.intConst 17)) (.literal () (Lambda.LConst.intConst 5))
---
info: 17 mod 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 17 mod 5 #end

/--
info: B3: .binaryOp () .eq (.literal () (Lambda.LConst.intConst 5)) (.literal () (Lambda.LConst.intConst 5))
---
info: 5 == 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 5 == 5 #end

/--
info: B3: .binaryOp () .neq (.literal () (Lambda.LConst.intConst 3)) (.literal () (Lambda.LConst.intConst 7))
---
info: 3 != 7
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 3 != 7 #end

/--
info: B3: .binaryOp () .le (.literal () (Lambda.LConst.intConst 3)) (.literal () (Lambda.LConst.intConst 5))
---
info: 3 <= 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 3 <= 5 #end

/--
info: B3: .binaryOp () .lt (.literal () (Lambda.LConst.intConst 2)) (.literal () (Lambda.LConst.intConst 8))
---
info: 2 < 8
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 2 < 8 #end

/--
info: B3: .binaryOp () .ge (.literal () (Lambda.LConst.intConst 10)) (.literal () (Lambda.LConst.intConst 5))
---
info: 10 >= 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 10 >= 5 #end

/--
info: B3: .binaryOp () .gt (.literal () (Lambda.LConst.intConst 15)) (.literal () (Lambda.LConst.intConst 3))
---
info: 15 > 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 15 > 3 #end

/--
info: B3: .binaryOp () .add (.literal () (Lambda.LConst.intConst 2)) (.binaryOp () .mul (.literal () (Lambda.LConst.intConst 3)) (.literal () (Lambda.LConst.intConst 4)))
---
info: 2 + 3 * 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 2 + 3 * 4 #end

/--
info: B3: .binaryOp () .mul (.binaryOp () .add (.literal () (Lambda.LConst.intConst 2)) (.literal () (Lambda.LConst.intConst 3))) (.literal () (Lambda.LConst.intConst 4))
---
info: (2 + 3) * 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check (2 + 3) * 4 #end

/--
info: B3: .binaryOp () .add (.binaryOp () .add (.literal () (Lambda.LConst.intConst 1)) (.literal () (Lambda.LConst.intConst 2))) (.literal () (Lambda.LConst.intConst 3))
---
info: 1 + 2 + 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 1 + 2 + 3 #end

/--
info: B3: .binaryOp () .lt (.binaryOp () .add (.literal () (Lambda.LConst.intConst 1)) (.literal () (Lambda.LConst.intConst 2))) (.literal () (Lambda.LConst.intConst 5))
---
info: 1 + 2 < 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 1 + 2 < 5 #end

/--
info: B3: .binaryOp () .add (.binaryOp () .sub (.literal () (Lambda.LConst.intConst 10)) (.literal () (Lambda.LConst.intConst 3))) (.literal () (Lambda.LConst.intConst 2))
---
info: 10 - 3 + 2
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 10 - 3 + 2 #end

/--
info: B3: .binaryOp () .mul (.binaryOp () .div (.literal () (Lambda.LConst.intConst 20)) (.literal () (Lambda.LConst.intConst 4))) (.literal () (Lambda.LConst.intConst 3))
---
info: 20 div 4 * 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 20 div 4 * 3 #end

/--
info: B3: .binaryOp () .lt (.literal () (Lambda.LConst.intConst 1)) (.binaryOp () .add (.binaryOp () .mul (.literal () (Lambda.LConst.intConst 2)) (.literal () (Lambda.LConst.intConst 3))) (.literal () (Lambda.LConst.intConst 4)))
---
info: 1 < 2 * 3 + 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 1 < 2 * 3 + 4 #end

/--
info: B3: .ite () (.literal () (Lambda.LConst.boolConst true)) (.literal () (Lambda.LConst.intConst 1)) (.literal () (Lambda.LConst.intConst 0))
---
info: if true then 1 else 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check if true then 1 else 0 #end

/--
info: B3: .quantifierExpr () .forall i "int" [] (.binaryOp () .ge (.id () i) (.literal () (Lambda.LConst.intConst 0)))
---
info: forall i : int i >= 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check forall i : int i >= 0 #end

/--
info: B3: .quantifierExpr () .exists y "bool" [] (.binaryOp () .or (.id () y) (.unaryOp () .not (.id () y)))
---
info: exists y : bool y || !y
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check exists y : bool y || !y #end

/--
info: B3: .quantifierExpr () .forall x "int" [.pattern () [.functionCall () f [.id () x]]] (.binaryOp () .gt (.functionCall () f [.id () x]) (.literal () (Lambda.LConst.intConst 0)))
---
info: forall x : int pattern f(x), f(x) > 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check forall x : int pattern f(x), f(x) > 0 #end

/--
info: B3: .quantifierExpr () .exists y "bool" [.pattern () [.id () y], .pattern () [.unaryOp () .not (.id () y)]] (.binaryOp () .or (.id () y) (.unaryOp () .not (.id () y)))
---
info: exists y : bool pattern y, pattern !y, y || !y
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check exists y : bool pattern y, pattern !y, y || !y #end

/--
info: B3: .quantifierExpr () .forall z "int" [.pattern () [.id () z], .pattern () [.binaryOp () .add (.id () z) (.literal () (Lambda.LConst.intConst 1))], .pattern () [.binaryOp () .mul (.id () z) (.literal () (Lambda.LConst.intConst 2))]] (.binaryOp () .gt (.id () z) (.literal () (Lambda.LConst.intConst 0)))
---
info: forall z : int pattern z, pattern z + 1, pattern z * 2, z > 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check forall z : int pattern z, pattern z + 1, pattern z * 2, z > 0 #end

end ExpressionRoundtripTests

end B3
