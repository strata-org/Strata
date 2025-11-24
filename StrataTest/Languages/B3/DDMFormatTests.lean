/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.Parse
import Strata.Languages.B3.DDMTransform.Translate
import Strata.Languages.B3.DDMTransform.B3AST2DDM

namespace B3

open Std (Format)
open Strata
open Strata.B3DDM

/--
info: inductive B3.Expression : ExprParams → Type
number of parameters: 1
constructors:
B3.Expression.literal : {P : ExprParams} → P.Metadata → Lambda.LConst → Expression P
B3.Expression.id : {P : ExprParams} → P.Metadata → P.Identifier → Expression P
B3.Expression.ite : {P : ExprParams} → P.Metadata → Expression P → Expression P → Expression P → Expression P
B3.Expression.binaryOp : {P : ExprParams} → P.Metadata → BinaryOp → Expression P → Expression P → Expression P
B3.Expression.unaryOp : {P : ExprParams} → P.Metadata → UnaryOp → Expression P → Expression P
B3.Expression.functionCall : {P : ExprParams} → P.Metadata → P.Identifier → List (Expression P) → Expression P
B3.Expression.labeledExpr : {P : ExprParams} → P.Metadata → String → Expression P → Expression P
B3.Expression.letExpr : {P : ExprParams} → P.Metadata → P.Identifier → Expression P → Expression P → Expression P
B3.Expression.quantifierExpr : {P : ExprParams} →
  P.Metadata → QuantifierKind → P.Identifier → String → List (Pattern P) → Expression P → Expression P
-/
#guard_msgs in
#print Expression

/--
info: inductive Strata.B3DDM.Pattern : Type → Type
number of parameters: 1
constructors:
Strata.B3DDM.Pattern.pattern : {α : Type} → α → B3DDM.Expression α → B3DDM.Pattern α
-/
#guard_msgs in
#print B3DDM.Pattern

/--
info: inductive Strata.B3DDM.Patterns : Type → Type
number of parameters: 1
constructors:
Strata.B3DDM.Patterns.patternsAtom : {α : Type} → α → B3DDM.Pattern α → Patterns α
Strata.B3DDM.Patterns.patternsPush : {α : Type} → α → Patterns α → B3DDM.Pattern α → Patterns α
-/
#guard_msgs in
#print B3DDM.Patterns

-- Helpers to convert Unit annotations to SourceRange
mutual
  partial def exprFUnitToSourceRange : ExprF Unit → ExprF SourceRange
    | .bvar () idx => .bvar default idx
    | .fvar () idx => .fvar default idx
    | .fn () f => .fn default f
    | .app () f a => .app default (exprFUnitToSourceRange f) (argFUnitToSourceRange a)

  partial def argFUnitToSourceRange : ArgF Unit → ArgF SourceRange
    | .op op => .op { op with ann := default, args := op.args.map argFUnitToSourceRange }
    | .expr e => .expr (exprFUnitToSourceRange e)
    | .type t => .type (typeExprFUnitToSourceRange t)
    | .cat c => .cat (syntaxCatFUnitToSourceRange c)
    | .ident () x => .ident default x
    | .num () x => .num default x
    | .decimal () v => .decimal default v
    | .strlit () s => .strlit default s
    | .bytes () v => .bytes default v
    | .option () ma => .option default (ma.map argFUnitToSourceRange)
    | .seq () entries => .seq default (entries.map argFUnitToSourceRange)
    | .commaSepList () entries => .commaSepList default (entries.map argFUnitToSourceRange)

  partial def typeExprFUnitToSourceRange : TypeExprF Unit → TypeExprF SourceRange
    | .ident () tp a => .ident default tp (a.map typeExprFUnitToSourceRange)
    | .bvar () idx => .bvar default idx
    | .fvar () idx a => .fvar default idx (a.map typeExprFUnitToSourceRange)
    | .arrow () a r => .arrow default (typeExprFUnitToSourceRange a) (typeExprFUnitToSourceRange r)

  partial def syntaxCatFUnitToSourceRange : SyntaxCatF Unit → SyntaxCatF SourceRange
    | ⟨(), name, args⟩ => ⟨default, name, args.map syntaxCatFUnitToSourceRange⟩
end

-- Create a minimal B3 program to get the dialect context
def b3Program : Program := #strata program B3; #end

-- Helper to format DDM expressions with proper pretty-printing
-- Note: This function is deprecated as expressions should be created via #strata syntax
-- def formatExpr (e : Expr Unit) : Format :=
--   let ctx := b3Program.formatContext {}
--   let state := b3Program.formatState
--   cformat (exprFUnitToSourceRange e.toAst) ctx state

-- Helper to extract expression from a check statement and reformat it
-- With op-based expressions, everything is an operation, so we format the operation directly
def reformatExpr (p : Program) : Format :=
  match p.commands.toList with
  | [op] =>
    if op.name.name == "command_stmt" then
      match op.args.toList with
      | [ArgF.op stmt] =>
        if stmt.name.name == "check" then
          match stmt.args.toList with
          | [ArgF.op e] =>  -- With op, expressions are operations
            let ctx := p.formatContext {}
            let state := p.formatState
            cformat (ArgF.op e) ctx state
          | _ => s!"Error: expected op in check, got {repr stmt.args.toList}"
        else s!"Error: expected check statement, got {stmt.name.name}"
      | _ => "Error: expected statement op"
    else if op.name.name == "command_decl" then
       match op.args.toList with
      | [ArgF.op decl] =>
        if decl.name.name == "axiom_decl" then
          -- axiom_decl contains an AxiomBody
          match decl.args.toList with
          | [ArgF.op body] =>
            if body.name.name == "axiom" then
              -- Simple axiom: axiom (expr)
              match body.args.toList with
              | [ArgF.op e] =>  -- With op, expressions are operations
                let ctx := p.formatContext {}
                let state := p.formatState
                cformat (ArgF.op e) ctx state
              | _ => s!"Error: expected op in axiom body, got {repr body.args.toList}"
            else if body.name.name == "explain_axiom" then
              -- Axiom with explains: explain_axiom (names, expr)
              match body.args.toList with
              | [_, ArgF.op e] =>  -- With op, expressions are operations
                let ctx := p.formatContext {}
                let state := p.formatState
                cformat (ArgF.op e) ctx state
              | _ => s!"Error: expected names and op in explain_axiom, got {repr body.args.toList}"
            else s!"Error: expected axiom or explain_axiom body, got {body.name.name}"
          | _ => s!"Error: expected AxiomBody in axiom_decl, got {repr decl.args.toList}"
        else s!"Error: expected axiom declaration, got {decl.name.name}"
      | _ => "Error: expected axiom op"
    else
      s!"Error: expected command_stmt or command_decl, got {op.name.name}"
  | _ => "Error: expected single command"

section ExpressionFormatTests

/--
info: x
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; axiom x #end

/--
info: 5 + 3
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; axiom 5 + 3 #end

/--
info: true
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check true #end

/--
info: false
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check false #end

/--
info: 5 + 3
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 5 + 3 #end

/-- info: !true -/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check !true #end

/--
info: 10 - 3
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 10 - 3 #end

/--
info: 4 * 5
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 4 * 5 #end

/--
info: 20 div 4
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 20 div 4 #end

/--
info: 17 mod 5
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 17 mod 5 #end

/--
info: 5 == 5
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 5 == 5 #end

/--
info: 3 != 7
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 3 != 7 #end

/--
info: 3 <= 5
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 3 <= 5 #end

/--
info: 2 < 8
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 2 < 8 #end

/--
info: 10 >= 5
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 10 >= 5 #end

/--
info: 15 > 3
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 15 > 3 #end

/--
info: 2 + 3 * 4
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 2 + 3 * 4 #end

/--
info: (2 + 3) * 4
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check (2 + 3) * 4 #end

/--
info: 1 + 2 + 3
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 1 + 2 + 3 #end

/--
info: 1 + 2 < 5
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 1 + 2 < 5 #end

/--
info: 10 - 3 + 2
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 10 - 3 + 2 #end

/--
info: 20 div 4 * 3
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 20 div 4 * 3 #end

/--
info: 1 < 2 * 3 + 4
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check 1 < 2 * 3 + 4 #end

/--
info: if true then 1 else 0
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; check if true then 1 else 0 #end

/--
info: vaal temp := 10 temp + x == 7
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; axiom vaal temp := 10 temp + x == 7 #end

/--
info: important: result
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; axiom important: result #end

/--
info: forall i : int i >= 0
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; axiom forall i : int i >= 0 #end

/--
info: exists y : bool y || !y
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; axiom exists y : bool y || !y #end

/--
info: forall x : int pattern f(x), f(x) > 0
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; axiom forall x : int pattern f(x), f(x) > 0 #end

/--
info: exists y : bool pattern y, pattern !y, y || !y
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; axiom exists y : bool pattern y, pattern !y, y || !y #end

/--
info: forall z : int pattern z, pattern z + 1, pattern z * 2, z > 0
-/
#guard_msgs in
#eval reformatExpr $ #strata program B3; axiom forall z : int pattern z, pattern z + 1, pattern z * 2, z > 0 #end

end ExpressionFormatTests

-- Helper to convert OperationF Unit to OperationF SourceRange
def operationFUnitToSourceRange (op : OperationF Unit) : OperationF SourceRange :=
  { op with ann := default, args := op.args.map argFUnitToSourceRange }

-- Helper to extract statement from a program and reformat it
def reformatStmt (p : Program) : Format :=
  match p.commands.toList with
  | [op] =>
    if op.name.name == "command_stmt" then
      match op.args.toList with
      | [ArgF.op stmt] =>
        let ctx := p.formatContext {}
        let state := p.formatState
        cformat (ArgF.op stmt) ctx state
      | _ => "Error: expected statement op"
    else s!"Error: expected command_stmt, got {op.name.name}"
  | _ => "Error: expected single command"

section StatementFormatTests

/--
info: x := 42
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; x := 42 #end

/--
info: check 5 > 0
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; check 5 > 0 #end

/--
info: assume 10 >= 0
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; assume 10 >= 0 #end

/--
info: assert 5 > 0
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; assert 5 > 0 #end

/--
info: reach 5 == 5
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; reach 5 == 5 #end

/--
info: return
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; return #end

/--
info: {
  x := 1
  y := 2
}
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; { x := 1 y := 2 } #end

/--
info: if flag ⏎
  x := 1
else ⏎
  {
    x := 0
  }
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; if flag x := 1 else { x := 0 } #end

/--
info: loop ⏎
{
  i := i + 1
}
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; loop { i := i + 1 } #end

/--
info: loop
  invariant i >= 0
  invariant i <= n ⏎
{
  i := i + 1
}
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; loop invariant i >= 0 invariant i <= n { i := i + 1 } #end

/--
info: exit loop_start
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; exit loop_start #end

/--
info: loop_start: ⏎
x := 0
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; loop_start: x := 0 #end

/--
info: probe debug_point
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; probe debug_point #end

/--
info: var x : int
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; var x : int #end

/--
info: val x : bool := true
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; val x : bool := true #end

/--
info: var y : bool := true
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; var y : bool := true #end

/--
info: var z : int autoinv z >= 0
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; var z : int autoinv z >= 0 #end

/--
info: forall x : int ⏎
{
  check x >= 0
}
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; forall x : int { check x >= 0 } #end

/--
info: choose ⏎
{
  x := 1
} or ⏎
{
  x := 2
}
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; choose { x := 1 } or { x := 2 } #end

/--
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
#eval reformatStmt $ #strata program B3; if case x == 1 { y := 10 } case x == 2 { y := 20 } #end

/--
info:
compute(out result, a, b)
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; compute(out result, a, b) #end

/--
info:
modify(inout x, out y)
-/
#guard_msgs in
#eval reformatStmt $ #strata program B3; modify(inout x, out y) #end

end StatementFormatTests

end B3
