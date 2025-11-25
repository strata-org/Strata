/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.Parse
import Strata.Languages.B3.DDMTransform.Translate
import Strata.Languages.B3.DDMTransform.B3ToDDM
import Strata.Languages.B3.DDMTransform.DDMToB3

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
Strata.B3DDM.Patterns.patterns_cons : {α : Type} → α → B3DDM.Pattern α → Patterns α → Patterns α
Strata.B3DDM.Patterns.patterns_single : {α : Type} → α → B3DDM.Pattern α → Patterns α
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

-- Helper to strip SourceRange annotations and replace with Unit
mutual
  partial def stripAnnotations : B3DDM.Expression SourceRange → B3DDM.Expression Unit
    | .natLit _ n => .natLit () ⟨(), n.val⟩
    | .strLit _ s => .strLit () ⟨(), s.val⟩
    | .btrue _ => .btrue ()
    | .bfalse _ => .bfalse ()
    | .id _ name => .id () ⟨(), name.val⟩
    | .not _ arg => .not () (stripAnnotations arg)
    | .neg _ arg => .neg () (stripAnnotations arg)
    | .iff _ lhs rhs => .iff () (stripAnnotations lhs) (stripAnnotations rhs)
    | .implies _ lhs rhs => .implies () (stripAnnotations lhs) (stripAnnotations rhs)
    | .impliedBy _ lhs rhs => .impliedBy () (stripAnnotations lhs) (stripAnnotations rhs)
    | .and _ lhs rhs => .and () (stripAnnotations lhs) (stripAnnotations rhs)
    | .or _ lhs rhs => .or () (stripAnnotations lhs) (stripAnnotations rhs)
    | .equal _ lhs rhs => .equal () (stripAnnotations lhs) (stripAnnotations rhs)
    | .not_equal _ lhs rhs => .not_equal () (stripAnnotations lhs) (stripAnnotations rhs)
    | .lt _ lhs rhs => .lt () (stripAnnotations lhs) (stripAnnotations rhs)
    | .le _ lhs rhs => .le () (stripAnnotations lhs) (stripAnnotations rhs)
    | .ge _ lhs rhs => .ge () (stripAnnotations lhs) (stripAnnotations rhs)
    | .gt _ lhs rhs => .gt () (stripAnnotations lhs) (stripAnnotations rhs)
    | .add _ lhs rhs => .add () (stripAnnotations lhs) (stripAnnotations rhs)
    | .sub _ lhs rhs => .sub () (stripAnnotations lhs) (stripAnnotations rhs)
    | .mul _ lhs rhs => .mul () (stripAnnotations lhs) (stripAnnotations rhs)
    | .div _ lhs rhs => .div () (stripAnnotations lhs) (stripAnnotations rhs)
    | .mod _ lhs rhs => .mod () (stripAnnotations lhs) (stripAnnotations rhs)
    | .functionCall _ fn args => .functionCall () ⟨(), fn.val⟩ ⟨(), args.val.map stripAnnotations⟩
    | .labeledExpr _ label expr => .labeledExpr () ⟨(), label.val⟩ (stripAnnotations expr)
    | .letExpr _ var value body => .letExpr () ⟨(), var.val⟩ (stripAnnotations value) (stripAnnotations body)
    | .ite _ cond thenExpr elseExpr => .ite () (stripAnnotations cond) (stripAnnotations thenExpr) (stripAnnotations elseExpr)
    | .forall_expr_no_patterns _ var ty body => .forall_expr_no_patterns () ⟨(), var.val⟩ ⟨(), ty.val⟩ (stripAnnotations body)
    | .forall_expr _ var ty patterns body => .forall_expr () ⟨(), var.val⟩ ⟨(), ty.val⟩ (stripPatternsAnnotations patterns) (stripAnnotations body)
    | .exists_expr_no_patterns _ var ty body => .exists_expr_no_patterns () ⟨(), var.val⟩ ⟨(), ty.val⟩ (stripAnnotations body)
    | .exists_expr _ var ty patterns body => .exists_expr () ⟨(), var.val⟩ ⟨(), ty.val⟩ (stripPatternsAnnotations patterns) (stripAnnotations body)
    | .paren _ expr => .paren () (stripAnnotations expr)

  partial def stripPatternAnnotations : B3DDM.Pattern SourceRange → B3DDM.Pattern Unit
    | .pattern _ expr => .pattern () (stripAnnotations expr)

  partial def stripPatternsAnnotations : B3DDM.Patterns SourceRange → B3DDM.Patterns Unit
    | .patterns_single _ p => .patterns_single () (stripPatternAnnotations p)
    | .patterns_cons _ p ps => .patterns_cons () (stripPatternAnnotations p) (stripPatternsAnnotations ps)
end

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
info: B3: .binaryOp () (B3.BinaryOp.add) (.literal () (Lambda.LConst.intConst 5)) (.literal () (Lambda.LConst.intConst 3))
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
info: B3: .unaryOp () (B3.UnaryOp.not) (.literal () (Lambda.LConst.boolConst true))
---
info: !true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check !true #end

/--
info: B3: .binaryOp () (B3.BinaryOp.sub) (.literal () (Lambda.LConst.intConst 10)) (.literal () (Lambda.LConst.intConst 3))
---
info: 10 - 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 10 - 3 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.mul) (.literal () (Lambda.LConst.intConst 4)) (.literal () (Lambda.LConst.intConst 5))
---
info: 4 * 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 4 * 5 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.div) (.literal () (Lambda.LConst.intConst 20)) (.literal () (Lambda.LConst.intConst 4))
---
info: 20 div 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 20 div 4 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.mod) (.literal () (Lambda.LConst.intConst 17)) (.literal () (Lambda.LConst.intConst 5))
---
info: 17 mod 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 17 mod 5 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.eq) (.literal () (Lambda.LConst.intConst 5)) (.literal () (Lambda.LConst.intConst 5))
---
info: 5 == 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 5 == 5 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.neq) (.literal () (Lambda.LConst.intConst 3)) (.literal () (Lambda.LConst.intConst 7))
---
info: 3 != 7
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 3 != 7 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.le) (.literal () (Lambda.LConst.intConst 3)) (.literal () (Lambda.LConst.intConst 5))
---
info: 3 <= 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 3 <= 5 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.lt) (.literal () (Lambda.LConst.intConst 2)) (.literal () (Lambda.LConst.intConst 8))
---
info: 2 < 8
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 2 < 8 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.ge) (.literal () (Lambda.LConst.intConst 10)) (.literal () (Lambda.LConst.intConst 5))
---
info: 10 >= 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 10 >= 5 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.gt) (.literal () (Lambda.LConst.intConst 15)) (.literal () (Lambda.LConst.intConst 3))
---
info: 15 > 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 15 > 3 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.add) (.literal () (Lambda.LConst.intConst 2)) (.binaryOp () (B3.BinaryOp.mul) (.literal () (Lambda.LConst.intConst 3)) (.literal () (Lambda.LConst.intConst 4)))
---
info: 2 + 3 * 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 2 + 3 * 4 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.mul) (.binaryOp () (B3.BinaryOp.add) (.literal () (Lambda.LConst.intConst 2)) (.literal () (Lambda.LConst.intConst 3))) (.literal () (Lambda.LConst.intConst 4))
---
info: (2 + 3) * 4
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check (2 + 3) * 4 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.add) (.binaryOp () (B3.BinaryOp.add) (.literal () (Lambda.LConst.intConst 1)) (.literal () (Lambda.LConst.intConst 2))) (.literal () (Lambda.LConst.intConst 3))
---
info: 1 + 2 + 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 1 + 2 + 3 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.lt) (.binaryOp () (B3.BinaryOp.add) (.literal () (Lambda.LConst.intConst 1)) (.literal () (Lambda.LConst.intConst 2))) (.literal () (Lambda.LConst.intConst 5))
---
info: 1 + 2 < 5
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 1 + 2 < 5 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.add) (.binaryOp () (B3.BinaryOp.sub) (.literal () (Lambda.LConst.intConst 10)) (.literal () (Lambda.LConst.intConst 3))) (.literal () (Lambda.LConst.intConst 2))
---
info: 10 - 3 + 2
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 10 - 3 + 2 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.mul) (.binaryOp () (B3.BinaryOp.div) (.literal () (Lambda.LConst.intConst 20)) (.literal () (Lambda.LConst.intConst 4))) (.literal () (Lambda.LConst.intConst 3))
---
info: 20 div 4 * 3
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; check 20 div 4 * 3 #end

/--
info: B3: .binaryOp () (B3.BinaryOp.lt) (.literal () (Lambda.LConst.intConst 1)) (.binaryOp () (B3.BinaryOp.add) (.binaryOp () (B3.BinaryOp.mul) (.literal () (Lambda.LConst.intConst 2)) (.literal () (Lambda.LConst.intConst 3))) (.literal () (Lambda.LConst.intConst 4)))
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
info: B3: .quantifierExpr () (B3.QuantifierKind.forall) i "int" [] (.binaryOp () (B3.BinaryOp.ge) (.id () i) (.literal () (Lambda.LConst.intConst 0)))
---
info: forall i : int i >= 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; axiom forall i : int i >= 0 #end

/--
info: B3: .quantifierExpr () (B3.QuantifierKind.exists) y "bool" [] (.binaryOp () (B3.BinaryOp.or) (.id () y) (.unaryOp () (B3.UnaryOp.not) (.id () y)))
---
info: exists y : bool y || !y
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; axiom exists y : bool y || !y #end

/--
info: B3: .quantifierExpr () (B3.QuantifierKind.forall) x "int" [.pattern () [.functionCall () f [.id () x]]] (.binaryOp () (B3.BinaryOp.gt) (.functionCall () f [.id () x]) (.literal () (Lambda.LConst.intConst 0)))
---
info: forall x : int pattern f(x), f(x) > 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; axiom forall x : int pattern f(x), f(x) > 0 #end

/--
info: B3: .quantifierExpr () (B3.QuantifierKind.exists) y "bool" [.pattern () [.id () y], .pattern () [.unaryOp () (B3.UnaryOp.not) (.id () y)]] (.binaryOp () (B3.BinaryOp.or) (.id () y) (.unaryOp () (B3.UnaryOp.not) (.id () y)))
---
info: exists y : bool pattern y, pattern !y, y || !y
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; axiom exists y : bool pattern y, pattern !y, y || !y #end

/--
info: B3: .quantifierExpr () (B3.QuantifierKind.forall) z "int" [.pattern () [.id () z], .pattern () [.binaryOp () (B3.BinaryOp.add) (.id () z) (.literal () (Lambda.LConst.intConst 1))], .pattern () [.binaryOp () (B3.BinaryOp.mul) (.id () z) (.literal () (Lambda.LConst.intConst 2))]] (.binaryOp () (B3.BinaryOp.gt) (.id () z) (.literal () (Lambda.LConst.intConst 0)))
---
info: forall z : int pattern z, pattern z + 1, pattern z * 2, z > 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3; axiom forall z : int pattern z, pattern z + 1, pattern z * 2, z > 0 #end

end ExpressionRoundtripTests

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
