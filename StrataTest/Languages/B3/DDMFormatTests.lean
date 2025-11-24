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
info: @[reducible] def Strata.Expr : Type :=
ExprF SourceRange
---
info: inductive Strata.B3DDM.Expr : Type → Type
number of parameters: 1
constructors:
Strata.B3DDM.Expr.fvar : {α : Type} → α → Nat → B3DDM.Expr α
Strata.B3DDM.Expr.not : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.natLit : {α : Type} → α → Ann Nat α → B3DDM.Expr α
Strata.B3DDM.Expr.strLit : {α : Type} → α → Ann String α → B3DDM.Expr α
Strata.B3DDM.Expr.btrue : {α : Type} → α → B3DDM.Expr α
Strata.B3DDM.Expr.bfalse : {α : Type} → α → B3DDM.Expr α
Strata.B3DDM.Expr.id : {α : Type} → α → Ann String α → B3DDM.Expr α
Strata.B3DDM.Expr.letExpr : {α : Type} → α → Ann String α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.labeledExpr : {α : Type} → α → Ann String α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.ite : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.iff : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.implies : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.impliedBy : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.and : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.or : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.equal : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.not_equal : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.le : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.lt : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.ge : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.gt : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.neg : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.add : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.sub : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.mul : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.div : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.mod : {α : Type} → α → B3DDM.Expr α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.functionCall : {α : Type} → α → Ann String α → Ann (Array (B3DDM.Expr α)) α → B3DDM.Expr α
Strata.B3DDM.Expr.forall_expr : {α : Type} →
  α → Ann String α → Ann String α → Ann (Option (Patterns α)) α → B3DDM.Expr α → B3DDM.Expr α
Strata.B3DDM.Expr.exists_expr : {α : Type} →
  α → Ann String α → Ann String α → Ann (Option (Patterns α)) α → B3DDM.Expr α → B3DDM.Expr α
-/
#guard_msgs in
#print Expr

/--
info: inductive Strata.B3DDM.Pattern : Type → Type
number of parameters: 1
constructors:
Strata.B3DDM.Pattern.pattern : {α : Type} → α → B3DDM.Expr α → B3DDM.Pattern α
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
def formatExpr (e : Expr Unit) : Format :=
  let ctx := b3Program.formatContext {}
  let state := b3Program.formatState
  cformat (exprFUnitToSourceRange e.toAst) ctx state

-- Helper to extract expression from a check statement and reformat it
def reformatExpr (p : Program) : Format :=
  match p.commands.toList with
  | [op] =>
    if op.name.name == "command_stmt" then
      match op.args.toList with
      | [ArgF.op stmt] =>
        if stmt.name.name == "check" then
          match stmt.args.toList with
          | [ArgF.expr e] =>
            let ctx := p.formatContext {}
            let state := p.formatState
            cformat e ctx state
          | _ => "Error: expected expr in check"
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
              | [ArgF.expr e] =>
                let ctx := p.formatContext {}
                let state := p.formatState
                cformat e ctx state
              | _ => s!"Error: expected expr in axiom body, got {repr body.args.toList}"
            else if body.name.name == "explain_axiom" then
              -- Axiom with explains: explain_axiom (names, expr)
              match body.args.toList with
              | [_, ArgF.expr e] =>
                let ctx := p.formatContext {}
                let state := p.formatState
                cformat e ctx state
              | _ => s!"Error: expected names and expr in explain_axiom, got {repr body.args.toList}"
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
info: val temp := 10 temp + x
-/
#guard_msgs in
#eval formatExpr $ .letExpr () ⟨(), "temp"⟩ (.natLit () ⟨(), 10⟩)
  (.add () (.id () ⟨(), "temp"⟩) (.id () ⟨(), "x"⟩))

/--
info: important: result
-/
#guard_msgs in
#eval formatExpr $ .labeledExpr () ⟨(), "important"⟩ (.id () ⟨(), "result"⟩)

/--
info: forall i : int i >= 0
-/
#guard_msgs in
#eval formatExpr $ .forall_expr () ⟨(), "i"⟩ ⟨(), "int"⟩
  ⟨(), none⟩
  (.ge () (.id () ⟨(), "i"⟩) (.natLit () ⟨(), 0⟩))

/--
info: exists y : bool y || !y
-/
#guard_msgs in
#eval formatExpr $ .exists_expr () ⟨(), "y"⟩ ⟨(), "bool"⟩
  ⟨(), none⟩
  (.or () (.id () ⟨(), "y"⟩) (.not () (.id () ⟨(), "y"⟩)))

/--
info: forall x : int pattern f(x), f(x) > 0
-/
#guard_msgs in
#eval formatExpr $ Expr.forall_expr () ⟨(), "x"⟩ ⟨(), "int"⟩
  ⟨(), some (B3DDM.Patterns.patternsAtom () (B3DDM.Pattern.pattern () (Expr.functionCall () ⟨(), "f"⟩ ⟨(), #[Expr.id () ⟨(), "x"⟩]⟩)))⟩
  (Expr.gt () (Expr.functionCall () ⟨(), "f"⟩ ⟨(), #[Expr.id () ⟨(), "x"⟩]⟩) (Expr.natLit () ⟨(), 0⟩))

/--
info: exists y : bool pattern y, pattern !y, y || !y
-/
#guard_msgs in
#eval formatExpr $ Expr.exists_expr () ⟨(), "y"⟩ ⟨(), "bool"⟩
  ⟨(), some (B3DDM.Patterns.patternsPush ()
    (B3DDM.Patterns.patternsAtom () (B3DDM.Pattern.pattern () (Expr.id () ⟨(), "y"⟩)))
    (B3DDM.Pattern.pattern () (Expr.not () (Expr.id () ⟨(), "y"⟩))))⟩
  (Expr.or () (Expr.id () ⟨(), "y"⟩) (Expr.not () (Expr.id () ⟨(), "y"⟩)))

/--
info: forall z : int pattern z, pattern z + 1, pattern z * 2, z > 0
-/
#guard_msgs in
#eval formatExpr $ Expr.forall_expr () ⟨(), "z"⟩ ⟨(), "int"⟩
  ⟨(), some (B3DDM.Patterns.patternsPush ()
    (B3DDM.Patterns.patternsPush ()
      (B3DDM.Patterns.patternsAtom () (B3DDM.Pattern.pattern () (Expr.id () ⟨(), "z"⟩)))
      (B3DDM.Pattern.pattern () (Expr.add () (Expr.id () ⟨(), "z"⟩) (Expr.natLit () ⟨(), 1⟩))))
    (B3DDM.Pattern.pattern () (Expr.mul () (Expr.id () ⟨(), "z"⟩) (Expr.natLit () ⟨(), 2⟩))))⟩
  (Expr.gt () (Expr.id () ⟨(), "z"⟩) (Expr.natLit () ⟨(), 0⟩))

end ExpressionFormatTests

-- Helper to convert OperationF Unit to OperationF SourceRange
def operationFUnitToSourceRange (op : OperationF Unit) : OperationF SourceRange :=
  { op with ann := default, args := op.args.map argFUnitToSourceRange }

-- Helper to format DDM statements with proper pretty-printing
def formatStmt (s : Statement Unit) : Format :=
  let ctx := b3Program.formatContext {}
  let state := b3Program.formatState
  cformat (ArgF.op (operationFUnitToSourceRange s.toAst)) ctx state

section StatementFormatTests

/--
info: x := 42
-/
#guard_msgs in
#eval formatStmt $ .assign () ⟨(), "x"⟩ (.natLit () ⟨(), 42⟩)

/--
info: check 5 > 0
-/
#guard_msgs in
#eval formatStmt $ .check () (.gt () (.natLit () ⟨(), 5⟩) (.natLit () ⟨(), 0⟩))

/--
info: assume 10 >= 0
-/
#guard_msgs in
#eval formatStmt $ .assume () (.ge () (.natLit () ⟨(), 10⟩) (.natLit () ⟨(), 0⟩))

/--
info: assert 5 > 0
-/
#guard_msgs in
#eval formatStmt $ .assert () (.gt () (.natLit () ⟨(), 5⟩) (.natLit () ⟨(), 0⟩))

/--
info: reach 5 == 5
-/
#guard_msgs in
#eval formatStmt $ .reach () (.equal () (.natLit () ⟨(), 5⟩) (.natLit () ⟨(), 5⟩))

/--
info: return
-/
#guard_msgs in
#eval formatStmt $ .return_statement ()

/--
info: {
  x := 1
  y := 2
}
-/
#guard_msgs in
#eval formatStmt $ Statement.block () ⟨(), #[
  Statement.assign () ⟨(), "x"⟩ (Expr.natLit () ⟨(), 1⟩),
  Statement.assign () ⟨(), "y"⟩ (Expr.natLit () ⟨(), 2⟩)
]⟩

/--
info: if flag ⏎
  x := 1
else ⏎
  {
    x := 0
  }
-/
#guard_msgs in
#eval formatStmt $ Statement.if_statement ()
  (Expr.id () ⟨(), "flag"⟩)
  (Statement.assign () ⟨(), "x"⟩ (Expr.natLit () ⟨(), 1⟩))
  (Else.else_some () (Statement.block () ⟨(), #[Statement.assign () ⟨(), "x"⟩ (Expr.natLit () ⟨(), 0⟩)]⟩))

/--
info: loop ⏎
{
  i := i + 1
}
-/
#guard_msgs in
#eval formatStmt $ Statement.loop_statement () ⟨(), #[]⟩
  (Statement.block () ⟨(), #[
    Statement.assign () ⟨(), "i"⟩
      (Expr.add () (Expr.id () ⟨(), "i"⟩) (Expr.natLit () ⟨(), 1⟩))
  ]⟩)

/--
info: loop
  invariant i >= 0
  invariant i <= n ⏎
{
  i := i + 1
}
-/
#guard_msgs in
#eval formatStmt $ Statement.loop_statement ()
  ⟨(), #[Invariant.invariant () (Expr.ge () (Expr.id () ⟨(), "i"⟩) (Expr.natLit () ⟨(), 0⟩)),
    Invariant.invariant () (Expr.le () (Expr.id () ⟨(), "i"⟩) (Expr.id () ⟨(), "n"⟩))]⟩
  (Statement.block () ⟨(), #[
    Statement.assign () ⟨(), "i"⟩
      (Expr.add () (Expr.id () ⟨(), "i"⟩) (Expr.natLit () ⟨(), 1⟩))
  ]⟩)

/--
info: exit loop_start
-/
#guard_msgs in
#eval formatStmt $ Statement.exit_statement () ⟨(), some ⟨(), "loop_start"⟩⟩

/--
info: loop_start: ⏎
x := 0
-/
#guard_msgs in
#eval formatStmt $ Statement.labeled_statement () ⟨(), "loop_start"⟩
  (Statement.assign () ⟨(), "x"⟩ (Expr.natLit () ⟨(), 0⟩))

/--
info: probe debug_point
-/
#guard_msgs in
#eval formatStmt $ Statement.probe () ⟨(), "debug_point"⟩

/--
info: var x : int
-/
#guard_msgs in
#eval formatStmt $ Statement.var_decl () ⟨(), "x"⟩ (VarType.type_init_some () ⟨(), "int"⟩)
  (AutoInv.autoinv_none ()) (VarInit.var_init_none ())

/--
info: val x : bool := true
-/
#guard_msgs in
#eval formatStmt $ Statement.val_decl () ⟨(), "x"⟩ (VarType.type_init_some () ⟨(), "bool"⟩) (Expr.btrue ())


/--
info: var y : bool := true
-/
#guard_msgs in
#eval formatStmt $ Statement.var_decl () ⟨(), "y"⟩ (VarType.type_init_some () ⟨(), "bool"⟩)
  (AutoInv.autoinv_none ())
  (VarInit.var_init_some () (Expr.btrue ()))

/--
info: var z : int autoinv z >= 0
-/
#guard_msgs in
#eval formatStmt $ Statement.var_decl () ⟨(), "z"⟩ (VarType.type_init_some () ⟨(), "int"⟩)
  (AutoInv.autoinv_some () (Expr.ge () (Expr.id () ⟨(), "z"⟩) (Expr.natLit () ⟨(), 0⟩)))
  (VarInit.var_init_none ())

/--
info: forall x : int ⏎
{
  check x >= 0
}
-/
#guard_msgs in
#eval formatStmt $ Statement.aForall_statement () ⟨(), "x"⟩ ⟨(), "int"⟩
  (Statement.block () ⟨(), #[
    Statement.check () (Expr.ge () (Expr.id () ⟨(), "x"⟩) (Expr.natLit () ⟨(), 0⟩))
  ]⟩)

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
#eval formatStmt $ Statement.choose_statement ()
  (ChoiceBranches.choicePush ()
    (ChoiceBranches.choiceAtom () (ChoiceBranch.choice_branch () (Statement.block () ⟨(), #[Statement.assign () ⟨(), "x"⟩ (Expr.natLit () ⟨(), 1⟩)]⟩)))
    (ChoiceBranch.choice_branch () (Statement.block () ⟨(), #[Statement.assign () ⟨(), "x"⟩ (Expr.natLit () ⟨(), 2⟩)]⟩)))

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
#eval formatStmt $ Statement.if_case_statement () ⟨(), #[
  IfCaseBranch.if_case_branch () (Expr.equal () (Expr.id () ⟨(), "x"⟩) (Expr.natLit () ⟨(), 1⟩))
    (Statement.block () ⟨(), #[Statement.assign () ⟨(), "y"⟩ (Expr.natLit () ⟨(), 10⟩)]⟩),
  IfCaseBranch.if_case_branch () (Expr.equal () (Expr.id () ⟨(), "x"⟩) (Expr.natLit () ⟨(), 2⟩))
    (Statement.block () ⟨(), #[Statement.assign () ⟨(), "y"⟩ (Expr.natLit () ⟨(), 20⟩)]⟩)
]⟩

/--
info:
compute(out result, a, b)
-/
#guard_msgs in
#eval formatStmt $ Statement.call_statement () ⟨(), "compute"⟩ ⟨(), #[
  CallArg.call_arg_out () ⟨(), "result"⟩,
  CallArg.call_arg_expr () (Expr.id () ⟨(), "a"⟩),
  CallArg.call_arg_expr () (Expr.id () ⟨(), "b"⟩)
]⟩

/--
info:
modify(inout x, out y)
-/
#guard_msgs in
#eval formatStmt $ Statement.call_statement () ⟨(), "modify"⟩ ⟨(), #[
  CallArg.call_arg_inout () ⟨(), "x"⟩,
  CallArg.call_arg_out () ⟨(), "y"⟩
]⟩

end StatementFormatTests

end B3
