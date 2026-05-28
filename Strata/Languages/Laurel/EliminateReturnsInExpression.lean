/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
import Strata.Util.Tactics

/-!
# Eliminate Returns in Expression Position

Rewrites functional procedure bodies if possible, so they only get a single return on the outside of the body.
This depends on three transformations

1)
```
if <cond> then
  <returningExpr1>

<returningExpr2>
```

is converted into
```
return if <cond> then <stripped_returningExpr1> else <stripped_returningExpr2>
```

Where stripped_<expr> indicates the return has been stripped from <expr>

2)
```
if <cond> then <returningExpr1> else <returningExpr2>
```

is turned into
```
return if <cond> then <stripped_returningExpr1> else <stripped_returningExpr2>
```

3)
```
var x := <expr1>
<returningExpr>
```

is turned into

```
return
  var x := <expr1>
  <stripped_returningExpr>
```

-/

namespace Strata.Laurel

/-- Check whether a statement is "returning": all control-flow paths end with a `Return`. -/
partial def isReturning (stmt : StmtExprMd) : Bool :=
  match stmt.val with
  | .Return _ => true
  | .Block stmts _ =>
    match stmts.getLast? with
    | some last => isReturning last
    | none => false
  | .IfThenElse _ thenBr (some elseBr) => isReturning thenBr && isReturning elseBr
  | .IfThenElse _ thenBr none => isReturning thenBr
  | _ => false

/-- Strip the outermost `Return` wrapper from a returning statement, yielding the expression.
    Recurses into blocks (transforming the last statement) and if-then-else (transforming branches). -/
partial def stripReturn (stmt : StmtExprMd) : StmtExprMd :=
  match stmt.val with
  | .Return (some val) => val
  | .Return none => ⟨.LiteralBool true, stmt.source⟩
  | .Block stmts label =>
    match stmts.dropLast, stmts.getLast? with
    | init, some last =>
      let last' := stripReturn last
      if init.isEmpty then last'
      else ⟨.Block (init ++ [last']) label, stmt.source⟩
    | _, none => stmt
  | .IfThenElse cond thenBr (some elseBr) =>
    ⟨.IfThenElse cond (stripReturn thenBr) (some (stripReturn elseBr)), stmt.source⟩
  | .IfThenElse cond thenBr none =>
    ⟨.IfThenElse cond (stripReturn thenBr) none, stmt.source⟩
  | _ => stmt

mutual

/-- Transform a block's statement list by folding guard-return patterns into if-then-else.
    Scans left-to-right for `if cond then <returning>` (no else) where the remaining
    statements are also returning, and rewrites into `return if cond then ... else ...`. -/
partial def transformStmtList (stmts : List StmtExprMd) : List StmtExprMd :=
  match stmts with
  | [] => []
  | [single] => [transformStmt single]
  | stmt :: rest =>
    match stmt.val with
    | .IfThenElse cond thenBr none =>
      if isReturning thenBr then
        let rest' := transformStmtList rest
        let restExpr : StmtExprMd := match rest' with
          | [single] => single
          | many => ⟨.Block many none, stmt.source⟩
        if isReturning restExpr then
          let thenExpr := stripReturn (transformStmt thenBr)
          let elseExpr := stripReturn restExpr
          [⟨.Return (some ⟨.IfThenElse cond thenExpr (some elseExpr), stmt.source⟩), stmt.source⟩]
        else
          transformStmt stmt :: transformStmtList rest
      else
        transformStmt stmt :: transformStmtList rest
    | .IfThenElse cond thenBr (some elseBr) =>
      if isReturning thenBr && isReturning elseBr then
        let thenExpr := stripReturn (transformStmt thenBr)
        let elseExpr := stripReturn (transformStmt elseBr)
        let ite := ⟨.Return (some ⟨.IfThenElse cond thenExpr (some elseExpr), stmt.source⟩), stmt.source⟩
        ite :: transformStmtList rest
      else
        transformStmt stmt :: transformStmtList rest
    | .Assign [⟨.Declare _, _⟩] _ =>
      -- Case 3: var x := expr; <returningExpr> → return { var x := expr; <stripped> }
      let rest' := transformStmtList rest
      let restExpr : StmtExprMd := match rest' with
        | [single] => single
        | many => ⟨.Block many none, stmt.source⟩
      if isReturning restExpr then
        let stripped := stripReturn restExpr
        [⟨.Return (some ⟨.Block [stmt, stripped] none, stmt.source⟩), stmt.source⟩]
      else
        stmt :: transformStmtList rest
    | _ =>
      transformStmt stmt :: transformStmtList rest

/-- Recurse into a statement, applying the guard-return rewrite inside blocks and branches. -/
partial def transformStmt (stmt : StmtExprMd) : StmtExprMd :=
  match stmt.val with
  | .Block stmts label =>
    ⟨.Block (transformStmtList stmts) label, stmt.source⟩
  | .IfThenElse cond thenBr (some elseBr) =>
    if isReturning thenBr && isReturning elseBr then
      let thenExpr := stripReturn (transformStmt thenBr)
      let elseExpr := stripReturn (transformStmt elseBr)
      ⟨.Return (some ⟨.IfThenElse cond thenExpr (some elseExpr), stmt.source⟩), stmt.source⟩
    else
      ⟨.IfThenElse cond (transformStmt thenBr) (some (transformStmt elseBr)), stmt.source⟩
  | .IfThenElse cond thenBr none =>
    ⟨.IfThenElse cond (transformStmt thenBr) none, stmt.source⟩
  | .While cond invs dec body =>
    ⟨.While cond invs dec (transformStmt body), stmt.source⟩
  | _ => stmt

end

/-- Transform a single procedure by applying the guard-return elimination to its body. -/
private def eliminateReturnsInExpression (proc : Procedure) : Procedure :=
  match proc.body with
  | .Transparent body =>
    { proc with body := .Transparent (transformStmt body) }
  | .Opaque postconds (some impl) mods =>
    { proc with body := .Opaque postconds (some (transformStmt impl)) mods }
  | _ => proc

public section

/--
Transform a program by eliminating returns in all functional procedure bodies.
-/
def eliminateReturnsInExpressionTransform (program : Program) : Program :=
  { program with staticProcedures := program.staticProcedures.map eliminateReturnsInExpression }

end -- public section

end Laurel
