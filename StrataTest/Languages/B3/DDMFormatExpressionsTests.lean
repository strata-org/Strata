/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.B3.DDMFormatTests
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 Expression Formatting Tests

Tests for round-trip conversion and formatting of B3 expressions.
Verifies that DDM AST → B3 AST → B3 CST → formatted output preserves structure and catches conversion errors.

## Note on Test Syntax

Expressions are wrapped in `check` statements (e.g., `check 5 + 3`) because:
- our encoding of the B3 grammar doesn't allow bare expressions at the top level.
- Commands can only contain statements and declarations, not expressions
- The test extracts only the expression from the `check` statement for round-trip testing
- The `check` wrapper itself is not part of the tested AST - only the expression `5 + 3` is tested
-/

namespace B3

open Std (Format)
open Strata
open Strata.B3CST

-- Helper to perform the round-trip transformation and format
-- DDM OperationF → B3 AST → DDM → formatted output
partial def doRoundtrip (e : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) : Format :=
  match B3CST.Expression.ofAst e with
  | .ok cstExpr =>
      let (b3Expr, cstToAstErrors) := B3.expressionFromCST B3.FromCSTContext.empty cstExpr
      let (cstExpr', astToCstErrors) := B3.expressionToCST B3.ToCSTContext.empty b3Expr
      -- Convert to Unit metadata for repr
      let b3ExprUnit := B3AST.Expression.mapMetadata (fun _ => ()) b3Expr
      let reprStr := (repr b3ExprUnit).pretty
      let reprStr := cleanupExprRepr reprStr
      let reprStr := cleanupUnitRepr reprStr
      let errorStr := if cstToAstErrors.isEmpty && astToCstErrors.isEmpty then ""
        else
          let cstErrs := cstToAstErrors.map Std.format |> List.map (·.pretty) |> String.intercalate "\n  "
          let astErrs := astToCstErrors.map Std.format |> List.map (·.pretty) |> String.intercalate "\n  "
          let parts := [
            if cstToAstErrors.isEmpty then "" else s!"\nCST→AST Errors:\n  {cstErrs}",
            if astToCstErrors.isEmpty then "" else s!"\nAST→CST Errors:\n  {astErrs}"
          ]
          String.join parts
      dbg_trace f!"B3: {reprStr}{errorStr}"
      let cstAst := cstExpr'.toAst
      (mformat (ArgF.op cstAst) ctx state).format
  | .error msg => s!"Parse error: {msg}"

-- Helper to extract expression from a program and apply round-trip transformation
def roundtripExpr (p : Program) : Format :=
  let ctx := FormatContext.ofDialects p.dialects p.globalContext {}
  let state : FormatState := { openDialects := p.dialects.toList.foldl (init := {}) fun a d => a.insert d.name }
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

-- We are losing the context so this is why it's printing that way.
/--
info: B3: .id () 0
CST→AST Errors:
  Unresolved identifier 'x'
AST→CST Errors:
  Variable index @0 is out of bounds (context has 0 variables)
---
info: |@0|
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
info: if true 1 else 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check if true 1 else 0 #end

/--
info: B3: .quantifierExpr
  ()
  (.forall ())
  u #[.quantVarDecl () u "i" u "int"]
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
  u #[.quantVarDecl () u "y" u "bool"]
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
  u #[.quantVarDecl () u "x" u "int"]
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
  u #[.quantVarDecl () u "y" u "bool"]
  u #[.pattern () u #[.id () 0],
    .pattern
      ()
      u #[.unaryOp
        ()
        (.not ())
        (.id () 0)]]
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
  u #[.quantVarDecl () u "z" u "int"]
  u #[.pattern () u #[.id () 0],
    .pattern
      ()
      u #[.binaryOp
        ()
        (.add ())
        (.id () 0)
        (.literal () (.intLit () 1))],
    .pattern
      ()
      u #[.binaryOp
        ()
        (.mul ())
        (.id () 0)
        (.literal () (.intLit () 2))]]
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

/--
info: B3: .quantifierExpr
  ()
  (.forall ())
  u #[.quantVarDecl () u "x" u "int",
    .quantVarDecl () u "y" u "int"]
  u #[]
  (.binaryOp
    ()
    (.le ())
    (.id () 1)
    (.id () 0))
---
info: forall x : int, y : int x <= y
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check forall x : int, y : int x <= y #end

/--
info: B3: .quantifierExpr
  ()
  (.exists ())
  u #[.quantVarDecl () u "a" u "bool",
    .quantVarDecl () u "b" u "bool",
    .quantVarDecl () u "c" u "bool"]
  u #[]
  (.binaryOp
    ()
    (.and ())
    (.binaryOp
      ()
      (.and ())
      (.id () 2)
      (.id () 1))
    (.id () 0))
---
info: exists a : bool, b : bool, c : bool a && b && c
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check exists a : bool, b : bool, c : bool a && b && c #end

/--
info: B3: .quantifierExpr
  ()
  (.forall ())
  u #[.quantVarDecl () u "i" u "int",
    .quantVarDecl () u "j" u "int"]
  u #[.pattern
    ()
    u #[.binaryOp
      ()
      (.add ())
      (.id () 1)
      (.id () 0)]]
  (.binaryOp
    ()
    (.ge ())
    (.binaryOp
      ()
      (.add ())
      (.id () 1)
      (.id () 0))
    (.literal () (.intLit () 0)))
---
info: forall i : int, j : int pattern i + j i + j >= 0
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check forall i : int, j : int pattern i + j i + j >= 0 #end

end ExpressionRoundtripTests

section AssociativityAndPrecedenceTests

-- Test <== left-associativity
-- B3 grammar: ExpliesExpr ::= ( LogicalExpr "<==" )* LogicalExpr
-- Expected: true <== false <== true parses as (true <== false) <== true (left-associative)
/--
info: B3: .binaryOp
  ()
  (.impliedBy ())
  (.binaryOp
    ()
    (.impliedBy ())
    (.literal () (.boolLit () true))
    (.literal () (.boolLit () false)))
  (.literal () (.boolLit () true))
---
info: true <== false <== true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check true <== false <== true #end

-- Test <== with explicit left-associative parentheses
-- Should parse the same as without parentheses
/--
info: B3: .binaryOp
  ()
  (.impliedBy ())
  (.binaryOp
    ()
    (.impliedBy ())
    (.literal () (.boolLit () true))
    (.literal () (.boolLit () false)))
  (.literal () (.boolLit () true))
---
info: true <== false <== true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check (true <== false) <== true #end

-- Test <== with explicit right-associative parentheses
-- Should parse differently than without parentheses (if left-assoc is correct)
/--
info: B3: .binaryOp
  ()
  (.impliedBy ())
  (.literal () (.boolLit () true))
  (.binaryOp
    ()
    (.impliedBy ())
    (.literal () (.boolLit () false))
    (.literal () (.boolLit () true)))
---
info: true <== (false <== true)
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check true <== (false <== true) #end

-- Test ==> right-associativity
-- B3 grammar: ImpliesExpr ::= LogicalExpr "==>" ImpliesExpr
-- Expected: true ==> false ==> true parses as true ==> (false ==> true) (right-associative)
/--
info: B3: .binaryOp
  ()
  (.implies ())
  (.literal () (.boolLit () true))
  (.binaryOp
    ()
    (.implies ())
    (.literal () (.boolLit () false))
    (.literal () (.boolLit () true)))
---
info: true ==> false ==> true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check true ==> false ==> true #end

-- Test ==> with explicit right-associative parentheses
-- Should parse the same as without parentheses
/--
info: B3: .binaryOp
  ()
  (.implies ())
  (.literal () (.boolLit () true))
  (.binaryOp
    ()
    (.implies ())
    (.literal () (.boolLit () false))
    (.literal () (.boolLit () true)))
---
info: true ==> false ==> true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check true ==> (false ==> true) #end

-- Test ==> with explicit left-associative parentheses
-- Should parse differently than without parentheses (if right-assoc is correct)
/--
info: B3: .binaryOp
  ()
  (.implies ())
  (.binaryOp
    ()
    (.implies ())
    (.literal () (.boolLit () true))
    (.literal () (.boolLit () false)))
  (.literal () (.boolLit () true))
---
info: (true ==> false) ==> true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check (true ==> false) ==> true #end

-- Commented out for now because of an infinite issue
-- Test <==> left-associativity
-- B3 grammar: Expr ::= ( ImpExpExpr "<=>" )* ImpExpExpr
-- Expected: true <==> false <==> true parses as (true <==> false) <==> true (left-associative)
/--
info: B3: .binaryOp
  ()
  (.iff ())
  (.binaryOp
    ()
    (.iff ())
    (.literal () (.boolLit () true))
    (.literal () (.boolLit () false)))
  (.literal () (.boolLit () true))
---
info: true <==> false <==> true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check (true <==> false) <==> true #end

-- Might not resolve but we still need to parse them without error or infinite loop
/--
info: B3: .binaryOp
  ()
  (.le ())
  (.binaryOp
    ()
    (.le ())
    (.literal () (.intLit () 0))
    (.literal () (.intLit () 1)))
  (.literal () (.intLit () 2))
---
info: 0 <= 1 <= 2
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 0 <= 1 <= 2 #end

-- We capture this parsing error as ok just in case the DDM tolerates things differently.
/-- error: expected token -/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 0 <= 1 => 2 #end

/--
info: B3: .binaryOp
  ()
  (.lt ())
  (.binaryOp
    ()
    (.lt ())
    (.literal () (.intLit () 0))
    (.literal () (.intLit () 1)))
  (.literal () (.intLit () 2))
---
info: 0 < 1 < 2
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 0 < 1 < 2 #end

/--
info: B3: .binaryOp
  ()
  (.ge ())
  (.binaryOp
    ()
    (.ge ())
    (.literal () (.intLit () 0))
    (.literal () (.intLit () 1)))
  (.literal () (.intLit () 2))
---
info: 0 >= 1 >= 2
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 0 >= 1 >= 2 #end


/--
info: B3: .binaryOp
  ()
  (.gt ())
  (.binaryOp
    ()
    (.gt ())
    (.literal () (.intLit () 0))
    (.literal () (.intLit () 1)))
  (.literal () (.intLit () 2))
---
info: 0 > 1 > 2
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 0 > 1 > 2 #end


-- Test <==> binds looser than ==>
-- B3 grammar hierarchy: Expr (<==>)  contains ImpExpExpr (==>)
-- Expected: true <==> false ==> true parses as true <==> (false ==> true)
/--
info: B3: .binaryOp
  ()
  (.iff ())
  (.literal () (.boolLit () true))
  (.binaryOp
    ()
    (.implies ())
    (.literal () (.boolLit () false))
    (.literal () (.boolLit () true)))
---
info: true <==> false ==> true
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check true <==> false ==> true #end

-- Test if-else as PrimaryExpr to capture current behavior
-- It should be possible to remove parentheses around the if-else construct
-- because it's an endless expression, but there is no option yet in the DDM for that because that would require detecting that the else expression has the lowest precedence possible.
/--
info: B3: .binaryOp
  ()
  (.add ())
  (.literal () (.intLit () 1))
  (.ite
    ()
    (.literal () (.boolLit () true))
    (.literal () (.intLit () 2))
    (.literal () (.intLit () 3)))
---
info: 1 + (if true 2 else 3)
-/
#guard_msgs in
#eval roundtripExpr $ #strata program B3CST; check 1 + if true 2 else 3 #end

end AssociativityAndPrecedenceTests

end B3
