-- Test the minimal Laurel grammar
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.LaurelParser

open Laurel.Parser

-- Test parsing the AssertFalse example
def testAssertFalse : IO Unit := do
  let content ← IO.FS.readFile "Strata/Languages/Laurel/Examples/Fundamentals/AssertFalse.lr.st"

  IO.println "=== Parsing AssertFalse.lr.st ===\n"

  match parseProgram content with
  | Except.error err =>
    IO.println s!"✗ Parse failed: {err}"
  | Except.ok prog =>
    IO.println "✓ Parse succeeded!\n"

    -- Check: Should have 2 procedures
    if prog.staticProcedures.length != 2 then
      IO.println s!"✗ Expected 2 procedures, got {prog.staticProcedures.length}"
      return
    IO.println "✓ Found 2 procedures"

    -- Check procedure 'foo'
    match prog.staticProcedures.head? with
    | none =>
      IO.println "✗ No first procedure found"
      return
    | some foo =>
      if foo.name != "foo" then
        IO.println s!"✗ Expected first procedure named 'foo', got '{foo.name}'"
        return
      IO.println "✓ First procedure is named 'foo'"

      match foo.body with
      | Body.Transparent (StmtExpr.Block stmts none) =>
        if stmts.length != 3 then
          IO.println s!"✗ Expected 3 statements in foo, got {stmts.length}"
          return
        IO.println "✓ Procedure 'foo' has 3 statements"

        -- Check statements in foo
        match stmts with
        | [StmtExpr.Assert (StmtExpr.LiteralBool true),
           StmtExpr.Assert (StmtExpr.LiteralBool false),
           StmtExpr.Assert (StmtExpr.LiteralBool false)] =>
          IO.println "✓ Procedure 'foo' statements: assert true; assert false; assert false;"
        | _ =>
          IO.println s!"✗ Unexpected statement structure in 'foo'"
          return
      | _ =>
        IO.println "✗ Expected transparent body with block"
        return

    -- Check procedure 'bar'
    match prog.staticProcedures.tail.head? with
    | none =>
      IO.println "✗ No second procedure found"
      return
    | some bar =>
      if bar.name != "bar" then
        IO.println s!"✗ Expected second procedure named 'bar', got '{bar.name}'"
        return
      IO.println "✓ Second procedure is named 'bar'"

      match bar.body with
      | Body.Transparent (StmtExpr.Block stmts none) =>
        if stmts.length != 2 then
          IO.println s!"✗ Expected 2 statements in bar, got {stmts.length}"
          return
        IO.println "✓ Procedure 'bar' has 2 statements"

        -- Check statements in bar
        match stmts with
        | [StmtExpr.Assume (StmtExpr.LiteralBool false),
           StmtExpr.Assert (StmtExpr.LiteralBool true)] =>
          IO.println "✓ Procedure 'bar' statements: assume false; assert true;"
        | _ =>
          IO.println s!"✗ Unexpected statement structure in 'bar'"
          return
      | _ =>
        IO.println "✗ Expected transparent body with block"
        return

    IO.println "\n✓✓✓ All checks passed! ✓✓✓"

#eval testAssertFalse
