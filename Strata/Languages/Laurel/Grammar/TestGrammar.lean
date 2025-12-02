-- Test the minimal Laurel grammar
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTree
import Strata.DDM.Elab
import Strata.DDM.Parser

open Strata

namespace Laurel

-- Test parsing the AssertFalse example
def testAssertFalse : IO Unit := do
  let content ← IO.FS.readFile "Strata/Languages/Laurel/Examples/Fundamentals/AssertFalse.lr.st"

  IO.println "=== Parsing AssertFalse.lr.st ===\n"

  -- Create LoadedDialects with the Laurel dialect
  let laurelDialect: Strata.Dialect := Laurel
  let loader := Elab.LoadedDialects.ofDialects! #[laurelDialect]

  -- Create InputContext from the file content
  let inputCtx := Strata.Parser.stringInputContext "TestGrammar.lean" content

  -- Create empty Lean environment
  let leanEnv ← Lean.mkEmptyEnvironment 0

  -- Parse using the dialect
  let ddmResult := Elab.elabProgram loader leanEnv inputCtx

  -- Translate from DDM AST to Laurel AST
  let parseResult : Except String Laurel.Program := match ddmResult with
    | Except.ok ddmProgram =>
      let (laurelProgram, errors) := TransM.run inputCtx (translateProgram ddmProgram)
      if errors.isEmpty then
        Except.ok laurelProgram
      else
        Except.error s!"Translation errors: {errors}"
    | Except.error messages =>
      Except.error s!"Parse errors: {messages.size} error(s)"
  match parseResult with
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

      let .Transparent bodyExpr := foo.body
        | IO.println "✗ Expected transparent body"; return
      let .Block stmts none := bodyExpr
        | IO.println "✗ Expected block in transparent body"; return
      if stmts.length != 3 then
        IO.println s!"✗ Expected 3 statements in foo, got {stmts.length}"
        return
      IO.println "✓ Procedure 'foo' has 3 statements"

      -- Check statements in foo
      let [stmt1, stmt2, stmt3] := stmts
        | IO.println s!"✗ Unexpected statement structure in 'foo'"; return
      let .Assert (.LiteralBool true) := stmt1
        | IO.println s!"✗ First statement should be 'assert true'"; return
      let .Assert (.LiteralBool false) := stmt2
        | IO.println s!"✗ Second statement should be 'assert false'"; return
      let .Assert (.LiteralBool false) := stmt3
        | IO.println s!"✗ Third statement should be 'assert false'"; return
      IO.println "✓ Procedure 'foo' statements: assert true; assert false; assert false;"

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

      let .Transparent bodyExpr := bar.body
        | IO.println "✗ Expected transparent body"; return
      let .Block stmts none := bodyExpr
        | IO.println "✗ Expected block in transparent body"; return
      if stmts.length != 2 then
        IO.println s!"✗ Expected 2 statements in bar, got {stmts.length}"
        return
      IO.println "✓ Procedure 'bar' has 2 statements"

      -- Check statements in bar
      let [stmt1, stmt2] := stmts
        | IO.println s!"✗ Unexpected statement structure in 'bar'"; return
      let .Assume (.LiteralBool false) := stmt1
        | IO.println s!"✗ First statement should be 'assume false'"; return
      let .Assert (.LiteralBool true) := stmt2
        | IO.println s!"✗ Second statement should be 'assert true'"; return
      IO.println "✓ Procedure 'bar' statements: assume false; assert true;"

    IO.println "\n✓✓✓ All checks passed! ✓✓✓"

#eval testAssertFalse
