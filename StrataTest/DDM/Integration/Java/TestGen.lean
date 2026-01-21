/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Java
import Strata.DDM.Integration.Lean.Env  -- For dialectExt
import Strata.DDM.Integration.Lean.HashCommands  -- For #load_dialect
import Strata.Languages.Core.DDMTransform.Parse  -- Loads Strata Core dialect into env

namespace Strata.Java.Test

open Strata.Java

def check (s sub : String) : Bool := (s.splitOn sub).length > 1

-- Test 1: Basic dialect with 2 operators
#eval do
  let testDialect : Strata.Dialect := {
    name := "Test"
    imports := #[]
    declarations := #[
      .syncat { name := "Expr", argNames := #[] },
      .op {
        name := "literal"
        argDecls := .ofArray #[
          { ident := "value", kind := .cat (.atom .none ⟨"Init", "Num"⟩) }
        ]
        category := ⟨"Test", "Expr"⟩
        syntaxDef := { atoms := #[], prec := 0 }
      },
      .op {
        name := "add"
        argDecls := .ofArray #[
          { ident := "lhs", kind := .cat (.atom .none ⟨"Test", "Expr"⟩) },
          { ident := "rhs", kind := .cat (.atom .none ⟨"Test", "Expr"⟩) }
        ]
        category := ⟨"Test", "Expr"⟩
        syntaxDef := { atoms := #[], prec := 0 }
      }
    ]
  }
  let files := (generateDialect testDialect "com.test").toOption.get!
  assert! files.interfaces.any (fun i => check i.2 "sealed interface Expr")
  assert! files.records.size = 2
  assert! files.records.any (fun r => check r.1 "Literal")
  assert! files.records.any (fun r => check r.1 "Add")
  pure ()

-- Test 2: Reserved word escaping for fields
#eval do
  let testDialect : Strata.Dialect := {
    name := "Reserved"
    imports := #[]
    declarations := #[
      .syncat { name := "Stmt", argNames := #[] },
      .op {
        name := "int"
        argDecls := .ofArray #[
          { ident := "public", kind := .cat (.atom .none ⟨"Init", "Ident"⟩) }
        ]
        category := ⟨"Reserved", "Stmt"⟩
        syntaxDef := { atoms := #[], prec := 0 }
      }
    ]
  }
  let files := (generateDialect testDialect "com.test").toOption.get!
  assert! files.records.any (fun r => r.1 == "Int.java")
  assert! files.records.any (fun r => check r.2 "public_")
  pure ()

-- Test 3: Name collision (operator name matches category name)
#eval do
  let testDialect : Strata.Dialect := {
    name := "Collision"
    imports := #[]
    declarations := #[
      .syncat { name := "expr", argNames := #[] },
      .op {
        name := "Expr"
        argDecls := .ofArray #[]
        category := ⟨"Collision", "expr"⟩
        syntaxDef := { atoms := #[], prec := 0 }
      }
    ]
  }
  let files := (generateDialect testDialect "com.test").toOption.get!
  assert! files.interfaces.any (fun i => i.1 == "Expr.java")
  assert! files.records.any (fun r => r.1 == "Expr_.java")
  pure ()

-- Test 4: Duplicate operator names and reserved word collision
#eval do
  let testDialect : Strata.Dialect := {
    name := "Dup"
    imports := #[]
    declarations := #[
      .syncat { name := "A", argNames := #[] },
      .syncat { name := "B", argNames := #[] },
      .op { name := "foo", argDecls := .ofArray #[], category := ⟨"Dup", "A"⟩, syntaxDef := { atoms := #[], prec := 0 } },
      .op { name := "foo", argDecls := .ofArray #[], category := ⟨"Dup", "B"⟩, syntaxDef := { atoms := #[], prec := 0 } },  -- Duplicate
      .op { name := "class", argDecls := .ofArray #[], category := ⟨"Dup", "A"⟩, syntaxDef := { atoms := #[], prec := 0 } },
      .op { name := "class_", argDecls := .ofArray #[], category := ⟨"Dup", "B"⟩, syntaxDef := { atoms := #[], prec := 0 } }  -- Would clash after escaping
    ]
  }
  let files := (generateDialect testDialect "com.test").toOption.get!
  let recordNames := files.records.map Prod.fst
  assert! recordNames.toList.eraseDups.length == recordNames.size
  pure ()

-- Test 5: Category name collides with base class
#eval do
  let testDialect : Strata.Dialect := {
    name := "Base"
    imports := #[]
    declarations := #[
      .syncat { name := "Node", argNames := #[] },  -- Collides with base class
      .op { name := "leaf", argDecls := .ofArray #[], category := ⟨"Base", "Node"⟩, syntaxDef := { atoms := #[], prec := 0 } }
    ]
  }
  let files := (generateDialect testDialect "com.test").toOption.get!
  let allNames := #["Node.java", "SourceRange.java"] ++ files.interfaces.map Prod.fst ++ files.records.map Prod.fst
  assert! allNames.toList.eraseDups.length == allNames.size
  pure ()

-- Test 6: Snake_case to PascalCase conversion
#eval do
  let testDialect : Strata.Dialect := {
    name := "Snake"
    imports := #[]
    declarations := #[
      .syncat { name := "my_category", argNames := #[] },
      .op {
        name := "my_operator"
        argDecls := .ofArray #[]
        category := ⟨"Snake", "my_category"⟩
        syntaxDef := { atoms := #[], prec := 0 }
      }
    ]
  }
  let files := (generateDialect testDialect "com.test").toOption.get!
  assert! files.interfaces.any (fun i => i.1 == "MyCategory.java")
  assert! files.records.any (fun r => r.1 == "MyOperator.java")
  pure ()

-- Test 7: All DDM types map correctly
#eval! do
  let testDialect : Strata.Dialect := {
    name := "Types"
    imports := #[]
    declarations := #[
      .syncat { name := "Node", argNames := #[] },
      .op {
        name := "allTypes"
        argDecls := .ofArray #[
          { ident := "ident", kind := .cat (.atom .none ⟨"Init", "Ident"⟩) },
          { ident := "num", kind := .cat (.atom .none ⟨"Init", "Num"⟩) },
          { ident := "dec", kind := .cat (.atom .none ⟨"Init", "Decimal"⟩) },
          { ident := "str", kind := .cat (.atom .none ⟨"Init", "Str"⟩) },
          { ident := "b", kind := .cat (.atom .none ⟨"Init", "Bool"⟩) },
          { ident := "bytes", kind := .cat (.atom .none ⟨"Init", "ByteArray"⟩) },
          { ident := "opt", kind := .cat ⟨.none, ⟨"Init", "Option"⟩, #[.atom .none ⟨"Init", "Num"⟩]⟩ },
          { ident := "seq", kind := .cat ⟨.none, ⟨"Init", "Seq"⟩, #[.atom .none ⟨"Init", "Ident"⟩]⟩ }
        ]
        category := ⟨"Types", "Node"⟩
        syntaxDef := { atoms := #[], prec := 0 }
      }
    ]
  }
  let files := (generateDialect testDialect "com.test").toOption.get!
  let record := files.records[0]!.2
  assert! check record "java.lang.String ident"
  assert! check record "java.math.BigInteger num"
  assert! check record "java.math.BigDecimal dec"
  assert! check record "java.lang.String str"
  assert! check record "boolean b"
  assert! check record "byte[] bytes"
  assert! check record "java.util.Optional<java.math.BigInteger> opt"
  assert! check record "java.util.List<java.lang.String> seq"
  pure ()

-- Test 8: FQN usage (no imports that could conflict)
#eval! do
  let testDialect : Strata.Dialect := {
    name := "FQN"
    imports := #[]
    declarations := #[
      .syncat { name := "Node", argNames := #[] },
      .op {
        name := "test"
        argDecls := .ofArray #[]
        category := ⟨"FQN", "Node"⟩
        syntaxDef := { atoms := #[], prec := 0 }
      }
    ]
  }
  let files := (generateDialect testDialect "com.test").toOption.get!
  let record := files.records[0]!.2
  assert! !(check record "import java.")
  assert! check record "java.lang.String operationName()"
  pure ()

-- Test 9: Stub interfaces for referenced-but-empty categories
#eval do
  let testDialect : Strata.Dialect := {
    name := "Stub"
    imports := #[]
    declarations := #[
      .syncat { name := "Stmt", argNames := #[] },
      .op {
        name := "eval"
        argDecls := .ofArray #[
          { ident := "e", kind := .cat (.atom .none ⟨"Init", "Expr"⟩) }  -- References Init.Expr
        ]
        category := ⟨"Stub", "Stmt"⟩
        syntaxDef := { atoms := #[], prec := 0 }
      }
    ]
  }
  let files := (generateDialect testDialect "com.test").toOption.get!
  assert! files.interfaces.any (fun i => check i.2 "sealed interface Stmt")
  assert! files.interfaces.any (fun i => check i.2 "non-sealed interface Expr")
  pure ()

-- Test 10: Core dialect returns error (has type/function declarations not yet supported)
elab "#testCoreError" : command => do
  let env ← Lean.getEnv
  let state := Strata.dialectExt.getState env
  let some core := state.loaded.dialects["Core"]?
    | Lean.logError "Core dialect not found"; return
  match generateDialect core "com.strata.core" with
  | .error msg =>
    if !(check msg "type declaration" || check msg "function declaration") then
      Lean.logError s!"Expected error about type/function declaration, got: {msg}"
  | .ok _ => Lean.logError "Expected error for Core dialect"

#testCoreError

-- Test 11: Cross-dialect name collision (A.Num vs B.Num)
#eval do
  let testDialect : Strata.Dialect := {
    name := "A"
    imports := #[]
    declarations := #[
      .syncat { name := "Num", argNames := #[] },
      .op {
        name := "lit"
        argDecls := .ofArray #[
          { ident := "a", kind := .cat (.atom .none ⟨"A", "Num"⟩) },
          { ident := "b", kind := .cat (.atom .none ⟨"B", "Num"⟩) }
        ]
        category := ⟨"A", "Num"⟩
        syntaxDef := { atoms := #[], prec := 0 }
      }
    ]
  }
  let files := (generateDialect testDialect "com.test").toOption.get!
  -- Should have 2 interfaces: one for A.Num, one stub for B.Num
  assert! files.interfaces.size = 2
  let names : List String := files.interfaces.toList.map Prod.fst
  assert! names.any (fun n => (n.splitOn "A").length > 1)
  assert! names.any (fun n => (n.splitOn "B").length > 1)
  pure ()

-- Test 12: Generated Java compiles (requires javac)
#load_dialect "testdata/Simple.dialect.st"

elab "#testCompile" : command => do
  let javacCheck ← IO.Process.output { cmd := "javac", args := #["--version"] }
  if javacCheck.exitCode != 0 then
    Lean.logError "Test 12 failed: javac not found"
    return

  let env ← Lean.getEnv
  let state := Strata.dialectExt.getState env
  let some simple := state.loaded.dialects["Simple"]?
    | Lean.logError "Simple dialect not found"; return
  let files := (generateDialect simple "com.test").toOption.get!

  let dir : System.FilePath := "/tmp/strata-java-test"
  writeJavaFiles dir "com.test" files

  let fileNames := #["SourceRange.java", "Node.java", files.builders.1]
                   ++ files.interfaces.map Prod.fst
                   ++ files.records.map Prod.fst
  let pkgDir := (dir / "com" / "test").toString
  let filePaths := fileNames.map fun f => pkgDir ++ "/" ++ f

  let result ← IO.Process.output {
    cmd := "javac"
    args := filePaths
  }

  IO.FS.removeDirAll dir

  if result.exitCode != 0 then
    Lean.logError s!"javac failed:\n{result.stderr}"

#testCompile

-- Test 13: Roundtrip - verify Lean can read Java-generated Ion
-- Depends on testdata/comprehensive.ion
elab "#testRoundtrip" : command => do
  let env ← Lean.getEnv
  let state := Strata.dialectExt.getState env
  let some simple := state.loaded.dialects["Simple"]?
    | Lean.logError "Simple dialect not found"; return
  let dm := Strata.DialectMap.ofList! [Strata.initDialect, simple]
  let ionBytes ← IO.FS.readBinFile "StrataTest/DDM/Integration/Java/testdata/comprehensive.ion"
  match Strata.Program.fileFromIon dm "Simple" ionBytes with
  | .error e => Lean.logError s!"Roundtrip test failed: {e}"
  | .ok prog =>
    if prog.commands.size != 1 then Lean.logError "Expected 1 command"; return
    let cmd := prog.commands[0]!
    if cmd.name != (⟨"Simple", "block"⟩ : Strata.QualifiedIdent) then Lean.logError "Expected block command"; return
    if let .seq _ _ stmts := cmd.args[0]! then
      if stmts.size != 4 then Lean.logError s!"Expected 4 statements, got {stmts.size}"
    else Lean.logError "Expected seq argument"

#testRoundtrip

-- Test 14: Roundtrip with fromIonFiles - verify Lean can read Java-generated Ion array format
-- Depends on testdata/comprehensive-files.ion
elab "#testRoundtripFiles" : command => do
  let env ← Lean.getEnv
  let state := Strata.dialectExt.getState env
  let some simple := state.loaded.dialects["Simple"]?
    | Lean.logError "Simple dialect not found"; return
  let dm := Strata.DialectMap.ofList! [Strata.initDialect, simple]
  let ionBytes ← IO.FS.readBinFile "StrataTest/DDM/Integration/Java/testdata/comprehensive-files.ion"
  match Strata.Program.filesFromIon dm ionBytes with
  | .error e => Lean.logError s!"Roundtrip files test failed: {e}"
  | .ok files =>
    if files.length != 2 then
      Lean.logError s!"Expected 2 files, got {files.length}"
      return

    -- Check first file
    let file1 := files[0]!
    if file1.filePath != "file1.st" then
      Lean.logError s!"File 1: Expected path 'file1.st', got '{file1.filePath}'"
      return
    if file1.program.commands.size != 1 then
      Lean.logError s!"File 1: Expected 1 command, got {file1.program.commands.size}"
      return
    let cmd1 := file1.program.commands[0]!
    if cmd1.name != (⟨"Simple", "block"⟩ : Strata.QualifiedIdent) then
      Lean.logError "File 1: Expected block command"; return
    if let .seq _ _ stmts := cmd1.args[0]! then
      if stmts.size != 2 then
        Lean.logError s!"File 1: Expected 2 statements, got {stmts.size}"
        return
    else
      Lean.logError "File 1: Expected seq argument"; return

    -- Check second file
    let file2 := files[1]!
    if file2.filePath != "file2.st" then
      Lean.logError s!"File 2: Expected path 'file2.st', got '{file2.filePath}'"
      return
    if file2.program.commands.size != 1 then
      Lean.logError s!"File 2: Expected 1 command, got {file2.program.commands.size}"
      return
    let cmd2 := file2.program.commands[0]!
    if cmd2.name != (⟨"Simple", "block"⟩ : Strata.QualifiedIdent) then
      Lean.logError "File 2: Expected block command"; return
    if let .seq _ _ stmts := cmd2.args[0]! then
      if stmts.size != 3 then
        Lean.logError s!"File 2: Expected 3 statements, got {stmts.size}"
        return
    else
      Lean.logError "File 2: Expected seq argument"; return

#testRoundtripFiles

end Strata.Java.Test
