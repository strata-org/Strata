/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Java
import Strata.DDM.Integration.Lean.Env  -- For dialectExt
import Strata.Languages.Boogie.DDMTransform.Parse  -- Loads Boogie dialect into env

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
  let files := generateDialect testDialect "com.test"
  assert! files.interfaces.any (fun i => check i.2 "sealed interface Expr")
  assert! files.records.size = 2
  assert! files.records.any (fun r => check r.1 "Literal")
  assert! files.records.any (fun r => check r.1 "Add")
  pure ()

-- Test 2: Java reserved word escaping
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
  let files := generateDialect testDialect "com.test"
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
  let files := generateDialect testDialect "com.test"
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
  let files := generateDialect testDialect "com.test"
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
  let files := generateDialect testDialect "com.test"
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
  let files := generateDialect testDialect "com.test"
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
  let files := generateDialect testDialect "com.test"
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
  let files := generateDialect testDialect "com.test"
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
  let files := generateDialect testDialect "com.test"
  assert! files.interfaces.any (fun i => check i.2 "sealed interface Stmt")
  assert! files.interfaces.any (fun i => check i.2 "non-sealed interface Expr")
  pure ()

-- Test 10: Real dialect - Boogie
elab "#testBoogie" : command => do
  let env ← Lean.getEnv
  let state := Strata.dialectExt.getState env
  let some boogie := state.loaded.dialects["Boogie"]?
    | Lean.logError "Boogie dialect not found"
      return
  let files := generateDialect boogie "com.strata.boogie"
  if files.records.size < 30 then
    Lean.logError s!"Expected 30+ records, got {files.records.size}"
  if files.interfaces.size < 10 then
    Lean.logError s!"Expected 10+ interfaces, got {files.interfaces.size}"

#testBoogie

-- Test 11: Generated Java compiles (requires javac)
#eval do
  let javacCheck ← IO.Process.output { cmd := "javac", args := #["--version"] }
  if javacCheck.exitCode != 0 then
    IO.println "Test 11 skipped: javac not found"
    return

  let testDialect : Strata.Dialect := {
    name := "Compile"
    imports := #[]
    declarations := #[
      .syncat { name := "MyExpr", argNames := #[] },
      .op {
        name := "num"
        argDecls := .ofArray #[
          { ident := "value", kind := .cat (.atom .none ⟨"Init", "Num"⟩) }
        ]
        category := ⟨"Compile", "MyExpr"⟩
        syntaxDef := { atoms := #[], prec := 0 }
      },
      .op {
        name := "add"
        argDecls := .ofArray #[
          { ident := "left", kind := .cat (.atom .none ⟨"Compile", "MyExpr"⟩) },
          { ident := "right", kind := .cat (.atom .none ⟨"Compile", "MyExpr"⟩) }
        ]
        category := ⟨"Compile", "MyExpr"⟩
        syntaxDef := { atoms := #[], prec := 0 }
      }
    ]
  }
  let files := generateDialect testDialect "com.test"
  
  -- Write to temp directory  
  let dir := "/tmp/strata-java-test"
  IO.FS.createDirAll (dir ++ "/com/test")
  IO.FS.writeFile (dir ++ "/com/test/SourceRange.java") files.sourceRange
  IO.FS.writeFile (dir ++ "/com/test/Node.java") files.node
  for (name, content) in files.interfaces do
    IO.FS.writeFile (dir ++ "/com/test/" ++ name) content
  for (name, content) in files.records do
    IO.FS.writeFile (dir ++ "/com/test/" ++ name) content

  let fileNames := #["SourceRange.java", "Node.java"] 
                   ++ files.interfaces.map Prod.fst 
                   ++ files.records.map Prod.fst
  let filePaths := fileNames.map (dir ++ "/com/test/" ++ ·)

  let result ← IO.Process.output {
    cmd := "javac"
    args := #["--enable-preview", "--release", "17"] ++ filePaths
  }

  IO.FS.removeDirAll dir

  if result.exitCode != 0 then
    IO.eprintln s!"javac failed:\n{result.stderr}"
    assert! false
  pure ()

-- Test 12: Roundtrip - verify Lean can read Java-generated Ion
def simpleDialect : Strata.Dialect := 
  let cat (d n : String) : Strata.SyntaxCat := ⟨.none, ⟨d, n⟩, #[]⟩
  let seq c : Strata.SyntaxCat := ⟨.none, ⟨"Init", "Seq"⟩, #[c]⟩
  let opt c : Strata.SyntaxCat := ⟨.none, ⟨"Init", "Option"⟩, #[c]⟩
  let arg n c : Strata.ArgDecl := { ident := n, kind := .cat c }
  let op n args (c : Strata.QualifiedIdent) : Strata.Decl := 
    .op { name := n, argDecls := .ofArray args, category := c, syntaxDef := { atoms := #[], prec := 0 } }
  { name := "Simple", imports := #[], declarations := #[
    .syncat { name := "Expr", argNames := #[] },
    op "num" #[arg "value" (cat "Init" "Num")] ⟨"Simple", "Expr"⟩,
    op "add" #[arg "left" (cat "Simple" "Expr"), arg "right" (cat "Simple" "Expr")] ⟨"Simple", "Expr"⟩,
    op "neg" #[arg "inner" (cat "Simple" "Expr")] ⟨"Simple", "Expr"⟩,
    .syncat { name := "Stmt", argNames := #[] },
    op "print" #[arg "msg" (cat "Init" "Str")] ⟨"Simple", "Stmt"⟩,
    op "assign" #[arg "name" (cat "Init" "Ident"), arg "value" (cat "Simple" "Expr")] ⟨"Simple", "Stmt"⟩,
    op "block" #[arg "stmts" (seq (cat "Simple" "Stmt"))] ⟨"Simple", "Stmt"⟩,
    op "ifStmt" #[arg "cond" (cat "Init" "Bool"), arg "then" (cat "Simple" "Stmt"), arg "else" (opt (cat "Simple" "Stmt"))] ⟨"Simple", "Stmt"⟩,
    op "data" #[arg "bytes" (cat "Init" "ByteArray")] ⟨"Simple", "Stmt"⟩,
    op "decimal" #[arg "value" (cat "Init" "Decimal")] ⟨"Simple", "Stmt"⟩
  ]}

#eval do
  let dm := Strata.DialectMap.ofList! [Strata.initDialect, simpleDialect]
  let ionBytes ← IO.FS.readBinFile "StrataTest/DDM/Integration/Java/testdata/comprehensive.ion"
  match Strata.Program.fromIon dm "Simple" ionBytes with
  | .error e => IO.eprintln s!"Roundtrip test failed: {e}"; assert! false
  | .ok prog =>
    -- Verify structure: 1 block command with 4 statements
    assert! prog.commands.size == 1
    let cmd := prog.commands[0]!
    assert! cmd.name == (⟨"Simple", "block"⟩ : Strata.QualifiedIdent)
    let arg := cmd.args[0]!
    if let .seq _ stmts := arg then
      assert! stmts.size == 4
    else
      assert! false

end Strata.Java.Test
