/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Command
public meta import Strata.DDM.Integration.Java.Gen
public meta import Strata.Util.IonDeserializer

open Strata.Java

namespace Strata.Java.Test

meta def check (s sub : String) : Bool := (s.splitOn sub).length > 1

-- Test types
structure Point where
  x : Nat
  y : Nat
deriving Repr, BEq

inductive Color where
  | red
  | green
  | blue
deriving Repr, BEq

inductive Shape where
  | circle (radius : Nat)
  | rect (width : Nat) (height : Nat)
deriving Repr, BEq

structure Person where
  name : String
  age : Nat
  active : Bool
deriving Repr, BEq

structure Line where
  start : Point
  stop : Point
deriving Repr, BEq

inductive Tree where
  | leaf (value : Nat)
  | node (left : Tree) (right : Tree)
deriving Repr, BEq

-- Test 1: Structure generates a record with field-name-keyed Ion struct
elab "#testPoint" : command => do
  let files := getIonSerializer% Point "com.test"
  if files.files.size != 1 then Lean.logError "Expected 1 file"; return
  let (name, content) := files.files[0]!
  if name != "Point.java" then Lean.logError s!"Expected Point.java, got {name}"; return
  if !check content "public record Point(" then Lean.logError "Missing record Point"; return
  if !check content "long x" then Lean.logError "Missing long x"; return
  if !check content "long y" then Lean.logError "Missing long y"; return
  if !check content "toIon" then Lean.logError "Missing toIon"; return
  if !check content "s.put(\"x\"" then Lean.logError "Missing s.put(\"x\""; return
  if !check content "s.put(\"y\"" then Lean.logError "Missing s.put(\"y\""; return

#testPoint

-- Test 2: Multi-constructor inductive generates sealed interface with records
elab "#testColor" : command => do
  let files := getIonSerializer% Color "com.test"
  if files.files.size != 1 then Lean.logError "Expected 1 file"; return
  let (name, content) := files.files[0]!
  if name != "Color.java" then Lean.logError s!"Expected Color.java, got {name}"; return
  if !check content "sealed interface Color" then Lean.logError "Missing sealed interface"; return
  if !check content "record Red" then Lean.logError "Missing record Red"; return
  if !check content "record Green" then Lean.logError "Missing record Green"; return
  if !check content "record Blue" then Lean.logError "Missing record Blue"; return
  if !check content "newSymbol(\"red\")" then Lean.logError "Missing newSymbol red"; return
  if !check content "newSymbol(\"green\")" then Lean.logError "Missing newSymbol green"; return
  if !check content "newSymbol(\"blue\")" then Lean.logError "Missing newSymbol blue"; return

#testColor

-- Test 3: Multi-constructor inductive with fields
elab "#testShape" : command => do
  let files := getIonSerializer% Shape "com.test"
  if files.files.size != 1 then Lean.logError "Expected 1 file"; return
  let (_, content) := files.files[0]!
  if !check content "sealed interface Shape" then Lean.logError "Missing sealed interface"; return
  if !check content "record Circle(long radius)" then Lean.logError "Missing Circle record"; return
  if !check content "record Rect(long width, long height)" then Lean.logError "Missing Rect record"; return
  if !check content "newSymbol(\"circle\")" then Lean.logError "Missing newSymbol circle"; return
  if !check content "newSymbol(\"rect\")" then Lean.logError "Missing newSymbol rect"; return

#testShape

-- Test 4: Structure with String and Bool fields
elab "#testPerson" : command => do
  let files := getIonSerializer% Person "com.test"
  if files.files.size != 1 then Lean.logError "Expected 1 file"; return
  let (_, content) := files.files[0]!
  if !check content "java.lang.String name" then Lean.logError "Missing String name"; return
  if !check content "long age" then Lean.logError "Missing long age"; return
  if !check content "boolean active" then Lean.logError "Missing boolean active"; return
  if !check content "newString(name())" then Lean.logError "Missing newString"; return
  if !check content "newInt(age())" then Lean.logError "Missing newInt"; return
  if !check content "newBool(active())" then Lean.logError "Missing newBool"; return

#testPerson

-- Test 5: Nested structure generates files for both types
elab "#testLine" : command => do
  let files := getIonSerializer% Line "com.test"
  if files.files.size != 2 then Lean.logError s!"Expected 2 files, got {files.files.size}"; return
  if !files.files.any (fun f => f.1 == "Line.java") then Lean.logError "Missing Line.java"; return
  if !files.files.any (fun f => f.1 == "Point.java") then Lean.logError "Missing Point.java"; return
  for (fname, content) in files.files do
    if fname == "Line.java" then
      if !check content "Point start" then Lean.logError "Missing Point start"; return
      if !check content "Point stop" then Lean.logError "Missing Point stop"; return
      if !check content "start().toIon(ion)" then Lean.logError "Missing start().toIon"; return
      if !check content "stop().toIon(ion)" then Lean.logError "Missing stop().toIon"; return

#testLine

-- Test 6: Recursive type generates files
elab "#testTree" : command => do
  let files := getIonSerializer% Tree "com.test"
  if files.files.size != 1 then Lean.logError s!"Expected 1 file, got {files.files.size}"; return
  let (_, content) := files.files[0]!
  if !check content "sealed interface Tree" then Lean.logError "Missing sealed interface"; return
  if !check content "record Leaf(long value)" then Lean.logError "Missing Leaf record"; return
  if !check content "record Node(Tree left, Tree right)" then Lean.logError "Missing Node record"; return
  if !check content "left().toIon(ion)" then Lean.logError "Missing left().toIon"; return
  if !check content "right().toIon(ion)" then Lean.logError "Missing right().toIon"; return

#testTree

-- Test 7: Package name appears in generated files
elab "#testPackage" : command => do
  let files := getIonSerializer% Point "com.example.mypackage"
  let (_, content) := files.files[0]!
  if !check content "package com.example.mypackage;" then Lean.logError "Missing package"; return

#testPackage

-- Test 8: writeJavaFiles writes to correct directory
elab "#testWriteFiles" : command => do
  let dir : System.FilePath := "/tmp/strata-java-test-write"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  let files : GeneratedFiles := { files := #[("Test.java", "package com.test;\npublic record Test() {}\n")] }
  writeJavaFiles dir "com.test" files
  let path := dir / "com" / "test" / "Test.java"
  if !(← path.pathExists) then
    Lean.logError "Expected file not found"
  IO.FS.removeDirAll dir

#testWriteFiles

-- Test 9: Generated Java compiles (requires javac + ion-java jar)
elab "#testCompile" : command => do
  let javacCheck ← IO.Process.output { cmd := "javac", args := #["--version"] }
  if javacCheck.exitCode != 0 then
    Lean.logError "Test failed: javac not found"
    return

  let jarPath := "StrataTestExtra/DDM/Integration/Java/testdata/ion-java-1.11.11.jar"
  if !(← System.FilePath.pathExists jarPath) then
    Lean.logError s!"Test failed: ion-java jar not found at {jarPath}"
    return

  let dir : System.FilePath := "/tmp/strata-java-test-compile"
  if ← dir.pathExists then IO.FS.removeDirAll dir

  let shapeFiles := getIonSerializer% Shape "com.test"
  let lineFiles := getIonSerializer% Line "com.test"

  let mut allFiles : Std.HashMap String String := {}
  for (name, content) in shapeFiles.files do allFiles := allFiles.insert name content
  for (name, content) in lineFiles.files do allFiles := allFiles.insert name content

  let pkgDir := dir / "com" / "test"
  IO.FS.createDirAll pkgDir
  let mut filePaths : Array String := #[]
  for (name, content) in allFiles do
    let path := pkgDir / name
    IO.FS.writeFile path content
    filePaths := filePaths.push path.toString

  let result ← IO.Process.output {
    cmd := "javac"
    args := #["-cp", s!"{jarPath}:{dir}"] ++ filePaths
  }

  if result.exitCode != 0 then
    Lean.throwError s!"javac failed:\n{result.stderr}"

  IO.FS.removeDirAll dir

#testCompile

-- Test 10: Roundtrip - Java serializes Ion, Lean deserializes it
elab "#testRoundtrip" : command => do
  let javacCheck ← IO.Process.output { cmd := "javac", args := #["--version"] }
  if javacCheck.exitCode != 0 then
    Lean.logError "Roundtrip test skipped: javac not found"
    return

  let jarPath := "StrataTestExtra/DDM/Integration/Java/testdata/ion-java-1.11.11.jar"
  if !(← System.FilePath.pathExists jarPath) then
    Lean.logError s!"Roundtrip test skipped: ion-java jar not found at {jarPath}"
    return

  let dir : System.FilePath := "/tmp/strata-java-roundtrip"
  if ← dir.pathExists then IO.FS.removeDirAll dir

  let pointFiles := getIonSerializer% Point "com.test"
  let pkgDir := dir / "com" / "test"
  IO.FS.createDirAll pkgDir
  for (name, content) in pointFiles.files do
    IO.FS.writeFile (pkgDir / name) content

  let driverContent := "
import com.test.*;
import com.amazon.ion.*;
import com.amazon.ion.system.*;
import java.io.*;

public class RoundtripTest {
    public static void main(String[] args) throws Exception {
        var ionSystem = IonSystemBuilder.standard().build();
        var point = new Point(42, 7);
        var ionValue = point.toIon(ionSystem);

        try (var out = new FileOutputStream(args[0])) {
            var writer = IonBinaryWriterBuilder.standard().build(out);
            ionValue.writeTo(writer);
            writer.close();
        }
    }
}
"
  IO.FS.writeFile (dir / "RoundtripTest.java") driverContent

  let mut javaPaths : Array String := #[(dir / "RoundtripTest.java").toString]
  for (name, _) in pointFiles.files do
    javaPaths := javaPaths.push (pkgDir / name).toString

  let compileResult ← IO.Process.output {
    cmd := "javac"
    args := #["-cp", s!"{jarPath}:{dir}"] ++ javaPaths
  }
  if compileResult.exitCode != 0 then
    Lean.logError s!"Roundtrip compile failed:\n{compileResult.stderr}"
    IO.FS.removeDirAll dir
    return

  let ionFile := dir / "point.ion"
  let runResult ← IO.Process.output {
    cmd := "java"
    args := #["-cp", s!"{jarPath}:{dir}", "RoundtripTest", ionFile.toString]
  }
  if runResult.exitCode != 0 then
    Lean.logError s!"Roundtrip run failed:\n{runResult.stderr}"
    IO.FS.removeDirAll dir
    return

  let ionBytes ← IO.FS.readBinFile ionFile
  let deserializePoint : ByteArray → Except Std.Format Point := getIonDeserializer% Point
  match deserializePoint ionBytes with
  | .ok point =>
    if point.x != 42 || point.y != 7 then
      Lean.logError s!"Roundtrip mismatch: expected (42, 7), got ({point.x}, {point.y})"
  | .error e =>
    Lean.logError s!"Roundtrip deserialization failed: {e}"

  IO.FS.removeDirAll dir

#testRoundtrip

end Strata.Java.Test
