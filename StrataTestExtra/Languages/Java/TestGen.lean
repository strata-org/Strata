/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Command
public meta import Strata.Java.Gen
public meta import Strata.Util.IonDeserializer
-- Non-meta as well: the deserializer tests below bind readers as top-level
-- `partial def`s, which recursive types require.
public import Strata.Util.IonDeserializer

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

/-- A single-constructor inductive: encoded as an Ion struct with *positional*
keys (`_0`, `_1`), distinct from both field-name-keyed structs and multi-ctor
sexps. -/
inductive Wrapper where
  | mk (value : Nat) (label : String)
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

structure Team where
  name : String
  members : List String
  mascot : Option String
deriving Repr, BEq

/-- Exercises nested containers, whose elements cannot be serialized with
`toIon` because `java.util.List` does not implement it. -/
structure League where
  rosters : Option (List String)
  groups : List (List String)
deriving Repr, BEq

/-- An inductive with no constructors: `permits` has nothing to list. -/
inductive Void where

/-- Two constructors whose names collide after escaping and PascalCasing:
`myCase` and `my_case` both fold to `MyCase`. -/
inductive CollidingCtors where
  | myCase (x : Nat)
  | my_case (y : Nat)

/-- Two fields whose names collide after escaping: `a?b` and `ab` both fold to
`ab` once non-alphanumeric characters are stripped. -/
structure CollidingFields where
  «a?b» : Nat
  ab : Nat

-- Test 1: Structure generates a record with field-name-keyed Ion struct
elab "#testPoint" : command => do
  let files := getIonSerializer% Point "com.test"
  let some (_, content) := files.files.find? (·.1 == "Point.java")
    | Lean.logError "Expected Point.java"; return
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
  let some (_, content) := files.files.find? (·.1 == "Color.java")
    | Lean.logError "Expected Color.java"; return
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
  let some (_, content) := files.files.find? (·.1 == "Shape.java")
    | Lean.logError "Expected Shape.java"; return
  if !check content "sealed interface Shape" then Lean.logError "Missing sealed interface"; return
  if !check content "record Circle(long radius)" then Lean.logError "Missing Circle record"; return
  if !check content "record Rect(long width, long height)" then Lean.logError "Missing Rect record"; return
  if !check content "newSymbol(\"circle\")" then Lean.logError "Missing newSymbol circle"; return
  if !check content "newSymbol(\"rect\")" then Lean.logError "Missing newSymbol rect"; return

#testShape

-- Test 3b: Single-constructor inductive uses positional `_0`, `_1` Ion keys.
elab "#testWrapper" : command => do
  let files := getIonSerializer% Wrapper "com.test"
  let some (_, content) := files.files.find? (·.1 == "Wrapper.java")
    | Lean.logError "Expected Wrapper.java"; return
  -- A single-ctor inductive is a record, not a sealed interface.
  if !check content "public record Wrapper(" then Lean.logError "Missing record Wrapper"; return
  if check content "sealed interface" then Lean.logError "Single-ctor must not be a sealed interface"; return
  if !check content "long value" then Lean.logError "Missing long value"; return
  if !check content "java.lang.String label" then Lean.logError "Missing String label"; return
  -- Positional keys, not field-name keys.
  if !check content "s.put(\"_0\"" then Lean.logError "Missing positional key _0"; return
  if !check content "s.put(\"_1\"" then Lean.logError "Missing positional key _1"; return

#testWrapper

-- Test 4: Structure with String and Bool fields
elab "#testPerson" : command => do
  let files := getIonSerializer% Person "com.test"
  let some (_, content) := files.files.find? (·.1 == "Person.java")
    | Lean.logError "Expected Person.java"; return
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
  let some (_, content) := files.files.find? (·.1 == "Tree.java")
    | Lean.logError "Expected Tree.java"; return
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
  let content := "package com.test;\npublic record Test() {}\n"
  let files : GeneratedFiles := { files := #[("Test.java", content)] }
  writeJavaFiles dir "com.test" files
  let path := dir / "com" / "test" / "Test.java"
  if !(← path.pathExists) then
    Lean.logError "Expected file not found"
  else
    let written ← IO.FS.readFile path
    if written != content then
      Lean.logError s!"Written content mismatch: got {written}"
  IO.FS.removeDirAll dir

#testWriteFiles

-- Test 9: Generated Java compiles (requires javac + ion-java jar)
elab "#testCompile" : command => do
  let javacCheck ← IO.Process.output { cmd := "javac", args := #["--version"] }
  if javacCheck.exitCode != 0 then
    Lean.logWarning "Test skipped: javac not found"
    return

  let jarPath := "StrataTestExtra/Languages/Java/testdata/ion-java-1.11.11.jar"
  if !(← System.FilePath.pathExists jarPath) then
    Lean.logWarning s!"Test skipped: ion-java jar not found at {jarPath}"
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
    Lean.logWarning "Roundtrip test skipped: javac not found"
    return

  let jarPath := "StrataTestExtra/Languages/Java/testdata/ion-java-1.11.11.jar"
  if !(← System.FilePath.pathExists jarPath) then
    Lean.logWarning s!"Roundtrip test skipped: ion-java jar not found at {jarPath}"
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

-- Test 11: Structure with List and Option fields
elab "#testTeam" : command => do
  let files := getIonSerializer% Team "com.test"
  let some (_, content) := files.files.find? (·.1 == "Team.java")
    | Lean.logError "Expected Team.java"; return
  if !check content "public record Team(" then Lean.logError "Missing record Team"; return
  if !check content "java.lang.String name" then Lean.logError "Missing String name"; return
  if !check content "java.util.List<java.lang.String> members" then Lean.logError "Missing List members"; return
  if !check content "java.util.Optional<java.lang.String> mascot" then Lean.logError "Missing Option mascot"; return
  if !check content "for (var e : members())" then Lean.logError "Missing list loop"; return
  if !check content "mascot().isPresent()" then Lean.logError "Missing isPresent check for option"; return

#testTeam

-- Test 12: Nested containers serialize without calling `toIon` on a java.util.List
elab "#testLeague" : command => do
  let files := getIonSerializer% League "com.test"
  let some (_, content) := files.files.find? (·.1 == "League.java")
    | Lean.logError "Expected League.java"; return
  if !check content "java.util.Optional<java.util.List<java.lang.String>> rosters" then
    Lean.logError "Missing Optional<List<String>> rosters"; return
  if !check content "java.util.List<java.util.List<java.lang.String>> groups" then
    Lean.logError "Missing List<List<String>> groups"; return
  -- The inner list must be built via ion.newList(...), never `.toIon(ion)`.
  if !check content "ion.newList(rosters().get().stream()" then
    Lean.logError "Option-of-list must serialize via ion.newList"; return
  if check content "rosters().get().toIon(ion)" then
    Lean.logError "Option-of-list must not call toIon on a java.util.List"; return
  -- The nested lambda binder must not shadow the enclosing `for (var e : ...)`.
  if !check content "for (var e : groups()) _l_groups.add(ion.newList(e.stream()" then
    Lean.logError "List-of-list must build the inner list via ion.newList"; return
  if !check content "_e1 ->" then
    Lean.logError "Nested list lambda must use a depth-suffixed binder"; return

#testLeague

-- Test 13: Generated Java for nested containers compiles
elab "#testCompileNested" : command => do
  let javacCheck ← IO.Process.output { cmd := "javac", args := #["--version"] }
  if javacCheck.exitCode != 0 then
    Lean.logWarning "Test skipped: javac not found"
    return

  let jarPath := "StrataTestExtra/Languages/Java/testdata/ion-java-1.11.11.jar"
  if !(← System.FilePath.pathExists jarPath) then
    Lean.logWarning s!"Test skipped: ion-java jar not found at {jarPath}"
    return

  let dir : System.FilePath := "/tmp/strata-java-test-nested"
  if ← dir.pathExists then IO.FS.removeDirAll dir

  let files := getIonSerializer% League "com.test"
  let pkgDir := dir / "com" / "test"
  IO.FS.createDirAll pkgDir
  let mut filePaths : Array String := #[]
  for (name, content) in files.files do
    let path := pkgDir / name
    IO.FS.writeFile path content
    filePaths := filePaths.push path.toString

  let result ← IO.Process.output {
    cmd := "javac"
    args := #["-cp", s!"{jarPath}:{dir}"] ++ filePaths
  }
  if result.exitCode != 0 then
    Lean.throwError s!"javac failed for nested containers:\n{result.stderr}"

  IO.FS.removeDirAll dir

#testCompileNested

-- Test 13a: a zero-constructor inductive drops *both* `sealed` and `permits`.
-- `sealed interface Void extends ToIon permits  {` is not valid Java, and
-- neither is `sealed interface Void extends ToIon {` — javac rejects a sealed
-- type with no permitted subtype (`sealed class must have subclasses`), so
-- omitting only `permits` would swap one uncompilable form for another.
--
-- The expected declaration is anchored with its leading `public ` on purpose:
-- `"interface Void extends ToIon {"` is a *substring* of the broken sealed
-- line, so an unanchored check cannot tell the two apart.
elab "#testVoid" : command => do
  let files := getIonSerializer% Void "com.test"
  let some (_, content) := files.files.find? (·.1 == "Void.java")
    | Lean.logError "Expected Void.java"; return
  if !check content "public interface Void extends ToIon {" then
    Lean.logError "Zero-ctor inductive must emit a non-sealed interface"; return
  if check content "sealed" then
    Lean.logError "Zero-ctor inductive must not emit the sealed keyword"; return
  if check content "permits" then
    Lean.logError "Zero-ctor inductive must not emit a permits keyword"; return

#testVoid

-- Test 13a-bis: the zero-ctor interface actually compiles. `#testVoid` above
-- asserts on the emitted text; this pins that the text is *valid Java*, which
-- string assertions alone cannot establish.
elab "#testCompileVoid" : command => do
  let javacCheck ← IO.Process.output { cmd := "javac", args := #["--version"] }
  if javacCheck.exitCode != 0 then
    Lean.logWarning "Test skipped: javac not found"
    return

  let jarPath := "StrataTestExtra/Languages/Java/testdata/ion-java-1.11.11.jar"
  if !(← System.FilePath.pathExists jarPath) then
    Lean.logWarning s!"Test skipped: ion-java jar not found at {jarPath}"
    return

  let dir : System.FilePath := "/tmp/strata-java-test-void"
  if ← dir.pathExists then IO.FS.removeDirAll dir

  let files := getIonSerializer% Void "com.test"
  let pkgDir := dir / "com" / "test"
  IO.FS.createDirAll pkgDir
  let mut filePaths : Array String := #[]
  for (name, content) in files.files do
    let path := pkgDir / name
    IO.FS.writeFile path content
    filePaths := filePaths.push path.toString

  let result ← IO.Process.output {
    cmd := "javac"
    args := #["-cp", s!"{jarPath}:{dir}"] ++ filePaths
  }
  if result.exitCode != 0 then
    Lean.throwError s!"javac failed for zero-ctor inductive:\n{result.stderr}"

  IO.FS.removeDirAll dir

#testCompileVoid

-- Test 13b: constructor names that fold to the same Java identifier are
-- disambiguated, so the sealed interface has no duplicate record.
elab "#testCollidingCtors" : command => do
  let files := getIonSerializer% CollidingCtors "com.test"
  let some (_, content) := files.files.find? (·.1 == "CollidingCtors.java")
    | Lean.logError "Expected CollidingCtors.java"; return
  -- First `MyCase` keeps the plain name; the collision gets a `_` suffix.
  if !check content "record MyCase(" then Lean.logError "Missing MyCase record"; return
  if !check content "record MyCase_(" then
    Lean.logError "Colliding ctor must be disambiguated to MyCase_"; return
  if !check content "permits CollidingCtors.MyCase, CollidingCtors.MyCase_" then
    Lean.logError "permits clause must list both disambiguated records"; return
  -- The Ion tags stay the original short names, so the wire format is unchanged.
  if !check content "newSymbol(\"myCase\")" then Lean.logError "Ion tag myCase must be preserved"; return
  if !check content "newSymbol(\"my_case\")" then Lean.logError "Ion tag my_case must be preserved"; return

#testCollidingCtors

-- Test 13c: record-component names that fold to the same Java identifier are
-- disambiguated, while their Ion struct keys stay distinct.
elab "#testCollidingFields" : command => do
  let files := getIonSerializer% CollidingFields "com.test"
  let some (_, content) := files.files.find? (·.1 == "CollidingFields.java")
    | Lean.logError "Expected CollidingFields.java"; return
  -- Both escape to `ab`; the second becomes `ab_`.
  if !check content "long ab, long ab_" then
    Lean.logError "Colliding fields must be disambiguated to ab and ab_"; return
  -- Both original names remain the Ion keys.
  if !check content "s.put(\"a?b\"" then Lean.logError "Ion key a?b must be preserved"; return
  if !check content "s.put(\"ab\"" then Lean.logError "Ion key ab must be preserved"; return

#testCollidingFields

/-! ## Deserializer behaviour

`#testRoundtrip` covers only `Point`, and only with javac available. The tests
below pin what `getIonDeserializer%` actually decodes for the shapes the
elaborator exists to handle — field-keyed structs, multi-constructor sexps,
recursion, and nested containers — with no external tooling.

The expected input is built as an `Ion` *tree* and then serialized, rather than
as literal bytes, so these tests describe the encoding without being sensitive
to how it is laid out on the wire.
-/

private partial def desPoint : ByteArray → Except Std.Format Point :=
  getIonDeserializer% Point

private partial def desShape : ByteArray → Except Std.Format Shape :=
  getIonDeserializer% Shape

private partial def desWrapper : ByteArray → Except Std.Format Wrapper :=
  getIonDeserializer% Wrapper

private partial def desTree : ByteArray → Except Std.Format Tree :=
  getIonDeserializer% Tree

private partial def desTeam : ByteArray → Except Std.Format Team :=
  getIonDeserializer% Team

private partial def desLeague : ByteArray → Except Std.Format League :=
  getIonDeserializer% League

private def encode (v : Ion.Ion String) : ByteArray :=
  Ion.internAndSerialize [v]

private def leafIon (n : Int) : Ion.Ion String :=
  .sexp #[.symbol "leaf", .int n]

private def teamIon (members : Array (Ion.Ion String)) (mascot : Ion.Ion String) :
    Ion.Ion String :=
  .struct #[("name", .string "Rockets"), ("members", .list members),
            ("mascot", mascot)]

-- Test 14: structures decode from their field-name-keyed struct encoding.
#guard (desPoint (encode (.struct #[("x", .int 10), ("y", .int 20)]))).toOption
    == some { x := 10, y := 20 }

-- Test 14b: single-constructor inductives decode from their positional-key
-- struct encoding (`_0`, `_1`), distinct from field-name-keyed structs.
#guard (desWrapper (encode (.struct #[("_0", .int 7), ("_1", .string "hi")]))).toOption
    == some (.mk 7 "hi")

-- Test 15: multi-constructor inductives decode from their sexp encoding.
#guard (desShape (encode (.sexp #[.symbol "circle", .int 5]))).toOption
    == some (.circle 5)
#guard (desShape (encode (.sexp #[.symbol "rect", .int 3, .int 4]))).toOption
    == some (.rect 3 4)
-- An unknown constructor tag must be rejected, not silently mapped.
#guard (desShape (encode (.sexp #[.symbol "triangle", .int 1]))).toOption == none

-- Test 16: recursive types decode through nested sexps.
-- Start with the base case: a bare `leaf`, with no recursion at all.
#guard (desTree (encode (leafIon 99))).toOption == some (.leaf 99)
#guard (desTree (encode (.sexp #[.symbol "node", leafIon 1, leafIon 2]))).toOption
    == some (.node (.leaf 1) (.leaf 2))
-- Nest one level deeper to exercise the recursive reader past its first use.
#guard (desTree (encode (.sexp #[.symbol "node",
      .sexp #[.symbol "node", leafIon 1, leafIon 2], leafIon 3]))).toOption
    == some (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))

-- Test 17: struct fields, `List`, and both `Option` cases.
#guard (desTeam (encode (teamIon #[.string "ann", .string "bo"] (.string "comet")))).toOption
    == some { name := "Rockets", members := ["ann", "bo"], mascot := some "comet" }
-- An Ion null decodes to `none`, and an empty list to `[]` — not an error.
#guard (desTeam (encode (teamIon #[] (.null)))).toOption
    == some { name := "Rockets", members := [], mascot := none }

-- Test 18: nested containers decode, mirroring the `#testLeague` serializer
-- coverage of `Option (List T)` and `List (List T)`.
#guard (desLeague (encode (.struct #[
    ("rosters", .list #[.string "a", .string "b"]),
    ("groups", .list #[.list #[.string "x"], .list #[.string "y", .string "z"]])]))).toOption
    == some { rosters := some ["a", "b"], groups := [["x"], ["y", "z"]] }
#guard (desLeague (encode (.struct #[("rosters", .null), ("groups", .list #[])]))).toOption
    == some { rosters := none, groups := [] }

end Strata.Java.Test
