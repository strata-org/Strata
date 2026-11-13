/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataCortex.Implementation.Pipeline
meta import StrataCortex.Implementation.Interpret

/-!
# Arrays in Cortex

Wire programs that allocate, read and write arrays, run on the Cortex
interpreter. Each expected output lists the offsets of the assertions that
fail and the reason a run stopped.
-/

open Strata Cortex.Wire

namespace Cortex.ArraysTest

meta def at_ (n : Nat) : FileRange := { file := .file "T.java", range := { start := ⟨n⟩, stop := ⟨n + 1⟩ } }

meta def blk (label : String) (cmds : List Cmd) (t : Transfer) : Block := { label, cmds, transfer := t }

meta def int32 : Constrained :=
  { name := "int32", base := .int, binder := "$v",
    constraint := .op "Bool.And" [.op "Int.Le" [.int (-2147483648), .var "$v"], .op "Int.Le" [.var "$v", .int 2147483647]],
    witness := some (.int 0) }

meta def bv32 : Ty := .bv 32
meta def bv64 : Ty := .bv 64
meta def i32 : Ty := .named "int32"

/-- An entry procedure with one block. -/
meta def entry (name : String) (cmds : List Cmd) : Wire.Procedure :=
  { name, inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 0,
    body := some { entry := "b0", handlers := [], blocks := [blk "b0" cmds (.finish (at_ 0))] } }

/-- A program over the array types `Ints` (`bv32`), `Longs` (`bv64`), `Flags` (`bool`),
`Boxes` (references to `Box`) and `Checked` (the constrained type `int32`). -/
meta def program (procedures : List Wire.Procedure) : Wire.Program :=
  { composites := [{ name := "Object", extending := [], fields := [] },
                   { name := "Box", extending := ["Object"], fields := [{ name := "v", ty := bv32 }] }],
    constrained := [int32],
    arrays := [{ name := "Ints", elem := bv32, extending := ["Object"] },
               { name := "Longs", elem := bv64, extending := ["Object"] },
               { name := "Flags", elem := .bool, extending := ["Object"] },
               { name := "Boxes", elem := .named "Box", extending := ["Object"] },
               { name := "Checked", elem := i32, extending := ["Object"] }],
    procedures }

meta def interpret (p : Wire.Program) : IO Unit :=
  match Cortex.interpretWire p 1000 with
  | .error e => IO.println s!"error: {e}"
  | .ok outcome => do
    for m in outcome.diagnostics do
      IO.println s!"{m.fileRange.range.start.byteIdx}: {m.message}"
    for (name, reason) in outcome.errors do
      IO.println s!"stopped: '{name}': {reason}"

meta def isTrue (label : String) (cond : Wire.Expr) (n : Nat) : Cmd := .assert label cond none (at_ n)

/-! Every element of a new array is the default of the element type, and the length is the
one given. The assertions at offsets 20 to 24 state the opposite of those before them and
fail, so the ones before them are checked. -/

meta def defaults : Wire.Procedure :=
  entry "defaults" [
    .init "a" (.named "Ints") none (at_ 1), .newArray "a" "Ints" (.int 3) (at_ 1),
    .init "l" (.named "Longs") none (at_ 2), .newArray "l" "Longs" (.op "Int.Add" [.int 1, .int 1]) (at_ 2),
    .init "f" (.named "Flags") none (at_ 3), .newArray "f" "Flags" (.int 1) (at_ 3),
    .init "b" (.named "Boxes") none (at_ 4), .newArray "b" "Boxes" (.int 1) (at_ 4),
    .init "e" (.named "Ints") none (at_ 5), .newArray "e" "Ints" (.int 0) (at_ 5),
    .init "x" bv32 none (at_ 6), .readElem "x" (.var "a") (.int 2) bv32 (at_ 6),
    .init "y" bv64 none (at_ 7), .readElem "y" (.var "l") (.int 1) bv64 (at_ 7),
    .init "z" .bool none (at_ 8), .readElem "z" (.var "f") (.int 0) .bool (at_ 8),
    .init "o" (.named "Box") none (at_ 9), .readElem "o" (.var "b") (.int 0) (.named "Box") (at_ 9),
    .init "n" .int none (at_ 10), .arrayLength "n" (.var "a") (at_ 10),
    .init "m" .int none (at_ 11), .arrayLength "m" (.var "e") (at_ 11),
    isTrue "intDefault" (.eq (.var "x") (.bv 32 0)) 12,
    isTrue "longDefault" (.eq (.var "y") (.bv 64 0)) 13,
    isTrue "boolDefault" (.op "Bool.Not" [.var "z"]) 14,
    isTrue "refDefault" (.op "Bool.Not" [.eq (.var "o") (.var "b")]) 15,
    isTrue "length" (.eq (.var "n") (.int 3)) 16,
    isTrue "emptyLength" (.eq (.var "m") (.int 0)) 17,
    isTrue "intNotDefault" (.op "Bool.Not" [.eq (.var "x") (.bv 32 0)]) 20,
    isTrue "longNotDefault" (.op "Bool.Not" [.eq (.var "y") (.bv 64 0)]) 21,
    isTrue "boolNotDefault" (.var "z") 22,
    isTrue "otherLength" (.eq (.var "n") (.int 2)) 23,
    isTrue "emptyNotEmpty" (.eq (.var "m") (.int 1)) 24]

/--
info: 20: assertion does not hold
21: assertion does not hold
22: assertion does not hold
23: assertion does not hold
24: assertion does not hold
-/
#guard_msgs in
#eval interpret (program [defaults])

/-! A write changes the element it names and no other. Two variables that hold the same
reference see each other's writes, and a second array is a different object. An array is an
instance of its own array type and of the types that one extends, and of no other array type. -/

meta def writes : Wire.Procedure :=
  entry "writes" [
    .init "a" (.named "Ints") none (at_ 1), .newArray "a" "Ints" (.int 3) (at_ 1),
    .init "b" (.named "Ints") (some (.var "a")) (at_ 2),
    .init "c" (.named "Ints") none (at_ 3), .newArray "c" "Ints" (.int 3) (at_ 3),
    .writeElem (.var "a") (.int 1) (.bv 32 7) bv32 (at_ 4),
    .writeElem (.var "b") (.int 2) (.bv 32 (-1)) bv32 (at_ 5),
    .init "x0" bv32 none (at_ 6), .readElem "x0" (.var "a") (.int 0) bv32 (at_ 6),
    .init "x1" bv32 none (at_ 7), .readElem "x1" (.var "b") (.int 1) bv32 (at_ 7),
    .init "x2" bv32 none (at_ 8), .readElem "x2" (.var "a") (.int 2) bv32 (at_ 8),
    .init "y1" bv32 none (at_ 9), .readElem "y1" (.var "c") (.int 1) bv32 (at_ 9),
    .init "isInts" .bool none (at_ 10), .instanceOf "isInts" (.var "a") "Ints" (at_ 10),
    .init "isObject" .bool none (at_ 11), .instanceOf "isObject" (.var "a") "Object" (at_ 11),
    .init "isLongs" .bool none (at_ 12), .instanceOf "isLongs" (.var "a") "Longs" (at_ 12),
    isTrue "untouched" (.eq (.var "x0") (.bv 32 0)) 13,
    isTrue "written" (.eq (.var "x1") (.bv 32 7)) 14,
    isTrue "writtenThroughAlias" (.eq (.var "x2") (.bv 32 4294967295)) 15,
    isTrue "otherArray" (.eq (.var "y1") (.bv 32 0)) 16,
    isTrue "sameReference" (.eq (.var "a") (.var "b")) 17,
    isTrue "differentReference" (.op "Bool.Not" [.eq (.var "a") (.var "c")]) 18,
    isTrue "instanceOfOwnType" (.var "isInts") 19,
    isTrue "instanceOfParent" (.var "isObject") 20,
    isTrue "notInstanceOfOtherArray" (.op "Bool.Not" [.var "isLongs"]) 21,
    isTrue "writeLost" (.eq (.var "x1") (.bv 32 0)) 30,
    isTrue "instanceOfOtherArray" (.var "isLongs") 31]

/--
info: 30: assertion does not hold
31: assertion does not hold
-/
#guard_msgs in
#eval interpret (program [writes])

/-! An element of a constrained type is checked when it is written: the write at offset 3
stores a value outside `int32`. A read yields a value of the element type, here the one the
write at offset 2 stored. -/

meta def constrainedElements : Wire.Procedure :=
  entry "constrainedElements" [
    .init "a" (.named "Checked") none (at_ 1), .newArray "a" "Checked" (.int 2) (at_ 1),
    .writeElem (.var "a") (.int 0) (.int 5) i32 (at_ 2),
    .writeElem (.var "a") (.int 1) (.int 2147483648) i32 (at_ 3),
    .init "x" i32 none (at_ 4), .readElem "x" (.var "a") (.int 0) i32 (at_ 4),
    isTrue "read" (.eq (.var "x") (.int 5)) 5,
    isTrue "notRead" (.eq (.var "x") (.int 0)) 6]

/--
info: 3: assertion does not hold
6: assertion does not hold
-/
#guard_msgs in
#eval interpret (program [constrainedElements])

/-! A run stops at a negative length, at an index outside the array, at an array command on
an object that is not an array, at an element type that is not the array's, and at a written
value that is not of the element type. The default element of an array of references is no
object, so reading a field of it stops the run too. -/

meta def ints (cmds : List Cmd) : List Cmd :=
  [.init "a" (.named "Ints") none (at_ 1), .newArray "a" "Ints" (.int 3) (at_ 1),
   .init "x" bv32 none (at_ 2), .init "w" bv64 none (at_ 2), .init "n" .int none (at_ 2),
   .init "o" (.named "Box") none (at_ 2), .new "o" "Box" (at_ 2)] ++ cmds

/--
info: stopped: 'negativeLength': array length -1 is negative
stopped: 'readAtLength': index 3 is out of range for an array of length 3
stopped: 'readBelowZero': index -1 is out of range for an array of length 3
stopped: 'writeAtLength': index 3 is out of range for an array of length 3
stopped: 'writeBelowZero': index -2 is out of range for an array of length 3
stopped: 'lengthOfObject': not an array
stopped: 'readOfObject': not an array
stopped: 'writeOfObject': not an array
stopped: 'readAsLong': element type bv64 does not match array type Ints
stopped: 'writeAsLong': element type bv64 does not match array type Ints
stopped: 'writeIllTyped': ill-typed value
stopped: 'fieldOfDefaultElement': not a reference
-/
#guard_msgs in
#eval interpret (program [
  entry "negativeLength" (ints [.newArray "a" "Ints" (.op "Int.Sub" [.int 0, .int 1]) (at_ 3)]),
  entry "readAtLength" (ints [.readElem "x" (.var "a") (.int 3) bv32 (at_ 3)]),
  entry "readBelowZero" (ints [.readElem "x" (.var "a") (.int (-1)) bv32 (at_ 3)]),
  entry "writeAtLength" (ints [.writeElem (.var "a") (.int 3) (.bv 32 1) bv32 (at_ 3)]),
  entry "writeBelowZero" (ints [.writeElem (.var "a") (.int (-2)) (.bv 32 1) bv32 (at_ 3)]),
  entry "lengthOfObject" (ints [.arrayLength "n" (.var "o") (at_ 3)]),
  entry "readOfObject" (ints [.readElem "x" (.var "o") (.int 0) bv32 (at_ 3)]),
  entry "writeOfObject" (ints [.writeElem (.var "o") (.int 0) (.bv 32 1) bv32 (at_ 3)]),
  entry "readAsLong" (ints [.readElem "w" (.var "a") (.int 0) bv64 (at_ 3)]),
  entry "writeAsLong" (ints [.writeElem (.var "a") (.int 0) (.bv 64 1) bv64 (at_ 3)]),
  entry "writeIllTyped" (ints [.writeElem (.var "a") (.int 0) (.bool true) bv32 (at_ 3)]),
  entry "fieldOfDefaultElement" (ints [
    .init "b" (.named "Boxes") none (at_ 3), .newArray "b" "Boxes" (.int 1) (at_ 3),
    .readElem "o" (.var "b") (.int 0) (.named "Box") (at_ 4),
    .readField "x" (.var "o") "Box" "v" (at_ 5)])])

/-! The longest array the interpreter allocates has 65536 elements. An array of that length
is allocated whole: its length is the one given and its last element is the default. The
assertions at offsets 10 and 11 state the opposite of those before them and fail, so the ones
before them are checked. A greater length stops the run without allocating: one more than
the limit, and the greatest length a Java array can be given. -/

meta def atLengthLimit : Wire.Procedure :=
  entry "atLengthLimit" [
    .init "a" (.named "Ints") none (at_ 1), .newArray "a" "Ints" (.int 65536) (at_ 1),
    .init "n" .int none (at_ 2), .arrayLength "n" (.var "a") (at_ 2),
    .init "x" bv32 none (at_ 3), .readElem "x" (.var "a") (.int 65535) bv32 (at_ 3),
    isTrue "length" (.eq (.var "n") (.int 65536)) 4,
    isTrue "lastDefault" (.eq (.var "x") (.bv 32 0)) 5,
    isTrue "otherLength" (.eq (.var "n") (.int 65535)) 10,
    isTrue "lastNotDefault" (.op "Bool.Not" [.eq (.var "x") (.bv 32 0)]) 11]

/--
info: 10: assertion does not hold
11: assertion does not hold
stopped: 'oneOverLengthLimit': array length 65537 is over the interpreter's limit of 65536
stopped: 'greatestJavaLength': array length 2147483647 is over the interpreter's limit of 65536
-/
#guard_msgs in
#eval interpret (program [
  atLengthLimit,
  entry "oneOverLengthLimit" (ints [.newArray "a" "Ints" (.op "Int.Add" [.int 65536, .int 1]) (at_ 3)]),
  entry "greatestJavaLength" (ints [.newArray "a" "Ints" (.int 2147483647) (at_ 3)])])

/-! `new` names a composite and `newArray` an array type, and the two kinds of type share
one name space. -/

/--
info: error: invalid Cortex program: 'p': `new` of array type 'Ints'
-/
#guard_msgs in
#eval interpret (program [entry "p" [.init "a" (.named "Ints") none (at_ 1), .new "a" "Ints" (at_ 1)]])

/--
info: error: invalid Cortex program: 'p': `newArray` of 'Box', which is not an array type
-/
#guard_msgs in
#eval interpret (program [entry "p" [.init "a" (.named "Box") none (at_ 1), .newArray "a" "Box" (.int 1) (at_ 1)]])

/--
info: error: invalid Cortex program: duplicate composite 'Box'
-/
#guard_msgs in
#eval interpret { program [] with arrays := [{ name := "Box", elem := bv32, extending := [] }] }

/--
info: error: invalid Cortex program: composite 'Ints' extends unknown composite 'Missing'
-/
#guard_msgs in
#eval interpret { program [] with arrays := [{ name := "Ints", elem := bv32, extending := ["Missing"] }] }

/-! A call to a procedure without a body gives an output of array type a new array of
length 0, which is an instance of the array type and is not the array the caller holds. -/

meta def bodiless : Wire.Program :=
  program [
    { name := "lib", inputs := [], outputs := [{ name := "r", ty := .named "Ints" }], throws := none, requires := [],
      body := none, entry := false, source := at_ 0 },
    entry "bodiless" [
      .init "a" (.named "Ints") none (at_ 1), .newArray "a" "Ints" (.int 3) (at_ 1),
      .init "r" (.named "Ints") none (at_ 2), .call ["r"] "lib" [] (at_ 2),
      .init "n" .int none (at_ 3), .arrayLength "n" (.var "r") (at_ 3),
      .init "isInts" .bool none (at_ 4), .instanceOf "isInts" (.var "r") "Ints" (at_ 4),
      isTrue "empty" (.eq (.var "n") (.int 0)) 5,
      isTrue "instanceOfArrayType" (.var "isInts") 6,
      isTrue "newObject" (.op "Bool.Not" [.eq (.var "r") (.var "a")]) 7,
      isTrue "notEmpty" (.eq (.var "n") (.int 3)) 10,
      isTrue "sameObject" (.eq (.var "r") (.var "a")) 11]]

/--
info: 10: assertion does not hold
11: assertion does not hold
-/
#guard_msgs in
#eval interpret bodiless

/-! The translation to Core has no encoding of arrays and reports the array commands. -/

meta def toCore (p : Wire.Program) : IO Unit :=
  match Cortex.wireToCortex p >>= (Cortex.toCoreProgram ·) with
  | .error e => IO.println s!"error: {e}"
  | .ok _ => IO.println "translated to Core"

/--
info: error: LowerHeap: Cortex array commands are not lowered to Core
-/
#guard_msgs in
#eval toCore (program [defaults])

end Cortex.ArraysTest
