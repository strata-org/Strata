/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataCortex.Implementation.Pipeline
meta import StrataCortex.Implementation.Interpret
meta import StrataDDM.Util.Ion

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

/-- The `bv32` values from -128 to 127. -/
meta def byte : Constrained :=
  { name := "byte", base := bv32, binder := "$v",
    constraint := .op "Bool.And" [.op "Bv32.SLe" [.bv 32 (-128), .var "$v"], .op "Bv32.SLe" [.var "$v", .bv 32 127]],
    witness := some (.bv 32 0) }

/-- The `bv32` values 0 and 1. -/
meta def bit : Constrained :=
  { name := "bit", base := bv32, binder := "$v", constraint := .op "Bv32.ULe" [.var "$v", .bv 32 1],
    witness := some (.bv 32 0) }

meta def byteTy : Ty := .named "byte"
meta def bitTy : Ty := .named "bit"

/-- An entry procedure with one block. -/
meta def entry (name : String) (cmds : List Cmd) : Wire.Procedure :=
  { name, inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 0,
    body := some { entry := "b0", handlers := [], blocks := [blk "b0" cmds (.finish (at_ 0))] } }

meta def ints : Ty := .array bv32
meta def longs : Ty := .array bv64
meta def flags : Ty := .array .bool
meta def boxes : Ty := .array (.named "Box")
meta def checked : Ty := .array i32
meta def bytes : Ty := .array byteTy
meta def bits : Ty := .array bitTy

/-- A program over the classes `Object` and `Box`, in which every array type is a subtype of
`Object`. It declares no array type: `Array T` is there for every `T`. -/
meta def program (procedures : List Wire.Procedure) : Wire.Program :=
  { composites := [{ name := "Object", extending := [], fields := [] },
                   { name := "Box", extending := ["Object"], fields := [{ name := "v", ty := bv32 }] }],
    constrained := [int32, byte, bit],
    arrayParents := ["Object"],
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
    .init "a" ints none (at_ 1), .newArray "a" bv32 (.int 3) (at_ 1),
    .init "l" longs none (at_ 2), .newArray "l" bv64 (.op "Int.Add" [.int 1, .int 1]) (at_ 2),
    .init "f" flags none (at_ 3), .newArray "f" .bool (.int 1) (at_ 3),
    .init "b" boxes none (at_ 4), .newArray "b" (.named "Box") (.int 1) (at_ 4),
    .init "e" ints none (at_ 5), .newArray "e" bv32 (.int 0) (at_ 5),
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
instance of its own array type and of the array parents, and of no other array type. -/

meta def writes : Wire.Procedure :=
  entry "writes" [
    .init "a" ints none (at_ 1), .newArray "a" bv32 (.int 3) (at_ 1),
    .init "b" ints (some (.var "a")) (at_ 2),
    .init "c" ints none (at_ 3), .newArray "c" bv32 (.int 3) (at_ 3),
    .writeElem (.var "a") (.int 1) (.bv 32 7) bv32 (at_ 4),
    .writeElem (.var "b") (.int 2) (.bv 32 (-1)) bv32 (at_ 5),
    .init "x0" bv32 none (at_ 6), .readElem "x0" (.var "a") (.int 0) bv32 (at_ 6),
    .init "x1" bv32 none (at_ 7), .readElem "x1" (.var "b") (.int 1) bv32 (at_ 7),
    .init "x2" bv32 none (at_ 8), .readElem "x2" (.var "a") (.int 2) bv32 (at_ 8),
    .init "y1" bv32 none (at_ 9), .readElem "y1" (.var "c") (.int 1) bv32 (at_ 9),
    .init "isInts" .bool none (at_ 10), .instanceOf "isInts" (.var "a") ints (at_ 10),
    .init "isObject" .bool none (at_ 11), .instanceOf "isObject" (.var "a") (.named "Object") (at_ 11),
    .init "isLongs" .bool none (at_ 12), .instanceOf "isLongs" (.var "a") longs (at_ 12),
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
write at offset 2 stored. A constrained element type is not its base type, so the array is
no instance of `Array int`, at offset 7. -/

meta def constrainedElements : Wire.Procedure :=
  entry "constrainedElements" [
    .init "a" checked none (at_ 1), .newArray "a" i32 (.int 2) (at_ 1),
    .writeElem (.var "a") (.int 0) (.int 5) i32 (at_ 2),
    .writeElem (.var "a") (.int 1) (.int 2147483648) i32 (at_ 3),
    .init "x" i32 none (at_ 4), .readElem "x" (.var "a") (.int 0) i32 (at_ 4),
    .init "isBase" .bool none (at_ 4), .instanceOf "isBase" (.var "a") (.array .int) (at_ 4),
    isTrue "read" (.eq (.var "x") (.int 5)) 5,
    isTrue "notRead" (.eq (.var "x") (.int 0)) 6,
    isTrue "notArrayOfBase" (.op "Bool.Not" [.var "isBase"]) 7,
    isTrue "arrayOfBase" (.var "isBase") 8]

/--
info: 3: assertion does not hold
6: assertion does not hold
8: assertion does not hold
-/
#guard_msgs in
#eval interpret (program [constrainedElements])

/-! Two constrained types over one base type are different element types. An array of `byte`
is an instance of `Array byte` and of the array parents, and of neither `Array bit` nor
`Array bv32`, and the same holds one level down, for `Array (Array byte)`. The elements are
values of the base type: they start at its default, and a write is checked against the
constraint of the element type, which the one at offset 6 fails. The assertions from offset
30 on state the opposite of earlier ones and fail. -/

meta def elementTypesOverOneBase : Wire.Procedure :=
  entry "elementTypesOverOneBase" ([
    .init "a" bytes none (at_ 1), .newArray "a" byteTy (.int 2) (at_ 1),
    .init "f" bits none (at_ 2), .newArray "f" bitTy (.int 1) (at_ 2),
    .init "aa" (.array bytes) none (at_ 3), .newArray "aa" bytes (.int 1) (at_ 3),
    .init "d" bitTy none (at_ 4), .readElem "d" (.var "f") (.int 0) bitTy (at_ 4),
    .writeElem (.var "a") (.int 0) (.bv 32 100) byteTy (at_ 5),
    .writeElem (.var "a") (.int 1) (.bv 32 200) byteTy (at_ 6),
    .writeElem (.var "f") (.int 0) (.bv 32 1) bitTy (at_ 7),
    .init "x" byteTy none (at_ 8), .readElem "x" (.var "a") (.int 0) byteTy (at_ 8),
    .init "y" bv32 none (at_ 9), .readElem "y" (.var "f") (.int 0) bitTy (at_ 9)] ++
    [("isBytes", "a", bytes), ("isBits", "a", bits), ("isInts", "a", .array bv32),
     ("isObject", "a", .named "Object"), ("bitsAreBits", "f", bits), ("bitsAreBytes", "f", bytes),
     ("nested", "aa", .array bytes), ("nestedOther", "aa", .array bits)].flatMap (fun (x, obj, ty) =>
      [.init x .bool none (at_ 10), .instanceOf x (.var obj) ty (at_ 10)]) ++ [
    isTrue "default" (.eq (.var "d") (.bv 32 0)) 11,
    isTrue "read" (.eq (.var "x") (.bv 32 100)) 12,
    isTrue "readIntoBase" (.eq (.var "y") (.bv 32 1)) 13,
    isTrue "ownType" (.var "isBytes") 14,
    isTrue "notOtherConstrained" (.op "Bool.Not" [.var "isBits"]) 15,
    isTrue "notBase" (.op "Bool.Not" [.var "isInts"]) 16,
    isTrue "arrayParent" (.var "isObject") 17,
    isTrue "otherOwnType" (.op "Bool.And" [.var "bitsAreBits", .op "Bool.Not" [.var "bitsAreBytes"]]) 18,
    isTrue "nestedOwnType" (.op "Bool.And" [.var "nested", .op "Bool.Not" [.var "nestedOther"]]) 19,
    isTrue "notDefault" (.eq (.var "d") (.bv 32 1)) 30,
    isTrue "notRead" (.eq (.var "x") (.bv 32 0)) 31,
    isTrue "otherConstrained" (.var "isBits") 32,
    isTrue "base" (.var "isInts") 33,
    isTrue "otherIsBytes" (.var "bitsAreBytes") 34,
    isTrue "nestedIsOther" (.var "nestedOther") 35])

/--
info: 6: assertion does not hold
30: assertion does not hold
31: assertion does not hold
32: assertion does not hold
33: assertion does not hold
34: assertion does not hold
35: assertion does not hold
-/
#guard_msgs in
#eval interpret (program [elementTypesOverOneBase])

/-! An array command names the element type of the array it works on: a run stops at a read or
a write of an array of `byte` at another constrained type over the same base type or at the
base type. -/

meta def withBytes (cmds : List Cmd) : List Cmd :=
  [.init "a" bytes none (at_ 1), .newArray "a" byteTy (.int 1) (at_ 1),
   .init "x" bv32 none (at_ 2)] ++ cmds

/--
info: 3: the interpreter fails here: an expression did not evaluate
stopped: 'readAtOtherConstrained': an expression did not evaluate
stopped: 'readAtBase': an expression did not evaluate
stopped: 'writeAtOtherConstrained': an expression did not evaluate
stopped: 'writeAtBase': an expression did not evaluate
-/
#guard_msgs in
#eval interpret (program [
  entry "readAtOtherConstrained" (withBytes [.readElem "x" (.var "a") (.int 0) bitTy (at_ 3)]),
  entry "readAtBase" (withBytes [.readElem "x" (.var "a") (.int 0) bv32 (at_ 3)]),
  entry "writeAtOtherConstrained" (withBytes [.writeElem (.var "a") (.int 0) (.bv 32 1) bitTy (at_ 3)]),
  entry "writeAtBase" (withBytes [.writeElem (.var "a") (.int 0) (.bv 32 1) bv32 (at_ 3)])])

/--
info: stopped: 'writeIllTyped': type error: procedure writeIllTyped: expression 1 has type int, expected bv32: Impossible to unify int with bv32.
-/
#guard_msgs in
#eval interpret (program [
  entry "writeIllTyped" (withBytes [.writeElem (.var "a") (.int 0) (.int 1) byteTy (at_ 3)])])

/-! Lowering the constrained types keeps the element type of an array type and replaces every
other constrained type by its base type: `a` stays an `Array byte` while `x`, declared a
`byte`, becomes a `bv32`. The constrained types that an array type names stay declared, here
`byte` and `bit` and not `int32`, and a program without arrays is left with none. -/

meta def lowered (p : Wire.Program) : IO Unit :=
  match Cortex.wireToCortex p >>= Cortex.LowerCTE.runWith true with
  | .error e => IO.println s!"error: {e}"
  | .ok q => do
    IO.println s!"constrained: {q.constrained.map (·.name)}"
    let inits := q.procedures.flatMap fun pr => (pr.body.map fun b => b.cfg.blocks.flatMap fun (_, blk) =>
      blk.cmds.filterMap fun
        | .cmd (.init x (.forAll _ t) _ _) => some s!"{x.name}: {Cortex.mangle t}"
        | _ => none).getD []
    IO.println (", ".intercalate inits)

/--
info: constrained: [byte, bit]
a: Array$byte, f: Array$bit, x: bv32
-/
#guard_msgs in
#eval lowered (program [entry "arrays" [
  .init "a" bytes none (at_ 1), .newArray "a" byteTy (.int 1) (at_ 1),
  .init "f" bits none (at_ 2),
  .init "x" byteTy (some (.bv 32 1)) (at_ 3)]])

/--
info: constrained: []
x: bv32, n: int
-/
#guard_msgs in
#eval lowered (program [entry "noArrays" [
  .init "x" byteTy (some (.bv 32 1)) (at_ 1),
  .init "n" i32 (some (.int 1)) (at_ 2)]])

/-! A run stops at a negative length, at an index outside the array, at an array command on
an object that is not an array, at an element type that the array's type is not an array of,
and at an element type that has no default value. The default element of an array of references is no object, so reading a
field of it stops the run too. Each is also reported at the command that raised it, once for
each message and place. -/

meta def withInts (cmds : List Cmd) : List Cmd :=
  [.init "a" ints none (at_ 1), .newArray "a" bv32 (.int 3) (at_ 1),
   .init "x" bv32 none (at_ 2), .init "w" bv64 none (at_ 2), .init "n" .int none (at_ 2),
   .init "o" (.named "Box") none (at_ 2), .new "o" "Box" (at_ 2)] ++ cmds

/--
info: 3: the interpreter fails here: an expression did not evaluate
5: the interpreter fails here: an expression did not evaluate
stopped: 'negativeLength': an expression did not evaluate
stopped: 'readAtLength': an expression did not evaluate
stopped: 'readBelowZero': an expression did not evaluate
stopped: 'writeAtLength': an expression did not evaluate
stopped: 'writeBelowZero': an expression did not evaluate
stopped: 'lengthOfObject': an expression did not evaluate
stopped: 'readOfObject': an expression did not evaluate
stopped: 'writeOfObject': an expression did not evaluate
stopped: 'readAsLong': an expression did not evaluate
stopped: 'writeAsLong': an expression did not evaluate
stopped: 'undeclaredElementType': an expression did not evaluate
stopped: 'fieldOfDefaultElement': an expression did not evaluate
-/
#guard_msgs in
#eval interpret (program [
  entry "negativeLength" (withInts [.newArray "a" bv32 (.op "Int.Sub" [.int 0, .int 1]) (at_ 3)]),
  entry "readAtLength" (withInts [.readElem "x" (.var "a") (.int 3) bv32 (at_ 3)]),
  entry "readBelowZero" (withInts [.readElem "x" (.var "a") (.int (-1)) bv32 (at_ 3)]),
  entry "writeAtLength" (withInts [.writeElem (.var "a") (.int 3) (.bv 32 1) bv32 (at_ 3)]),
  entry "writeBelowZero" (withInts [.writeElem (.var "a") (.int (-2)) (.bv 32 1) bv32 (at_ 3)]),
  entry "lengthOfObject" (withInts [.arrayLength "n" (.var "o") (at_ 3)]),
  entry "readOfObject" (withInts [.readElem "x" (.var "o") (.int 0) bv32 (at_ 3)]),
  entry "writeOfObject" (withInts [.writeElem (.var "o") (.int 0) (.bv 32 1) bv32 (at_ 3)]),
  entry "readAsLong" (withInts [.readElem "w" (.var "a") (.int 0) bv64 (at_ 3)]),
  entry "writeAsLong" (withInts [.writeElem (.var "a") (.int 0) (.bv 64 1) bv64 (at_ 3)]),
  entry "undeclaredElementType" (withInts [
    .init "u" (.array (.named "Missing")) none (at_ 3), .newArray "u" (.named "Missing") (.int 1) (at_ 3)]),
  entry "fieldOfDefaultElement" (withInts [
    .init "b" boxes none (at_ 3), .newArray "b" (.named "Box") (.int 1) (at_ 3),
    .readElem "o" (.var "b") (.int 0) (.named "Box") (at_ 4),
    .readField "x" (.var "o") "Box" "v" (at_ 5)])])

/--
info: stopped: 'writeIllTyped': type error: procedure writeIllTyped: expression true has type bool, expected bv32: Impossible to unify bool with bv32.
-/
#guard_msgs in
#eval interpret (program [
  entry "writeIllTyped" (withInts [.writeElem (.var "a") (.int 0) (.bool true) bv32 (at_ 3)])])

/-! An array of 65536 elements is allocated whole: its length is the one given and its last
element is the default. The assertions at offsets 10 and 11 state the opposite of those before
them and fail, so the ones before them are checked. There is no length limit: one more than
65536, and the greatest length a Java array can be given, are allocated too, and those runs
end without a verdict. -/

meta def atLengthLimit : Wire.Procedure :=
  entry "atLengthLimit" [
    .init "a" ints none (at_ 1), .newArray "a" bv32 (.int 65536) (at_ 1),
    .init "n" .int none (at_ 2), .arrayLength "n" (.var "a") (at_ 2),
    .init "x" bv32 none (at_ 3), .readElem "x" (.var "a") (.int 65535) bv32 (at_ 3),
    isTrue "length" (.eq (.var "n") (.int 65536)) 4,
    isTrue "lastDefault" (.eq (.var "x") (.bv 32 0)) 5,
    isTrue "otherLength" (.eq (.var "n") (.int 65535)) 10,
    isTrue "lastNotDefault" (.op "Bool.Not" [.eq (.var "x") (.bv 32 0)]) 11]

/--
info: 10: assertion does not hold
11: assertion does not hold
-/
#guard_msgs in
#eval interpret (program [
  atLengthLimit,
  entry "oneOverLengthLimit" (withInts [.newArray "a" bv32 (.op "Int.Add" [.int 65536, .int 1]) (at_ 3)]),
  entry "greatestJavaLength" (withInts [.newArray "a" bv32 (.int 2147483647) (at_ 3)])])

/-! The array types take no name from the program: a composite may be called `Array`. Its
objects are not arrays, and no array is an instance of it. -/

meta def compositeNamedArray : Wire.Program :=
  { program [entry "compositeNamedArray" [
      .init "c" (.named "Array") none (at_ 1), .new "c" "Array" (at_ 1),
      .init "a" ints none (at_ 2), .newArray "a" bv32 (.int 1) (at_ 2),
      .init "cIsClass" .bool none (at_ 3), .instanceOf "cIsClass" (.var "c") (.named "Array") (at_ 3),
      .init "cIsInts" .bool none (at_ 4), .instanceOf "cIsInts" (.var "c") ints (at_ 4),
      .init "aIsClass" .bool none (at_ 5), .instanceOf "aIsClass" (.var "a") (.named "Array") (at_ 5),
      isTrue "objectOfClass" (.var "cIsClass") 6,
      isTrue "objectNotArray" (.op "Bool.Not" [.var "cIsInts"]) 7,
      isTrue "arrayNotOfClass" (.op "Bool.Not" [.var "aIsClass"]) 8,
      isTrue "objectIsArray" (.var "cIsInts") 10,
      isTrue "arrayOfClass" (.var "aIsClass") 11,
      .init "n" .int none (at_ 12), .arrayLength "n" (.var "c") (at_ 12)]] with
    composites := [{ name := "Object", extending := [], fields := [] },
                   { name := "Array", extending := ["Object"], fields := [] }] }

/--
info: 12: the interpreter fails here: an expression did not evaluate
stopped: 'compositeNamedArray': an expression did not evaluate
-/
#guard_msgs in
#eval interpret compositeNamedArray

/--
info: 10: assertion does not hold
11: assertion does not hold
-/
#guard_msgs in
#eval interpret { compositeNamedArray with
  procedures := compositeNamedArray.procedures.map fun p =>
    { p with body := p.body.map fun b =>
        { b with blocks := b.blocks.map fun blk => { blk with cmds := blk.cmds.dropLast.dropLast } } } }

/-! A call to a procedure without a body gives an output of array type a new array of
length 0, which is an instance of the array type and is not the array the caller holds. -/

meta def bodiless : Wire.Program :=
  program [
    { name := "lib", inputs := [], outputs := [{ name := "r", ty := ints }], throws := none, requires := [],
      body := none, entry := false, source := at_ 0 },
    entry "bodiless" [
      .init "a" ints none (at_ 1), .newArray "a" bv32 (.int 3) (at_ 1),
      .init "r" ints none (at_ 2), .call ["r"] "lib" [] (at_ 2),
      .init "n" .int none (at_ 3), .arrayLength "n" (.var "r") (at_ 3),
      .init "isInts" .bool none (at_ 4), .instanceOf "isInts" (.var "r") ints (at_ 4),
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

/-! ## Array parents

Every array type is a subtype of each array parent and of what the parent extends, so an
array is an instance of them, has their fields and is held by a variable of their type. It
is an instance of no other composite. -/

meta def parentsProgram (arrayParents : List String) (procedures : List Wire.Procedure) : Wire.Program :=
  { composites := [{ name := "Base", extending := [], fields := [{ name := "tag", ty := bv32 }] },
                   { name := "Parent", extending := ["Base"], fields := [] },
                   { name := "Other", extending := ["Base"], fields := [] }],
    constrained := [], arrayParents, procedures }

meta def parentTests : List Cmd := [
    .init "a" (.array ints) none (at_ 1), .newArray "a" ints (.int 2) (at_ 1),
    .init "isParent" .bool none (at_ 2), .instanceOf "isParent" (.var "a") (.named "Parent") (at_ 2),
    .init "isBase" .bool none (at_ 3), .instanceOf "isBase" (.var "a") (.named "Base") (at_ 3),
    .init "isOther" .bool none (at_ 4), .instanceOf "isOther" (.var "a") (.named "Other") (at_ 4),
    isTrue "parent" (.var "isParent") 5,
    isTrue "parentOfParent" (.var "isBase") 6,
    isTrue "notOther" (.op "Bool.Not" [.var "isOther"]) 7,
    .init "held" (.named "Base") (some (.var "a")) (at_ 8),
    .init "n" .int none (at_ 9), .arrayLength "n" (.var "held") (at_ 9),
    isTrue "length" (.eq (.var "n") (.int 2)) 10,
    isTrue "otherLength" (.eq (.var "n") (.int 0)) 11]

meta def parentField : List Cmd := [
    .writeField (.var "a") "Base" "tag" (.bv 32 7) (at_ 12),
    .init "t" bv32 none (at_ 13), .readField "t" (.var "held") "Base" "tag" (at_ 13),
    isTrue "field" (.eq (.var "t") (.bv 32 7)) 14,
    isTrue "fieldLost" (.eq (.var "t") (.bv 32 0)) 15]

/--
info: 11: assertion does not hold
15: assertion does not hold
-/
#guard_msgs in
#eval interpret (parentsProgram ["Parent"] [entry "parents" (parentTests ++ parentField)])

/-! Without an array parent, an array is an instance of no composite, and a run stops at a
field of it. -/

/--
info: 5: assertion does not hold
6: assertion does not hold
11: assertion does not hold
12: the interpreter fails here: an expression did not evaluate
stopped: 'parentField': an expression did not evaluate
-/
#guard_msgs in
#eval interpret (parentsProgram [] [entry "parents" parentTests, entry "parentField" (parentTests ++ parentField)])

/-! An array parent is a composite of the program. -/

/--
info: error: invalid Cortex program: array parent 'Missing' is not a composite
-/
#guard_msgs in
#eval interpret (parentsProgram ["Parent", "Missing"] [])

/--
info: error: invalid Cortex program: array parent 'int32' is not a composite
-/
#guard_msgs in
#eval interpret { program [] with arrayParents := ["int32"] }

/-! ## Subtyping between array types -/

meta def objRef : Ty := .named "java.lang.Object"
meta def arrObj : Ty := .array objRef
meta def arrA : Ty := .array (.named "A")
meta def arrB : Ty := .array (.named "B")

/-- An entry procedure with the body `blocks`, entered at `b0`, under `handlers`. -/
meta def entryBlocks (name : String) (blocks : List Block) (handlers : List Wire.Handler := []) : Wire.Procedure :=
  { name, inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 0,
    body := some { entry := "b0", handlers, blocks } }

/-- A program over the classes `A` and `B`, which extends `A`, in which every array type is a
subtype of `java.lang.Object`. -/
meta def refProgram (procedures : List Wire.Procedure) (covariantArrays : Bool := true) : Wire.Program :=
  { composites := [{ name := "java.lang.Object", extending := [], fields := [] },
                   { name := "A", extending := ["java.lang.Object"], fields := [] },
                   { name := "B", extending := ["A"], fields := [] },
                   { name := "java.lang.ClassCastException", extending := ["java.lang.Object"], fields := [] },
                   { name := "java.lang.ArrayStoreException", extending := ["java.lang.Object"], fields := [] }],
    constrained := [int32],
    covariantArrays,
    arrayParents := ["java.lang.Object"],
    procedures }

/-- `var x: bool; x := obj instanceof ty`, at offset `n`. -/
meta def isInstance (x obj : String) (ty : Ty) (n : Nat) : List Cmd :=
  [.init x .bool none (at_ n), .instanceOf x (.var obj) ty (at_ n)]

/-- An assertion at offset `n` that `obj` is an instance of `ty`. -/
meta def expectInstance (obj : String) (ty : Ty) (n : Nat) : List Cmd :=
  isInstance s!"is{n}" obj ty n ++ [isTrue s!"is{n}" (.var s!"is{n}") n]

/-- Asserts, at the offset given with each, that an array is an instance of a type. The
arrays are `b` of type `Array B`, `a` of type `Array A`, `bb` of type `Array (Array B)`, `i`
of type `Array bv32` and `ii` of type `Array (Array bv32)`; `o` is an object of class `A`. -/
meta def subtyping : Wire.Procedure :=
  entry "subtyping" ([
    .init "b" arrB none (at_ 0), .newArray "b" (.named "B") (.int 1) (at_ 0),
    .init "a" arrA none (at_ 0), .newArray "a" (.named "A") (.int 1) (at_ 0),
    .init "bb" (.array arrB) none (at_ 0), .newArray "bb" arrB (.int 1) (at_ 0),
    .init "i" ints none (at_ 0), .newArray "i" bv32 (.int 1) (at_ 0),
    .init "ii" (.array ints) none (at_ 0), .newArray "ii" ints (.int 1) (at_ 0),
    .init "o" (.named "A") none (at_ 0), .new "o" "A" (at_ 0)] ++
    expectInstance "b" arrB 1 ++
    expectInstance "b" arrA 2 ++
    expectInstance "b" arrObj 3 ++
    expectInstance "b" objRef 4 ++
    expectInstance "a" arrB 5 ++
    expectInstance "a" arrObj 6 ++
    expectInstance "b" ints 7 ++
    expectInstance "b" (.array arrA) 8 ++
    expectInstance "bb" (.array arrA) 9 ++
    expectInstance "bb" (.array arrObj) 10 ++
    expectInstance "bb" arrObj 11 ++
    expectInstance "bb" objRef 12 ++
    expectInstance "bb" arrB 13 ++
    expectInstance "i" ints 14 ++
    expectInstance "i" objRef 15 ++
    expectInstance "i" arrObj 16 ++
    expectInstance "i" longs 17 ++
    expectInstance "ii" (.array ints) 18 ++
    expectInstance "ii" arrObj 19 ++
    expectInstance "ii" (.array longs) 20 ++
    expectInstance "o" arrA 21 ++
    expectInstance "b" (.named "A") 22)

/-! With covariant arrays, `Array S` is a subtype of `Array T` when `S` is a reference type
and a subtype of `T`, at any depth: an `Array B` is an `Array A` and an `Array
java.lang.Object`, and an `Array (Array B)` is an `Array (Array A)`. An array type is a
reference type, so an `Array (Array bv32)` is an `Array java.lang.Object`. An element type
that is not a reference type has no subtype but itself: an `Array bv32` is no
`Array java.lang.Object` and no `Array bv64`. The offsets listed are the tests that are
false. -/

/--
info: 5: assertion does not hold
7: assertion does not hold
8: assertion does not hold
13: assertion does not hold
16: assertion does not hold
17: assertion does not hold
20: assertion does not hold
21: assertion does not hold
22: assertion does not hold
-/
#guard_msgs in
#eval interpret (refProgram [subtyping])

/-! Without covariant arrays, an array is an instance of its own array type and of the array
parents only: the tests at offsets 2, 3, 6, 9, 10, 11 and 19 are false as well. -/

/--
info: 2: assertion does not hold
3: assertion does not hold
5: assertion does not hold
6: assertion does not hold
7: assertion does not hold
8: assertion does not hold
9: assertion does not hold
10: assertion does not hold
11: assertion does not hold
13: assertion does not hold
16: assertion does not hold
17: assertion does not hold
19: assertion does not hold
20: assertion does not hold
21: assertion does not hold
22: assertion does not hold
-/
#guard_msgs in
#eval interpret (refProgram [subtyping] (covariantArrays := false))

/-- An entry procedure that holds a new array of elements of type `elem` in a variable of type
`held` and casts it to `target`, as a frontend translates a checked cast: by an `instanceOf`,
and a `ClassCastException` thrown at offset `n + 1` when it is false. After the cast the
array is used at type `target`: the assertion at `n + 3` holds and the one at `n + 4` fails. -/
meta def castArray (name : String) (elem held target : Ty) (n : Nat) : Wire.Procedure :=
  entryBlocks name [
    blk "b0" ([.init "a" held none (at_ n), .newArray "a" elem (.int 1) (at_ n),
               .init "e" (.named "java.lang.ClassCastException") none (at_ n),
               .init "b" target none (at_ n), .init "len" .int none (at_ n)] ++
              isInstance "ok" "a" target n)
      (.condGoto (.var "ok") "cast" "fail" (at_ n)),
    blk "fail" [.new "e" "java.lang.ClassCastException" (at_ (n + 1)), .throw (.var "e") none (at_ (n + 1))]
      (.finish (at_ (n + 1))),
    blk "cast" [.set "b" (some (.var "a")) (at_ (n + 2)), .arrayLength "len" (.var "b") (at_ (n + 2)),
                isTrue "length" (.eq (.var "len") (.int 1)) (n + 3),
                isTrue "otherLength" (.eq (.var "len") (.int 0)) (n + 4)]
      (.finish (at_ (n + 2)))]

/-! A cast from `Array A` to `Array B` succeeds on an `Array B` and throws on an `Array A`.
A cast from `java.lang.Object` to `Array bv32` succeeds on an `Array bv32` and throws on an
`Array bv64`. -/

/--
info: 14: assertion does not hold
21: uncaught exception is not thrown does not hold
34: assertion does not hold
41: uncaught exception is not thrown does not hold
-/
#guard_msgs in
#eval interpret (refProgram [
  castArray "downcastOfArrayB" (.named "B") arrA arrB 10,
  castArray "downcastOfArrayA" (.named "A") arrA arrB 20,
  castArray "objectToInts" bv32 objRef ints 30,
  castArray "objectToIntsOfLongs" bv64 objRef ints 40])

/-! A handler catches a thrown array when the array type is a subtype of the type it catches.
The handler for `A` does not catch an `Array A`, and the one for `java.lang.Object` after it
does: the block at offset 10 is reached with the array, and the one at offset 20 is not.
Without a handler for one of its supertypes, the array leaves the procedure. -/

meta def throwArray (name : String) (catchTypes : List (String × String)) : Wire.Procedure :=
  entryBlocks name
    [blk "b0" [.init "e" objRef none (at_ 1), .init "n" .int none (at_ 1),
               .init "a" arrA none (at_ 2), .newArray "a" (.named "A") (.int 2) (at_ 2),
               .throw (.var "a") none (at_ 3)] (.finish (at_ 3)),
     blk "caught" [.arrayLength "n" (.var "e") (at_ 10),
                   isTrue "thrownArray" (.eq (.var "n") (.int 2)) 11,
                   isTrue "otherArray" (.eq (.var "n") (.int 0)) 12] (.finish (at_ 10)),
     blk "wrong" [isTrue "notReached" (.bool false) 20] (.finish (at_ 20))]
    (catchTypes.map fun (ty, target) =>
      { covered := ["b0"], catchType := some ty, binder := "e", target, source := at_ 4 })

/--
info: 12: assertion does not hold
3: uncaught exception is not thrown does not hold
-/
#guard_msgs in
#eval interpret (refProgram [
  throwArray "caughtByParent" [("A", "wrong"), ("java.lang.Object", "caught")],
  throwArray "notCaught" [("A", "wrong"), ("java.lang.ClassCastException", "wrong")]])

/-! ## Elements of arrays of references

An element command names the element type it reads or writes the array at. With covariant
arrays, an `Array B` held in a variable of type `Array A` is read and written at element
type `A`, and at its own element type `B` through a variable of type `Array B`. -/

meta def throughParentVariable : Wire.Procedure :=
  entry "throughParentVariable" [
    .init "b" arrB none (at_ 1), .newArray "b" (.named "B") (.int 2) (at_ 1),
    .init "a" arrA (some (.var "b")) (at_ 2),
    .init "o" (.named "B") none (at_ 3), .new "o" "B" (at_ 3),
    .writeElem (.var "a") (.int 1) (.var "o") (.named "A") (at_ 4),
    .init "x" (.named "B") none (at_ 5), .readElem "x" (.var "b") (.int 1) (.named "B") (at_ 5),
    .init "y" (.named "A") none (at_ 6), .readElem "y" (.var "a") (.int 1) (.named "A") (at_ 6),
    .init "z" (.named "A") none (at_ 7), .readElem "z" (.var "a") (.int 0) (.named "A") (at_ 7),
    .init "n" .int none (at_ 8), .arrayLength "n" (.var "a") (at_ 8),
    isTrue "writtenThroughParent" (.eq (.var "x") (.var "o")) 10,
    isTrue "readThroughParent" (.eq (.var "y") (.var "o")) 11,
    isTrue "untouched" (.op "Bool.Not" [.eq (.var "z") (.var "o")]) 12,
    isTrue "length" (.eq (.var "n") (.int 2)) 13,
    isTrue "writeLost" (.op "Bool.Not" [.eq (.var "x") (.var "o")]) 20,
    isTrue "readLost" (.op "Bool.Not" [.eq (.var "y") (.var "o")]) 21,
    isTrue "otherLength" (.eq (.var "n") (.int 1)) 22]

/--
info: 20: assertion does not hold
21: assertion does not hold
22: assertion does not hold
-/
#guard_msgs in
#eval interpret (refProgram [throughParentVariable])

/-! Without covariant arrays, an `Array B` is no `Array A`, and the write at element type `A`
stops the run. With or without them, an `Array A` is not read at the element type `B` of a
subtype. -/

/--
info: 4: the interpreter fails here: an expression did not evaluate
2: the interpreter fails here: an expression did not evaluate
stopped: 'throughParentVariable': an expression did not evaluate
stopped: 'readAsChildElement': an expression did not evaluate
-/
#guard_msgs in
#eval interpret (refProgram (covariantArrays := false) [
  throughParentVariable,
  entry "readAsChildElement" [
    .init "a" arrA none (at_ 1), .newArray "a" (.named "A") (.int 1) (at_ 1),
    .init "x" (.named "B") none (at_ 2), .readElem "x" (.var "a") (.int 0) (.named "B") (at_ 2)]])

/--
info: 2: the interpreter fails here: an expression did not evaluate
stopped: 'readAsChildElement': an expression did not evaluate
-/
#guard_msgs in
#eval interpret (refProgram [
  entry "readAsChildElement" [
    .init "a" arrA none (at_ 1), .newArray "a" (.named "A") (.int 1) (at_ 1),
    .init "x" (.named "B") none (at_ 2), .readElem "x" (.var "a") (.int 0) (.named "B") (at_ 2)]])

/-! ## The store check

`instanceOfComponent` tests an object against the element type of an array, which is what
decides whether the object may be stored in it. -/

/-- `var x: bool; x := obj instanceof element type of arr`, at offset `n`. -/
meta def storable (x obj arr : String) (n : Nat) : List Cmd :=
  [.init x .bool none (at_ n), .instanceOfComponent x (.var obj) (.var arr) (at_ n)]

/-- New arrays `arrObj`, `arrA` and `arrB` of the types `Array java.lang.Object`, `Array A`
and `Array B`, and new objects `o`, `a` and `b` of the classes `java.lang.Object`, `A` and
`B`, before `cmds`. -/
meta def refs (cmds : List Cmd) : List Cmd :=
  [.init "arrObj" arrObj none (at_ 1), .newArray "arrObj" objRef (.int 1) (at_ 1),
   .init "arrA" arrA none (at_ 1), .newArray "arrA" (.named "A") (.int 1) (at_ 1),
   .init "arrB" arrB none (at_ 1), .newArray "arrB" (.named "B") (.int 1) (at_ 1),
   .init "o" objRef none (at_ 2), .new "o" "java.lang.Object" (at_ 2),
   .init "a" (.named "A") none (at_ 2), .new "a" "A" (at_ 2),
   .init "b" (.named "B") none (at_ 2), .new "b" "B" (at_ 2)] ++ cmds

/-! An object is an instance of the element type when its class is the element type or
extends it: an `A` and a `B` may be stored in an `Array A`, a `B` in an `Array B`, and any
object, an array included, in an `Array java.lang.Object`. An `A` may not be stored in an
`Array B`, nor a `java.lang.Object` in an `Array A`. The element type is that of the array
object, not of the variable: `held` has type `Array A` and holds an `Array B`, which takes a
`B` and no `A`. -/

meta def storeChecks : Wire.Procedure :=
  entry "storeChecks" (refs (
    [.init "held" arrA (some (.var "arrB")) (at_ 3)] ++
    storable "bIntoArrA" "b" "arrA" 4 ++ storable "aIntoArrA" "a" "arrA" 5 ++
    storable "oIntoArrA" "o" "arrA" 6 ++ storable "aIntoArrB" "a" "arrB" 7 ++
    storable "bIntoArrB" "b" "arrB" 8 ++ storable "oIntoArrObj" "o" "arrObj" 9 ++
    storable "bIntoArrObj" "b" "arrObj" 10 ++ storable "arrBIntoArrObj" "arrB" "arrObj" 11 ++
    storable "aIntoHeld" "a" "held" 12 ++ storable "bIntoHeld" "b" "held" 13 ++
    storable "arrAIntoArrA" "arrA" "arrA" 14 ++ [
    isTrue "childIntoParentArray" (.var "bIntoArrA") 20,
    isTrue "ownClass" (.var "aIntoArrA") 21,
    isTrue "notParentIntoArray" (.op "Bool.Not" [.var "oIntoArrA"]) 22,
    isTrue "notParentIntoChildArray" (.op "Bool.Not" [.var "aIntoArrB"]) 23,
    isTrue "childIntoChildArray" (.var "bIntoArrB") 24,
    isTrue "objectIntoObjectArray" (.var "oIntoArrObj") 25,
    isTrue "anyIntoObjectArray" (.var "bIntoArrObj") 26,
    isTrue "arrayIntoObjectArray" (.var "arrBIntoArrObj") 27,
    isTrue "notParentIntoHeldChildArray" (.op "Bool.Not" [.var "aIntoHeld"]) 28,
    isTrue "childIntoHeldChildArray" (.var "bIntoHeld") 29,
    isTrue "notArrayIntoItself" (.op "Bool.Not" [.var "arrAIntoArrA"]) 30,
    isTrue "parentIntoChildArray" (.var "aIntoArrB") 40,
    isTrue "parentIntoHeldChildArray" (.var "aIntoHeld") 41,
    isTrue "notChildIntoParentArray" (.op "Bool.Not" [.var "bIntoArrA"]) 42,
    isTrue "notAnyIntoObjectArray" (.op "Bool.Not" [.var "bIntoArrObj"]) 43,
    isTrue "notChildIntoHeldChildArray" (.op "Bool.Not" [.var "bIntoHeld"]) 44]))

/--
info: 40: assertion does not hold
41: assertion does not hold
42: assertion does not hold
43: assertion does not hold
44: assertion does not hold
-/
#guard_msgs in
#eval interpret (refProgram [storeChecks])

/-! The element type of an array of arrays is an array type. With covariant arrays, an
`Array (Array A)` takes an `Array A` and an `Array B`, and no object that is not such an
array. An `Array (Array B)` held in a variable of type `Array (Array A)` takes an `Array B`
and no `Array A`. -/

meta def arrayElements : Wire.Procedure :=
  entry "arrayElements" (refs (
    [.init "aa" (.array arrA) none (at_ 3), .newArray "aa" arrA (.int 1) (at_ 3),
     .init "ab" (.array arrB) none (at_ 3), .newArray "ab" arrB (.int 1) (at_ 3),
     .init "held" (.array arrA) (some (.var "ab")) (at_ 3)] ++
    storable "arrAIntoAA" "arrA" "aa" 4 ++ storable "arrBIntoAA" "arrB" "aa" 5 ++
    storable "aIntoAA" "a" "aa" 6 ++ storable "arrObjIntoAA" "arrObj" "aa" 7 ++
    storable "aaIntoAA" "aa" "aa" 8 ++ storable "arrAIntoHeld" "arrA" "held" 9 ++
    storable "arrBIntoHeld" "arrB" "held" 10 ++ storable "abIntoArrObj" "ab" "arrObj" 11 ++ [
    isTrue "arrayIntoArrayOfArrays" (.var "arrAIntoAA") 20,
    isTrue "childArrayIntoArrayOfArrays" (.var "arrBIntoAA") 21,
    isTrue "notElementIntoArrayOfArrays" (.op "Bool.Not" [.var "aIntoAA"]) 22,
    isTrue "notParentArrayIntoArrayOfArrays" (.op "Bool.Not" [.var "arrObjIntoAA"]) 23,
    isTrue "notArrayOfArraysIntoItself" (.op "Bool.Not" [.var "aaIntoAA"]) 24,
    isTrue "notParentArrayIntoHeld" (.op "Bool.Not" [.var "arrAIntoHeld"]) 25,
    isTrue "childArrayIntoHeld" (.var "arrBIntoHeld") 26,
    isTrue "arrayOfArraysIntoObjectArray" (.var "abIntoArrObj") 27,
    isTrue "elementIntoArrayOfArrays" (.var "aIntoAA") 40,
    isTrue "parentArrayIntoHeld" (.var "arrAIntoHeld") 41,
    isTrue "notArrayIntoArrayOfArrays" (.op "Bool.Not" [.var "arrAIntoAA"]) 42,
    isTrue "notChildArrayIntoHeld" (.op "Bool.Not" [.var "arrBIntoHeld"]) 43]))

/--
info: 40: assertion does not hold
41: assertion does not hold
42: assertion does not hold
43: assertion does not hold
-/
#guard_msgs in
#eval interpret (refProgram [arrayElements])

/-! Without covariant arrays, an `Array (Array A)` takes no `Array B`: the assertion at
offset 21 fails as well. -/

/--
info: 21: assertion does not hold
40: assertion does not hold
41: assertion does not hold
42: assertion does not hold
43: assertion does not hold
-/
#guard_msgs in
#eval interpret (refProgram [arrayElements] (covariantArrays := false))

/-- An entry procedure that stores a new `A` in a new array of elements of type `elem`, held
in a variable of type `Array java.lang.Object`, as a frontend translates a checked store: by
an `instanceOfComponent`, and an `ArrayStoreException` thrown at offset `n + 1` when it is
false. After the store, the assertion at `n + 3` holds and the one at `n + 4` fails. -/
meta def storeA (name : String) (elem : Ty) (n : Nat) : Wire.Procedure :=
  entryBlocks name [
    blk "b0" ([.init "arr" arrObj none (at_ n), .newArray "arr" elem (.int 1) (at_ n),
               .init "a" (.named "A") none (at_ n), .new "a" "A" (at_ n),
               .init "e" (.named "java.lang.ArrayStoreException") none (at_ n),
               .init "x" objRef none (at_ n)] ++ storable "ok" "a" "arr" n)
      (.condGoto (.var "ok") "store" "fail" (at_ n)),
    blk "fail" [.new "e" "java.lang.ArrayStoreException" (at_ (n + 1)), .throw (.var "e") none (at_ (n + 1))]
      (.finish (at_ (n + 1))),
    blk "store" [.writeElem (.var "arr") (.int 0) (.var "a") objRef (at_ (n + 2)),
                 .readElem "x" (.var "arr") (.int 0) objRef (at_ (n + 2)),
                 isTrue "stored" (.eq (.var "x") (.var "a")) (n + 3),
                 isTrue "notStored" (.op "Bool.Not" [.eq (.var "x") (.var "a")]) (n + 4)]
      (.finish (at_ (n + 2)))]

/-! The check guards a store: an `A` is stored in an `Array A`, and storing it in an
`Array B` throws. -/

/--
info: 14: assertion does not hold
21: uncaught exception is not thrown does not hold
-/
#guard_msgs in
#eval interpret (refProgram [storeA "storeIntoArrayA" (.named "A") 10, storeA "storeIntoArrayB" (.named "B") 20])

/-! `writeElem` does not test the stored object against the element type of the array:
without the check, an `A` is stored in an `Array B`. -/

/--
info: 5: assertion does not hold
-/
#guard_msgs in
#eval interpret (refProgram [entry "uncheckedStore" (refs [
  .init "held" arrA (some (.var "arrB")) (at_ 3),
  .writeElem (.var "held") (.int 0) (.var "a") (.named "A") (at_ 3),
  .init "x" (.named "A") none (at_ 3), .readElem "x" (.var "held") (.int 0) (.named "A") (at_ 3),
  isTrue "stored" (.eq (.var "x") (.var "a")) 4,
  isTrue "notStored" (.op "Bool.Not" [.eq (.var "x") (.var "a")]) 5])])

/-! A run stops at an `instanceOfComponent` on an object that is not an array and on an array
whose elements are not references. The default element of an array of references is no
object, so it has to be told apart before the check. -/

/--
info: 3: the interpreter fails here: an expression did not evaluate
4: the interpreter fails here: an expression did not evaluate
stopped: 'arrayIsObject': an expression did not evaluate
stopped: 'primitiveArray': an expression did not evaluate
stopped: 'defaultElement': an expression did not evaluate
stopped: 'defaultArray': an expression did not evaluate
-/
#guard_msgs in
#eval interpret (refProgram [
  entry "arrayIsObject" (refs (storable "ok" "b" "a" 3)),
  entry "primitiveArray" (refs (
    [.init "i" ints none (at_ 3), .newArray "i" bv32 (.int 1) (at_ 3)] ++
    storable "ok" "a" "i" 4)),
  entry "defaultElement" (refs (
    [.init "x" (.named "A") none (at_ 3), .readElem "x" (.var "arrA") (.int 0) (.named "A") (at_ 3)] ++
    storable "ok" "x" "arrA" 4)),
  entry "defaultArray" (refs (
    [.init "aa" (.array arrA) none (at_ 3), .newArray "aa" arrA (.int 1) (at_ 3),
     .init "x" arrA none (at_ 3), .readElem "x" (.var "aa") (.int 0) arrA (at_ 3)] ++
    storable "ok" "a" "x" 4))])

/-! An `instanceOf` against a type constrained over `int` tests the constraint: 5 is an `int32` and
2^31 is not; the assertion at 20 states the opposite of that at 10. On a reference to no object, an
`instanceOf` against an array type stops the run. -/

/--
info: 20: assertion does not hold
6: the interpreter fails here: an expression did not evaluate
stopped: 'arrayDefault': an expression did not evaluate
-/
#guard_msgs in
#eval interpret (refProgram [
  entry "constrainedInt" (
    [.init "small" .int (some (.int 5)) (at_ 4),
     .init "big" .int (some (.int 2147483648)) (at_ 4)] ++
    isInstance "smallIsInt32" "small" i32 4 ++ isInstance "bigIsInt32" "big" i32 4 ++ [
    isTrue "smallIsInt32" (.var "smallIsInt32") 10,
    isTrue "bigIsNoInt32" (.op "Bool.Not" [.var "bigIsInt32"]) 11,
    isTrue "smallIsNoInt32" (.op "Bool.Not" [.var "smallIsInt32"]) 20]),
  entry "arrayDefault" (refs (
    [.init "aa" (.array arrA) none (at_ 3), .newArray "aa" arrA (.int 1) (at_ 3),
     .init "x" arrA none (at_ 3), .readElem "x" (.var "aa") (.int 0) arrA (at_ 3)] ++
    isInstance "ok" "x" arrA 6))])

/-! ## The Ion encoding

An array type is written `(array elem)`, at any depth. `covariantArrays` and `arrayParents`
are optional: a program written without them has invariant arrays and no array parent. -/

meta def programIon (extra : Array (String × Ion.Ion String)) : Ion.Ion String :=
  .struct (#[
    ("composites", .list #[.struct #[
      ("name", .string "C"), ("extending", .list #[]),
      ("fields", .list #[.struct #[
        ("name", .string "f"),
        ("ty", .sexp #[.symbol "array", .sexp #[.symbol "array", .sexp #[.symbol "named", .string "C"]]])]])]]),
    ("constrained", .list #[]), ("procedures", .list #[])] ++ extra)

meta def decode (ion : Ion.Ion String) : IO Unit :=
  match readProgram (Ion.internAndSerialize [ion]) with
  | .error e => IO.println s!"error: {e}"
  | .ok p => do
    IO.println s!"{repr (p.composites.flatMap fun c => c.fields.map (·.ty.toMono))}"
    IO.println s!"covariantArrays := {p.covariantArrays}, arrayParents := {p.arrayParents}"

/--
info: [Lambda.LMonoTy.tcons "Array" [Lambda.LMonoTy.tcons "Array" [Lambda.LMonoTy.tcons "C" []]]]
covariantArrays := false, arrayParents := []
-/
#guard_msgs in
#eval decode (programIon #[])

/--
info: [Lambda.LMonoTy.tcons "Array" [Lambda.LMonoTy.tcons "Array" [Lambda.LMonoTy.tcons "C" []]]]
covariantArrays := true, arrayParents := [C]
-/
#guard_msgs in
#eval decode (programIon #[("covariantArrays", .bool true), ("arrayParents", .list #[.string "C"])])

/-! ## The translation to Core

The translation to Core has no encoding of arrays. It reports an array type where a variable
or an `instanceOf` names one, and the array commands of a program that names none. -/

meta def toCore (p : Wire.Program) : IO Unit :=
  match Cortex.wireToCortex p >>= (Cortex.toCoreProgram ·) with
  | .error e => IO.println s!"error: {e}"
  | .ok _ => IO.println "translated to Core"

/-- A procedure with the inputs `arr` of type `arrTy` and `a` of class `A`, the output `ok`
and the body `cmds`. -/
meta def onArray (arrTy : Ty) (cmds : List Cmd) : Wire.Procedure :=
  { name := "onArray", inputs := [{ name := "arr", ty := arrTy }, { name := "a", ty := .named "A" }],
    outputs := [{ name := "ok", ty := .bool }], throws := none, requires := [], entry := false, source := at_ 0,
    body := some { entry := "b0", handlers := [], blocks := [blk "b0" cmds (.finish (at_ 1))] } }

/--
info: error: LowerHeap: Cortex array types are not lowered to Core
-/
#guard_msgs in
#eval toCore (program [defaults])

/--
info: error: LowerHeap: Cortex array types are not lowered to Core
-/
#guard_msgs in
#eval toCore (refProgram [onArray arrA []])

/--
info: error: LowerHeap: Cortex array types are not lowered to Core
-/
#guard_msgs in
#eval toCore (refProgram [onArray objRef [.instanceOf "ok" (.var "arr") arrA (at_ 1)]])

/--
info: error: LowerHeap: Cortex array commands are not lowered to Core
-/
#guard_msgs in
#eval toCore (refProgram [onArray objRef [.instanceOfComponent "ok" (.var "a") (.var "arr") (at_ 1)]])

/-! The same procedure without an array type or command is translated. -/

/--
info: translated to Core
-/
#guard_msgs in
#eval toCore (refProgram [onArray objRef [.instanceOf "ok" (.var "arr") (.named "A") (at_ 1)]])

end Cortex.ArraysTest
