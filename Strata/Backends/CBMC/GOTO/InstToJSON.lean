/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Program
import Strata.Backends.CBMC.StrataToCBMC

namespace CProverGOTO
open Lean
open CProverJSON

-------------------------------------------------------------------------------

/-- Convert `Ty` to JSON format -/
def tyToJson (ty : Ty) : Json :=
  match ty with
  | .Boolean => boolType
  | .Integer => integerType
  | .String => stringType
  | .Empty => emptyType
  | .SignedBV width => mkSignedBVType width
  | .UnsignedBV width => mkUnsignedBVType width
  | _ => Json.mkObj [("id", "unknown")]

/-- Convert `Expr` to JSON format -/
partial def exprToJson (expr : Expr) : Json :=
  match expr.id with
  | .nullary (.symbol name) => mkSymbol name (tyToJson expr.type)
  | .nullary (.constant value) =>
    Json.mkObj [
      ("id", "constant"),
      ("namedSub", Json.mkObj [
        ("type", tyToJson expr.type),
        ("value", Json.mkObj [("id", value)])
      ])
    ]
  | .nullary (.nondet name) =>
    Json.mkObj [
      ("id", "nondet"),
      ("namedSub", Json.mkObj [
        ("identifier", Json.mkObj [("id", name)]),
        ("type", tyToJson expr.type)
      ])
    ]
  | .unary op =>
    let op_str := toString f!"{op}"
    Json.mkObj [
      ("id", op_str),
      ("namedSub", Json.mkObj [("type", tyToJson expr.type)]),
      ("sub", Json.arr (expr.operands.map exprToJson).toArray)
    ]
  | .binary op =>
    let op_str := toString f!"{op}"
    Json.mkObj [
      ("id", op_str),
      ("namedSub", Json.mkObj [("type", tyToJson expr.type)]),
      ("sub", Json.arr (expr.operands.map exprToJson).toArray)
    ]
  | .multiary op =>
    let op_str := toString f!"{op}"
    Json.mkObj [
      ("id", op_str),
      ("namedSub", Json.mkObj [("type", tyToJson expr.type)]),
      ("sub", Json.arr (expr.operands.map exprToJson).toArray)
    ]
  | .side_effect effect =>
    let effect_str := toString f!"{effect}"
    Json.mkObj [
      ("id", "side_effect"),
      ("namedSub", Json.mkObj [
        ("statement", Json.mkObj [("id", effect_str)]),
        ("type", tyToJson expr.type)
      ]),
      ("sub", Json.arr (expr.operands.map exprToJson).toArray)
    ]
  | _ => panic s!"[exprToJson] Unsupported expr: {format expr}"

/-- Convert `Code` to operands list -/
def codeToOperands (code : Code) : List Json :=
  code.operands.map exprToJson

/-- Convert SourceLocation to JSON. -/
def sourceLocationToJson (loc : SourceLocation) : Json :=
  Json.mkObj [
    ("file", Json.str loc.file),
    ("function", Json.str loc.function),
    ("line", Json.str (toString loc.line)),
    ("workingDirectory", Json.str loc.workingDir)
  ]

/--
Generate instruction string for display
(FIXME) This doesn't quite match the CBMC pretty-printing right now.
-/
def instructionToString (inst : Instruction) : String :=
  let comment := s!"        // {inst.locationNum} file {inst.sourceLoc.file} line {inst.sourceLoc.line} function {inst.sourceLoc.function}\n"
  let instrStr := match inst.type with
    | .ASSUME => s!"        {inst.type} {format inst.guard}\n"
    | .ASSERT => s!"        {inst.type} {format inst.guard}\n"
    | _ => s!"        {inst.type} {format inst.code}\n"
  comment ++ instrStr

/-- Main function to convert `Instruction` to JSON -/
def instructionToJson (inst : Instruction) : Json :=
  let baseFields := [
    ("instruction", Json.str (instructionToString inst)),
    ("instructionId", Json.str (toString inst.type))
  ]
  let guardField := if Expr.beq inst.guard Expr.true then [] else [("guard", exprToJson inst.guard)]
  let operandsField := if inst.code.operands.isEmpty then [] else [("operands", Json.arr (codeToOperands inst.code).toArray)]
  let sourceField :=  if inst.sourceLoc.file.isEmpty then [] else [("sourceLocation", sourceLocationToJson inst.sourceLoc)]
  Json.mkObj (baseFields ++ guardField ++ operandsField ++ sourceField)

/-- Convert `Program` to JSON -/
def programToJson (name : String) (program : Program)
    (isBodyAvailable : Bool := true) (isInternal : Bool := false)
    : Json :=
  Json.mkObj [
    ("instructions", Json.arr (program.instructions.map instructionToJson)),
    ("isBodyAvailable", isBodyAvailable),
    ("isInternal", isInternal),
    ("name", name)
  ]

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

section Tests

/-
int simpleAdd(int x, int y) {
  __CPROVER_assume(x > 0 && x < 0x0F000000);
  __CPROVER_assume(y > 0 && y < 0x0F000000);
  int z = x + y;
  return z;
}

-- GOTO Program before instrumentation
-- goto-cc simpleAdd.c -o simpleAdd.gb
-- # Textual representation of GOTO instructions.
-- cbmc simpleAdd.gb --function simpleAdd --show-goto-functions
-- # JSON representation of GOTO instructions.
-- cbmc simpleAdd.gb --function simpleAdd --show-goto-functions --json-ui > simpleAdd.goto.json


simpleAdd /* simpleAdd */
        // 0 file simpleAdd.c line 6 function simpleAdd
        ASSUME simpleAdd::x > 0 ∧ simpleAdd::x < 251658240
        // 1 file simpleAdd.c line 7 function simpleAdd
        ASSUME simpleAdd::y > 0 ∧ simpleAdd::y < 251658240
        // 2 file simpleAdd.c line 8 function simpleAdd
        DECL simpleAdd::1::z : signedbv[32]
        // 3 file simpleAdd.c line 8 function simpleAdd
        ASSERT ¬(overflow-+(simpleAdd::x, simpleAdd::y)) // arithmetic overflow on signed + in x + y
        // 4 file simpleAdd.c line 8 function simpleAdd
        ASSIGN simpleAdd::1::z := simpleAdd::x + simpleAdd::y
        // 5 file simpleAdd.c line 9 function simpleAdd
        SET RETURN VALUE simpleAdd::1::z
        // 6 file simpleAdd.c line 9 function simpleAdd
        DEAD simpleAdd::1::z
        // 7 file simpleAdd.c line 10 function simpleAdd
        END_FUNCTION
-/

private def simpleAddProgram : Program := {
  instructions := #[
    -- ASSUME simpleAdd::x > 0 ∧ simpleAdd::x < 251658240
    { type := .ASSUME, locationNum := 0,
      guard := Expr.and [(Expr.gt (Expr.symbol "simpleAdd::x" (Ty.SignedBV 32)) (Expr.constant "0" (Ty.SignedBV 32))),
                         (Expr.lt (Expr.symbol "simpleAdd::x" (Ty.SignedBV 32)) (Expr.constant "251658240" (Ty.SignedBV 32)))],
      sourceLoc := {function := "simpleAdd", line := 6, file := "simpleAdd.c", workingDir := ""}},

    -- ASSUME simpleAdd::y > 0 ∧ simpleAdd::y < 251658240
    { type := .ASSUME, locationNum := 1,
      guard := Expr.and [(Expr.gt (Expr.symbol "simpleAdd::y" (Ty.SignedBV 32)) (Expr.constant "0" (Ty.SignedBV 32))),
                         (Expr.lt (Expr.symbol "simpleAdd::y" (Ty.SignedBV 32)) (Expr.constant "251658240" (Ty.SignedBV 32)))],
      sourceLoc := {function := "simpleAdd", line := 7, file := "simpleAdd.c", workingDir := ""}},

    -- DECL simpleAdd::1::z : signedbv[32]
    { type := .DECL, locationNum := 2,
      code := Code.decl (Expr.symbol "simpleAdd::1::z" (Ty.SignedBV 32)),
      sourceLoc := {function := "simpleAdd", line := 8, file := "simpleAdd.c", workingDir := ""}},

    -- ASSERT ¬(overflow-+(simpleAdd::x, simpleAdd::y))
    { type := .ASSERT, locationNum := 3,
      guard := Expr.not (Expr.plus_overflow (Expr.symbol "simpleAdd::x" (Ty.SignedBV 32)) (Expr.symbol "simpleAdd::y" (Ty.SignedBV 32))),
      sourceLoc := {function := "simpleAdd", line := 8, file := "simpleAdd.c", workingDir := ""}},

    -- ASSIGN simpleAdd::1::z := simpleAdd::x + simpleAdd::y
    { type := .ASSIGN, locationNum := 4,
      code := Code.assign (Expr.symbol "simpleAdd::1::z" (Ty.SignedBV 32))
                          (Expr.add [Expr.symbol "simpleAdd::x" (Ty.SignedBV 32), Expr.symbol "simpleAdd::y" (Ty.SignedBV 32)]),
      sourceLoc := {function := "simpleAdd", line := 8, file := "simpleAdd.c", workingDir := ""}},

    -- SET RETURN VALUE simpleAdd::1::z
    { type := .SET_RETURN_VALUE, locationNum := 5,
      code := Code.set_return_value (Expr.symbol "simpleAdd::1::z" (Ty.SignedBV 32)),
      sourceLoc := {function := "simpleAdd", line := 9, file := "simpleAdd.c", workingDir := ""} },

    -- DEAD simpleAdd::1::z
    { type := .DEAD, locationNum := 6,
      code := Code.dead (Expr.symbol "simpleAdd::1::z" (Ty.SignedBV 32)),
      sourceLoc := {function := "simpleAdd", line := 9, file := "simpleAdd.c", workingDir := ""} },

    -- END_FUNCTION
    { type := .END_FUNCTION, locationNum := 7,
      sourceLoc := {function := "simpleAdd", line := 10, file := "simpleAdd.c", workingDir := ""}}
  ]
}

/--
info: {"name": "simpleAdd",
 "isInternal": false,
 "isBodyAvailable": true,
 "instructions":
 [{"sourceLocation":
   {"workingDirectory": "",
    "line": "6",
    "function": "simpleAdd",
    "file": "simpleAdd.c"},
   "instructionId": "ASSUME",
   "instruction":
   "        // 0 file simpleAdd.c line 6 function simpleAdd\n        ASSUME (((((simpleAdd::x : signedbv[32]) > (0 : signedbv[32])) : bool) and (((simpleAdd::x : signedbv[32]) < (251658240 : signedbv[32])) : bool)) : bool)\n",
   "guard":
   {"sub":
    [{"sub":
      [{"namedSub":
        {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
         "identifier": {"id": "simpleAdd::x"}},
        "id": "symbol"},
       {"namedSub":
        {"value": {"id": "0"},
         "type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"}},
        "id": "constant"}],
      "namedSub": {"type": {"id": "bool"}},
      "id": ">"},
     {"sub":
      [{"namedSub":
        {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
         "identifier": {"id": "simpleAdd::x"}},
        "id": "symbol"},
       {"namedSub":
        {"value": {"id": "251658240"},
         "type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"}},
        "id": "constant"}],
      "namedSub": {"type": {"id": "bool"}},
      "id": "<"}],
    "namedSub": {"type": {"id": "bool"}},
    "id": "and"}},
  {"sourceLocation":
   {"workingDirectory": "",
    "line": "7",
    "function": "simpleAdd",
    "file": "simpleAdd.c"},
   "instructionId": "ASSUME",
   "instruction":
   "        // 1 file simpleAdd.c line 7 function simpleAdd\n        ASSUME (((((simpleAdd::y : signedbv[32]) > (0 : signedbv[32])) : bool) and (((simpleAdd::y : signedbv[32]) < (251658240 : signedbv[32])) : bool)) : bool)\n",
   "guard":
   {"sub":
    [{"sub":
      [{"namedSub":
        {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
         "identifier": {"id": "simpleAdd::y"}},
        "id": "symbol"},
       {"namedSub":
        {"value": {"id": "0"},
         "type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"}},
        "id": "constant"}],
      "namedSub": {"type": {"id": "bool"}},
      "id": ">"},
     {"sub":
      [{"namedSub":
        {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
         "identifier": {"id": "simpleAdd::y"}},
        "id": "symbol"},
       {"namedSub":
        {"value": {"id": "251658240"},
         "type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"}},
        "id": "constant"}],
      "namedSub": {"type": {"id": "bool"}},
      "id": "<"}],
    "namedSub": {"type": {"id": "bool"}},
    "id": "and"}},
  {"sourceLocation":
   {"workingDirectory": "",
    "line": "8",
    "function": "simpleAdd",
    "file": "simpleAdd.c"},
   "operands":
   [{"namedSub":
     {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
      "identifier": {"id": "simpleAdd::1::z"}},
     "id": "symbol"}],
   "instructionId": "DECL",
   "instruction":
   "        // 2 file simpleAdd.c line 8 function simpleAdd\n        DECL (decl (simpleAdd::1::z : signedbv[32]))\n"},
  {"sourceLocation":
   {"workingDirectory": "",
    "line": "8",
    "function": "simpleAdd",
    "file": "simpleAdd.c"},
   "instructionId": "ASSERT",
   "instruction":
   "        // 3 file simpleAdd.c line 8 function simpleAdd\n        ASSERT ((not(((simpleAdd::x : signedbv[32]) overflow-+ (simpleAdd::y : signedbv[32])) : bool)) : bool)\n",
   "guard":
   {"sub":
    [{"sub":
      [{"namedSub":
        {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
         "identifier": {"id": "simpleAdd::x"}},
        "id": "symbol"},
       {"namedSub":
        {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
         "identifier": {"id": "simpleAdd::y"}},
        "id": "symbol"}],
      "namedSub": {"type": {"id": "bool"}},
      "id": "overflow-+"}],
    "namedSub": {"type": {"id": "bool"}},
    "id": "not"}},
  {"sourceLocation":
   {"workingDirectory": "",
    "line": "8",
    "function": "simpleAdd",
    "file": "simpleAdd.c"},
   "operands":
   [{"namedSub":
     {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
      "identifier": {"id": "simpleAdd::1::z"}},
     "id": "symbol"},
    {"sub":
     [{"namedSub":
       {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
        "identifier": {"id": "simpleAdd::x"}},
       "id": "symbol"},
      {"namedSub":
       {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
        "identifier": {"id": "simpleAdd::y"}},
       "id": "symbol"}],
     "namedSub":
     {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"}},
     "id": "+"}],
   "instructionId": "ASSIGN",
   "instruction":
   "        // 4 file simpleAdd.c line 8 function simpleAdd\n        ASSIGN (assign (simpleAdd::1::z : signedbv[32]) (((simpleAdd::x : signedbv[32]) + (simpleAdd::y : signedbv[32])) : signedbv[32]))\n"},
  {"sourceLocation":
   {"workingDirectory": "",
    "line": "9",
    "function": "simpleAdd",
    "file": "simpleAdd.c"},
   "operands":
   [{"namedSub":
     {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
      "identifier": {"id": "simpleAdd::1::z"}},
     "id": "symbol"}],
   "instructionId": "SET_RETURN_VALUE",
   "instruction":
   "        // 5 file simpleAdd.c line 9 function simpleAdd\n        SET_RETURN_VALUE (return (simpleAdd::1::z : signedbv[32]))\n"},
  {"sourceLocation":
   {"workingDirectory": "",
    "line": "9",
    "function": "simpleAdd",
    "file": "simpleAdd.c"},
   "operands":
   [{"namedSub":
     {"type": {"namedSub": {"width": {"id": "32"}}, "id": "signedbv"},
      "identifier": {"id": "simpleAdd::1::z"}},
     "id": "symbol"}],
   "instructionId": "DEAD",
   "instruction":
   "        // 6 file simpleAdd.c line 9 function simpleAdd\n        DEAD (dead (simpleAdd::1::z : signedbv[32]))\n"},
  {"sourceLocation":
   {"workingDirectory": "",
    "line": "10",
    "function": "simpleAdd",
    "file": "simpleAdd.c"},
   "instructionId": "END_FUNCTION",
   "instruction":
   "        // 7 file simpleAdd.c line 10 function simpleAdd\n        END_FUNCTION skip\n"}]}
-/
#guard_msgs in
#eval programToJson "simpleAdd" simpleAddProgram

end Tests

-------------------------------------------------------------------------------
