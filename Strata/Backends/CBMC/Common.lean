/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Data.Json
import Strata.DL.Util.Map

-------------------------------------------------------------------------------

open Lean

namespace Strata
namespace CBMC

/-- Configuration for CBMC output -/
structure CBMCConfig where
  sourceFile : String := ""
  workingDirectory : String := ""
  module : String := ""
  builtinFile : String := "<builtin-architecture-strings>"
  builtinLine : String := "20"
  intWidth : String := "32"
  longWidth : String := "64"
  charWidth : String := "8"
  pointerWidth : String := "64"

def CBMCConfig.empty : CBMCConfig := {}

/-- Simple structure to hold any CBMC-compatible JSON node -/
structure JsonNode where
  id : String
  namedSub : Option Json := none
  sub : Option (Array Json) := none
  deriving FromJson, ToJson

-------------------------------------------------------------------------------

/-! # Source Location -/

/-- Location structure -/
structure Location where
  id : String := ""
  namedSub : Option Json := none
  deriving FromJson, ToJson

structure SourceLoc where
  functionName : String
  lineNum : String

def builtinSourceLocation (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", ""),
    ("namedSub", Json.mkObj [
      ("file", Json.mkObj [("id", config.builtinFile)]),
      ("function", Json.mkObj [("id", "")]),
      ("line", Json.mkObj [("id", config.builtinLine)]),
      ("working_directory", Json.mkObj [("id", config.workingDirectory)])
    ])
  ]

def mkSourceLocation (file : String) (function : String) (line : String) (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", ""),
    ("namedSub", Json.mkObj [
      ("file", Json.mkObj [("id", file)]),
      ("function", Json.mkObj [("id", function)]),
      ("line", Json.mkObj [("id", line)]),
      ("working_directory", Json.mkObj [("id", config.workingDirectory)])
    ])
  ]

-------------------------------------------------------------------------------

/-! # Types -/

def emptyType : Json := Json.mkObj [("id", "empty")]
def boolType : Json := Json.mkObj [("id", "bool")]
def integerType : Json := Json.mkObj [("id", "integer")]
def stringType : Json := Json.mkObj [("id", "string")]

def mkIntType (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", Json.mkObj [
      ("#c_type", Json.mkObj [("id", "signed_int")]),
      ("width", Json.mkObj [("id", config.intWidth)])
    ])
  ]

def mkCharType (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", Json.mkObj [
      ("#c_type", Json.mkObj [("id", "char")]),
      ("width", Json.mkObj [("id", config.charWidth)])
    ])
  ]

def mkCharConstantType (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", Json.mkObj [
      ("#c_type", Json.mkObj [("id", "char")]),
      ("#constant", Json.mkObj [("id", "1")]),
      ("width", Json.mkObj [("id", config.charWidth)])
    ])
  ]

def mkLongType (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", Json.mkObj [
      ("#c_type", Json.mkObj [("id", "signed_long_int")]),
      ("width", Json.mkObj [("id", config.longWidth)])
    ])
  ]

def mkPointerType (subType : Json) (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "pointer"),
    ("namedSub", Json.mkObj [("width", Json.mkObj [("id", config.pointerWidth)])]),
    ("sub", Json.arr #[subType])
  ]

def mkSignedBVType (width : Nat) : Json :=
  Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", Json.mkObj [
      ("width", Json.mkObj [("id", toString width)])
    ])
  ]

def mkUnsignedBVType (width : Nat) : Json :=
  Json.mkObj [
    ("id", "unsignedbv"),
    ("namedSub", Json.mkObj [
      ("width", Json.mkObj [("id", toString width)])
    ])
  ]

-------------------------------------------------------------------------------

/-! # Symbols -/

/-- Main CBMC Symbol structure with defaults -/
structure CBMCSymbol where
  baseName : String
  isAuxiliary : Bool := false
  isExported : Bool := false
  isExtern : Bool := false
  isFileLocal : Bool := false
  isInput : Bool := false
  isLvalue : Bool := false
  isMacro : Bool := false
  isOutput : Bool := false
  isParameter : Bool := false
  isProperty : Bool := false
  isStateVar : Bool := false
  isStaticLifetime : Bool := false
  isThreadLocal : Bool := false
  isType : Bool := false
  isVolatile : Bool := false
  isWeak : Bool := false
  location : Location
  mode : String
  module : String
  name : String
  prettyName : String := ""
  prettyType : String := ""
  prettyValue : String := ""
  type : Json
  value : Json
  deriving FromJson, ToJson

instance : ToJson (Map String CBMCSymbol) where
  toJson m := Json.mkObj (m.map fun (k, v) => (k, toJson v))

def createSymbol (baseName : String) (line : String) (isParameter : Bool) (isStateVar : Bool) (namePrefix : String) (functionName : String) (config : CBMCConfig := .empty) (prettyName : String := "") : CBMCSymbol :=
  let locationNamedSub := Json.mkObj [
    ("file", Json.mkObj [("id", config.sourceFile)]),
    ("function", Json.mkObj [("id", functionName)]),
    ("line", Json.mkObj [("id", line)]),
    ("working_directory", Json.mkObj [("id", config.workingDirectory)])
  ]

  let location : Location := {
    id := "",
    namedSub := some locationNamedSub
  }

  let typeNamedSub := Json.mkObj [
    ("#c_type", Json.mkObj [("id", "signed_int")]),
    ("width", Json.mkObj [("id", config.intWidth)])
  ]

  let typeJson := Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", typeNamedSub)
  ]

  let valueJson := Json.mkObj [("id", "nil")]
  let fullName := s!"{namePrefix}{baseName}"

  {
    baseName := baseName,
    isFileLocal := true,
    isLvalue := true,
    isParameter := isParameter,
    isStateVar := isStateVar,
    isThreadLocal := true,
    location := location,
    mode := "C",
    module := "from_andrew",
    name := fullName,
    prettyName := if prettyName.isEmpty then "" else prettyName,
    prettyType := "signed int",
    prettyValue := "",
    type := typeJson,
    value := valueJson
  }

def mkSymbol (identifier : String) (symbolType : Json) : Json :=
  Json.mkObj [
    ("id", "symbol"),
    ("namedSub", Json.mkObj [
      ("identifier", Json.mkObj [("id", identifier)]),
      ("type", symbolType)
    ])
  ]

-------------------------------------------------------------------------------

/-! # Constants -/

def i32ToHex (s : String) : String :=
  match s.toInt? with
  | some n =>
    let unsigned := if n < 0 then UInt32.size + n else n
    ("".intercalate ((Nat.toDigits 16 unsigned.natAbs).map (λ c => c.toUpper.toString)))
  | none => panic! "Failed to convert String to int"

def mkConstant (value : String) (base : String) (sourceLocation : Json) (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "constant"),
    ("namedSub", Json.mkObj [
      ("#base", Json.mkObj [("id", base)]),
      ("#source_location", sourceLocation),
      ("type", mkIntType config),
      ("value", Json.mkObj [("id", i32ToHex value)])
    ])
  ]

def mkConstantTrue (sourceLocation : Json) (config : CBMCConfig := .empty) : Json :=
    Json.mkObj [
      ("id", "notequal"),
      ("namedSub", Json.mkObj [
        ("#source_location", sourceLocation),
        ("type", Json.mkObj [("id", "bool")])
      ]),
      ("sub", Json.arr #[
        mkConstant "1" "10" sourceLocation config,
        Json.mkObj [
          ("id", "constant"),
          ("namedSub", Json.mkObj [
            ("type", mkIntType config),
            ("value", Json.mkObj [("id", "0")])
          ])
        ]
      ])
    ]

def mkStringConstant (value : String) (line : String) (functionName : String) (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "address_of"),
    ("namedSub", Json.mkObj [
      ("type", Json.mkObj [
        ("id", "pointer"),
        ("namedSub", Json.mkObj [("width", Json.mkObj [("id", config.pointerWidth)])]),
        ("sub", Json.arr #[mkCharType config])
      ])
    ]),
    ("sub", Json.arr #[
      Json.mkObj [
        ("id", "index"),
        ("namedSub", Json.mkObj [
          ("type", mkCharType config)
        ]),
        ("sub", Json.arr #[
          Json.mkObj [
            ("id", "string_constant"),
            ("namedSub", Json.mkObj [
              ("#lvalue", Json.mkObj [("id", "1")]),
              ("#source_location", mkSourceLocation config.sourceFile functionName line config),
              ("type", Json.mkObj [
                ("id", "array"),
                ("namedSub", Json.mkObj [
                  ("size", Json.mkObj [
                    ("id", "constant"),
                    ("namedSub", Json.mkObj [
                      ("type", mkLongType config),
                      ("value", Json.mkObj [("id", "C")])
                    ])
                  ])
                ]),
                ("sub", Json.arr #[mkCharType config])
              ]),
              ("value", Json.mkObj [("id", value)])
            ])
          ],
          Json.mkObj [
            ("id", "constant"),
            ("namedSub", Json.mkObj [
              ("type", mkLongType config),
              ("value", Json.mkObj [("id", "0")])
            ])
          ]
        ])
      ]
    ])
  ]

-------------------------------------------------------------------------------

/-! # Contracts -/

/-- Parameter structure for contracts -/
structure Parameter where
  id : String := "parameter"
  namedSub : Json
  deriving FromJson, ToJson

/-- Contract type structure -/
structure ContractType where
  id : String := "code"
  namedSub : Json
  deriving FromJson, ToJson

def mkParameter (baseName : String) (functionName : String) (line : String) (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "parameter"),
    ("namedSub", Json.mkObj [
      ("#base_name", Json.mkObj [("id", baseName)]),
      ("#identifier", Json.mkObj [("id", s!"{functionName}::{baseName}")]),
      ("#source_location", mkSourceLocation config.sourceFile functionName line config),
      ("type", mkIntType config)
    ])
  ]

def mkAssertParam (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "parameter"),
    ("namedSub", Json.mkObj [
      ("#base_name", Json.mkObj [("id", "assertion")]),
      ("#identifier", Json.mkObj [("id", "")]),
      ("#source_location", mkSourceLocation config.builtinFile "__CPROVER_assert" config.builtinLine config),
      ("type", boolType)
    ])
  ]

def mkStringParam (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "parameter"),
    ("namedSub", Json.mkObj [
      ("#base_name", Json.mkObj [("id", "description")]),
      ("#identifier", Json.mkObj [("id", "")]),
      ("#source_location", mkSourceLocation config.builtinFile "__CPROVER_assert" config.builtinLine config),
      ("type", Json.mkObj [
        ("id", "pointer"),
        ("namedSub", Json.mkObj [
          ("#source_location", mkSourceLocation config.builtinFile "__CPROVER_assert" config.builtinLine config),
          ("width", Json.mkObj [("id", config.pointerWidth)])
        ]),
        ("sub", Json.arr #[mkCharConstantType config])
      ])
    ])
  ]

def mkAssumeParam (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "parameter"),
    ("namedSub", Json.mkObj [
      ("#base_name", Json.mkObj [("id", "assumption")]),
      ("#identifier", Json.mkObj [("id", "")]),
      ("#source_location", mkSourceLocation config.builtinFile "__CPROVER_assume" config.builtinLine config),
      ("type", boolType)
    ])
  ]

-------------------------------------------------------------------------------

/-! # Expressions -/

/-- Lambda expression structure -/
structure LambdaExpr where
  id : String := "lambda"
  namedSub : Json
  sub : Array Json
  deriving FromJson, ToJson

def mkSideEffect (statement : String) (line : String) (functionName : String) (effectType : Json) (sub : Array Json) (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "side_effect"),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation config.sourceFile functionName line config),
      ("statement", Json.mkObj [("id", statement)]),
      ("type", effectType)
    ]),
    ("sub", Json.arr sub)
  ]

def mkLvalueSymbol (identifier : String) (line : String) (functionName : String) (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "symbol"),
    ("namedSub", Json.mkObj [
      ("#lvalue", Json.mkObj [("id", "1")]),
      ("#source_location", mkSourceLocation config.sourceFile functionName line config),
      ("identifier", Json.mkObj [("id", identifier)]),
      ("type", mkIntType config)
    ])
  ]

def opToStr (op: String) : String :=
  match op with
  | "Int.Gt" => ">"
  | "Int.Lt" => "<"
  | "Int.Ge" => ">="
  | "Int.Le" => "<="
  | "Int.Add" => "+"
  | "Int.Sub" => "-"
  | _ => panic! "Unimplemented"

def opToOutTypeJson (op: String) (config : CBMCConfig := .empty): Json :=
  match op with
  | ">" => boolType
  | "<" => boolType
  | ">=" => boolType
  | "<=" => boolType
  | "+" => mkIntType config
  | "-" => mkIntType config
  | _ => panic! "Unimplemented"


def mkBinaryOp (op : String) (line : String) (functionName : String) (left : Json) (right : Json) (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", op),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation config.sourceFile functionName line config),
      ("type", (opToOutTypeJson op config))
    ]),
    ("sub", Json.arr #[left, right])
  ]

def createParameterSymbol (baseName : String) (functionName : String) (config : CBMCConfig := .empty) : CBMCSymbol :=
  createSymbol baseName "1" true true s!"{functionName}::" functionName config

def createLocalSymbol (baseName : String) (functionName : String) (config : CBMCConfig := .empty) : CBMCSymbol :=
  let fullName := s!"{functionName}::1::{baseName}"
  createSymbol baseName "5" false false s!"{functionName}::1::" functionName config fullName

-------------------------------------------------------------------------------

/-! # Code -/

def mkCodeBlock (statement : String) (line : String) (functionName : String) (sub : Array Json) (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation config.sourceFile functionName line config),
      ("statement", Json.mkObj [("id", statement)]),
      ("type", emptyType)
    ]),
    ("sub", Json.arr sub)
  ]

def mkBuiltinFunction (_funcName : String) (paramTypes : Array Json) (config : CBMCConfig := .empty) : Json :=
  Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#source_location", builtinSourceLocation config),
      ("parameters", Json.mkObj [
        ("id", ""),
        ("sub", Json.arr paramTypes)
      ]),
      ("return_type", Json.mkObj [
        ("id", "empty"),
        ("namedSub", Json.mkObj [
          ("#source_location", builtinSourceLocation config)
        ])
      ])
    ])
  ]

def returnStmt (functionName : String) (config : CBMCConfig := .empty): Json :=
  Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation config.sourceFile functionName "14" config),
      ("statement", Json.mkObj [("id", "return")]),
      ("type", emptyType)
    ]),
    ("sub", Json.arr #[
      mkConstant "0" "10" (mkSourceLocation config.sourceFile functionName "14" config) config
    ])
  ]

-------------------------------------------------------------------------------

end CBMC
end Strata
