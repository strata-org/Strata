/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Data.Json
import Strata.DL.Util.Map
import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

open Lean

-- Our test program
def SimpleTestEnv :=
#strata
program C_Simp;

int procedure simpleTest (x: int, y: int)
  //@pre y > 0;
  //@post true;
{
  var z : int;
  //@assume [test_assume_y_pos] y > 0;
  //@assume [test_assume_x_pos] x > 0;
  //@assume [test_assume_y_smol] y < 90;
  //@assume [test_assume_x_smol] x < 90;
  z = x + y;
  //@assert [test_assert] z > x;
  if (z > 10) {
    z = z - 1;
  } else {
    z = z + 1;
  }
  return 0;
}

#end

open Strata.C_Simp in
def SimpleTestEnvAST := TransM.run (translateProgram (SimpleTestEnv.commands))

def myFunc : Strata.C_Simp.Function := SimpleTestEnvAST.fst.funcs.head!

-- Configuration for CBMC output
structure CBMCConfig where
  sourceFile : String := "from_andrew.c"
  -- Likely want to set this from CSimp file once we have one:
  workingDirectory : String := "/tmp"
  module : String := "from_andrew"
  builtinFile : String := "<builtin-architecture-strings>"
  builtinLine : String := "20"
  intWidth : String := "32"
  longWidth : String := "64"
  charWidth : String := "8"
  pointerWidth : String := "64"

def defaultConfig : CBMCConfig := {}

-- Common JSON type constants
def emptyType : Json := Json.mkObj [("id", "empty")]
def boolType : Json := Json.mkObj [("id", "bool")]

def mkIntType (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", Json.mkObj [
      ("#c_type", Json.mkObj [("id", "signed_int")]),
      ("width", Json.mkObj [("id", config.intWidth)])
    ])
  ]

def mkCharType (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", Json.mkObj [
      ("#c_type", Json.mkObj [("id", "char")]),
      ("width", Json.mkObj [("id", config.charWidth)])
    ])
  ]

def mkCharConstantType (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", Json.mkObj [
      ("#c_type", Json.mkObj [("id", "char")]),
      ("#constant", Json.mkObj [("id", "1")]),
      ("width", Json.mkObj [("id", config.charWidth)])
    ])
  ]

def mkLongType (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", Json.mkObj [
      ("#c_type", Json.mkObj [("id", "signed_long_int")]),
      ("width", Json.mkObj [("id", config.longWidth)])
    ])
  ]

def mkPointerType (subType : Json) (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", "pointer"),
    ("namedSub", Json.mkObj [("width", Json.mkObj [("id", config.pointerWidth)])]),
    ("sub", Json.arr #[subType])
  ]

def builtinSourceLocation (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", ""),
    ("namedSub", Json.mkObj [
      ("file", Json.mkObj [("id", config.builtinFile)]),
      ("function", Json.mkObj [("id", "")]),
      ("line", Json.mkObj [("id", config.builtinLine)]),
      ("working_directory", Json.mkObj [("id", config.workingDirectory)])
    ])
  ]

-- Simple structure to hold any JSON node
structure JsonNode where
  id : String
  namedSub : Option Json := none
  sub : Option (Array Json) := none
  deriving FromJson, ToJson

-- Location structure
structure Location where
  id : String := ""
  namedSub : Option Json := none
  deriving FromJson, ToJson

-- Parameter structure for contracts
structure Parameter where
  id : String := "parameter"
  namedSub : Json
  deriving FromJson, ToJson

-- Lambda expression structure
structure LambdaExpr where
  id : String := "lambda"
  namedSub : Json
  sub : Array Json
  deriving FromJson, ToJson

-- Contract type structure
structure ContractType where
  id : String := "code"
  namedSub : Json
  deriving FromJson, ToJson

-- Main CBMC Symbol structure with defaults
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

def createSymbol (baseName : String) (line : String) (isParameter : Bool) (isStateVar : Bool) (namePrefix : String) (functionName : String) (prettyName : String := "") (config : CBMCConfig := defaultConfig) : CBMCSymbol :=
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

def mkSourceLocation (file : String) (function : String) (line : String) (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", ""),
    ("namedSub", Json.mkObj [
      ("file", Json.mkObj [("id", file)]),
      ("function", Json.mkObj [("id", function)]),
      ("line", Json.mkObj [("id", line)]),
      ("working_directory", Json.mkObj [("id", config.workingDirectory)])
    ])
  ]

def mkParameter (baseName : String) (functionName : String) (line : String) (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", "parameter"),
    ("namedSub", Json.mkObj [
      ("#base_name", Json.mkObj [("id", baseName)]),
      ("#identifier", Json.mkObj [("id", s!"{functionName}::{baseName}")]),
      ("#source_location", mkSourceLocation config.sourceFile functionName line config),
      ("type", mkIntType config)
    ])
  ]

def mkSymbol (identifier : String) (symbolType : Json) : Json :=
  Json.mkObj [
    ("id", "symbol"),
    ("namedSub", Json.mkObj [
      ("identifier", Json.mkObj [("id", identifier)]),
      ("type", symbolType)
    ])
  ]

def i32ToHex (s : String) : String :=
  match s.toInt? with
  | some n =>
    let unsigned := if n < 0 then UInt32.size + n else n
    ("".intercalate ((Nat.toDigits 16 unsigned.natAbs).map (λ c => c.toUpper.toString)))
  | none => panic! "Failed to convert String to int"

def mkConstant (value : String) (base : String) (sourceLocation : Json) (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", "constant"),
    ("namedSub", Json.mkObj [
      ("#base", Json.mkObj [("id", base)]),
      ("#source_location", sourceLocation),
      ("type", mkIntType config),
      ("value", Json.mkObj [("id", i32ToHex value)])
    ])
  ]

def mkCodeBlock (statement : String) (line : String) (functionName : String) (sub : Array Json) (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation config.sourceFile functionName line config),
      ("statement", Json.mkObj [("id", statement)]),
      ("type", emptyType)
    ]),
    ("sub", Json.arr sub)
  ]

def mkSideEffect (statement : String) (line : String) (functionName : String) (effectType : Json) (sub : Array Json) (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", "side_effect"),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation config.sourceFile functionName line config),
      ("statement", Json.mkObj [("id", statement)]),
      ("type", effectType)
    ]),
    ("sub", Json.arr sub)
  ]

def mkLvalueSymbol (identifier : String) (line : String) (functionName : String) (config : CBMCConfig := defaultConfig) : Json :=
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

def opToOutTypeJson (op: String) : Json :=
  match op with
  | ">" => boolType
  | "<" => boolType
  | ">=" => boolType
  | "<=" => boolType
  | "+" => mkIntType
  | "-" => mkIntType
  | _ => panic! "Unimplemented"

def mkBinaryOp (op : String) (line : String) (functionName : String) (left : Json) (right : Json) (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", op),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation config.sourceFile functionName line config),
      ("type", (opToOutTypeJson op))
    ]),
    ("sub", Json.arr #[left, right])
  ]

def mkBuiltinFunction (_funcName : String) (paramTypes : Array Json) (config : CBMCConfig := defaultConfig) : Json :=
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

def mkAssertParam (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", "parameter"),
    ("namedSub", Json.mkObj [
      ("#base_name", Json.mkObj [("id", "assertion")]),
      ("#identifier", Json.mkObj [("id", "")]),
      ("#source_location", mkSourceLocation config.builtinFile "__CPROVER_assert" config.builtinLine config),
      ("type", boolType)
    ])
  ]

def mkStringParam (config : CBMCConfig := defaultConfig) : Json :=
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

def mkAssumeParam (config : CBMCConfig := defaultConfig) : Json :=
  Json.mkObj [
    ("id", "parameter"),
    ("namedSub", Json.mkObj [
      ("#base_name", Json.mkObj [("id", "assumption")]),
      ("#identifier", Json.mkObj [("id", "")]),
      ("#source_location", mkSourceLocation config.builtinFile "__CPROVER_assume" config.builtinLine config),
      ("type", boolType)
    ])
  ]

def mkStringConstant (value : String) (line : String) (functionName : String) (config : CBMCConfig := defaultConfig) : Json :=
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
          ("type", mkCharType)
        ]),
        ("sub", Json.arr #[
          Json.mkObj [
            ("id", "string_constant"),
            ("namedSub", Json.mkObj [
              ("#lvalue", Json.mkObj [("id", "1")]),
              ("#source_location", mkSourceLocation "from_andrew.c" functionName line),
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

def createParameterSymbol (baseName : String) (functionName : String := "simpleTest") : CBMCSymbol :=
  createSymbol baseName "1" true true s!"{functionName}::" functionName

def createLocalSymbol (baseName : String) (functionName : String := "simpleTest") : CBMCSymbol :=
  let fullName := s!"{functionName}::1::{baseName}"
  createSymbol baseName "5" false false s!"{functionName}::1::" functionName fullName

instance : ToJson (Map String CBMCSymbol) where
  toJson m := Json.mkObj (m.map fun (k, v) => (k, toJson v))

-- Convert LExpr to CBMC JSON format for contracts
def lexprToCBMC (expr : Strata.C_Simp.Expression.Expr) (functionName : String) : Json :=
  match expr with
  | .app (.app (.op op _) (.fvar varName _)) (.const value _) =>
    mkBinaryOp (opToStr op) "2" functionName
      (Json.mkObj [
        ("id", "symbol"),
        ("namedSub", Json.mkObj [
          ("#base_name", Json.mkObj [("id", varName)]),
          ("#id_class", Json.mkObj [("id", "1")]),
          ("#lvalue", Json.mkObj [("id", "1")]),
          ("#source_location", mkSourceLocation "from_andrew.c" functionName "2"),
          ("identifier", Json.mkObj [("id", s!"{functionName}::{varName}")]),
          ("type", mkIntType)
        ])
      ])
      (mkConstant value "10" (mkSourceLocation "from_andrew.c" functionName "2"))
  | .const "true" _ =>
    Json.mkObj [
      ("id", "notequal"),
      ("namedSub", Json.mkObj [
        ("#source_location", mkSourceLocation "from_andrew.c" functionName "3"),
        ("type", Json.mkObj [("id", "bool")])
      ]),
      ("sub", Json.arr #[
        mkConstant "1" "10" (mkSourceLocation "from_andrew.c" functionName "3"),
        Json.mkObj [
          ("id", "constant"),
          ("namedSub", Json.mkObj [
            ("type", mkIntType),
            ("value", Json.mkObj [("id", "0")])
          ])
        ]
      ])
    ]
  | _ => panic! "Unimplemented"

def createContractSymbolFromAST (func : Strata.C_Simp.Function) : CBMCSymbol :=
  let location : Location := {
    id := "",
    namedSub := some (Json.mkObj [
      ("file", Json.mkObj [("id", "from_andrew.c")]),
      ("function", Json.mkObj [("id", "")]),
      ("line", Json.mkObj [("id", "1")]),
      ("working_directory", Json.mkObj [("id", "/home/ub-backup/tautschn/cbmc-github.git")])
    ])
  }

  let sourceLocation := mkSourceLocation "from_andrew.c" func.name "2"
  let ensuresSourceLocation := mkSourceLocation "from_andrew.c" func.name "3"

  let mathFunctionType := Json.mkObj [
    ("id", "mathematical_function"),
    ("sub", Json.arr #[
      Json.mkObj [
        ("id", ""),
        ("sub", Json.arr #[mkIntType, mkIntType, mkIntType])
      ],
      Json.mkObj [("id", "bool")]
    ])
  ]

  let parameterTuple := Json.mkObj [
    ("id", "tuple"),
    ("namedSub", Json.mkObj [("type", Json.mkObj [("id", "tuple")])]),
    ("sub", Json.arr #[
      mkSymbol "__CPROVER_return_value" mkIntType,
      mkSymbol s!"{func.name}::x" mkIntType,
      mkSymbol s!"{func.name}::y" mkIntType
    ])
  ]

  let requiresLambda := Json.mkObj [
    ("id", "lambda"),
    ("namedSub", Json.mkObj [
      ("#source_location", sourceLocation),
      ("type", mathFunctionType)
    ]),
    ("sub", Json.arr #[
      parameterTuple,
      lexprToCBMC func.pre func.name
    ])
  ]

  let ensuresLambda := Json.mkObj [
    ("id", "lambda"),
    ("namedSub", Json.mkObj [
      ("#source_location", ensuresSourceLocation),
      ("type", mathFunctionType)
    ]),
    ("sub", Json.arr #[
      parameterTuple,
      lexprToCBMC func.post func.name
    ])
  ]

  let parameters := Json.mkObj [
    ("id", ""),
    ("sub", Json.arr #[
      mkParameter "x" func.name "1",
      mkParameter "y" func.name "1"
    ])
  ]

  let contractType := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation "from_andrew.c" "" "1"),
      ("#spec_assigns", Json.mkObj [("id", "")]),
      ("#spec_ensures", Json.mkObj [
        ("id", ""),
        ("sub", Json.arr #[ensuresLambda])
      ]),
      ("#spec_frees", Json.mkObj [("id", "")]),
      ("#spec_requires", Json.mkObj [
        ("id", ""),
        ("sub", Json.arr #[requiresLambda])
      ]),
      ("parameters", parameters),
      ("return_type", mkIntType)
    ])
  ]

  {
    baseName := func.name,
    isProperty := true,
    location := location,
    mode := "C",
    module := "from_andrew",
    name := s!"contract::{func.name}",
    prettyName := func.name,
    prettyType := "signed int (signed int x, signed int y)",
    type := contractType,
    value := Json.mkObj [("id", "nil")]
  }

structure SourceLoc where
  functionName : String
  lineNum : String

def getParamJson(func: Strata.C_Simp.Function) : Json :=
  Json.mkObj [
    ("id", ""),
    ("sub", Json.arr (func.inputs.map (λ i => mkParameter i.fst func.name "1")).toArray)
  ]

def returnStmt (functionName : String) (config : CBMCConfig := defaultConfig): Json :=
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

def exprToJson (e : Strata.C_Simp.Expression.Expr) (loc: SourceLoc) : Json :=
  match e with
  | .app (.app (.op op _) left) right =>
    let leftJson := match left with
      | .fvar "z" _ => mkLvalueSymbol s!"{loc.functionName}::1::z" loc.lineNum loc.functionName
      | .fvar varName _ => mkLvalueSymbol s!"{loc.functionName}::{varName}" loc.lineNum loc.functionName
      | _ => exprToJson left loc
    let rightJson := match right with
      | .fvar varName _ => mkLvalueSymbol s!"{loc.functionName}::{varName}" loc.lineNum loc.functionName
      | .const value _ => mkConstant value "10" (mkSourceLocation "from_andrew.c" loc.functionName loc.lineNum)
      | _ => exprToJson right loc
    mkBinaryOp (opToStr op) loc.lineNum loc.functionName leftJson rightJson
  | .const n _ =>
    mkConstant n "10" (mkSourceLocation "from_andrew.c" loc.functionName "14")
  | _ => panic! "Unimplemented"

def cmdToJson (e : Strata.C_Simp.Command) (loc: SourceLoc) : Json :=
  match e with
  | .init name _ _ _ =>
    mkCodeBlock "decl" "5" loc.functionName #[
      Json.mkObj [
        ("id", "symbol"),
        ("namedSub", Json.mkObj [
          ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "5"),
          ("identifier", Json.mkObj [("id", s!"{loc.functionName}::1::{name}")]),
          ("type", mkIntType)
        ])
      ]
    ]
  | .set ("return") _ _ => returnStmt loc.functionName
  | .set name expr _ =>
    let exprLoc : SourceLoc := { functionName := loc.functionName, lineNum := "6" }
    mkCodeBlock "expression" "6" loc.functionName #[
      mkSideEffect "assign" "6" loc.functionName mkIntType #[
        mkLvalueSymbol s!"{loc.functionName}::1::{name}" "6" loc.functionName,
        exprToJson expr exprLoc
      ]
    ]
  | .assert label expr _ =>
    let exprLoc : SourceLoc := { functionName := loc.functionName, lineNum := "7" }
    mkCodeBlock "expression" "7" loc.functionName #[
      mkSideEffect "function_call" "7" loc.functionName
        (Json.mkObj [
          ("id", "empty"),
          ("namedSub", Json.mkObj [
            ("#source_location", builtinSourceLocation)
          ])
        ]) #[
        Json.mkObj [
          ("id", "symbol"),
          ("namedSub", Json.mkObj [
            ("#lvalue", Json.mkObj [("id", "1")]),
            ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "7"),
            ("identifier", Json.mkObj [("id", "__CPROVER_assert")]),
            ("type", mkBuiltinFunction "__CPROVER_assert" #[mkAssertParam, mkStringParam])
          ])
        ],
        Json.mkObj [
          ("id", "arguments"),
          ("sub", Json.arr #[
            exprToJson expr exprLoc,
            mkStringConstant label "7" loc.functionName
          ])
        ]
      ]
    ]
  | .assume _ expr _ =>
    let exprLoc : SourceLoc := { functionName := loc.functionName, lineNum := "13" }
    mkCodeBlock "expression" "13" loc.functionName #[
      mkSideEffect "function_call" "13" loc.functionName
        (Json.mkObj [
          ("id", "empty"),
          ("namedSub", Json.mkObj [
            ("#source_location", builtinSourceLocation)
          ])
        ]) #[
        Json.mkObj [
          ("id", "symbol"),
          ("namedSub", Json.mkObj [
            ("#lvalue", Json.mkObj [("id", "1")]),
            ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "13"),
            ("identifier", Json.mkObj [("id", "__CPROVER_assume")]),
            ("type", mkBuiltinFunction "__CPROVER_assume" #[mkAssumeParam])
          ])
        ],
        Json.mkObj [
          ("id", "arguments"),
          ("sub", Json.arr #[
            exprToJson expr exprLoc
          ])
        ]
      ]
    ]
  | .havoc _ _ => panic! "Unimplemented"

mutual
partial def blockToJson (b: Imperative.Block Strata.C_Simp.Expression Strata.C_Simp.Command) (loc: SourceLoc) : Json :=
  Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#end_location", mkSourceLocation "from_andrew.c" loc.functionName "10"),
      ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "8"),
      ("statement", Json.mkObj [("id", "block")]),
      ("type", emptyType)
    ]),
    ("sub", Json.arr (b.ss.map (stmtToJson · loc)).toArray)
  ]

partial def stmtToJson (e : Strata.C_Simp.Statement) (loc: SourceLoc) : Json :=
  match e with
  | .cmd cmd => cmdToJson cmd loc
  | .ite cond thenb elseb _ =>
    Json.mkObj [
      ("id", "code"),
      ("namedSub", Json.mkObj [
        ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "8"),
        ("statement", Json.mkObj [("id", "ifthenelse")]),
        ("type", emptyType)
      ]),
      ("sub", Json.arr #[
        exprToJson cond loc,
        blockToJson thenb loc,
        blockToJson elseb loc,
      ])
    ]
  | _ => panic! "Unimplemented"
end

def createImplementationSymbolFromAST (func : Strata.C_Simp.Function) : CBMCSymbol :=
  let location : Location := {
    namedSub := some (Json.mkObj [
      ("file", Json.mkObj [("id", "from_andrew.c")]),
      ("function", Json.mkObj [("id", "")]),
      ("line", Json.mkObj [("id", "1")]),
      ("working_directory", Json.mkObj [("id", "/home/ub-backup/tautschn/cbmc-github.git")])
    ])
  }

  let parameters := getParamJson func

  let implType := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation "from_andrew.c" "" "1"),
      ("parameters", parameters),
      ("return_type", mkIntType)
    ])
  ]

  -- For now, keep the hardcoded implementation but use function name from AST
  let loc : SourceLoc := { functionName := func.name, lineNum := "1" }
  let stmtJsons := (func.body.map (stmtToJson · loc)) --++ [returnStmt]

  let implValue := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#end_location", mkSourceLocation "from_andrew.c" func.name "15"),
      ("#source_location", mkSourceLocation "from_andrew.c" func.name "4"),
      ("statement", Json.mkObj [("id", "block")]),
      ("type", emptyType)
    ]),
    ("sub", Json.arr stmtJsons.toArray)
  ]

  {
    baseName := func.name,
    isLvalue := true,
    location := location,
    mode := "C",
    module := "from_andrew",
    name := func.name,
    prettyName := func.name,
    prettyType := s!"signed int (signed int {String.intercalate ", signed int " func.inputs.keys})",
    prettyValue := "{\n  signed int z;\n  z = x + y;\n  __CPROVER_assert(z > x, \"test_assert\");\n  if(z > 10)\n  {\n    z = z - 1;\n  }\n\n  else\n  {\n    z = z + 1;\n  }\n  __CPROVER_assume(z > 0);\n  return 0;\n}",
    type := implType,
    value := implValue
  }

def testSymbols : String := Id.run do
  -- Generate symbols using AST data
  let contractSymbol := createContractSymbolFromAST myFunc
  let implSymbol := createImplementationSymbolFromAST myFunc

  -- Get parameter names from AST
  let paramNames := myFunc.inputs.keys

  -- Hardcode local variable for now
  let zSymbol := createLocalSymbol "z"

  -- Build symbol map
  let mut m : Map String CBMCSymbol := Map.empty
  m := m.insert s!"contract::{myFunc.name}" contractSymbol
  m := m.insert myFunc.name implSymbol

  -- Add parameter symbols
  for paramName in paramNames do
    let paramSymbol := createParameterSymbol paramName
    m := m.insert s!"{myFunc.name}::{paramName}" paramSymbol

  -- Add local variable
  m := m.insert s!"{myFunc.name}::1::z" zSymbol

  toString (toJson m)
