/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.Common
import Strata.DL.Util.Map
import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

section

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

open CProverJson Lean

open Strata.C_Simp in
def SimpleTestEnvAST := TransM.run Inhabited.default (translateProgram (SimpleTestEnv.commands))

def myFunc : Strata.C_Simp.Function := SimpleTestEnvAST.fst.funcs.head!

def defaultConfig : CBMCConfig := {
    sourceFile := "from_andrew.c"
    -- Likely want to set this from CSimp file once we have one:
    workingDirectory := "/home/ub-backup/tautschn/cbmc-github.git"
    module := "from_andrew"
}

-- Lambda expression structure
structure LambdaExpr where
  id : String := "lambda"
  namedSub : Json
  sub : Array Json
  deriving FromJson, ToJson

instance : ToJson (Map String CProverJson.CBMCSymbol) where
  toJson m := Json.mkObj (m.map fun (k, v) => (k, toJson v))

-- Convert LExpr to CBMC JSON format for contracts
def lexprToCBMC (expr : Strata.C_Simp.Expression.Expr) (functionName : String) : Json :=
  match expr with
  | .app (.app (.op op _) (.fvar varName _)) (.const value _) =>
    mkBinaryOp (opToStr op) "2" functionName (config := defaultConfig)
      (Json.mkObj [
        ("id", "symbol"),
        ("namedSub", Json.mkObj [
          ("#base_name", Json.mkObj [("id", varName)]),
          ("#id_class", Json.mkObj [("id", "1")]),
          ("#lvalue", Json.mkObj [("id", "1")]),
          ("#source_location", mkSourceLocation "from_andrew.c" functionName "2" defaultConfig),
          ("identifier", Json.mkObj [("id", s!"{functionName}::{varName}")]),
          ("type", mkIntType defaultConfig)
        ])
      ])
      (mkConstant value "10" (mkSourceLocation "from_andrew.c" functionName "2" defaultConfig) defaultConfig)
  | .const "true" _ =>
    Json.mkObj [
      ("id", "notequal"),
      ("namedSub", Json.mkObj [
        ("#source_location", mkSourceLocation "from_andrew.c" functionName "3" defaultConfig),
        ("type", Json.mkObj [("id", "bool")])
      ]),
      ("sub", Json.arr #[
        mkConstant "1" "10" (mkSourceLocation "from_andrew.c" functionName "3" defaultConfig) defaultConfig,
        Json.mkObj [
          ("id", "constant"),
          ("namedSub", Json.mkObj [
            ("type", mkIntType defaultConfig),
            ("value", Json.mkObj [("id", "0")])
          ])
        ]
      ])
    ]
  | _ => panic! "Unimplemented"

def createContractSymbolFromAST (func : Strata.C_Simp.Function) : CProverJson.CBMCSymbol :=
  let location : Location := {
    id := "",
    namedSub := some (Json.mkObj [
      ("file", Json.mkObj [("id", "from_andrew.c")]),
      ("function", Json.mkObj [("id", "")]),
      ("line", Json.mkObj [("id", "1")]),
      ("working_directory", Json.mkObj [("id", "/home/ub-backup/tautschn/cbmc-github.git")])
    ])
  }

  let sourceLocation := mkSourceLocation "from_andrew.c" func.name "2" defaultConfig
  let ensuresSourceLocation := mkSourceLocation "from_andrew.c" func.name "3" defaultConfig

  let intType := mkIntType defaultConfig

  let mathFunctionType := Json.mkObj [
    ("id", "mathematical_function"),
    ("sub", Json.arr #[
      Json.mkObj [
        ("id", ""),
        ("sub", Json.arr #[intType, intType, intType])
      ],
      Json.mkObj [("id", "bool")]
    ])
  ]

  let parameterTuple := Json.mkObj [
    ("id", "tuple"),
    ("namedSub", Json.mkObj [("type", Json.mkObj [("id", "tuple")])]),
    ("sub", Json.arr #[
      mkSymbol "__CPROVER_return_value" intType,
      mkSymbol s!"{func.name}::x" intType,
      mkSymbol s!"{func.name}::y" intType
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
      mkParameter "x" func.name "1" defaultConfig,
      mkParameter "y" func.name "1" defaultConfig
    ])
  ]

  let contractType := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation "from_andrew.c" "" "1" defaultConfig),
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
      ("return_type", intType)
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
    ("sub", Json.arr (func.inputs.map (λ i => mkParameter i.fst func.name "1" defaultConfig)).toArray)
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
      | .fvar "z" _ => mkLvalueSymbol s!"{loc.functionName}::1::z" loc.lineNum loc.functionName defaultConfig
      | .fvar varName _ => mkLvalueSymbol s!"{loc.functionName}::{varName}" loc.lineNum loc.functionName defaultConfig
      | _ => exprToJson left loc
    let rightJson := match right with
      | .fvar varName _ => mkLvalueSymbol s!"{loc.functionName}::{varName}" loc.lineNum loc.functionName defaultConfig
      | .const value _ => mkConstant value "10" (mkSourceLocation "from_andrew.c" loc.functionName loc.lineNum defaultConfig) defaultConfig
      | _ => exprToJson right loc
    mkBinaryOp (opToStr op) loc.lineNum loc.functionName leftJson rightJson defaultConfig
  | .const n _ =>
    mkConstant n "10" (mkSourceLocation "from_andrew.c" loc.functionName "14" defaultConfig) defaultConfig
  | _ => panic! "Unimplemented"

def cmdToJson (e : Strata.C_Simp.Command) (loc: SourceLoc) : Json :=
  match e with
  | .init name _ _ _ =>
    mkCodeBlock "decl" "5" loc.functionName (config := defaultConfig) #[
      Json.mkObj [
        ("id", "symbol"),
        ("namedSub", Json.mkObj [
          ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "5" defaultConfig),
          ("identifier", Json.mkObj [("id", s!"{loc.functionName}::1::{name}")]),
          ("type", mkIntType defaultConfig)
        ])
      ]
    ]
  | .set ("return") _ _ => returnStmt loc.functionName
  | .set name expr _ =>
    let exprLoc : SourceLoc := { functionName := loc.functionName, lineNum := "6" }
    mkCodeBlock "expression" "6" loc.functionName (config := defaultConfig) #[
      mkSideEffect "assign" "6" loc.functionName (mkIntType defaultConfig) (config := defaultConfig) #[
        mkLvalueSymbol s!"{loc.functionName}::1::{name}" "6" loc.functionName defaultConfig,
        exprToJson expr exprLoc
      ]
    ]
  | .assert label expr _ =>
    let exprLoc : SourceLoc := { functionName := loc.functionName, lineNum := "7" }
    mkCodeBlock "expression" "7" loc.functionName (config := defaultConfig) #[
      mkSideEffect "function_call" "7" loc.functionName (config := defaultConfig)
        (Json.mkObj [
          ("id", "empty"),
          ("namedSub", Json.mkObj [
            ("#source_location", builtinSourceLocation defaultConfig)
          ])
        ]) #[
        Json.mkObj [
          ("id", "symbol"),
          ("namedSub", Json.mkObj [
            ("#lvalue", Json.mkObj [("id", "1")]),
            ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "7" (config := defaultConfig)),
            ("identifier", Json.mkObj [("id", "__CPROVER_assert")]),
            ("type", mkBuiltinFunction "__CPROVER_assert" (config := defaultConfig)
                      #[mkAssertParam (config := defaultConfig), mkStringParam (config := defaultConfig)])
          ])
        ],
        Json.mkObj [
          ("id", "arguments"),
          ("sub", Json.arr #[
            exprToJson expr exprLoc,
            mkStringConstant label "7" loc.functionName (config := defaultConfig)
          ])
        ]
      ]
    ]
  | .assume _ expr _ =>
    let exprLoc : SourceLoc := { functionName := loc.functionName, lineNum := "13" }
    mkCodeBlock "expression" "13" loc.functionName (config := defaultConfig) #[
      mkSideEffect "function_call" "13" loc.functionName (config := defaultConfig)
        (Json.mkObj [
          ("id", "empty"),
          ("namedSub", Json.mkObj [
            ("#source_location", builtinSourceLocation (config := defaultConfig))
          ])
        ]) #[
        Json.mkObj [
          ("id", "symbol"),
          ("namedSub", Json.mkObj [
            ("#lvalue", Json.mkObj [("id", "1")]),
            ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "13" (config := defaultConfig)),
            ("identifier", Json.mkObj [("id", "__CPROVER_assume")]),
            ("type", mkBuiltinFunction "__CPROVER_assume" #[mkAssumeParam (config := defaultConfig)] (config := defaultConfig))
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
      ("#end_location", mkSourceLocation "from_andrew.c" loc.functionName "10" (config := defaultConfig)),
      ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "8" (config := defaultConfig)),
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
        ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "8" (config := defaultConfig)),
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

def createImplementationSymbolFromAST (func : Strata.C_Simp.Function) : CProverJson.CBMCSymbol :=
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
      ("#source_location", mkSourceLocation "from_andrew.c" "" "1" (config := defaultConfig)),
      ("parameters", parameters),
      ("return_type", mkIntType (config := defaultConfig))
    ])
  ]

  -- For now, keep the hardcoded implementation but use function name from AST
  let loc : SourceLoc := { functionName := func.name, lineNum := "1" }
  let stmtJsons := (func.body.map (stmtToJson · loc)) --++ [returnStmt]

  let implValue := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#end_location", mkSourceLocation "from_andrew.c" func.name "15" (config := defaultConfig)),
      ("#source_location", mkSourceLocation "from_andrew.c" func.name "4" (config := defaultConfig)),
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
  let zSymbol := createLocalSymbol "z" "simpleTest" defaultConfig

  -- Build symbol map
  let mut m : Map String CProverJson.CBMCSymbol := Map.empty
  m := m.insert s!"contract::{myFunc.name}" contractSymbol
  m := m.insert myFunc.name implSymbol

  -- Add parameter symbols
  for paramName in paramNames do
    let paramSymbol := createParameterSymbol paramName "simpleTest" defaultConfig
    m := m.insert s!"{myFunc.name}::{paramName}" paramSymbol

  -- Add local variable
  m := m.insert s!"{myFunc.name}::1::z" zSymbol

  toString (toJson m)

end
