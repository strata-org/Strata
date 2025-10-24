/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Data.Json
import Strata.DL.Util.Map
import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify
import Strata.Backends.CBMC.Common

open Lean
open Strata.CBMC

namespace CSimp

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

-- Convert LExpr to CBMC JSON format for contracts
def lexprToCBMC (expr : Strata.C_Simp.Expression.Expr) (functionName : String) : Json :=
  let cfg := CBMCConfig.empty
  match expr with
  | .app (.app (.op op _) (.fvar varName _)) (.const value _) =>
    mkBinaryOp (opToStr op.name) "2" functionName (config := cfg)
      (Json.mkObj [
        ("id", "symbol"),
        ("namedSub", Json.mkObj [
          ("#base_name", Json.mkObj [("id", varName.name)]),
          ("#id_class", Json.mkObj [("id", "1")]),
          ("#lvalue", Json.mkObj [("id", "1")]),
          ("#source_location", mkSourceLocation "from_andrew.c" functionName "2" cfg),
          ("identifier", Json.mkObj [("id", s!"{functionName}::{varName}")]),
          ("type", mkIntType cfg)
        ])
      ])
      (mkConstant value "10" (mkSourceLocation "from_andrew.c" functionName "2" cfg) cfg)
  | .const "true" _ =>
    Json.mkObj [
      ("id", "notequal"),
      ("namedSub", Json.mkObj [
        ("#source_location", mkSourceLocation "from_andrew.c" functionName "3" cfg),
        ("type", Json.mkObj [("id", "bool")])
      ]),
      ("sub", Json.arr #[
        mkConstant "1" "10" (mkSourceLocation "from_andrew.c" functionName "3" cfg) cfg,
        Json.mkObj [
          ("id", "constant"),
          ("namedSub", Json.mkObj [
            ("type", mkIntType cfg),
            ("value", Json.mkObj [("id", "0")])
          ])
        ]
      ])
    ]
  | _ => panic! "Unimplemented"

def createContractSymbolFromAST (func : Strata.C_Simp.Function) : CBMCSymbol :=
  let cfg := CBMCConfig.empty
  let location : Location := {
    id := "",
    namedSub := some (Json.mkObj [
      ("file", Json.mkObj [("id", "from_andrew.c")]),
      ("function", Json.mkObj [("id", "")]),
      ("line", Json.mkObj [("id", "1")]),
      ("working_directory", Json.mkObj [("id", "/home/ub-backup/tautschn/cbmc-github.git")])
    ])
  }

  let sourceLocation := mkSourceLocation "from_andrew.c" func.name.name "2"
  let ensuresSourceLocation := mkSourceLocation "from_andrew.c" func.name.name "3"

  let mathFunctionType := Json.mkObj [
    ("id", "mathematical_function"),
    ("sub", Json.arr #[
      Json.mkObj [
        ("id", ""),
        ("sub", Json.arr #[mkIntType cfg, mkIntType cfg, mkIntType cfg])
      ],
      Json.mkObj [("id", "bool")]
    ])
  ]

  let parameterTuple := Json.mkObj [
    ("id", "tuple"),
    ("namedSub", Json.mkObj [("type", Json.mkObj [("id", "tuple")])]),
    ("sub", Json.arr #[
      mkSymbol "__CPROVER_return_value" (mkIntType cfg),
      mkSymbol s!"{func.name}::x" (mkIntType cfg),
      mkSymbol s!"{func.name}::y" (mkIntType cfg)
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
      lexprToCBMC func.pre func.name.name
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
      lexprToCBMC func.post func.name.name
    ])
  ]

  let parameters := Json.mkObj [
    ("id", ""),
    ("sub", Json.arr #[
      mkParameter "x" func.name.name "1" cfg,
      mkParameter "y" func.name.name "1" cfg
    ])
  ]

  let contractType := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation "from_andrew.c" "" "1" cfg),
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
      ("return_type", mkIntType cfg)
    ])
  ]

  {
    baseName := func.name.name,
    isProperty := true,
    location := location,
    mode := "C",
    module := "from_andrew",
    name := s!"contract::{func.name}",
    prettyName := func.name.name,
    prettyType := "signed int (signed int x, signed int y)",
    type := contractType,
    value := Json.mkObj [("id", "nil")]
  }

def getParamJson(func: Strata.C_Simp.Function) : Json :=
  let cfg := CBMCConfig.empty
  Json.mkObj [
    ("id", ""),
    ("sub", Json.arr (func.inputs.map (λ i => mkParameter i.fst.name func.name.name "1" cfg)).toArray)
  ]

def exprToJson (e : Strata.C_Simp.Expression.Expr) (loc: SourceLoc) : Json :=
  let cfg := CBMCConfig.empty
  match e with
  | .app (.app (.op op _) left) right =>
    let leftJson := match left with
      | .fvar "z" _ => mkLvalueSymbol s!"{loc.functionName}::1::z" loc.lineNum loc.functionName cfg
      | .fvar varName _ => mkLvalueSymbol s!"{loc.functionName}::{varName}" loc.lineNum loc.functionName cfg
      | _ => exprToJson left loc
    let rightJson := match right with
      | .fvar varName _ => mkLvalueSymbol s!"{loc.functionName}::{varName}" loc.lineNum loc.functionName cfg
      | .const value _ => mkConstant value "10" (mkSourceLocation "from_andrew.c" loc.functionName loc.lineNum cfg) cfg
      | _ => exprToJson right loc
    mkBinaryOp (opToStr op.name) loc.lineNum loc.functionName leftJson rightJson cfg
  | .const n _ =>
    mkConstant n "10" (mkSourceLocation "from_andrew.c" loc.functionName "14" cfg) cfg
  | _ => panic! "Unimplemented"

def cmdToJson (e : Strata.C_Simp.Command) (loc: SourceLoc) : Json :=
  let cfg := CBMCConfig.empty
  match e with
  | .init name _ _ _ =>
    mkCodeBlock "decl" "5" loc.functionName (config := cfg) #[
      Json.mkObj [
        ("id", "symbol"),
        ("namedSub", Json.mkObj [
          ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "5" cfg),
          ("identifier", Json.mkObj [("id", s!"{loc.functionName}::1::{name}")]),
          ("type", mkIntType cfg)
        ])
      ]
    ]
  | .set ("return") _ _ => returnStmt loc.functionName
  | .set name expr _ =>
    let exprLoc : SourceLoc := { functionName := loc.functionName, lineNum := "6" }
    mkCodeBlock "expression" "6" loc.functionName (config := cfg) #[
      mkSideEffect "assign" "6" loc.functionName (mkIntType cfg) (config := cfg) #[
        mkLvalueSymbol s!"{loc.functionName}::1::{name}" "6" loc.functionName cfg,
        exprToJson expr exprLoc
      ]
    ]
  | .assert label expr _ =>
    let exprLoc : SourceLoc := { functionName := loc.functionName, lineNum := "7" }
    mkCodeBlock "expression" "7" loc.functionName (config := cfg) #[
      mkSideEffect "function_call" "7" loc.functionName (config := cfg)
        (Json.mkObj [
          ("id", "empty"),
          ("namedSub", Json.mkObj [
            ("#source_location", builtinSourceLocation cfg)
          ])
        ]) #[
        Json.mkObj [
          ("id", "symbol"),
          ("namedSub", Json.mkObj [
            ("#lvalue", Json.mkObj [("id", "1")]),
            ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "7" cfg),
            ("identifier", Json.mkObj [("id", "__CPROVER_assert")]),
            ("type", mkBuiltinFunction "__CPROVER_assert" #[mkAssertParam cfg, mkStringParam cfg] cfg)
          ])
        ],
        Json.mkObj [
          ("id", "arguments"),
          ("sub", Json.arr #[
            exprToJson expr exprLoc,
            mkStringConstant label "7" loc.functionName cfg
          ])
        ]
      ]
    ]
  | .assume _ expr _ =>
    let exprLoc : SourceLoc := { functionName := loc.functionName, lineNum := "13" }
    mkCodeBlock "expression" "13" loc.functionName (config := cfg) #[
      mkSideEffect "function_call" "13" loc.functionName (config := cfg)
        (Json.mkObj [
          ("id", "empty"),
          ("namedSub", Json.mkObj [
            ("#source_location", builtinSourceLocation cfg)
          ])
        ]) #[
        Json.mkObj [
          ("id", "symbol"),
          ("namedSub", Json.mkObj [
            ("#lvalue", Json.mkObj [("id", "1")]),
            ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "13" cfg),
            ("identifier", Json.mkObj [("id", "__CPROVER_assume")]),
            ("type", mkBuiltinFunction "__CPROVER_assume" #[mkAssumeParam cfg] cfg)
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
  let cfg := CBMCConfig.empty
  Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#end_location", mkSourceLocation "from_andrew.c" loc.functionName "10" cfg),
      ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "8" cfg),
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
  let loc : SourceLoc := { functionName := func.name.name, lineNum := "1" }
  let stmtJsons := (func.body.map (stmtToJson · loc)) --++ [returnStmt]

  let implValue := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#end_location", mkSourceLocation "from_andrew.c" func.name.name "15"),
      ("#source_location", mkSourceLocation "from_andrew.c" func.name.name "4"),
      ("statement", Json.mkObj [("id", "block")]),
      ("type", emptyType)
    ]),
    ("sub", Json.arr stmtJsons.toArray)
  ]

  {
    baseName := func.name.name,
    isLvalue := true,
    location := location,
    mode := "C",
    module := "from_andrew",
    name := func.name.name,
    prettyName := func.name.name,
    prettyType := s!"signed int (signed int {String.intercalate ", signed int " (func.inputs.keys.map Lambda.Identifier.name)})",
    prettyValue := "{\n  signed int z;\n  z = x + y;\n  __CPROVER_assert(z > x, \"test_assert\");\n  if(z > 10)\n  {\n    z = z - 1;\n  }\n\n  else\n  {\n    z = z + 1;\n  }\n  __CPROVER_assume(z > 0);\n  return 0;\n}",
    type := implType,
    value := implValue
  }

def testSymbols (myFunc: Strata.C_Simp.Function) : String := Id.run do
  -- Generate symbols using AST data
  let contractSymbol := createContractSymbolFromAST myFunc
  let implSymbol := createImplementationSymbolFromAST myFunc

  -- Get parameter names from AST
  let paramNames := myFunc.inputs.keys

  -- Hardcode local variable for now
  let zSymbol := createLocalSymbol "z" myFunc.name.name

  -- Build symbol map
  let mut m : Map String CBMCSymbol := Map.empty
  m := m.insert s!"contract::{myFunc.name}" contractSymbol
  m := m.insert myFunc.name.name implSymbol

  -- Add parameter symbols
  for paramName in paramNames do
    let paramSymbol := createParameterSymbol paramName.name myFunc.name.name
    m := m.insert s!"{myFunc.name}::{paramName}" paramSymbol

  -- Add local variable
  m := m.insert s!"{myFunc.name}::1::z" zSymbol

  toString (toJson m)

end CSimp
