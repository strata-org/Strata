/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Data.Json
import Strata.Languages.Boogie.Env
import Strata.Languages.Boogie.DDMTransform.Parse
import Strata.Languages.Boogie.DDMTransform.Translate
import Strata.DL.Util.Map
import Strata.Languages.Boogie.Boogie
import Strata.Backends.CBMC.Common

open Lean
open Strata.CBMC

namespace Boogie
-- Our test program
def SimpleTestEnv :=
#strata
program Boogie;

procedure simpleTest(x : int, y : int) returns (ret : int)
spec {
  requires [x_positive]:    (x > 0);
}
{
  var z : int;
  z := x;
  //assume [foo]: z < 10;
  z := z + 1;
  ret := 0;
};
#end

open Boogie in
def SimpleTestEnvAST := Strata.TransM.run (Strata.translateProgram (SimpleTestEnv))

def myFunc : Boogie.Procedure := match SimpleTestEnvAST.fst.decls.head! with
  | .proc f => f
  | _ => panic! "Expected function"

def boogieIdentToStr (id: Boogie.BoogieIdent) : String :=
  id.snd

-- Convert LExpr to CBMC JSON format for contracts
def lexprToCBMC (expr : Boogie.Expression.Expr) (functionName : String) : Json :=
  match expr with
  | .app (.app (.op op _) (.fvar varName _)) (.const value _) =>
    mkBinaryOp (opToStr (boogieIdentToStr op)) "2" functionName
      (Json.mkObj [
        ("id", "symbol"),
        ("namedSub", Json.mkObj [
          ("#base_name", Json.mkObj [("id", (boogieIdentToStr varName))]),
          ("#id_class", Json.mkObj [("id", "1")]),
          ("#lvalue", Json.mkObj [("id", "1")]),
          ("#source_location", mkSourceLocation "from_andrew.c" functionName "2"),
          ("identifier", Json.mkObj [("id", s!"{functionName}::{boogieIdentToStr varName}")]),
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

def listToExpr (l: ListMap BoogieLabel Boogie.Procedure.Check) : Boogie.Expression.Expr :=
  match l with
  | _ => .const "true" none

def createContractSymbolFromAST (func : Boogie.Procedure) : CBMCSymbol :=
  let location : Location := {
    id := "",
    namedSub := some (Json.mkObj [
      ("file", Json.mkObj [("id", "from_andrew.c")]),
      ("function", Json.mkObj [("id", "")]),
      ("line", Json.mkObj [("id", "1")]),
      ("working_directory", Json.mkObj [("id", "/home/ub-backup/tautschn/cbmc-github.git")])
    ])
  }

  let sourceLocation := mkSourceLocation "from_andrew.c" (boogieIdentToStr func.header.name) "2"
  let ensuresSourceLocation := mkSourceLocation "from_andrew.c" (boogieIdentToStr func.header.name) "3"

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
      mkSymbol s!"{boogieIdentToStr func.header.name}::x" mkIntType,
      mkSymbol s!"{boogieIdentToStr func.header.name}::y" mkIntType
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
      lexprToCBMC (listToExpr func.spec.preconditions) (boogieIdentToStr func.header.name)
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
      lexprToCBMC (listToExpr func.spec.postconditions) (boogieIdentToStr func.header.name)
    ])
  ]

  let parameters := Json.mkObj [
    ("id", ""),
    ("sub", Json.arr #[
      mkParameter "x" (boogieIdentToStr func.header.name) "1",
      mkParameter "y" (boogieIdentToStr func.header.name) "1"
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
    baseName := (boogieIdentToStr func.header.name),
    isProperty := true,
    location := location,
    mode := "C",
    module := "from_andrew",
    name := s!"contract::{(boogieIdentToStr func.header.name)}",
    prettyName := (boogieIdentToStr func.header.name),
    prettyType := "signed int (signed int x, signed int y)",
    type := contractType,
    value := Json.mkObj [("id", "nil")]
  }

def getParamJson(func: Boogie.Procedure) : Json :=
  Json.mkObj [
    ("id", ""),
    ("sub", Json.arr (func.header.inputs.map (λ i => mkParameter i.fst.snd (boogieIdentToStr func.header.name) "1")).toArray)
  ]

def exprToJson (e : Boogie.Expression.Expr) (loc: SourceLoc) : Json :=
  match e with
  | .app (.app (.op op _) left) right =>
    let leftJson := match left with
      | .fvar "z" _ => mkLvalueSymbol s!"{loc.functionName}::1::z" loc.lineNum loc.functionName
      | .fvar varName _ => mkLvalueSymbol s!"{loc.functionName}::{boogieIdentToStr varName}" loc.lineNum loc.functionName
      | _ => exprToJson left loc
    let rightJson := match right with
      | .fvar varName _ => mkLvalueSymbol s!"{loc.functionName}::{boogieIdentToStr varName}" loc.lineNum loc.functionName
      | .const value _ => mkConstant value "10" (mkSourceLocation "from_andrew.c" loc.functionName loc.lineNum)
      | _ => exprToJson right loc
    mkBinaryOp (opToStr (boogieIdentToStr op)) loc.lineNum loc.functionName leftJson rightJson
  | .const n _ =>
    mkConstant n "10" (mkSourceLocation "from_andrew.c" loc.functionName "14")
  | .fvar name _ =>
    mkLvalueSymbol s!"{loc.functionName}::{boogieIdentToStr name}" loc.lineNum loc.functionName
  | _ => panic! "Unimplemented"

def cmdToJson (e : Boogie.Command) (loc: SourceLoc) : Json :=
  match e with
  | .call _ _ _ _ => panic! "Not supported"
  | .cmd c =>
    match c with
    | .init name _ _ _ =>
      mkCodeBlock "decl" "5" loc.functionName #[
        Json.mkObj [
          ("id", "symbol"),
          ("namedSub", Json.mkObj [
            ("#source_location", mkSourceLocation "from_andrew.c" loc.functionName "5"),
            ("identifier", Json.mkObj [("id", s!"{loc.functionName}::1::{boogieIdentToStr name}")]),
            ("type", mkIntType)
          ])
        ]
      ]
    | .set ("ret") _ _ =>
      returnStmt loc.functionName
    | .set name expr _ =>
      let exprLoc : SourceLoc := { functionName := loc.functionName, lineNum := "6" }
      mkCodeBlock "expression" "6" loc.functionName #[
        mkSideEffect "assign" "6" loc.functionName mkIntType #[
          mkLvalueSymbol s!"{loc.functionName}::1::{boogieIdentToStr name}" "6" loc.functionName,
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
partial def blockToJson (b: Imperative.Block Boogie.Expression Boogie.Command) (loc: SourceLoc) : Json :=
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

partial def stmtToJson (e : Boogie.Statement) (loc: SourceLoc) : Json :=
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

def createImplementationSymbolFromAST (func : Boogie.Procedure) : CBMCSymbol :=
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
  let loc : SourceLoc := { functionName := (boogieIdentToStr func.header.name), lineNum := "1" }
  let stmtJsons := (func.body.map (stmtToJson · loc)) --++ [returnStmt]

  let implValue := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#end_location", mkSourceLocation "from_andrew.c" (boogieIdentToStr func.header.name) "15"),
      ("#source_location", mkSourceLocation "from_andrew.c" (boogieIdentToStr func.header.name) "4"),
      ("statement", Json.mkObj [("id", "block")]),
      ("type", emptyType)
    ]),
    ("sub", Json.arr stmtJsons.toArray)
  ]

  {
    baseName := (boogieIdentToStr func.header.name),
    isLvalue := true,
    location := location,
    mode := "C",
    module := "from_andrew",
    name := (boogieIdentToStr func.header.name),
    prettyName := (boogieIdentToStr func.header.name),
    prettyType := s!"signed int (signed int {String.intercalate ", signed int " (func.header.inputs.keys.map (λ p => p.snd))})",
    prettyValue := "{\n  signed int z;\n  z = x;\n  z = z + 1;\n  return z;\n}",
    type := implType,
    value := implValue
  }

def testSymbols (myFunc: Boogie.Procedure) : String := Id.run do
  -- Generate symbols using AST data
  let contractSymbol := createContractSymbolFromAST myFunc
  let implSymbol := createImplementationSymbolFromAST myFunc

  -- Get parameter names from AST
  let paramNames : List String := myFunc.header.inputs.keys.map (λ p => p.snd)

  -- Hardcode local variable for now
  let zSymbol := createLocalSymbol "z"

  -- Build symbol map
  let mut m : Map String CBMCSymbol := Map.empty
  m := m.insert s!"contract::{myFunc.header.name.snd}" contractSymbol
  m := m.insert myFunc.header.name.snd implSymbol

  -- Add parameter symbols
  for paramName in paramNames do
    let paramSymbol := createParameterSymbol paramName
    m := m.insert s!"{myFunc.header.name.snd}::{paramName}" paramSymbol

  -- Add local variable
  m := m.insert s!"{myFunc.header.name.snd}::1::z" zSymbol
  toString (toJson m)

end Boogie
