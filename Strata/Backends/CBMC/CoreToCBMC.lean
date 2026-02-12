/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Data.Json
import Strata.Languages.Core.Env
import Strata.Languages.Core.DDMTransform.Parse
import Strata.Languages.Core.DDMTransform.Translate
import Strata.DL.Util.Map
import Strata.Languages.Core.Core
import Strata.Backends.CBMC.Common
import Strata.Util.Tactics

open Lean
open Strata.CBMC

namespace Core
-- Our test program
def SimpleTestEnv :=
#strata
program Core;

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

open Core in
def SimpleTestEnvAST := Strata.TransM.run Inhabited.default (Strata.translateProgram (SimpleTestEnv))

def myProc : Core.Procedure := match SimpleTestEnvAST.fst.decls.head!.getProc? with
  | .some p => p
  | .none => panic! "Expected procedure"


class IdentToStr (I : Type) where
  toStr : I → String

instance : IdentToStr CoreIdent where
  toStr id := id.toPretty

instance : IdentToStr String where
  toStr := id

class HasLExpr (P : Imperative.PureExpr) (I : Lambda.LExprParams) where
  expr_eq : P.Expr = Lambda.LExpr I.mono

instance : HasLExpr Core.Expression CoreLParams where
  expr_eq := rfl

def exprToJson (I : Lambda.LExprParams) [IdentToStr (Lambda.Identifier I.IDMeta)] (e : Lambda.LExpr I.mono) (loc: SourceLoc) : Json :=
  match e with
  | .app _ (.app _ (.op _ op _) left) right =>
    let leftJson := match left with
      | .fvar _ varName _ =>
        if IdentToStr.toStr varName == "z" then
          mkLvalueSymbol s!"{loc.functionName}::1::z" loc.lineNum loc.functionName
        else
          mkLvalueSymbol s!"{loc.functionName}::{IdentToStr.toStr varName}" loc.lineNum loc.functionName
      | _ => exprToJson (I:=I) left loc
    let rightJson := match right with
      | .fvar _ varName _ => mkLvalueSymbol s!"{loc.functionName}::{IdentToStr.toStr varName}" loc.lineNum loc.functionName
      | .intConst _ value => mkConstant (toString value) "10" (mkSourceLocation "ex_prog.c" loc.functionName loc.lineNum)
      | _ => exprToJson (I:=I) right loc
    mkBinaryOp (opToStr (IdentToStr.toStr op)) loc.lineNum loc.functionName leftJson rightJson
  | .true _ => mkConstantTrue (mkSourceLocation "ex_prog.c" loc.functionName "3")
  | .intConst _ n =>
    mkConstant (toString n) "10" (mkSourceLocation "ex_prog.c" loc.functionName "14")
  | .fvar _ name _ =>
    mkLvalueSymbol s!"{loc.functionName}::{IdentToStr.toStr name}" loc.lineNum loc.functionName
  | _ => panic! "Unimplemented"

def cmdToJson (e : Core.Command) (loc: SourceLoc) : Json :=
  match e with
  | .call _ _ _ _ => panic! "Not supported"
  | .cmd c =>
    match c with
    | .init name _ _ _ =>
      mkCodeBlock "decl" "5" loc.functionName #[
        Json.mkObj [
          ("id", "symbol"),
          ("namedSub", Json.mkObj [
            ("#source_location", mkSourceLocation "ex_prog.c" loc.functionName "5"),
            ("identifier", Json.mkObj [("id", s!"{loc.functionName}::1::{name.toPretty}")]),
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
          mkLvalueSymbol s!"{loc.functionName}::1::{name.toPretty}" "6" loc.functionName,
          exprToJson (I:=CoreLParams) expr exprLoc
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
              ("#source_location", mkSourceLocation "ex_prog.c" loc.functionName "7"),
              ("identifier", Json.mkObj [("id", "__CPROVER_assert")]),
              ("type", mkBuiltinFunction "__CPROVER_assert" #[mkAssertParam, mkStringParam])
            ])
          ],
          Json.mkObj [
            ("id", "arguments"),
            ("sub", Json.arr #[
              exprToJson (I:=CoreLParams) expr exprLoc,
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
              ("#source_location", mkSourceLocation "ex_prog.c" loc.functionName "13"),
              ("identifier", Json.mkObj [("id", "__CPROVER_assume")]),
              ("type", mkBuiltinFunction "__CPROVER_assume" #[mkAssumeParam])
            ])
          ],
          Json.mkObj [
            ("id", "arguments"),
            ("sub", Json.arr #[
              exprToJson (I:=CoreLParams) expr exprLoc
            ])
          ]
        ]
      ]
    | .cover _ _ md =>
       panic! s!"{Imperative.MetaData.formatFileRangeD md}\
                  cover unimplemented"
    | .havoc _ md =>
       panic! s!"{Imperative.MetaData.formatFileRangeD md}\
                  havoc unimplemented"

mutual
def blockToJson {P : Imperative.PureExpr} (I : Lambda.LExprParams) [IdentToStr (Lambda.Identifier I.IDMeta)] [HasLExpr P I]
  (b: Imperative.Block P Command) (loc: SourceLoc) : Json :=
  Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#end_location", mkSourceLocation "ex_prog.c" loc.functionName "10"),
      ("#source_location", mkSourceLocation "ex_prog.c" loc.functionName "8"),
      ("statement", Json.mkObj [("id", "block")]),
      ("type", emptyType)
    ]),
    ("sub", Json.arr (b.map (stmtToJson (I:=I) · loc)).toArray)
  ]
  termination_by (Imperative.Block.sizeOf b)
  decreasing_by term_by_mem [Stmt, Imperative.sizeOf_stmt_in_block]

def stmtToJson {P : Imperative.PureExpr} (I : Lambda.LExprParams) [IdentToStr (Lambda.Identifier I.IDMeta)] [HasLExpr P I]
  (e : Imperative.Stmt P Command) (loc: SourceLoc) : Json :=
  match e with
  | .cmd cmd => cmdToJson cmd loc
  | .ite cond thenb elseb _ =>
    let converted_cond : Lambda.LExpr I.mono := @HasLExpr.expr_eq P (I:=I) _ ▸ cond
    Json.mkObj [
      ("id", "code"),
      ("namedSub", Json.mkObj [
        ("#source_location", mkSourceLocation "ex_prog.c" loc.functionName "8"),
        ("statement", Json.mkObj [("id", "ifthenelse")]),
        ("type", emptyType)
      ]),
      ("sub", Json.arr #[
        exprToJson (I:=I) converted_cond loc,
        blockToJson (I:=I) thenb loc,
        blockToJson (I:=I) elseb loc,
      ])
    ]
  | _ => panic! "Unimplemented"
  termination_by (Imperative.Stmt.sizeOf e)
  decreasing_by all_goals term_by_mem
end

def listToExpr (l: ListMap CoreLabel Core.Procedure.Check) : Core.Expression.Expr :=
  match l with
  | _ => .true ()

def createContractSymbolFromAST (func : Core.Procedure) : CBMCSymbol :=
  let location : Location := {
    id := "",
    namedSub := some (Json.mkObj [
      ("file", Json.mkObj [("id", "ex_prog.c")]),
      ("function", Json.mkObj [("id", "")]),
      ("line", Json.mkObj [("id", "1")]),
      ("working_directory", Json.mkObj [("id", "/tmp")])
    ])
  }

  let sourceLocation := mkSourceLocation "ex_prog.c" (func.header.name.toPretty) "2"
  let ensuresSourceLocation := mkSourceLocation "ex_prog.c" (func.header.name.toPretty) "3"

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
      mkSymbol s!"{func.header.name.toPretty}::x" mkIntType,
      mkSymbol s!"{func.header.name.toPretty}::y" mkIntType
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
      exprToJson (I:=CoreLParams) (listToExpr func.spec.preconditions) {functionName := func.header.name.toPretty, lineNum := "2"}
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
      exprToJson (I:=CoreLParams) (listToExpr func.spec.postconditions) {functionName := func.header.name.toPretty, lineNum := "2"}
    ])
  ]

  let parameters := Json.mkObj [
    ("id", ""),
    ("sub", Json.arr #[
      mkParameter "x" (func.header.name.toPretty) "1",
      mkParameter "y" (func.header.name.toPretty) "1"
    ])
  ]

  let contractType := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation "ex_prog.c" "" "1"),
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
    baseName := (func.header.name.toPretty),
    isProperty := true,
    location := location,
    mode := "C",
    module := "ex_prog",
    name := s!"contract::{(func.header.name.toPretty)}",
    prettyName := (func.header.name.toPretty),
    prettyType := "signed int (signed int x, signed int y)",
    type := contractType,
    value := Json.mkObj [("id", "nil")]
  }

def getParamJson(func: Core.Procedure) : Json :=
  Json.mkObj [
    ("id", ""),
    ("sub", Json.arr (func.header.inputs.map (λ i => mkParameter i.fst.name (func.header.name.toPretty) "1")).toArray)
  ]


def createImplementationSymbolFromAST (func : Core.Procedure) : CBMCSymbol :=
  let location : Location := {
    namedSub := some (Json.mkObj [
      ("file", Json.mkObj [("id", "ex_prog.c")]),
      ("function", Json.mkObj [("id", "")]),
      ("line", Json.mkObj [("id", "1")]),
      ("working_directory", Json.mkObj [("id", "/tmp")])
    ])
  }

  let parameters := getParamJson func

  let implType := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#source_location", mkSourceLocation "ex_prog.c" "" "1"),
      ("parameters", parameters),
      ("return_type", mkIntType)
    ])
  ]

  -- For now, keep the hardcoded implementation but use function name from AST
  let loc : SourceLoc := { functionName := (func.header.name.toPretty), lineNum := "1" }
  let stmtJsons := (func.body.map (stmtToJson (I:=CoreLParams) · loc))

  let implValue := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj [
      ("#end_location", mkSourceLocation "ex_prog.c" (func.header.name.toPretty) "15"),
      ("#source_location", mkSourceLocation "ex_prog.c" (func.header.name.toPretty) "4"),
      ("statement", Json.mkObj [("id", "block")]),
      ("type", emptyType)
    ]),
    ("sub", Json.arr stmtJsons.toArray)
  ]

  {
    baseName := (func.header.name.toPretty),
    isLvalue := true,
    location := location,
    mode := "C",
    module := "ex_prog",
    name := (func.header.name.toPretty),
    prettyName := (func.header.name.toPretty),
    prettyType := s!"signed int (signed int {String.intercalate ", signed int " (func.header.inputs.keys.map (λ p => p.name))})",
    prettyValue := "{\n  signed int z;\n  z = x;\n  z = z + 1;\n  return z;\n}",
    type := implType,
    value := implValue
  }

def testSymbols (proc: Core.Procedure) : String := Id.run do
  -- Generate symbols using AST data
  let contractSymbol := createContractSymbolFromAST proc
  let implSymbol := createImplementationSymbolFromAST proc

  -- Get parameter names from AST
  let paramNames : List String := proc.header.inputs.keys.map (λ p => p.name)

  -- Hardcode local variable for now
  let zSymbol := createLocalSymbol "z" proc.header.name.toPretty

  -- Build symbol map
  let mut m : Map String CBMCSymbol := Map.empty
  m := m.insert s!"contract::{proc.header.name.name}" contractSymbol
  m := m.insert proc.header.name.name implSymbol

  -- Add parameter symbols
  for paramName in paramNames do
    let paramSymbol := createParameterSymbol paramName proc.header.name.toPretty
    m := m.insert s!"{proc.header.name.name}::{paramName}" paramSymbol

  -- Add local variable
  m := m.insert s!"{proc.header.name.name}::1::z" zSymbol
  toString (toJson m)

end Core
