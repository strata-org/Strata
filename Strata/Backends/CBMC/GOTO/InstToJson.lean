/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.Common
public import Strata.Util.Json
public import Strata.Backends.CBMC.GOTO.Program

import Strata.Util.Tactics

public section

namespace CProverGOTO
open Lean
open Strata.CBMC

-------------------------------------------------------------------------------

/--
Convert SourceLocation to JSON.

NOTE: CBMC's `--show-goto-functions` renders source location using the named
field `sourceLocation`, which is different from `#source_location` rendered by
`--show-symbol-table`.
-/
def sourceLocationToJson (loc : SourceLocation) : String × Json :=
  ("sourceLocation",
  if loc == .nil then Json.mkObj [] else
  Json.mkObj [
    ("file", Json.str loc.file),
    ("function", Json.str loc.function),
    ("line", Json.str (toString loc.line)),
    ("workingDirectory", Json.str loc.workingDir),
    ("comment", Json.str loc.comment),
  ])

def mkSymbolWithSourceLocation (identifier : String) (symbolType : Json) (loc : SourceLocation) : Json :=
  let loc_obj := sourceLocationToJson loc
  Json.mkObj [
    ("id", "symbol"),
    ("namedSub", Json.mkObj [
      ("identifier", Json.mkObj [("id", identifier)]),
      ("type", symbolType)
    ]),
    loc_obj
  ]

/-- Convert `Ty` to JSON format -/
def tyToJson (ty : Ty) : Json :=
  match ty with
  | .Boolean => boolType
  | .Integer => integerType
  | .String => stringType
  | .Regex => regexType
  | .Real => realType
  | .Empty => emptyType
  | .SignedBV width => mkSignedBVType width
  | .UnsignedBV width => mkUnsignedBVType width
  | .StructTag name => Json.mkObj [
      ("id", "struct_tag"),
      ("namedSub", Json.mkObj [
        ("identifier", Json.mkObj [("id", s!"tag-{name}")])
      ])
    ]
  | .Array elemTy => Json.mkObj [
      ("id", "array"),
      ("sub", Json.arr #[tyToJson elemTy])
    ]
  | { id := .code, subtypes := retTy :: paramTypes, .. } =>
    let paramSubs := paramTypes.map fun pTy =>
      Json.mkObj [("namedSub", Json.mkObj [("type", tyToJson pTy)])]
    Json.mkObj [
      ("id", "code"),
      ("namedSub", Json.mkObj [
        ("parameters", Json.mkObj [("sub", Json.arr paramSubs.toArray)]),
        ("return_type", tyToJson retTy)])]
  | { id := .code, .. } => Json.mkObj [
      ("id", "code"),
      ("namedSub", Json.mkObj [
        ("parameters", Json.mkObj [("sub", Json.arr #[])]),
        ("return_type", Json.mkObj [("id", "empty")])])]
  | _ => Json.mkObj [("id", "unknown")]

/-- Convert `Expr` to JSON format -/
def exprToJson (expr : Expr) : Except String Json := do
  let srcField := sourceLocationToJson expr.sourceLoc
  let mkOpJson (opStr : String) : Except String Json := do
    let subs ← expr.operands.mapM exprToJson
    return Json.mkObj [
      ("id", opStr),
      ("namedSub", Json.mkObj [("type", tyToJson expr.type)]),
      ("sub", Json.arr subs.toArray),
      srcField
    ]
  let exprObj ← match expr.id with
    | .nullary (.symbol name) => pure (mkSymbolWithSourceLocation name (tyToJson expr.type) expr.sourceLoc)
    | .nullary (.constant value) => do
      let value ← match expr.type.id with
        | .bitVector (.signedbv w) => bvToHex value w
        | .bitVector (.unsignedbv w) => bvToHex value w
        | _ => pure value
      pure (Json.mkObj [
        ("id", "constant"),
        ("namedSub", Json.mkObj [
          ("type", tyToJson expr.type),
          ("value", Json.mkObj [("id", value)])
        ]),
        srcField
      ])
    | .nullary (.nondet name) =>
      pure (Json.mkObj [
        ("id", "nondet"),
        ("namedSub", Json.mkObj [
          ("identifier", Json.mkObj [("id", name)]),
          ("type", tyToJson expr.type)
        ]),
        srcField
      ])
    | .unary op => mkOpJson (toString f!"{op}")
    | .binary op =>
      -- CBMC's binding_exprt expects op0 to be a tuple of bound variables
      match op with
      | .Forall | .Exists => do
        let opStr := toString f!"{op}"
        let subs ← expr.operands.mapM exprToJson
        let sub0 := Json.mkObj [
          ("id", "tuple"),
          ("namedSub", Json.mkObj [("type", Json.mkObj [("id", "tuple")])]),
          ("sub", Json.arr #[subs[0]!])
        ]
        pure (Json.mkObj [
          ("id", opStr),
          ("namedSub", Json.mkObj [("type", tyToJson expr.type)]),
          ("sub", Json.arr #[sub0, subs[1]!]),
          srcField
        ])
      | _ => mkOpJson (toString f!"{op}")
    | .multiary op => mkOpJson (toString f!"{op}")
    | .ternary op => mkOpJson (toString f!"{op}")
    | .side_effect effect => do
      let effect_str := toString f!"{effect}"
      let subs ← expr.operands.mapM exprToJson
      pure (Json.mkObj [
        ("id", "side_effect"),
        ("namedSub", Json.mkObj [
          ("statement", Json.mkObj [("id", effect_str)]),
          ("type", tyToJson expr.type)
        ]),
        ("sub", Json.arr subs.toArray),
        srcField
      ])
    | .functionApplication name => do
      let domainTypes := expr.operands.map (fun op => tyToJson op.type)
      let mathFnType := Json.mkObj [
        ("id", "mathematical_function"),
        ("sub", Json.arr (#[
          Json.mkObj [("id", ""), ("sub", Json.arr domainTypes.toArray)],
          tyToJson expr.type
        ]))
      ]
      let fnSymbol := mkSymbolWithSourceLocation name mathFnType expr.sourceLoc
      let argsSubs ← expr.operands.mapM exprToJson
      let argsTuple := Json.mkObj [
        ("id", "tuple"),
        ("sub", Json.arr argsSubs.toArray)
      ]
      pure (Json.mkObj [
        ("id", "function_application"),
        ("namedSub", Json.mkObj [("type", tyToJson expr.type)]),
        ("sub", Json.arr #[fnSymbol, argsTuple]),
        srcField
      ])
    | _ => throw s!"[exprToJson] Unsupported expr: {format expr}"
  return exprObj
  termination_by (SizeOf.sizeOf expr)
  decreasing_by all_goals (cases expr; term_by_mem)

/-- Merge `Expr.namedFields` into the JSON produced by `exprToJson`. -/
partial def exprToJsonWithNamedFields (expr : Expr) : Except String Json := do
  let base ← exprToJson expr
  if expr.namedFields.isEmpty then return base
  else
    let extraFields ← expr.namedFields.mapM fun (k, v) => do return (k, ← exprToJsonWithNamedFields v)
    match base.getObjValD "namedSub" with
    | .obj nsm =>
      let merged := extraFields.foldl (fun acc (k, v) => acc.insert k v) nsm
      return base.setObjVal! "namedSub" (.obj merged)
    | _ => return base

/-- Convert `Code` to Json -/
def codeToJson (code : Code) : Except String Json := do
  let namedSub := ("namedSub",
        (Json.mkObj [
              ("statement", Json.mkObj [("id", s!"{format code.id}")]),
              ("type", Json.mkObj [("id", "empty")])]))
  let sourceField := sourceLocationToJson code.sourceLoc
  -- Function calls need special serialization for the arguments node
  let sub ← match code.id with
    | .function .functionCall => do
      let rec go (ops : List Expr) (i : Nat) : Except String (List Json) := do
        match ops with
        | [] => pure []
        | op :: rest => do
          let j ← if i == 2 then do
            let subs ← op.operands.mapM exprToJson
            pure (Json.mkObj [("id", "arguments"),
                        ("sub", Json.arr subs.toArray)])
          else exprToJson op
          let rest ← go rest (i + 1)
          pure (j :: rest)
      let arr ← go code.operands 0
      pure ("sub", Json.arr arr.toArray)
    | _ => do
      let subs ← code.operands.mapM exprToJson
      pure ("sub", Json.arr subs.toArray)
  return Json.mkObj ([("id", Json.str "code"), namedSub, sub, sourceField])

/--
Generate instruction string for display-/
def instructionToString (inst : Instruction) : String :=
  let comment := s!"        // {inst.locationNum} file {inst.sourceLoc.file} line {inst.sourceLoc.line} function {inst.sourceLoc.function}\n"
  let instrStr := match inst.type with
    | .ASSUME => s!"        {inst.type} {format inst.guard}\n"
    | .ASSERT => s!"        {inst.type} {format inst.guard}\n"
    | _ => s!"        {inst.type} {format inst.code}\n"
  comment ++ instrStr

/-- Main function to convert `Instruction` to JSON -/
def instructionToJson (inst : Instruction) : Except String Json := do
  let baseFields := [
    ("instruction", Json.str (instructionToString inst)),
    ("instructionId", Json.str (toString inst.type)),
    ("locationNumber", Json.num inst.locationNum)
  ]
  let guardField ← if inst.type == .GOTO || !Expr.beq inst.guard Expr.true then do
    pure [("guard", ← exprToJsonWithNamedFields inst.guard)]
  else pure []
  let codeField ← if inst.code == Code.skip then pure [] else do
    pure [("code", ← codeToJson inst.code)]
  let targetsField := match inst.type, inst.target with
    | .GOTO, some t => [("targets", Json.arr #[Json.num t])]
    | _, _ => []
  let sourceField :=  [sourceLocationToJson inst.sourceLoc]
  return Json.mkObj (baseFields ++ guardField ++ codeField ++ targetsField ++ sourceField)

def programToJson (name : String) (program : Program) : Except String Json := do
  let instJsons ← program.instructions.mapM instructionToJson
  let body :=
      Json.mkObj [
        ("instructions", Json.arr instJsons),
        ("parameterIdentifiers", Json.arr (program.parameterIdentifiers.map toJson)),
        ("isBodyAvailable", program.isBodyAvailable),
        ("isInternal", program.isInternal),
        ("name", name)
      ]
  return body

/-- Write a program to JSON file -/
def writeProgramToFile (fileName : String) (programName : String) (program : Program) : IO Unit := do
  let json ← IO.ofExcept (programToJson programName program)
  writeJsonFile fileName json

/-- Convert `Program`s to JSON containing GOTO functions -/
def programsToJson (programs : List (String × Program)) : Except String Json := do
  let jsons ← programs.mapM (fun (n, p) => programToJson n p)
  let instructions := Json.arr jsons.toArray
  let functions := Json.mkObj [("functions", instructions)]
  return functions

/-- Write programs to JSON file -/
def writeProgramsToFile (fileName : String) (programs : List (String × Program)) : IO Unit := do
  let json ← IO.ofExcept (programsToJson programs)
  writeJsonFile fileName json

-------------------------------------------------------------------------------

/-
Utilities to create symbol table entries for symbols in a GOTO Assembly
program
-/

-- TODO: Sync with Common.lean
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
  -- (FIXME)
  -- location : SourceLocation := .nil
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

/--
CBMC expects formals to be in the namespace of the program.
So, e.g., `x` appears as `program::x`.
-/
def mkFormalSymbol (pname base : String) : String :=
  pname ++ "::" ++ base

/--
Local variables use `program::<depth>::<var>` notation.
(FIXME): Does `depth` refer to the scope level?
-/
def mkLocalSymbol (pname base : String) (depth : Nat := 1) : String :=
  pname ++ "::" ++ toString depth ++ "::" ++ base

/--
A symbol table entry for a variable (e.g., a function argument or a local
variable) can be fairly sparse in details at the level of GOTO instructions.

We can elide the type for a local variable. However, we must provide the correct
type for a function parameter (i.e., a formal).
-/
def createGOTOSymbol (programName baseName fullName : String)
  (isParameter isStateVar : Bool) (ty : Option Ty)
  : String × CBMCSymbol :=
  let tyJson := match ty with
    | none => Json.mkObj [("id", "nil")]
    | some ty => tyToJson ty
  (fullName,
  {
    baseName := baseName,
    isFileLocal := true,
    isLvalue := true,
    isParameter := isParameter,
    -- What's a "StateVar"? So far, function arguments (i.e., for which
    -- `isParameter` is true) appear to have `isStateVar` true too.
    isStateVar := isStateVar,
    isThreadLocal := true,
    -- location := .nil,
    mode := "C",
    module := programName,
    name := fullName,
    prettyName := baseName,
    prettyType := "unknown",
    prettyValue := "",
    type := tyJson,
    value := Json.mkObj [("id", "nil")]
  })

-- (FIXME) Sync. with mkParameter.
def mkParam (baseName : String) (fullName : String) (ty : Ty) : Json :=
  Json.mkObj [
    ("id", "parameter"),
    ("namedSub", Json.mkObj [
      ("#base_name", Json.mkObj [("id", baseName)]),
      ("#identifier", Json.mkObj [("id", fullName)]),
      ("type", tyToJson ty)
    ])
  ]

/-! ### Collecting symbols from GOTO programs -/

/-- Deduplicate a list by a string key, preserving first occurrence order. -/
private def dedupByName {α : Type} (getName : α → String) (xs : List α) : List α :=
  xs.foldl (fun acc x =>
    if acc.any (fun a => getName a == getName x) then acc else acc ++ [x]) []

/-- Collect items from all instructions in a program, deduplicated by name. -/
private def collectFromProgram {α : Type} (getName : α → String)
    (fromExpr : Expr → List α) (fromCode : Code → List α)
    (program : Program) : List α :=
  let fromInsts := program.instructions.toList.flatMap fun inst =>
    fromExpr inst.guard ++ fromCode inst.code
  dedupByName getName fromInsts

/-- Info about a function application: name, operand types, return type -/
structure FnAppInfo where
  name : String
  domainTypes : List Ty
  codomainType : Ty
  deriving BEq

private def collectFnAppsExpr (e : Expr) : List FnAppInfo :=
  let children := e.operands.flatMap collectFnAppsExpr
  match e.id with
  | .functionApplication name =>
    { name, domainTypes := e.operands.map (·.type), codomainType := e.type } :: children
  | _ => children
  termination_by (SizeOf.sizeOf e)
  decreasing_by all_goals (
    cases e; simp_all; rename_i x_in;
    have := List.sizeOf_lt_of_mem x_in; omega)

private def collectFnAppsCode (c : Code) : List FnAppInfo :=
  let fromOps := c.operands.flatMap collectFnAppsExpr
  let fromStmts := c.statements.flatMap collectFnAppsCode
  fromOps ++ fromStmts
  termination_by (SizeOf.sizeOf c)
  decreasing_by
    all_goals (cases c; simp_all; rename_i x_in; have := List.sizeOf_lt_of_mem x_in; omega)

/-- Collect all function application symbols from a GOTO program. -/
def collectFnApps (program : Program) : List FnAppInfo :=
  collectFromProgram (·.name) collectFnAppsExpr collectFnAppsCode program

/-- Create a symbol table entry for an uninterpreted function. -/
def createFnAppSymbol (info : FnAppInfo) : String × CBMCSymbol :=
  let mathFnType := Json.mkObj [
    ("id", "mathematical_function"),
    ("sub", Json.arr (#[
      Json.mkObj [("id", ""), ("sub", Json.arr (info.domainTypes.map tyToJson).toArray)],
      tyToJson info.codomainType
    ]))
  ]
  (info.name,
  {
    baseName := info.name,
    mode := "C",
    module := "",
    name := info.name,
    type := mathFnType,
    value := Json.mkObj [("id", "nil")]
  })

/-- Info about a symbol reference: name and type -/
structure SymbolRefInfo where
  name : String
  type : Ty
  deriving BEq

private def collectSymbolRefsExpr (e : Expr) : List SymbolRefInfo :=
  let children := e.operands.flatMap collectSymbolRefsExpr
  match e.id with
  | .nullary (.symbol name) => { name, type := e.type } :: children
  | _ => children
  termination_by (SizeOf.sizeOf e)
  decreasing_by all_goals (
    cases e; simp_all; rename_i x_in;
    have := List.sizeOf_lt_of_mem x_in; omega)

private def collectSymbolRefsCode (c : Code) : List SymbolRefInfo :=
  let fromOps := c.operands.flatMap collectSymbolRefsExpr
  let fromStmts := c.statements.flatMap collectSymbolRefsCode
  fromOps ++ fromStmts
  termination_by (SizeOf.sizeOf c)
  decreasing_by
    all_goals (cases c; simp_all; rename_i x_in; have := List.sizeOf_lt_of_mem x_in; omega)

/-- Collect all symbol references from a GOTO program, deduplicated by name. -/
def collectSymbolRefs (program : Program) : List SymbolRefInfo :=
  collectFromProgram (·.name) collectSymbolRefsExpr collectSymbolRefsCode program

def createFunctionSymbol (programName : String) (formals : Map String Ty) (ret : Ty)
    (contracts : List (String × Json) := []) :
  String × CBMCSymbol :=
  let baseNamedSub := [
      ("parameters", Json.mkObj [
        ("sub", Json.arr
                (formals.map (fun (name, ty) =>
                                mkParam name (mkFormalSymbol programName name) ty)).toArray)
      ]),
      ("return_type", tyToJson ret)
    ]
  let namedSub := baseNamedSub ++ contracts
  let code_type := Json.mkObj [
    ("id", "code"),
    ("namedSub", Json.mkObj namedSub)
  ]
  (programName,
  {
    baseName := programName,
    isLvalue := true,
    -- location := .nil,
    mode := "C",
    module := programName,
    name := programName,
    prettyName := programName,
    prettyType := "unknown",
    prettyValue := "",
    type := code_type
    value := Json.mkObj [("id", "compiled")]
  })

-------------------------------------------------------------------------------
