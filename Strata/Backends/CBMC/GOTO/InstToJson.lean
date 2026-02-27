/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Program
import Strata.Backends.CBMC.Common
import Strata.Util.Tactics

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
  | _ => Json.mkObj [("id", "unknown")]

/-- Convert `Expr` to JSON format -/
def exprToJson (expr : Expr) : Json :=
  let srcField := sourceLocationToJson expr.sourceLoc
  let mkOpJson (opStr : String) : Json :=
    Json.mkObj [
      ("id", opStr),
      ("namedSub", Json.mkObj [("type", tyToJson expr.type)]),
      ("sub", Json.arr (expr.operands.map exprToJson).toArray),
      srcField
    ]
  let exprObj := match expr.id with
    | .nullary (.symbol name) => mkSymbolWithSourceLocation name (tyToJson expr.type) expr.sourceLoc
    | .nullary (.constant value) =>
      let value := match expr.type.id with
        | .bitVector (.signedbv w) => bvToHex value w
        | .bitVector (.unsignedbv w) => bvToHex value w
        | _ => value
      Json.mkObj [
        ("id", "constant"),
        ("namedSub", Json.mkObj [
          ("type", tyToJson expr.type),
          ("value", Json.mkObj [("id", value)])
        ]),
        srcField
      ]
    | .nullary (.nondet name) =>
      Json.mkObj [
        ("id", "nondet"),
        ("namedSub", Json.mkObj [
          ("identifier", Json.mkObj [("id", name)]),
          ("type", tyToJson expr.type)
        ]),
        srcField
      ]
    | .unary op => mkOpJson (toString f!"{op}")
    | .binary op => mkOpJson (toString f!"{op}")
    | .multiary op => mkOpJson (toString f!"{op}")
    | .ternary op => mkOpJson (toString f!"{op}")
    | .side_effect effect =>
      let effect_str := toString f!"{effect}"
      Json.mkObj [
        ("id", "side_effect"),
        ("namedSub", Json.mkObj [
          ("statement", Json.mkObj [("id", effect_str)]),
          ("type", tyToJson expr.type)
        ]),
        ("sub", Json.arr (expr.operands.map exprToJson).toArray),
        srcField
      ]
    | .functionApplication name =>
      let domainTypes := expr.operands.map (fun op => tyToJson op.type)
      let mathFnType := Json.mkObj [
        ("id", "mathematical_function"),
        ("sub", Json.arr (#[
          Json.mkObj [("id", ""), ("sub", Json.arr domainTypes.toArray)],
          tyToJson expr.type
        ]))
      ]
      let fnSymbol := mkSymbolWithSourceLocation name mathFnType expr.sourceLoc
      let argsTuple := Json.mkObj [
        ("id", "tuple"),
        ("sub", Json.arr (expr.operands.map exprToJson).toArray)
      ]
      Json.mkObj [
        ("id", "function_application"),
        ("namedSub", Json.mkObj [("type", tyToJson expr.type)]),
        ("sub", Json.arr #[fnSymbol, argsTuple]),
        srcField
      ]
    | _ => panic s!"[exprToJson] Unsupported expr: {format expr}"
  exprObj
  termination_by (SizeOf.sizeOf expr)
  decreasing_by all_goals (cases expr; term_by_mem)

/-- Merge `Expr.namedFields` into the JSON produced by `exprToJson`. -/
partial def exprToJsonWithNamedFields (expr : Expr) : Json :=
  let base := exprToJson expr
  if expr.namedFields.isEmpty then base
  else
    let extraFields := expr.namedFields.map fun (k, v) => (k, exprToJsonWithNamedFields v)
    match base.getObjValD "namedSub" with
    | .obj nsm =>
      let merged := extraFields.foldl (fun acc (k, v) => acc.insert k v) nsm
      base.setObjVal! "namedSub" (.obj merged)
    | _ => base

/-- Convert `Code` to Json -/
def codeToJson (code : Code) : Json :=
  let namedSub := ("namedSub",
        (Json.mkObj [
              ("statement", Json.mkObj [("id", s!"{format code.id}")]),
              ("type", Json.mkObj [("id", "empty")])]))
  let sourceField := sourceLocationToJson code.sourceLoc
  -- Function calls need special serialization for the arguments node
  let sub := match code.id with
    | .function .functionCall =>
      let rec go (ops : List Expr) (i : Nat) : List Json :=
        match ops with
        | [] => []
        | op :: rest =>
          let j := if i == 2 then
            Json.mkObj [("id", "arguments"),
                        ("sub", Json.arr (op.operands.map exprToJson).toArray)]
          else exprToJson op
          j :: go rest (i + 1)
      ("sub", Json.arr (go code.operands 0).toArray)
    | _ => ("sub", Json.arr (code.operands.map exprToJson).toArray)
  let obj := Json.mkObj ([("id", Json.str "code"), namedSub, sub, sourceField])
  obj

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
def instructionToJson (inst : Instruction) : Json :=
  let baseFields := [
    ("instruction", Json.str (instructionToString inst)),
    ("instructionId", Json.str (toString inst.type)),
    ("locationNumber", Json.num inst.locationNum.toNat)
  ]
  let guardField := if inst.type == .GOTO || !Expr.beq inst.guard Expr.true then [("guard", exprToJsonWithNamedFields inst.guard)] else []
  let codeField := if inst.code == Code.skip then [] else [("code", codeToJson inst.code)]
  let targetsField := match inst.type, inst.target with
    | .GOTO, some t => [("targets", Json.arr #[Json.num t.toNat])]
    | _, _ => []
  let sourceField :=  [sourceLocationToJson inst.sourceLoc]
  Json.mkObj (baseFields ++ guardField ++ codeField ++ targetsField ++ sourceField)

def programToJson (name : String) (program : Program) : Json :=
  let body :=
      Json.mkObj [
        ("instructions", Json.arr (program.instructions.map instructionToJson)),
        ("parameterIdentifiers", Json.arr (program.parameterIdentifiers.map toJson)),
        ("isBodyAvailable", program.isBodyAvailable),
        ("isInternal", program.isInternal),
        ("name", name)
      ]
  body

/-- Write a program to JSON file -/
def writeProgramToFile (fileName : String) (programName : String) (program : Program) : IO Unit := do
  let json := programToJson programName program
  IO.FS.writeFile fileName json.pretty

/-- Convert `Program`s to JSON containing GOTO functions -/
def programsToJson (programs : List (String × Program)) : Json :=
  let instructions := Json.arr (programs.map (fun (n, p) => programToJson n p)).toArray
  let functions := Json.mkObj [("functions", instructions)]
  functions

/-- Write programs to JSON file -/
def writeProgramsToFile (fileName : String) (programs : List (String × Program)) : IO Unit := do
  let json := programsToJson programs
  IO.FS.writeFile fileName json.pretty

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
