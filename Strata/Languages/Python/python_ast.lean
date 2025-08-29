import Lean.Data.Json
import Lean.Data.Json.Parser
import Lean.Data.RBTree
--import Midi.Languages.ASTTracker

set_option trace.Elab.Deriving true

-- Base structure for Python AST nodes
structure BaseNode where
  _type : String
  lineno : Nat
  col_offset : Nat
  end_lineno : Nat
  end_col_offset : Nat
deriving Repr, Lean.FromJson, Lean.ToJson

-- Context types for Python AST
structure Py_Store where
  _type : String
deriving Repr, Lean.FromJson, Lean.ToJson

structure Py_Load where
  _type : String
deriving Repr, Lean.FromJson, Lean.ToJson

inductive Py_Context where
  | Store : Py_Store → Py_Context
  | Load : Py_Load → Py_Context
deriving Repr, Lean.FromJson, Lean.ToJson

-- Python operators
structure Py_Add where
  _type : String
deriving Repr, Lean.FromJson, Lean.ToJson

structure Py_Sub where
  _type : String
deriving Repr, Lean.FromJson, Lean.ToJson

structure Py_Mult where
  _type : String
deriving Repr, Lean.FromJson, Lean.ToJson

structure Py_Div where
  _type : String
deriving Repr, Lean.FromJson, Lean.ToJson

structure Py_Lt where
  _type : String
deriving Repr, Lean.FromJson, Lean.ToJson

structure Py_Gt where
  _type : String
deriving Repr, Lean.FromJson, Lean.ToJson

structure Py_Eq where
  _type : String
deriving Repr, Lean.FromJson, Lean.ToJson

inductive Py_Operator where
  | Add : Py_Add → Py_Operator
  | Sub : Py_Sub → Py_Operator
  | Mult : Py_Mult → Py_Operator
  | Div : Py_Div → Py_Operator
  | Lt : Py_Lt → Py_Operator
  | Gt : Py_Gt → Py_Operator
  | Eq : Py_Eq → Py_Operator
deriving Repr, Lean.FromJson, Lean.ToJson

-- Py_thon constant values
structure Py_Constant extends BaseNode where
  value : Float  -- Simplified to Float for now
  kind : Option String
  n : Option Nat  -- For numeric constants
  s : Option Float  -- For string constants (simplified)
deriving Repr, Lean.FromJson, Lean.ToJson

-- Py_thon name (variable identifier)
structure Py_Name extends BaseNode where
  id : String
  ctx : Py_Context
deriving Repr, Lean.FromJson, Lean.ToJson

mutual
  -- Py_thon subscript (array/dict access)
  structure Py_Subscript extends BaseNode where
    value : Py_Expression
    slice : Py_Expression
    ctx : Py_Context
  deriving Repr, Lean.FromJson, Lean.ToJson

  -- Py_thon binary operation
  structure Py_BinOp extends BaseNode where
    left : Py_Expression
    op : Py_Operator
    right : Py_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  -- Py_thon comparison operation
  structure Py_Compare extends BaseNode where
    left : Py_Expression
    ops : Array Py_Operator
    comparators : Array Py_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  -- Py_thon dictionary
  structure Py_Dict extends BaseNode where
    keys : Array Py_Expression
    values : Array Py_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  -- Python function call
  structure Py_Call extends BaseNode where
    func : Py_Expression
    args : Array Py_Expression
    keywords : Array String  -- Simplified
  deriving Repr, Lean.FromJson, Lean.ToJson

  -- Py_thon expressions
  inductive Py_Expression where
    | Py_Constant : Py_Constant → Py_Expression
    | Py_Name : Py_Name → Py_Expression
    | Py_BinOp : Py_BinOp → Py_Expression
    | Py_Subscript : Py_Subscript → Py_Expression
    | Py_Dict : Py_Dict → Py_Expression
    | Py_Compare : Py_Compare → Py_Expression
    | Py_Call : Py_Call → Py_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure Py_Expr extends BaseNode where
    value : Py_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson
end

-- Python assignment statement
structure Py_Assign extends BaseNode where
  targets : Array Py_Expression
  value : Py_Expression
  type_comment : Option String
deriving Repr, Lean.FromJson, Lean.ToJson

-- Python import statement
structure Py_Import extends BaseNode where
  names : Array String  -- Simplified: just module names
deriving Repr, Lean.FromJson, Lean.ToJson



-- Python return statement
structure Py_Return extends BaseNode where
  value : Option Py_Expression  -- Return value (optional for void functions)
deriving Repr, Lean.FromJson, Lean.ToJson

mutual

-- Python function definition
structure Py_FunctionDef extends BaseNode where
  name : String
  args : Array String  -- Simplified: just parameter names
  body : Array Py_Statement
  returns : Option Py_Expression  -- Return type annotation (optional)
deriving Repr, Lean.FromJson, Lean.ToJson

  -- Py_thon if statement
  structure Py_If extends BaseNode where
    test : Py_Expression
    body : Array Py_Statement
    orelse : Array Py_Statement  -- Py_thon uses 'orelse' for else clause
  deriving Repr, Lean.FromJson, Lean.ToJson

  -- Python statements
  inductive Py_Statement where
    | Py_Assign : Py_Assign → Py_Statement
    | Py_If : Py_If → Py_Statement
    | Py_Import : Py_Import → Py_Statement
    | Py_FunctionDef : Py_FunctionDef → Py_Statement
    | Py_Return : Py_Return → Py_Statement
    | Py_Expr : Py_Expr → Py_Statement  -- Expression statements (like function calls)
  deriving Repr, Lean.FromJson, Lean.ToJson
end

-- Py_thon module (top-level)
structure Py_Module where
  _type : String
  body : Array Py_Statement
  type_ignores : Array String  -- Simplified from Lean.Json
deriving Repr, Lean.FromJson, Lean.ToJson
def loadJsonFile (path : System.FilePath) : IO Py_Module := do
  let contents ← IO.FS.readFile path
  let json ← match Lean.Json.parse contents with
    | Except.ok json => pure json
    | Except.error err => throw (IO.userError s!"Failed to parse JSON: {err}")
  match Lean.FromJson.fromJson? json with
    | Except.ok module => pure module
    | Except.error err => throw (IO.userError s!"Failed to convert JSON to Module: {err}")

def test_json_to_module (json: Lean.Json) : IO Unit :=
  let result: Except String Py_Module := Lean.FromJson.fromJson? json
  IO.println s!"{repr result}"
