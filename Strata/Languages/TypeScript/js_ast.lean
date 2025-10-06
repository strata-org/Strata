/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Data.Json
import Lean.Data.Json.Parser
import Lean.Data.RBTree

set_option trace.Elab.Deriving true


structure Position where
  line : Nat
  column : Nat
  index : Nat
deriving Repr, Lean.FromJson, Lean.ToJson

structure SourceLocation where
  start_loc : Position
  end_loc : Position
  identifierName: Option String
deriving Repr, Lean.FromJson, Lean.ToJson

structure BaseNode where
  type : String
  start_loc : Nat
  end_loc : Nat
  loc : SourceLocation
deriving Repr, Lean.FromJson, Lean.ToJson

--#beginAST
structure TS_TSNumberKeyword extends BaseNode where
deriving Repr, Lean.FromJson, Lean.ToJson

structure TS_TSBooleanKeyword extends BaseNode where
deriving Repr, Lean.FromJson, Lean.ToJson

structure TS_TSStringKeyword extends BaseNode where
deriving Repr, Lean.FromJson, Lean.ToJson

mutual
  inductive TS_TSTypeKeyword where
    | TS_TSNumberKeyword : TS_TSNumberKeyword → TS_TSTypeKeyword
    | TS_TSBooleanKeyword : TS_TSBooleanKeyword → TS_TSTypeKeyword
    | TS_TSStringKeyword : TS_TSStringKeyword → TS_TSTypeKeyword
    | TS_TSArrayType : TS_TSArrayType → TS_TSTypeKeyword
  deriving Repr, Lean.FromJson, Lean.ToJson

  -- TODO: Array not as a type?
  structure TS_TSArrayType extends BaseNode where
    elementType : TS_TSTypeKeyword
  deriving Repr, Lean.FromJson, Lean.ToJson
end

structure TS_TSTypeAnnotation extends BaseNode where
  typeAnnotation : Option TS_TSTypeKeyword
deriving Repr, Lean.FromJson, Lean.ToJson

structure TS_Identifier extends BaseNode where
  name : String
  typeAnnotation : Option TS_TSTypeAnnotation
deriving Repr, Lean.FromJson, Lean.ToJson


structure TS_Parameter extends BaseNode where
  name : String
  typeAnnotation : TS_TSTypeAnnotation
  identifierName? : Option String := none
deriving Repr, Lean.FromJson, Lean.ToJson

structure TS_NumericLiteralExtra where
  rawValue: Float
  raw: String
deriving Repr, Lean.FromJson, Lean.ToJson

structure TS_NumericLiteral extends BaseNode where
  value: Float
  extra: TS_NumericLiteralExtra
deriving Repr, Lean.FromJson, Lean.ToJson

structure TS_BooleanLiteral extends BaseNode where
  value: Bool
deriving Repr, Lean.FromJson, Lean.ToJson

structure TS_StringLiteral extends BaseNode where
  value: String
deriving Repr, Lean.FromJson, Lean.ToJson

structure TS_NullLiteral extends BaseNode where
deriving Repr, Lean.FromJson, Lean.ToJson

mutual
  structure TS_MemberExpression extends BaseNode where
    object: TS_Expression
    property: TS_Expression
    computed: Bool
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_BinaryExpression extends BaseNode where
    left : TS_Expression
    operator : String
    right : TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_ConditionalExpression extends BaseNode where
      test : TS_Expression
      consequent : TS_Expression
      alternate : TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_LogicalExpression extends BaseNode where
    left : TS_Expression
    operator : String
    right : TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  inductive TS_AssignmentIdentifier where
    | TS_Identifier : TS_Identifier → TS_AssignmentIdentifier
    | TS_MemberExpression: TS_MemberExpression → TS_AssignmentIdentifier

  structure TS_AssignmentExpression extends BaseNode where
    operator: String
    left: TS_AssignmentIdentifier
    right: TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_UnaryExpression extends BaseNode where
    operator: String
    argument: TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_ObjectProperty extends BaseNode where
    method: Bool
    -- Key can be any expression (NumericLiteral, StringLiteral, etc.)
    key: TS_Expression
    computed: Bool
    shorthand: Bool
    value: TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_ObjectExpression extends BaseNode where
    properties: Array TS_ObjectProperty
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_ArrayExpression extends BaseNode where
    elements : Array TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_CallExpression extends BaseNode where
    callee : TS_Identifier
    arguments : Array TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_FunctionExpression extends BaseNode where
    -- id : TS_Identifier
    -- expression : Bool
    -- generator : Bool
    -- async : Bool
    params : Array TS_Identifier
    body: TS_Statement
  deriving Repr, Lean.FromJson, Lean.ToJson

  inductive TS_Expression where
    | TS_BinaryExpression : TS_BinaryExpression → TS_Expression
    | TS_ConditionalExpression : TS_ConditionalExpression → TS_Expression
    | TS_LogicalExpression : TS_LogicalExpression → TS_Expression
    | TS_AssignmentExpression : TS_AssignmentExpression → TS_Expression
    | TS_NumericLiteral : TS_NumericLiteral → TS_Expression
    | TS_BooleanLiteral : TS_BooleanLiteral → TS_Expression
    | TS_StringLiteral : TS_StringLiteral → TS_Expression
    | TS_NullLiteral : TS_NullLiteral → TS_Expression
    | TS_IdExpression : TS_Identifier → TS_Expression
    | TS_UnaryExpression: TS_UnaryExpression → TS_Expression
    | TS_ObjectExpression: TS_ObjectExpression → TS_Expression
    | TS_ArrayExpression: TS_ArrayExpression → TS_Expression
    | TS_MemberExpression: TS_MemberExpression → TS_Expression
    | TS_CallExpression: TS_CallExpression → TS_Expression
    | TS_FunctionExpression: TS_FunctionExpression → TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson


  structure TS_VariableDeclarator extends BaseNode where
    id : TS_Identifier
    init: TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_VariableDeclaration extends BaseNode where
    declarations : Array TS_VariableDeclarator := #[]
    kind : Option String
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_EmptyStatement extends BaseNode where
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_ExpressionStatement extends BaseNode where
    expression : TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_ThrowStatement extends BaseNode where
    argument: TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson


  structure TS_BlockStatement extends BaseNode where
    body : Array TS_Statement
    directives : Array String := #[]
    -- innerComments is an array of comments
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_IfStatement extends BaseNode where
    test : TS_Expression
    consequent : TS_Statement
    alternate : Option TS_Statement
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_ReturnStatement extends BaseNode where
    argument : Option TS_Expression
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_FunctionDeclaration extends BaseNode where
    id : TS_Identifier
    params : Array TS_Identifier
    returnType : TS_TSTypeAnnotation
    body : TS_Statement
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_WhileStatement extends BaseNode where
    test: TS_Expression
    body: TS_Statement
  deriving Repr, Lean.FromJson, Lean.ToJson

  structure TS_ContinueStatement extends BaseNode where
    label: Option TS_Identifier
  deriving Repr, Lean.FromJson, Lean.ToJson

  /- TODO: Add support for for(let a=0, b=0;a!=0 and b!=0;a++,b++) -/
  structure TS_ForStatement extends BaseNode where
    init: TS_VariableDeclaration
    test: TS_Expression
    update: TS_AssignmentExpression
    body: TS_Statement
  deriving Repr, Lean.FromJson, Lean.ToJson

  /-- `break;` (labels optional; ESTree uses null when absent) -/
  structure TS_BreakStatement extends BaseNode where
    label : Option TS_Identifier := none
  deriving Repr, Lean.FromJson, Lean.ToJson

  inductive TS_Statement where
    | TS_IfStatement : TS_IfStatement → TS_Statement
    | TS_VariableDeclaration : TS_VariableDeclaration → TS_Statement
    | TS_ExpressionStatement : TS_ExpressionStatement → TS_Statement
    | TS_BlockStatement : TS_BlockStatement → TS_Statement
    | TS_ThrowStatement : TS_ThrowStatement → TS_Statement
    | TS_ReturnStatement : TS_ReturnStatement → TS_Statement
    | TS_FunctionDeclaration : TS_FunctionDeclaration → TS_Statement
    | TS_WhileStatement: TS_WhileStatement → TS_Statement
    | TS_ContinueStatement: TS_ContinueStatement → TS_Statement
    | TS_BreakStatement: TS_BreakStatement → TS_Statement
    | TS_ForStatement : TS_ForStatement → TS_Statement
  deriving Repr, Lean.FromJson, Lean.ToJson
end

structure TS_Comment extends BaseNode where
deriving Repr, Lean.FromJson, Lean.ToJson


structure TS_Program extends BaseNode where
  sourceType : String
  interpreter : Option String := none
  body : Array TS_Statement
  directives : Array String := #[]
deriving Repr, Lean.FromJson, Lean.ToJson

structure TS_File extends BaseNode where
  errors : Array String := #[]
  program : TS_Program
  comments : Array TS_Comment
deriving Repr, Lean.FromJson, Lean.ToJson

--#endAST

def test_json_to_x (x: Lean.Json) : IO Unit :=
  let e: Except String TS_Expression := Lean.FromJson.fromJson? x
  IO.println s!"{repr e}"

-- #eval test_json_to_x example_expression

def loadJsonFile (path : System.FilePath) : IO TS_File := do
  let contents ← IO.FS.readFile path
  let json ← match Lean.Json.parse contents with
    | Except.ok json => pure json
    | Except.error err => throw (IO.userError s!"Failed to parse JSON: {err}")
  match Lean.FromJson.fromJson? json with
    | Except.ok file => pure file
    | Except.error err => throw (IO.userError s!"Failed to convert JSON to Node: {err}")
