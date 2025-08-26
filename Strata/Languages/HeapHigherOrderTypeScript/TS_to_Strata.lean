import Strata.Languages.HeapHigherOrderTypeScript.js_ast
import Strata.DL.HeapHigherOrder.HeapHigherOrder
import Strata.DL.Heap.Heap
import Strata.DL.HigherOrder.HigherOrder

-- Combined TypeScript to Strata translation
-- Uses Heap dialect as the base, with HigherOrder dialect only for function-related constructs

namespace TSHeapHigherOrderStrata

open CallHeapHigherOrder

-- Storage for function definitions during translation
abbrev TranslationContext := CallHeapHigherOrderTranslationContext

def TranslationContext.empty : TranslationContext := {
  functions := []
}

-- Add Inhabited instances
instance : Inhabited TranslationContext where
  default := TranslationContext.empty

instance : Inhabited (TranslationContext × List CallHeapHigherOrderStrataStatement) where
  default := (TranslationContext.empty, [])

-- Helper to check if an expression is a function call
def isFunctionCall (expr: TS_Expression) : Bool :=
  match expr with
  | .TS_CallExpression _ => true
  | _ => false

-- Convert TypeScript type to Heap type
def TS_type_to_HMonoTy (ty: String) : Heap.HMonoTy :=
  match ty with
  | "TS_TSNumberKeyword" => Heap.HMonoTy.int
  | "TS_TSBooleanKeyword" => Heap.HMonoTy.bool
  | _ => Heap.HMonoTy.int

def Option_TS_TSTypeKeyword_to_str (i: Option TS_TSTypeKeyword) : String :=
  match i with
  | .some s => match s with
    | .TS_TSNumberKeyword _ => "TS_TSNumberKeyword"
    | .TS_TSBooleanKeyword _ => "TS_TSBooleanKeyword"
    | .TS_TSStringKeyword _ => "TS_TSStringKeyword"
  | .none => "TS_TSNumberKeyword"

-- Helper to extract type from optional type annotation
def extract_type_from_annotation (ann: Option TS_TSTypeAnnotation) : String :=
  match ann with
  | .some a => Option_TS_TSTypeKeyword_to_str a.typeAnnotation
  | .none => "TS_TSNumberKeyword"

-- Infer type from expression when no annotation is provided
partial def infer_type_from_expr (expr: TS_Expression) : Heap.HMonoTy :=
  match expr with
  | .TS_ObjectExpression _ => Heap.HMonoTy.addr
  | .TS_NumericLiteral _ => Heap.HMonoTy.int
  | .TS_BooleanLiteral _ => Heap.HMonoTy.bool
  | .TS_BinaryExpression e =>
    match e.operator with
    | "+" | "-" | "*" | "/" => Heap.HMonoTy.int
    | "==" | "<=" | "<" | ">=" | ">" => Heap.HMonoTy.bool
    | _ => Heap.HMonoTy.int
  | _ => Heap.HMonoTy.int

-- Get type for variable declaration, preferring annotation over inference
def get_var_type (ann: Option TS_TSTypeAnnotation) (expr: TS_Expression) : Heap.HMonoTy :=
  match ann with
  | .some a => TS_type_to_HMonoTy (Option_TS_TSTypeKeyword_to_str a.typeAnnotation)
  | .none => infer_type_from_expr expr

-- Translate TypeScript expressions to Heap expressions (for non-function expressions)
partial def translate_expr_to_heap (e: TS_Expression) : Heap.HExpr :=
  match e with
  | .TS_BinaryExpression e =>
    let lhs := translate_expr_to_heap e.left
    let rhs := translate_expr_to_heap e.right
    match e.operator with
    | "+" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Add" none) lhs) rhs
    | "-" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Sub" none) lhs) rhs
    | "*" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Mul" none) lhs) rhs
    | "/" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Div" none) lhs) rhs
    | "==" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Eq" none) lhs) rhs
    | _ => panic! s!"Unsupported binary operator: {e.operator}"

  | .TS_NumericLiteral n =>
    Heap.HExpr.int n.extra.raw.toInt!

  | .TS_BooleanLiteral b =>
    if b.value then Heap.HExpr.true else Heap.HExpr.false

  | .TS_IdExpression id =>
    Heap.HExpr.lambda (.fvar id.name none)

  | .TS_MemberExpression e =>
    let objExpr := translate_expr_to_heap e.object
    match e.property with
    | .TS_NumericLiteral numLit =>
      let field := Float.floor numLit.value |>.toUInt64.toNat
      Heap.HExpr.deref objExpr field
    | _ =>
      let fieldExpr := translate_expr_to_heap e.property
      Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAccess" none) objExpr) fieldExpr

  | .TS_ObjectExpression e =>
    let fields := e.properties.toList.map (fun prop =>
      let key := match prop.key with
        | .TS_NumericLiteral numLit => Float.floor numLit.value |>.toUInt64.toNat
        | _ => panic! "Expected numeric literal as object key"
      let value := translate_expr_to_heap prop.value
      (key, value))
    Heap.HExpr.allocSimple fields

  | _ => panic! s!"Unimplemented heap expression: {repr e}"

-- Translate TypeScript expressions to HigherOrder expressions (for function expressions)
partial def translate_expr_to_higher_order (e: TS_Expression) : HigherOrder.HOExpr :=
  match e with
  | .TS_CallExpression call =>
    let args := call.arguments.toList.map translate_expr_to_higher_order
    match args with
    | [] => HigherOrder.HOExpr.lambda (Lambda.LExpr.fvar call.callee.name Lambda.LMonoTy.int)
    | [arg1] => HigherOrder.HOExpr.app (HigherOrder.HOExpr.var call.callee.name) arg1
    | [arg1, arg2] =>
      let partialApp := HigherOrder.HOExpr.app (HigherOrder.HOExpr.var call.callee.name) arg1
      HigherOrder.HOExpr.app partialApp arg2
    | _ => HigherOrder.HOExpr.const "error_unsupported_args"

  | .TS_NumericLiteral n =>
    HigherOrder.HOExpr.const n.extra.raw

  | .TS_BooleanLiteral b =>
    HigherOrder.HOExpr.const (if b.value then "true" else "false")

  | .TS_IdExpression id =>
    HigherOrder.HOExpr.var id.name

  | .TS_BinaryExpression binExpr =>
    -- Handle arithmetic operations like y + taintedValue
    let leftExpr := translate_expr_to_higher_order binExpr.left
    let rightExpr := translate_expr_to_higher_order binExpr.right
    HigherOrder.HOExpr.arith binExpr.operator leftExpr rightExpr

  | _ => HigherOrder.HOExpr.const "unsupported_expr"

-- Translate TypeScript statements to combined CallHeapHigherOrder statements
partial def translate_statement (s: TS_Statement) (ctx : TranslationContext) : TranslationContext × List CallHeapHigherOrderStrataStatement :=
  match s with
  | .TS_VariableDeclaration decl =>
    match decl.declarations[0]? with
    | .none => panic! "VariableDeclarations should have at least one declaration"
    | .some d =>
      if isFunctionCall d.init then
        -- Function call assignment goes to CallHigherOrder dialect
        let initExpr := translate_expr_to_higher_order d.init
        let cmd := Call.CallCmd.imperativeCmd (Imperative.Cmd.init d.id.name Lambda.LMonoTy.int initExpr)
        let callHOStmt : CallHigherOrder.CallHigherOrderStrataStatement := .cmd cmd
        (ctx, [.callHigherOrder callHOStmt])
      else
        -- Regular variable declaration goes to CallHeap dialect
        let value := translate_expr_to_heap d.init
        let ty := get_var_type d.id.typeAnnotation d.init
        let cmd := Call.CallCmd.imperativeCmd (Imperative.Cmd.init d.id.name ty value)
        let callHeapStmt : CallHeap.CallHeapStrataStatement := .cmd cmd
        (ctx, [.callHeap callHeapStmt])

  | .TS_FunctionDeclaration func =>
    -- Function declarations go to CallHigherOrder dialect
    let funcBody := match func.body with
      | .TS_BlockStatement blockStmt =>
        dbg_trace s!"found {blockStmt.body.toList.length} statements for {func.id.name}. before mapping"
        (blockStmt.body.toList.map (fun stmt => translate_statement stmt ctx |>.snd)).flatten
      | _ => panic! s!"Expected block statement as function body, got: {repr func.body}"
    dbg_trace s!"found {funcBody.length} statements for {func.id.name}."
    let strataFunc : Generic.StrataFunction CallHeapHigherOrderStrataStatement CallHeapHigherOrderTy := {
      name := func.id.name,
      params := func.params.toList.map (·.name),
      body := funcBody,
      returnType := none
    }
    let newCtx := { ctx with functions := strataFunc :: ctx.functions }
    (newCtx, [])

  | .TS_ExpressionStatement expr =>
    match expr.expression with
    | .TS_CallExpression call =>
      -- Standalone function call goes to CallHigherOrder dialect
      let args := call.arguments.toList.map translate_expr_to_higher_order
      let cmd := Call.CallCmd.directCall [] call.callee.name args
      let callHOStmt : CallHigherOrder.CallHigherOrderStrataStatement := .cmd cmd
      (ctx, [.callHigherOrder callHOStmt])
    | .TS_AssignmentExpression assgn =>
      match assgn.left with
      | .TS_Identifier id =>
        -- Simple assignment goes to CallHeap dialect
        let value := translate_expr_to_heap assgn.right
        let cmd := Call.CallCmd.imperativeCmd (Imperative.Cmd.set id.name value)
        let callHeapStmt : CallHeap.CallHeapStrataStatement := .cmd cmd
        (ctx, [.callHeap callHeapStmt])
      | .TS_MemberExpression member =>
        -- Field assignment goes to CallHeap dialect
        let objExpr := translate_expr_to_heap member.object
        let valueExpr := translate_expr_to_heap assgn.right
        match member.property with
        | .TS_NumericLiteral numLit =>
          let fieldIndex := Float.floor numLit.value |>.toUInt64.toNat
          let assignExpr := Heap.HExpr.assign objExpr fieldIndex valueExpr
          let cmd := Call.CallCmd.imperativeCmd (Imperative.Cmd.set "temp_assign_result" assignExpr)
          let callHeapStmt : CallHeap.CallHeapStrataStatement := .cmd cmd
          (ctx, [.callHeap callHeapStmt])
        | _ =>
          panic! "Dynamic field assignment not implemented"
      --| _ => panic! "Unsupported assignment target"
    | _ => (ctx, [])

  | .TS_ReturnStatement ret =>
    -- Return statements go to CallHigherOrder dialect (following MIDI pattern)
    match ret.argument with
    | some expr =>
      let returnExpr := translate_expr_to_higher_order expr
      let cmd := Call.CallCmd.imperativeCmd (Imperative.Cmd.init "return_value" Lambda.LMonoTy.int returnExpr)
      let callHOStmt : CallHigherOrder.CallHigherOrderStrataStatement := .cmd cmd
      (ctx, [.callHigherOrder callHOStmt])
    | none =>
      let cmd := Call.CallCmd.imperativeCmd (Imperative.Cmd.init "return_value" Lambda.LMonoTy.int (HigherOrder.HOExpr.const "1"))
      let callHOStmt : CallHigherOrder.CallHigherOrderStrataStatement := .cmd cmd
      (ctx, [.callHigherOrder callHOStmt])

  | _ => (ctx, [])

def translate_program (statements: List TS_Statement) : TranslationContext × List CallHeapHigherOrderStrataStatement :=
  statements.foldl (fun (accCtx, accStmts) stmt =>
    let (newCtx, stmts) := translate_statement stmt accCtx
    (newCtx, accStmts ++ stmts)) (TranslationContext.empty, [])

-- Translate a full Program structure
def translate_full_program (prog: TS_Program) : TranslationContext × List CallHeapHigherOrderStrataStatement :=
  translate_program prog.body.toList

-- Translate a full TS_File structure
def translate_full_ts_program (file: TS_File) : TranslationContext × List CallHeapHigherOrderStrataStatement :=
  translate_full_program file.program

end TSHeapHigherOrderStrata
