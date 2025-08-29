import Strata.Languages.Python.python_ast
import Strata.DL.HeapHigherOrder.HeapHigherOrder
import Strata.DL.Heap.Heap
import Strata.DL.HigherOrder.HigherOrder

-- Combined Python to Strata translation
-- Uses Heap dialect as the base, with HigherOrder dialect only for function-related constructs

namespace PythonHeapHigherOrderStrata

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
def isFunctionCall (expr: Py_Expression) : Bool :=
  match expr with
  | .Py_Call _ => true
  | _ => false

-- Convert Python type to Heap type
def infer_type_from_expr (expr: Py_Expression) : Heap.HMonoTy :=
  match expr with
  | .Py_Dict _ => Heap.HMonoTy.addr
  | .Py_Constant _ => Heap.HMonoTy.int
  | .Py_BinOp _ => Heap.HMonoTy.int
  | _ => Heap.HMonoTy.int

-- Translate Python expressions to Heap expressions (for non-function operations)
partial def translate_expr_to_heap (e: Py_Expression) : Heap.HExpr :=
  match e with
  | .Py_BinOp e =>
    let lhs := translate_expr_to_heap e.left
    let rhs := translate_expr_to_heap e.right
    match e.op with
    | .Add _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Add" none) lhs) rhs
    | .Sub _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Sub" none) lhs) rhs
    | .Mult _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Mul" none) lhs) rhs
    | _ => Heap.HExpr.int 0

  | .Py_Constant c =>
    Heap.HExpr.int (Float.floor c.value).toUInt64.toNat

  | .Py_Name n =>
    Heap.HExpr.lambda (.fvar n.id none)

  | .Py_Dict d =>
    -- Translate {1: value1, 5: value5} to heap allocation
    let fields := d.keys.toList.zip d.values.toList |>.map (fun (key, value) =>
      let keyIndex := match key with
        | .Py_Constant numConst => numConst.value.floor.toUInt64.toNat
        | _ => panic! s!"Expected constant as dictionary key, got: {repr key}"
      let valueExpr := translate_expr_to_heap value
      (keyIndex, valueExpr))
    -- Use allocSimple which handles the object type automatically
    Heap.HExpr.allocSimple fields

  | .Py_Subscript sub =>
    -- Translate obj[index] to heap field access
    let objExpr := translate_expr_to_heap sub.value
    match sub.slice with
    | .Py_Constant numConst =>
      let field := numConst.value.floor.toUInt64.toNat
      Heap.HExpr.deref objExpr field
    | _ =>
      let fieldExpr := translate_expr_to_heap sub.slice
      Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAccess" none) objExpr) fieldExpr

  | _ => panic! s!"Unimplemented heap expression: {repr e}"

-- Translate Python expressions to HigherOrder expressions (for function expressions)
partial def translate_expr_to_higher_order (e: Py_Expression) : HigherOrder.HOExpr :=
  match e with
  | .Py_Call call =>
    let args := call.args.toList.map translate_expr_to_higher_order
    let funcName := match call.func with
      | .Py_Name name => name.id
      | _ => "unknown_func"
    match args with
    | [] => HigherOrder.HOExpr.lambda (Lambda.LExpr.fvar funcName Lambda.LMonoTy.int)
    | [arg1] => HigherOrder.HOExpr.app (HigherOrder.HOExpr.var funcName) arg1
    | [arg1, arg2] =>
      let partialApp := HigherOrder.HOExpr.app (HigherOrder.HOExpr.var funcName) arg1
      HigherOrder.HOExpr.app partialApp arg2
    | _ => HigherOrder.HOExpr.const "error_unsupported_args"

  | .Py_Constant c =>
    HigherOrder.HOExpr.const c.value.toString

  | .Py_Name n =>
    HigherOrder.HOExpr.var n.id

  | .Py_BinOp binExpr =>
    let leftExpr := translate_expr_to_higher_order binExpr.left
    let rightExpr := translate_expr_to_higher_order binExpr.right
    let opStr := match binExpr.op with
      | .Add _ => "+"
      | .Sub _ => "-"
      | .Mult _ => "*"
      | _ => "+"
    HigherOrder.HOExpr.arith opStr leftExpr rightExpr

  | _ => HigherOrder.HOExpr.const "unsupported_expr"

-- Translate Python statements to combined CallHeapHigherOrder statements
partial def translate_statement (s: Py_Statement) (ctx : TranslationContext) : TranslationContext × List CallHeapHigherOrderStrataStatement :=
  match s with
  | .Py_Assign assign =>
    match assign.targets[0]? with
    | .none => panic! "Assignment should have at least one target"
    | .some target =>
      match target with
      | .Py_Name name =>
        if isFunctionCall assign.value then
          -- Function call assignment goes to CallHigherOrder dialect
          let initExpr := translate_expr_to_higher_order assign.value
          let cmd := Call.CallCmd.imperativeCmd (Imperative.Cmd.init name.id Lambda.LMonoTy.int initExpr)
          let callHOStmt : CallHigherOrder.CallHigherOrderStrataStatement := .cmd cmd
          (ctx, [.callHigherOrder callHOStmt])
        else
          -- Regular variable assignment goes to CallHeap dialect
          let value := translate_expr_to_heap assign.value
          let ty := infer_type_from_expr assign.value
          let cmd := Call.CallCmd.imperativeCmd (Imperative.Cmd.init name.id ty value)
          let callHeapStmt : CallHeap.CallHeapStrataStatement := .cmd cmd
          (ctx, [.callHeap callHeapStmt])
      | _ => panic! s!"Unsupported assignment target: {repr target}"

  | .Py_FunctionDef func =>
    -- Function declarations go to CallHigherOrder dialect
    let funcBody := (func.body.toList.map (fun stmt => translate_statement stmt ctx |>.snd)).flatten
    let strataFunc : Generic.StrataFunction CallHeapHigherOrderStrataStatement CallHeapHigherOrderTy := {
      name := func.name,
      params := func.args.toList,
      body := funcBody,
      returnType := none
    }
    let newCtx := { ctx with functions := strataFunc :: ctx.functions }
    (newCtx, [])

  | .Py_Expr expr =>
    match expr.value with
    | .Py_Call call =>
      -- Standalone function call goes to CallHigherOrder dialect
      let args := call.args.toList.map translate_expr_to_higher_order
      let funcName := match call.func with
        | .Py_Name name => name.id
        | _ => "unknown_func"
      let cmd := Call.CallCmd.directCall [] funcName args
      let callHOStmt : CallHigherOrder.CallHigherOrderStrataStatement := .cmd cmd
      (ctx, [.callHigherOrder callHOStmt])
    | _ => (ctx, [])

  | .Py_Return ret =>
    match ret.value with
    | some expr =>
      let returnExpr := translate_expr_to_higher_order expr
      let cmd := Call.CallCmd.imperativeCmd (Imperative.Cmd.set "return_value" returnExpr)
      let callHOStmt : CallHigherOrder.CallHigherOrderStrataStatement := .cmd cmd
      (ctx, [.callHigherOrder callHOStmt])
    | none =>
      let cmd := Call.CallCmd.imperativeCmd (Imperative.Cmd.set "return_value" (HigherOrder.HOExpr.const "None"))
      let callHOStmt : CallHigherOrder.CallHigherOrderStrataStatement := .cmd cmd
      (ctx, [.callHigherOrder callHOStmt])

  | _ => (ctx, [])

def translate_program (statements: List Py_Statement) : TranslationContext × List CallHeapHigherOrderStrataStatement :=
  statements.foldl (fun (accCtx, accStmts) stmt =>
    let (newCtx, stmts) := translate_statement stmt accCtx
    (newCtx, accStmts ++ stmts)) (TranslationContext.empty, [])

-- Translate a full Module structure
def translate_full_module (module: Py_Module) : TranslationContext × List CallHeapHigherOrderStrataStatement :=
  translate_program module.body.toList

end PythonHeapHigherOrderStrata
