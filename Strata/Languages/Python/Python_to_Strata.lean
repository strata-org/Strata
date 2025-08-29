import Strata.Languages.Python.python_ast
import Strata.Languages.Python.PythonStrataStatement
-- import Strata.Languages.Python.PythonFunction  -- Commented out until we figure out function architecture
import Strata.DL.Heap.HExpr
import Strata.DL.Heap.HTy
import Strata.DL.Heap.Heap
import Strata.DL.CallHeap.CallHeapStrataStatement

-- Python to Strata translation for global straight-line code
-- Focus on global statements with full expression support

namespace PythonStrata

open Heap
open CallHeap

-- Use the generic CallHeap translation context
abbrev TranslationContext := CallHeapTranslationContext

def TranslationContext.empty : TranslationContext := Generic.TranslationContext.empty

-- Add Inhabited instances
instance : Inhabited TranslationContext where
  default := TranslationContext.empty

instance : Inhabited (TranslationContext × List PythonStrataStatement) where
  default := (TranslationContext.empty, [])

-- Infer type from Python expression when no annotation is provided
partial def infer_type_from_expr (expr: Py_Expression) : Heap.HMonoTy :=
  match expr with
  | .Py_Dict _ => Heap.HMonoTy.addr  -- Dictionaries are addresses
  | .Py_Constant c =>
    -- Python constants can be various types, we'll use Float for simplicity
    Heap.HMonoTy.int  -- Simplified to int for now
  | .Py_BinOp e =>
    -- Binary operations typically return numbers
    Heap.HMonoTy.int
  | _ => Heap.HMonoTy.int  -- Default fallback

-- Translate Python expressions to Heap expressions
partial def translate_expr (e: Py_Expression) : Heap.HExpr :=
  match e with
  | .Py_BinOp e =>
    let lhs := translate_expr e.left
    let rhs := translate_expr e.right
    match e.op with
    | .Add _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Add" none) lhs) rhs
    | .Sub _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Sub" none) lhs) rhs
    | .Mult _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Mul" none) lhs) rhs
    | .Div _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Div" none) lhs) rhs
    | .Lt _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Lt" none) lhs) rhs
    | .Gt _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Gt" none) lhs) rhs
    | .Eq _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Eq" none) lhs) rhs

  | .Py_Constant c =>
    -- Convert Python constant to appropriate Heap expression
    -- For now, assume it's a numeric value
    Heap.HExpr.int c.value.floor.toUInt64.toNat

  | .Py_Name n =>
    -- Simple variable reference
    Heap.HExpr.lambda (.fvar n.id none)

  | .Py_Subscript s =>
    -- Translate obj[index] to heap dereference
    let objExpr := translate_expr s.value
    -- Handle both constant and variable indices
    match s.slice with
    | .Py_Constant numConst =>
        -- Constant index (e.g., obj[5])
        let field := numConst.value.floor.toUInt64.toNat
        Heap.HExpr.deref objExpr field
    | .Py_Name varName =>
        -- Variable index (e.g., obj[x])
        -- Create a deferred operation that will be evaluated at runtime
        -- We'll use a special operation name to indicate this is a variable index
        let varExpr := Heap.HExpr.lambda (.fvar varName.id none)
        -- Create a deferred operation that takes the object and the variable index
        -- This will be evaluated at runtime to get the actual field value
        Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAccess" none) objExpr) varExpr
    | _ => panic! s!"Unsupported subscript index: {repr s.slice}"

  | .Py_Compare c =>
    -- Translate Python comparison to heap expression
    -- For now, handle simple single comparison (left op right)
    match c.ops.get? 0, c.comparators.get? 0 with
    | some op, some right =>
      let lhs := translate_expr c.left
      let rhs := translate_expr right
      match op with
      | .Lt _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Lt" none) lhs) rhs
      | .Gt _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Gt" none) lhs) rhs
      | .Eq _ => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Eq" none) lhs) rhs
      | _ => panic! s!"Unsupported comparison operator in PyCompare: {repr op}"
    | _, _ => panic! "PyCompare should have at least one operator and comparator"

  | .Py_Dict d =>
    -- Translate {1: value1, 5: value5} to heap allocation
    let fields := d.keys.toList.zip d.values.toList |>.map (fun (key, value) =>
      let keyIndex := match key with
        | .Py_Constant numConst => numConst.value.floor.toUInt64.toNat
        | _ => panic! s!"Expected constant as dictionary key, got: {repr key}"
      let valueExpr := translate_expr value
      (keyIndex, valueExpr))
    -- Use allocSimple which handles the object type automatically
    Heap.HExpr.allocSimple fields

  | .Py_Call call =>
    -- Handle function calls - translate to expressions for now
    match call.func with
    | .Py_Name funcName =>
      if funcName.id == "print" then
        -- No-op for print calls (instrumentation)
        Heap.HExpr.int 0  -- Return dummy value
      else
        -- For user-defined functions, we'll handle this in statement translation
        -- For now, create a placeholder that will be handled during call statement processing
        Heap.HExpr.lambda (.fvar s!"call_{funcName.id}" none)
    | _ => panic! s!"Unsupported function call expression: {repr call.func}"

-- Translate Python statements to PythonStrata statements
partial def translate_statement (s: Py_Statement) (ctx : TranslationContext) : TranslationContext × List PythonStrataStatement :=
  match s with
  | .Py_FunctionDef funcDef =>
    -- Translate function definition
    dbg_trace s!"[DEBUG] Translating function definition: {funcDef.name}"
    dbg_trace s!"[DEBUG] Function parameters: {funcDef.args.toList}"
    dbg_trace s!"[DEBUG] Function body has {funcDef.body.size} statements"

    let funcBody := (funcDef.body.toList.map (fun stmt => translate_statement stmt ctx |>.snd)).flatten
    dbg_trace s!"[DEBUG] Translated function body to {funcBody.length} Strata statements"

    let strataFunc : CallHeapStrataFunction := {
      name := funcDef.name,
      params := funcDef.args.toList,
      body := funcBody,
      returnType := none  -- We'll infer this later if needed
    }
    let newCtx := ctx.addFunction strataFunc
    dbg_trace s!"[DEBUG] Added function '{funcDef.name}' to context"
    -- Function definitions don't generate statements themselves, just update context
    (newCtx, [])

  | .Py_Return ret =>
    -- Handle return statements
    match ret.value with
    | some expr =>
      let returnExpr := translate_expr expr
      dbg_trace s!"[DEBUG] setting return expr {repr returnExpr}!"
      -- For now, store return value in a special variable
      -- TODO: Implement proper return handling
      (ctx, [.cmd (.set "return_value" returnExpr)])
    | none =>
      -- Void return
      (ctx, [.cmd (.set "return_value" (Heap.HExpr.int 1))])

  | .Py_Assign assign =>
    -- Handle assignment: target = value
    match assign.targets.get? 0 with
    | .none => panic! "Assignment should have at least one target"
    | .some target =>
      match target with
      | .Py_Name name =>
        -- Check if this is a function call assignment
        match assign.value with
        | .Py_Call call =>
          -- Handle function call assignment: x = func(args)
          match call.func with
          | .Py_Name funcName =>
            if funcName.id == "print" then
              -- Handle print specially
              let value := Heap.HExpr.int 0
              let ty := Heap.HMonoTy.int
              (ctx, [.cmd (.init name.id ty value)])
            else
              -- Translate to Call dialect directCall
              dbg_trace s!"[DEBUG] Translating function call assignment: {name.id} = {funcName.id}(...)"
              let args := call.args.toList.map translate_expr
              dbg_trace s!"[DEBUG] Function call has {args.length} arguments"
              let lhs := [name.id]  -- Left-hand side variables to store result
              (ctx, [.cmd (.directCall lhs funcName.id args)])
          | _ => panic! s!"Unsupported function call in assignment: {repr call.func}"
        | _ =>
          -- Handle simple variable assignment: x = value
          let value := translate_expr assign.value
          let ty := infer_type_from_expr assign.value
          (ctx, [.cmd (.init name.id ty value)])
      | .Py_Subscript subscript =>
        -- Handle subscript assignment: obj[index] = value
        let objExpr := translate_expr subscript.value
        -- Handle both constant and variable indices
        match subscript.slice with
        | .Py_Constant numConst =>
            -- Constant index (e.g., obj[5] = value)
            let fieldIndex := numConst.value.floor.toUInt64.toNat
            let valueExpr := translate_expr assign.value
            -- Create assignment expression and store result in a temporary variable
            let assignExpr := Heap.HExpr.assign objExpr fieldIndex valueExpr
            (ctx, [.cmd (.set "temp_assign_result" assignExpr)])
        | .Py_Name varName =>
            -- Variable index (e.g., obj[x] = value)
            -- Create a variable reference for the index
            let varExpr := Heap.HExpr.lambda (.fvar varName.id none)
            let valueExpr := translate_expr assign.value
            -- Create a deferred operation that takes the object, the variable index, and the value
            -- This will be evaluated at runtime to set the field
            let assignExpr := Heap.HExpr.app
                                (Heap.HExpr.app
                                  (Heap.HExpr.app
                                    (Heap.HExpr.deferredOp "DynamicFieldAssign" none)
                                    objExpr)
                                  varExpr)
                                valueExpr
            (ctx, [.cmd (.set "temp_assign_result" assignExpr)])
        | _ => panic! s!"Unsupported subscript index: {repr subscript.slice}"
      | _ => panic! s!"Unsupported assignment target: {repr target}"

  | .Py_Expr exprStmt =>
    -- Handle expression statements (like standalone function calls)
    match exprStmt.value with
    | .Py_Call call =>
      -- Handle standalone function call
      match call.func with
      | .Py_Name funcName =>
        if funcName.id == "print" then
          -- Handle print specially - no-op
          (ctx, [])
        else
          -- Translate to Call dialect directCall with no return value
          let args := call.args.toList.map translate_expr
          let lhs := []  -- No left-hand side for standalone calls
          (ctx, [.cmd (.directCall lhs funcName.id args)])
      | _ => panic! s!"Unsupported function call in expression statement: {repr call.func}"
    | _ =>
      -- Other expression statements - ignore for now
      (ctx, [])

  | .Py_If ifStmt =>
    -- Handle if statement: if test: body else: orelse
    let testExpr := translate_expr ifStmt.test
    let (ctx1, thenStmts) := ifStmt.body.toList.foldl
      (fun (accCtx, accStmts) stmt =>
        let (newCtx, stmts) := translate_statement stmt accCtx
        (newCtx, accStmts ++ stmts)) (ctx, [])
    let (ctx2, elseStmts) := ifStmt.orelse.toList.foldl
      (fun (accCtx, accStmts) stmt =>
        let (newCtx, stmts) := translate_statement stmt accCtx
        (newCtx, accStmts ++ stmts)) (ctx1, [])
    let thenBlock : Imperative.Block PythonStrataExpression PythonStrataCommand := { ss := thenStmts }
    let elseBlock : Imperative.Block PythonStrataExpression PythonStrataCommand := { ss := elseStmts }
    (ctx2, [.ite testExpr thenBlock elseBlock])

  | .Py_Import _ =>
    -- Skip import statements for now
    (ctx, [])
-- Translate list of Python statements with context
def translate_program (statements: List Py_Statement) : TranslationContext × List PythonStrataStatement :=
  statements.foldl (fun (accCtx, accStmts) stmt =>
    let (newCtx, stmts) := translate_statement stmt accCtx
    (newCtx, accStmts ++ stmts)) (TranslationContext.empty, [])

-- Translate a full PyModule structure
def translate_full_program (module: Py_Module) : TranslationContext × List PythonStrataStatement :=
  translate_program module.body.toList

-- Get just the statements (ignoring context) for backward compatibility
def translate_program_statements (statements: List Py_Statement) : List PythonStrataStatement :=
  (translate_program statements).snd

def translate_full_program_statements (module: Py_Module) : List PythonStrataStatement :=
  (translate_full_program module).snd

-- Helper to describe a PythonStrata statement
def describePythonStrataStatement (stmt: PythonStrataStatement) : String :=
  match stmt with
  | .cmd (.imperativeCmd (.init name ty expr _)) =>
    s!"init {name} : {repr ty} = {repr expr}"
  | .cmd (.imperativeCmd (.set name expr _)) =>
    s!"set {name} = {repr expr}"
  | .cmd (.imperativeCmd (.havoc name _)) =>
    s!"havoc {name}"
  | .cmd (.imperativeCmd (.assume name expr _)) =>
    s!"assume {name} : {repr expr}"
  | .cmd (.imperativeCmd (.assert name expr _)) =>
    s!"assert {name} : {repr expr}"
  | .cmd (.directCall lhs funcName args) =>
    let lhsStr := if lhs.isEmpty then "" else s!"{String.intercalate ", " lhs} = "
    let argsStr := String.intercalate ", " (args.map (fun arg => s!"{repr arg}"))
    s!"{lhsStr}{funcName}({argsStr})"
  | .block label block _ =>
    s!"block {label} ( {block.ss.length} statements )"
  | .ite cond thenBlock elseBlock _ =>
    s!"if {repr cond} then ( {thenBlock.ss.length} statements ) else ( {elseBlock.ss.length} statements )"
  | .loop guard measure invariant body _ =>
    let measureStr := match measure with | some m => s!" measure {repr m}" | none => ""
    let invariantStr := match invariant with | some i => s!" invariant {repr i}" | none => ""
    s!"loop {repr guard}{measureStr}{invariantStr} ( {body.ss.length} statements )"
  | .goto label _ =>
    s!"goto {label}"


end PythonStrata
