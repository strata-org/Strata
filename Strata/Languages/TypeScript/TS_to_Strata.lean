/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.TypeScript.js_ast
import Strata.Languages.TypeScript.TSStrataStatement
-- import Strata.Languages.TypeScript.TSFunction  -- Commented out until function architecture is ready
import Strata.DL.Heap.HExpr
import Strata.DL.Heap.HTy
import Strata.DL.Heap.Heap
import Strata.DL.CallHeap.CallHeapStrataStatement

-- TypeScript to Strata translation for global straight-line code
-- Focus on global statements with full expression support

namespace TSStrata

open Heap
open CallHeap

-- Use the generic CallHeap translation context
abbrev TranslationContext := CallHeapTranslationContext

def TranslationContext.empty : TranslationContext := Generic.TranslationContext.empty

-- Add Inhabited instances
instance : Inhabited TranslationContext where
  default := TranslationContext.empty

instance : Inhabited (TranslationContext × List TSStrataStatement) where
  default := (TranslationContext.empty, [])

-- ControlTargets tells where continue/break jumps to
structure ControlTargets where
  continueLabel? : Option String := none
  -- TODO: break control target defined but not yet implemented
  breakLabel? : Option String := none
  breakFlagVar? : Option String := none
deriving Inhabited

private def isBareContinueStmt (s : TS_Statement) : Bool :=
  match s with
  | .TS_ContinueStatement _ => true
  | _ => false

private def isIfWithBareContinue (s : TS_Statement) : Option TS_IfStatement :=
  match s with
  | .TS_IfStatement ifs =>
    let conseqIsBare :=
      match ifs.consequent with
      | .TS_ContinueStatement _ => true
      | .TS_BlockStatement b =>
          -- exactly one statement and it is `continue`
          match b.body.toList with
          | [one] => isBareContinueStmt one
          | _     => false
      | _ => false
    if conseqIsBare && ifs.alternate.isNone then some ifs else none
  | _ => none

def TS_type_to_HMonoTy (ty: String) : Heap.HMonoTy :=
  match ty with
  | "TS_TSNumberKeyword" => Heap.HMonoTy.int
  | "TS_TSBooleanKeyword" => Heap.HMonoTy.bool
  | "TS_TSStringKeyword" => Heap.HMonoTy.string
  | "TS_TSArrayType" => Heap.HMonoTy.addr
  | _ => panic! s!"Unsupported type: {ty}"

def Option_TS_TSTypeKeyword_to_str (i: Option TS_TSTypeKeyword) : String :=
  match i with
  | .some s => match s with
    | .TS_TSNumberKeyword _ => "TS_TSNumberKeyword"
    | .TS_TSBooleanKeyword _ => "TS_TSBooleanKeyword"
    | .TS_TSStringKeyword _ => "TS_TSStringKeyword"
    | .TS_TSArrayType _ => "TS_TSArrayType"
  | .none => panic! "Unimplemented"

-- Helper to extract type from optional type annotation
def extract_type_from_annotation (ann: Option TS_TSTypeAnnotation) : String :=
  match ann with
  | .some a => Option_TS_TSTypeKeyword_to_str a.typeAnnotation
  | .none => "TS_TSNumberKeyword"  -- Default to number if no annotation

-- Infer type from expression when no annotation is provided
partial def infer_type_from_expr (expr: TS_Expression) : Heap.HMonoTy :=
  match expr with
  | .TS_ObjectExpression _ => Heap.HMonoTy.addr  -- Objects are addresses
  | .TS_ArrayExpression _ => Heap.HMonoTy.addr   -- Arrays are addresses
  | .TS_NumericLiteral _ => Heap.HMonoTy.int
  | .TS_BooleanLiteral _ => Heap.HMonoTy.bool
  | .TS_BinaryExpression e =>
    match e.operator with
    | "+" | "-" | "*" | "/" | "%" => Heap.HMonoTy.int
    | "==" | "<=" | "<" | ">=" | ">" => Heap.HMonoTy.bool
    | _ => Heap.HMonoTy.int  -- Default
  | .TS_LogicalExpression _ => Heap.HMonoTy.bool
  | .TS_ConditionalExpression e => infer_type_from_expr e.consequent  -- Use consequent type
  | _ => Heap.HMonoTy.int  -- Default fallback

-- Get type for variable declaration, preferring annotation over inference
def get_var_type (ann: Option TS_TSTypeAnnotation) (expr: TS_Expression) : Heap.HMonoTy :=
  match ann with
  | .some a => TS_type_to_HMonoTy (Option_TS_TSTypeKeyword_to_str a.typeAnnotation)
  | .none => infer_type_from_expr expr

-- Translate TypeScript expressions to Heap expressions
partial def translate_expr (e: TS_Expression) : Heap.HExpr :=
  match e with
  | .TS_BinaryExpression e =>
    let lhs := translate_expr e.left
    let rhs := translate_expr e.right
    match e.operator with
    | "+" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Add" none) lhs) rhs
    | "-" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Sub" none) lhs) rhs
    | "*" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Mul" none) lhs) rhs
    | "/" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Div" none) lhs) rhs
    | "%" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Mod" none) lhs) rhs
    -- TODO: handle weak and strict equality properly
    | "===" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Eq" none) lhs) rhs
    | "==" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Eq" none) lhs) rhs
    --------------------------------------------------------
    | "<=" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Le" none) lhs) rhs
    | "<" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Lt" none) lhs) rhs
    | ">=" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Ge" none) lhs) rhs
    | ">" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Gt" none) lhs) rhs
    | _ => panic! s!"Unsupported binary operator: {e.operator}"

  | .TS_LogicalExpression e =>
    let lhs := translate_expr e.left
    let rhs := translate_expr e.right
    match e.operator with
    | "&&" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Bool.And" none) lhs) rhs
    | "||" => Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Bool.Or" none) lhs) rhs
    | _ => panic! s!"Unsupported logical operator: {e.operator}"

  | .TS_ConditionalExpression e =>
    let guard := translate_expr e.test
    let consequent := translate_expr e.consequent
    let alternate := translate_expr e.alternate
    -- Use deferred conditional instead of toLambda? checks
    Heap.HExpr.deferredIte guard consequent alternate

  | .TS_NumericLiteral n =>
    dbg_trace s!"[DEBUG] Translating numeric literal value={n.value}, raw={n.extra.raw}, rawValue={n.extra.rawValue}"
    Heap.HExpr.int n.extra.raw.toInt!

  | .TS_BooleanLiteral b =>
    if b.value then Heap.HExpr.true else Heap.HExpr.false

  | .TS_StringLiteral s =>
    Heap.HExpr.string s.value

  | .TS_IdExpression id =>
    -- Simple variable reference
    Heap.HExpr.lambda (.fvar id.name none)

  | .TS_NullLiteral _ =>
    Heap.HExpr.null

  | .TS_ArrayExpression arr =>
    -- Translate [value1, value2, value3] to heap allocation with numeric indices
    let fields := arr.elements.toList.mapIdx (fun idx elem =>
      (idx, translate_expr elem))
    -- Arrays store elements at numeric indices: 0->value1, 1->value2, etc.
    Heap.HExpr.allocSimple fields

  | .TS_MemberExpression e =>
    -- Translate str.length/obj[index] to heap dereference
    let objExpr := translate_expr e.object
    match e.property with
    | .TS_NumericLiteral numLit =>
      -- Static field access: obj[5]
      let field := Float.floor numLit.value |>.toUInt64.toNat
      Heap.HExpr.deref objExpr field
    | .TS_IdExpression id =>
      let keyName := id.name
      if !e.computed && keyName == "length" then
        -- String dot access: str.length
        let keyExpr := Heap.HExpr.string keyName
        Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "StringFieldAccess" none) objExpr) keyExpr
      else
        -- Dynamic field access: obj[variable]
        let varExpr := translate_expr (.TS_IdExpression id)
        Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAccess" none) objExpr) varExpr

    | _ =>
      -- Other dynamic expressions: obj[expr]
      let fieldExpr := translate_expr e.property
      Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAccess" none) objExpr) fieldExpr

  | .TS_ObjectExpression e =>
    -- Translate {1: value1, 5: value5} to heap allocation
    let fields := e.properties.toList.map (fun prop =>
      let key := match prop.key with
        | .TS_NumericLiteral numLit => Float.floor numLit.value |>.toUInt64.toNat
        | _ => panic! s!"Expected numeric literal as object key, got: {repr prop.key}"
      let value := translate_expr prop.value
      (key, value))
    -- Use allocSimple which handles the object type automatically
    Heap.HExpr.allocSimple fields

  | .TS_CallExpression call =>
    match call.callee with
      | .TS_MemberExpression member =>
        -- Handle method calls like arr.push(x) or arr.pop()
        let objExpr := translate_expr member.object
        match member.property with
        | .TS_IdExpression id =>
          match id.name with
          | "push" =>
            -- arr.push(value) - use DynamicFieldAssign with length as index
            match call.arguments[0]? with
            | some a =>
              let valueExpr := translate_expr a
              let lengthExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "LengthAccess" none) objExpr) (Heap.HExpr.string "length")
              Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAssign" none) objExpr) lengthExpr) valueExpr
            | none => panic! "push expects one argument"
          | "pop" =>
            -- arr.pop() - read arr[arr.length - 1]
            let lengthExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "LengthAccess" none) objExpr) (Heap.HExpr.string "length")
            let lastIndexExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Sub" none) lengthExpr) (Heap.HExpr.int 1)
            Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAccess" none) objExpr) lastIndexExpr
          | methodName =>
            Heap.HExpr.lambda (.fvar s!"call_{methodName}" none)
        | _ =>
          Heap.HExpr.lambda (.fvar "call_unknown_method" none)
      | .TS_IdExpression id =>
        -- Handle function calls - translate to expressions for now
        Heap.HExpr.lambda (.fvar s!"call_{id.name}" none)
      | _ =>
        panic! s!"Unsupported call expression callee: {repr call.callee}"

  | .TS_FunctionExpression e =>
  -- Translate function definition
    dbg_trace s!"[DEBUG] Translating TypeScript function expression at loc {e.start_loc}-{e.end_loc}"
    let funcName := s!"__anon_func_{e.start_loc}_{e.end_loc}"
    -- just return a heap lambda placeholder
    Heap.HExpr.lambda (.fvar funcName none)

  | .TS_ArrowFunctionExpression e =>
    Heap.HExpr.lambda (.fvar s!"__arrow_func_{e.start_loc}_{e.end_loc}" none)

  | _ => panic! s!"Unimplemented expression: {repr e}"

partial def translate_statement_core
  (s: TS_Statement)
  (ctx : TranslationContext)
  (ct: ControlTargets := {}) : TranslationContext × List TSStrataStatement :=
    match s with
      | .TS_FunctionDeclaration funcDecl =>
      -- Translate function definition
      dbg_trace s!"[DEBUG] Translating TypeScript function definition: {funcDecl.id.name}"
      dbg_trace s!"[DEBUG] Function parameters: {funcDecl.params.toList.map (·.name)}"
      dbg_trace s!"[DEBUG] Function body has statements"

      let (bodyCtx, funcBody) := match funcDecl.body with
          | .TS_BlockStatement blockStmt =>
            -- Thread context through function body to handle nested functions
            blockStmt.body.toList.foldl
              (fun (accCtx, accStmts) stmt =>
                let (newCtx, stmts) := translate_statement_core stmt accCtx ct
                (newCtx, accStmts ++ stmts))
              (ctx, [])
          | _ => panic! s!"Expected block statement as function body, got: {repr funcDecl.body}"

        dbg_trace s!"[DEBUG] Translated function body to {funcBody.length} Strata statements"

        let strataFunc : CallHeapStrataFunction := {
          name := funcDecl.id.name,
          params := funcDecl.params.toList.map (·.name),
          body := funcBody,
          returnType := none  -- We'll infer this later if needed
        }
        -- Use bodyCtx which includes any nested function declarations
        let newCtx := bodyCtx.addFunction strataFunc
        dbg_trace s!"[DEBUG] Added TypeScript function '{funcDecl.id.name}' to context"
        -- Function definitions don't generate statements themselves, just update context
        (newCtx, [])

      | .TS_ReturnStatement ret =>
        -- Handle return statements
        match ret.argument with
        | some expr =>
          let returnExpr := translate_expr expr
          dbg_trace s!"[DEBUG] setting return expr {repr returnExpr}!"
          -- For now, store return value in a special variable
          -- TODO: Implement proper return handling
          (ctx, [.cmd (.set "return_value" returnExpr)])
        | none =>
          -- Void return
          (ctx, [.cmd (.set "return_value" (Heap.HExpr.int 1))])

      | .TS_VariableDeclaration decl =>
        match decl.declarations[0]? with
        | .none => panic! "VariableDeclarations should have at least one declaration"
        | .some d =>
          let defaultInit :=
            let value := translate_expr d.init
            let ty := get_var_type d.id.typeAnnotation d.init
            (ctx, [.cmd (.init d.id.name ty value)])
          -- Check if this is a function call assignment
          match d.init with
          | .TS_CallExpression call =>
            -- Handle function call assignment: let x = func(args)
            match call.callee with
            | .TS_IdExpression id =>
              dbg_trace s!"[DEBUG] Translating TypeScript function call assignment: {d.id.name} = {id.name}(...)"
              let args := call.arguments.toList.map translate_expr
              let lhs := [d.id.name]
              (ctx, [.cmd (.directCall lhs id.name args)])
            | .TS_MemberExpression member =>
              match member.property with
              | .TS_IdExpression methodId =>
                if methodId.name == "pop" then
                  -- Handle Array.pop() method
                  let objExpr := translate_expr member.object
                  let lengthExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "LengthAccess" none) objExpr) (Heap.HExpr.string "length")
                  let lastIndexExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Sub" none) lengthExpr) (Heap.HExpr.int 1)
                  let tempIndexInit := .cmd (.init "temp_pop_index" Heap.HMonoTy.int lastIndexExpr)
                  let tempIndexVar := Heap.HExpr.lambda (.fvar "temp_pop_index" none)
                  let valueExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAccess" none) objExpr) tempIndexVar
                  let ty := infer_type_from_expr d.init
                  let initStmt := .cmd (.init d.id.name ty valueExpr)
                  let deleteExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "FieldDelete" none) objExpr) tempIndexVar) Heap.HExpr.null
                  let deleteStmt := .cmd (.set "temp_delete_result" deleteExpr)
                  (ctx, [tempIndexInit, initStmt, deleteStmt])
                else if methodId.name == "map" then
                  -- Handle Array.map()
                  let objExpr := translate_expr member.object
                  let (cbName, ctxAfterCb) :=
                    match call.arguments[0]? with
                    | some (.TS_FunctionExpression fexpr) =>
                      let funcName := s!"__anon_map_func_{fexpr.start_loc}_{fexpr.end_loc}"
                      let funcBody := match fexpr.body with
                        | .TS_BlockStatement blockStmt =>
                          (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
                        | _ => panic! s!"Expected block statement as function body, got: {repr fexpr.body}"
                      let strataFunc : CallHeapStrataFunction := {
                        name := funcName,
                        params := fexpr.params.toList.map (·.name),
                        body := funcBody,
                        returnType := none
                      }
                      let newCtx := ctx.addFunction strataFunc
                      (funcName, newCtx)
                    | some (.TS_ArrowFunctionExpression aexpr) =>
                      let funcName := s!"__anon_map_arrow_{aexpr.start_loc}_{aexpr.end_loc}"
                      let funcBody := match aexpr.body with
                        | .TS_BlockStatement blockStmt =>
                          (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
                        | _ => panic! s!"Expected block statement as function body, got: {repr aexpr.body}"
                      let strataFunc : CallHeapStrataFunction := {
                        name := funcName,
                        params := aexpr.params.toList.map (·.name),
                        body := funcBody,
                        returnType := none
                      }
                      let newCtx := ctx.addFunction strataFunc
                      (funcName, newCtx)
                    | some (.TS_IdExpression fid) =>
                      (fid.name, ctx)
                    | _ => panic! "map(callback) expects a function or identifier as the first argument"

                  -- Initialize destination array variable (bind to declared identifier)
                  let dstVar := d.id.name
                  let initDst : TSStrataStatement := .cmd (.init dstVar Heap.HMonoTy.addr (Heap.HExpr.allocSimple []))

                  -- idx/len
                  let idxVar := s!"temp_map_idx_{member.start_loc}"
                  let lenVar := s!"temp_map_len_{member.start_loc}"
                  let initIdx : TSStrataStatement := .cmd (.init idxVar Heap.HMonoTy.int (Heap.HExpr.int 0))
                  let lengthExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "LengthAccess" none) objExpr) (Heap.HExpr.string "length")
                  let initLen : TSStrataStatement := .cmd (.init lenVar Heap.HMonoTy.int lengthExpr)

                  -- guard idx < len
                  let idxRef := Heap.HExpr.lambda (.fvar idxVar none)
                  let lenRef := Heap.HExpr.lambda (.fvar lenVar none)
                  let guard := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Lt" none) idxRef) lenRef

                  -- value = obj[idx]; ret = cb(value, idx, obj); dst[idx] = ret; idx++
                  let valueExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAccess" none) objExpr) idxRef
                  let retVar := s!"temp_map_ret_{member.start_loc}"
                  let callCb : TSStrataStatement := .cmd (.directCall [retVar] cbName [valueExpr, idxRef, objExpr])

                  let dstRef := Heap.HExpr.lambda (.fvar dstVar none)
                  let assignExpr :=
                    Heap.HExpr.app
                      (Heap.HExpr.app
                        (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAssign" none) dstRef)
                        idxRef)
                      (Heap.HExpr.lambda (.fvar retVar none))
                  let writeStmt : TSStrataStatement := .cmd (.set "temp_map_assign_result" assignExpr)

                  let nextIdx := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Add" none) idxRef) (Heap.HExpr.int 1)
                  let incIdx : TSStrataStatement := .cmd (.set idxVar nextIdx)

                  let loopBody : Imperative.Block TSStrataExpression TSStrataCommand := { ss := [callCb, writeStmt, incIdx] }

                  (ctxAfterCb, [initDst, initIdx, initLen, .loop guard none none loopBody])
                else
                  defaultInit
              | _ => defaultInit
            | _ => defaultInit
          | .TS_FunctionExpression funcExpr =>
            -- Handle function expression assignment: let x = function(...) { ... }
            let funcName := d.id.name
            let funcBody := match funcExpr.body with
              | .TS_BlockStatement blockStmt =>
                (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
              | _ => panic! s!"Expected block statement as function body, got: {repr funcExpr.body}"
            dbg_trace s!"[DEBUG] Translating TypeScript function expression assignment: {d.id.name} = function(...)"
            let strataFunc : CallHeapStrataFunction := {
              name := funcName,
              params := funcExpr.params.toList.map (·.name),
              body := funcBody,
              returnType := none  -- We'll infer this later if needed
            }
            let newCtx := ctx.addFunction strataFunc
            dbg_trace s!"[DEBUG] Added function '{funcName}' to context"
            -- Initialize variable to the function reference
            let ty := get_var_type d.id.typeAnnotation d.init
            let funcRef := Heap.HExpr.lambda (.fvar funcName none)
            (newCtx, [.cmd (.init d.id.name ty funcRef)])
          | .TS_ArrowFunctionExpression funcExpr =>
            -- Handle arrow function assignment: let x = (args) => { ... }
            let funcName := d.id.name
            let funcBody := match funcExpr.body with
              | .TS_BlockStatement blockStmt =>
                (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
              | _ => panic! s!"Expected block statement as function body, got: {repr funcExpr.body}"
            dbg_trace s!"[DEBUG] Translating TypeScript arrow function assignment: {d.id.name} = (args) => function(...)"
            let strataFunc : CallHeapStrataFunction := {
              name := funcName,
              params := funcExpr.params.toList.map (·.name),
              body := funcBody,
              returnType := none  -- We'll infer this later if needed
            }
            let newCtx := ctx.addFunction strataFunc
            dbg_trace s!"[DEBUG] Added arrow function '{funcName}' to context"
            -- Initialize variable to the function reference
            let ty := get_var_type d.id.typeAnnotation d.init
            let funcRef := Heap.HExpr.lambda (.fvar funcName none)
            (newCtx, [.cmd (.init d.id.name ty funcRef)])
          | _ =>
            -- Handle simple variable declaration: let x = value
            let value := translate_expr d.init
            let ty := get_var_type d.id.typeAnnotation d.init
            (ctx, [.cmd (.init d.id.name ty value)])

      | .TS_ExpressionStatement expr =>
        match expr.expression with
        | .TS_CallExpression call =>
          match call.callee with
            | .TS_MemberExpression member =>
              -- Handle method calls like arr.push(x) or arr.pop()
              let objExpr := translate_expr member.object
              match member.property with
              | .TS_IdExpression id =>
                match id.name with
                | "push" =>
                  match call.arguments[0]? with
                  | some a =>
                      let valueExpr := translate_expr a
                      let lengthExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "LengthAccess" none) objExpr) (Heap.HExpr.string "length")
                      let pushExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAssign" none) objExpr) lengthExpr) valueExpr
                      (ctx, [.cmd (.set "temp_push_result" pushExpr)])
                  | none => panic! "push() expects 1 argument"
                | "pop" =>
                  -- arr.pop() standalone - read and delete
                  let lengthExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "LengthAccess" none) objExpr) (Heap.HExpr.string "length")
                  let lastIndexExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Sub" none) lengthExpr) (Heap.HExpr.int 1)
                  let tempIndexInit := .cmd (.init "temp_pop_index" Heap.HMonoTy.int lastIndexExpr)
                  let tempIndexVar := Heap.HExpr.lambda (.fvar "temp_pop_index" none)
                  -- Read the value
                  let popExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAccess" none) objExpr) tempIndexVar
                  let readStmt := .cmd (.set "temp_pop_result" popExpr)
                  -- Delete the element
                  let deleteExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAssign" none) objExpr) tempIndexVar) Heap.HExpr.null
                  let deleteStmt := .cmd (.set "temp_delete_result" deleteExpr)
                  (ctx, [tempIndexInit, readStmt, deleteStmt])
                | "forEach" =>
                  -- arr.forEach(callback)
                  let (cbName, ctxAfterCb) :=
                    match call.arguments[0]? with
                    | some (.TS_FunctionExpression fexpr) =>
                      let funcName := s!"__anon_foreach_func_{fexpr.start_loc}_{fexpr.end_loc}"
                      let funcBody := match fexpr.body with
                        | .TS_BlockStatement blockStmt =>
                          (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
                        | _ => panic! s!"Expected block statement as function body, got: {repr fexpr.body}"
                      let strataFunc : CallHeapStrataFunction := {
                        name := funcName,
                        params := fexpr.params.toList.map (·.name),
                        body := funcBody,
                        returnType := none
                      }
                      let newCtx := ctx.addFunction strataFunc
                      (funcName, newCtx)
                    | some (.TS_ArrowFunctionExpression aexpr) =>
                      let funcName := s!"__anon_foreach_arrow_{aexpr.start_loc}_{aexpr.end_loc}"
                      let funcBody := match aexpr.body with
                        | .TS_BlockStatement blockStmt =>
                          (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
                        | _ => panic! s!"Expected block statement as function body, got: {repr aexpr.body}"
                      let strataFunc : CallHeapStrataFunction := {
                        name := funcName,
                        params := aexpr.params.toList.map (·.name),
                        body := funcBody,
                        returnType := none
                      }
                      let newCtx := ctx.addFunction strataFunc
                      (funcName, newCtx)
                    | some (.TS_IdExpression fid) =>
                      (fid.name, ctx)
                    | _ => panic! "forEach(callback) expects a function or identifier as the first argument"

                  let idxVar := s!"temp_foreach_idx_{member.start_loc}"
                  let lenVar := s!"temp_foreach_len_{member.start_loc}"
                  let initIdx : TSStrataStatement := .cmd (.init idxVar Heap.HMonoTy.int (Heap.HExpr.int 0))
                  let lengthExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "LengthAccess" none) objExpr) (Heap.HExpr.string "length")
                  let initLen : TSStrataStatement := .cmd (.init lenVar Heap.HMonoTy.int lengthExpr)
                  -- Build guard: idx < len
                  let idxRef := Heap.HExpr.lambda (.fvar idxVar none)
                  let lenRef := Heap.HExpr.lambda (.fvar lenVar none)
                  let guard := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Lt" none) idxRef) lenRef
                  -- Loop body: value = obj[idx]; callback(value, idx, obj); idx = idx + 1
                  let valueExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAccess" none) objExpr) idxRef
                  let callCb : TSStrataStatement := .cmd (.directCall [] cbName [valueExpr, idxRef, objExpr])
                  let nextIdx := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Add" none) idxRef) (Heap.HExpr.int 1)
                  let incIdx : TSStrataStatement := .cmd (.set idxVar nextIdx)
                  let loopBody : Imperative.Block TSStrataExpression TSStrataCommand := { ss := [callCb, incIdx] }

                  (ctxAfterCb, [initIdx, initLen, .loop guard none none loopBody])
                | "map" =>
                  -- arr.map(callback)
                  dbg_trace s!"[DEBUG] Translating arr.map(callback) method call"
                  let (cbName, ctxAfterCb) :=
                    match call.arguments[0]? with
                    | some (.TS_FunctionExpression fexpr) =>
                      let funcName := s!"__anon_map_func_{fexpr.start_loc}_{fexpr.end_loc}"
                      let funcBody := match fexpr.body with
                        | .TS_BlockStatement blockStmt =>
                          (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
                        | _ => panic! s!"Expected block statement as function body, got: {repr fexpr.body}"
                      let strataFunc : CallHeapStrataFunction := {
                        name := funcName,
                        params := fexpr.params.toList.map (·.name),
                        body := funcBody,
                        returnType := none
                      }
                      let newCtx := ctx.addFunction strataFunc
                      (funcName, newCtx)
                    | some (.TS_ArrowFunctionExpression aexpr) =>
                      let funcName := s!"__anon_map_arrow_{aexpr.start_loc}_{aexpr.end_loc}"
                      let funcBody := match aexpr.body with
                        | .TS_BlockStatement blockStmt =>
                          (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
                        | _ => panic! s!"Expected block statement as function body, got: {repr aexpr.body}"
                      let strataFunc : CallHeapStrataFunction := {
                        name := funcName,
                        params := aexpr.params.toList.map (·.name),
                        body := funcBody,
                        returnType := none
                      }
                      let newCtx := ctx.addFunction strataFunc
                      (funcName, newCtx)
                    | some (.TS_IdExpression fid) =>
                      (fid.name, ctx)
                    | _ => panic! "map(callback) expects a function or identifier as the first argument"

                  -- Prepare destination array to hold mapped values
                  let dstVar := s!"temp_map_arr_{member.start_loc}"
                  let initDst : TSStrataStatement :=
                    .cmd (.init dstVar Heap.HMonoTy.addr (Heap.HExpr.allocSimple []))
                  -- idx/len like forEach
                  let idxVar := s!"temp_map_idx_{member.start_loc}"
                  let lenVar := s!"temp_map_len_{member.start_loc}"
                  let initIdx : TSStrataStatement := .cmd (.init idxVar Heap.HMonoTy.int (Heap.HExpr.int 0))
                  let lengthExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "LengthAccess" none) objExpr) (Heap.HExpr.string "length")
                  let initLen : TSStrataStatement := .cmd (.init lenVar Heap.HMonoTy.int lengthExpr)
                  -- Build guard: idx < len
                  let idxRef := Heap.HExpr.lambda (.fvar idxVar none)
                  let lenRef := Heap.HExpr.lambda (.fvar lenVar none)
                  let guard := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Lt" none) idxRef) lenRef
                  -- Loop body: value = obj[idx] ,ret = cb(value, idx, obj), dst[idx] = ret, idx = idx + 1
                  let valueExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAccess" none) objExpr) idxRef
                  let retVar := s!"temp_map_ret_{member.start_loc}"
                  let callCb : TSStrataStatement := .cmd (.directCall [retVar] cbName [valueExpr, idxRef, objExpr])

                  let dstRef := Heap.HExpr.lambda (.fvar dstVar none)
                  let assignExpr :=
                    Heap.HExpr.app
                      (Heap.HExpr.app
                        (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAssign" none) dstRef)
                        idxRef)
                      (Heap.HExpr.lambda (.fvar retVar none))
                  let writeStmt : TSStrataStatement := .cmd (.set "temp_map_assign_result" assignExpr)

                  let nextIdx := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Add" none) idxRef) (Heap.HExpr.int 1)
                  let incIdx : TSStrataStatement := .cmd (.set idxVar nextIdx)

                  let loopBody : Imperative.Block TSStrataExpression TSStrataCommand :=
                    { ss := [callCb, writeStmt, incIdx] }

                  (ctxAfterCb, [initDst, initIdx, initLen, .loop guard none none loopBody])
                | methodName =>
                  dbg_trace s!"[DEBUG] Translating method call: {methodName}(...)"
                  (ctx, [])
              | _ => (ctx, [])
            | .TS_IdExpression id =>
              -- Handle standalone function call
              dbg_trace s!"[DEBUG] Translating TypeScript standalone function call: {id.name}(...)"
              let args := call.arguments.toList.map translate_expr
              dbg_trace s!"[DEBUG] Function call has {args.length} arguments"
              let lhs := []  -- No left-hand side for standalone calls
              (ctx, [.cmd (.directCall lhs id.name args)])
            | _ => (ctx, [])
        | .TS_AssignmentExpression assgn =>
          assert! assgn.operator == "="
          match assgn.left with
          | .TS_Identifier id =>
            -- Handle identifier assignment: x = value
            match assgn.right with
            | .TS_FunctionExpression funcExpr =>
              -- Capture parameters and body here (since translate_expr is kept pure)
              let funcName := id.name
              let funcBody := match funcExpr.body with
                | .TS_BlockStatement blockStmt =>
                  (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
                | _ => panic! s!"Expected block statement as function body, got: {repr funcExpr.body}"
              let strataFunc : CallHeapStrataFunction := {
                name := funcName,
                params := funcExpr.params.toList.map (·.name),
                body := funcBody,
                returnType := none
              }
              let newCtx := ctx.addFunction strataFunc
              dbg_trace s!"[DEBUG] Added anonymous function '{funcName}' to context (assignment to identifier)"
              let funcRef := Heap.HExpr.lambda (.fvar funcName none)
              (newCtx, [.cmd (.set id.name funcRef)])
            | otherExpr =>
              let value := translate_expr otherExpr
              dbg_trace s!"[DEBUG] Assignment: {id.name} = {repr value}"
              (ctx, [.cmd (.set id.name value)])
          | .TS_MemberExpression member =>
            -- Handle field assignment: obj[field] = value
            let objExpr := translate_expr member.object

            -- If RHS is a function expression, capture params/body now and bind funcRef
            match assgn.right with
            | .TS_FunctionExpression funcExpr =>
              let funcName := s!"__anon_func_{funcExpr.start_loc}_{funcExpr.end_loc}"
              let funcBody := match funcExpr.body with
                | .TS_BlockStatement blockStmt =>
                  (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
                | _ => panic! s!"Expected block statement as function body, got: {repr funcExpr.body}"
              let strataFunc : CallHeapStrataFunction := {
                name := funcName,
                params := funcExpr.params.toList.map (·.name),
                body := funcBody,
                returnType := none
              }
              let newCtx := ctx.addFunction strataFunc
              dbg_trace s!"[DEBUG] Added anonymous function '{funcName}' to context (assignment to member)"
              let funcRef := Heap.HExpr.lambda (.fvar funcName none)
              -- Handle both static and dynamic field assignment using funcRef
              match member.property with
              | .TS_NumericLiteral numLit =>
                let fieldIndex := Float.floor numLit.value |>.toUInt64.toNat
                let assignExpr := Heap.HExpr.assign objExpr fieldIndex funcRef
                (newCtx, [.cmd (.set "temp_assign_result" assignExpr)])
              | .TS_IdExpression id =>
                let fieldExpr := translate_expr (.TS_IdExpression id)
                let assignExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAssign" none) objExpr) fieldExpr) funcRef
                (newCtx, [.cmd (.set "temp_assign_result" assignExpr)])
              | _ =>
                let fieldExpr := translate_expr member.property
                let assignExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAssign" none) objExpr) fieldExpr) funcRef
                (newCtx, [.cmd (.set "temp_assign_result" assignExpr)])
            | otherExpr =>
              let valueExpr := translate_expr otherExpr
              -- Handle both static and dynamic field assignment with normal RHS
              match member.property with
              | .TS_NumericLiteral numLit =>
                -- Static field assignment: obj[5] = value
                let fieldIndex := Float.floor numLit.value |>.toUInt64.toNat
                let assignExpr := Heap.HExpr.assign objExpr fieldIndex valueExpr
                (ctx, [.cmd (.set "temp_assign_result" assignExpr)])
              | .TS_IdExpression id =>
                -- Dynamic field assignment: obj[variable] = value
                let fieldExpr := translate_expr (.TS_IdExpression id)
                let assignExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAssign" none) objExpr) fieldExpr) valueExpr
                (ctx, [.cmd (.set "temp_assign_result" assignExpr)])
              | _ =>
                -- Other dynamic field assignment: obj[expr] = value
                let fieldExpr := translate_expr member.property
                let assignExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "DynamicFieldAssign" none) objExpr) fieldExpr) valueExpr
                (ctx, [.cmd (.set "temp_assign_result" assignExpr)])
          --| _ => panic! s!"Unsupported assignment target: {repr assgn.left}"
        | .TS_FunctionExpression funcExpr =>
          -- Handle standalone function expression (immediately invoked function expression - IIFE)
          let funcName := s!"__anon_func_{funcExpr.start_loc}_{funcExpr.end_loc}"
          let funcBody := match funcExpr.body with
            | .TS_BlockStatement blockStmt =>
              (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
            | _ => panic! s!"Expected block statement as function body, got: {repr funcExpr.body}"
          let strataFunc : CallHeapStrataFunction := {
            name := funcName,
            params := funcExpr.params.toList.map (·.name),
            body := funcBody,
            returnType := none  -- We'll infer this later if needed
          }
          let newCtx := ctx.addFunction strataFunc
          dbg_trace s!"[DEBUG] Added anonymous function '{funcName}' to context"
          -- For now, we don't execute the function; just define it
          (newCtx, [])
        | _ =>
          -- Other expression statements - ignore for now
          (ctx, [])

      | .TS_BlockStatement block =>
        -- lower inside loops:  if (cond) { continue; }  ==>  if (cond) { } else { <rest> }
        -- lower inside loops:  if (cond) { break; }    ==>  if (cond) { } else { <rest> }
        let stmts := block.body.toList

        -- consequent is exactly a bare `continue`
        let isBareContinueStmt : TS_Statement → Bool
          | .TS_ContinueStatement _ => true
          | _ => false

        -- consequent is exactly a bare `break`
        let isBareBreakStmt : TS_Statement → Bool
          | .TS_BreakStatement _ => true
          | _ => false

        let isIfWithBareContinue : TS_Statement → Option TS_IfStatement
          | .TS_IfStatement ifs =>
            let conseqIsBare :=
              match ifs.consequent with
              | .TS_ContinueStatement _ => true
              | .TS_BlockStatement b =>
                  match b.body.toList with
                  | [one] => isBareContinueStmt one
                  | _     => false
              | _ => false
            if conseqIsBare && ifs.alternate.isNone then some ifs else none
          | _ => none

        let isIfWithBareBreak : TS_Statement → Option TS_IfStatement
          | .TS_IfStatement ifs =>
            let conseqIsBare :=
              match ifs.consequent with
              | .TS_BreakStatement _ => true
              | .TS_BlockStatement b =>
                  match b.body.toList with
                  | [one] => isBareBreakStmt one
                  | _     => false
              | _ => false
            if conseqIsBare && ifs.alternate.isNone then some ifs else none
          | _ => none

        -- when we hit the pattern (in a loop), guard the tail with `else`
        let rec go (accCtx : TranslationContext) (acc : List TSStrataStatement) (rest : List TS_Statement)
          : TranslationContext × List TSStrataStatement :=
          match rest with
          | [] => (accCtx, acc)
          | s :: tail =>
            let continueMatch := isIfWithBareContinue s
            let breakMatch := isIfWithBareBreak s
            dbg_trace s!"[DEBUG] Block statement processing: continueMatch={continueMatch.isSome}, breakMatch={breakMatch.isSome}, ct.continueLabel?={ct.continueLabel?}, ct.breakLabel?={ct.breakLabel?}"
            match ct.continueLabel?, ct.breakFlagVar?, continueMatch, breakMatch with
            | some _, _, some ifs, _ =>
              -- Continue case: Translate the tail (everything after the `if`) under the `else` branch
              let (tailCtx, tailStmts) :=
                tail.foldl
                  (fun (p, accS) stmt =>
                    let (p2, ss2) := translate_statement_core stmt p ct
                    (p2, accS ++ ss2))
                  (accCtx, [])
              let cond := translate_expr ifs.test
              let thenBlk : Imperative.Block TSStrataExpression TSStrataCommand := { ss := [] }
              let elseBlk : Imperative.Block TSStrataExpression TSStrataCommand := { ss := tailStmts }
              -- Emit one conditional and STOP
              (tailCtx, acc ++ [ .ite cond thenBlk elseBlk ])
            | _, some breakFlagVar, _, some ifs =>
              -- Break case: Set break flag in then branch, execute tail in else branch
              let (tailCtx, tailStmts) :=
                tail.foldl
                  (fun (p, accS) stmt =>
                    let (p2, ss2) := translate_statement_core stmt p ct
                    (p2, accS ++ ss2))
                  (accCtx, [])
              let cond := translate_expr ifs.test
              let setBreakFlag : TSStrataStatement := .cmd (.set breakFlagVar Heap.HExpr.true)
              let thenBlk : Imperative.Block TSStrataExpression TSStrataCommand := { ss := [setBreakFlag] }
              let elseBlk : Imperative.Block TSStrataExpression TSStrataCommand := { ss := tailStmts }
              -- Emit conditional: if condition then set break flag, else execute remaining statements
              (tailCtx, acc ++ [ .ite cond thenBlk elseBlk ])
            | _, _, _, _ =>
              let (newCtx, ss) := translate_statement_core s accCtx ct
              go newCtx (acc ++ ss) tail

        go ctx [] stmts

      | .TS_IfStatement ifStmt =>
        -- Handle if statement: if test then consequent else alternate
        let testExpr := translate_expr ifStmt.test
        let (thenCtx, thenStmts) := translate_statement_core ifStmt.consequent ctx ct
        let (elseCtx, elseStmts) := match ifStmt.alternate with
          | some altStmt => translate_statement_core altStmt ctx ct
          | none => (ctx, [])
        let thenBlock : Imperative.Block TSStrataExpression TSStrataCommand := { ss := thenStmts }
        let elseBlock : Imperative.Block TSStrataExpression TSStrataCommand := { ss := elseStmts }
        -- For now, we'll use the then context (could be more sophisticated)
        (thenCtx, [.ite testExpr thenBlock elseBlock])

      | .TS_WhileStatement whileStmt =>
        dbg_trace s!"[DEBUG] Translating while statement at loc {whileStmt.start_loc}-{whileStmt.end_loc}"
        dbg_trace s!"[DEBUG] While test: {repr whileStmt.test}"
        dbg_trace s!"[DEBUG] While body: {repr whileStmt.body}"

        let continueLabel := s!"while_continue_{whileStmt.start_loc}"
        let breakLabel := s!"while_break_{whileStmt.start_loc}"
        let breakFlagVar := s!"break_flag_{whileStmt.start_loc}"

        -- Initialize break flag to false
        let initBreakFlag : TSStrataStatement := .cmd (.init breakFlagVar Heap.HMonoTy.bool Heap.HExpr.false)

        let testExpr := translate_expr whileStmt.test
        let (bodyCtx, bodyStmts) :=
          translate_statement_core whileStmt.body ctx { ct with continueLabel? := some continueLabel, breakLabel? := some breakLabel, breakFlagVar? := some breakFlagVar }

        -- Modify loop condition to include break flag check: (original_condition && !break_flag)
        -- Use deferredIte instead of boolean operations
        let breakFlagExpr := Heap.HExpr.lambda (.fvar breakFlagVar none)
        let combinedCondition := Heap.HExpr.deferredIte breakFlagExpr Heap.HExpr.false testExpr

        let bodyBlock : Imperative.Block TSStrataExpression TSStrataCommand := { ss := bodyStmts }
        (bodyCtx, [ initBreakFlag, .loop combinedCondition none none bodyBlock ])

        | .TS_ForStatement forStmt =>
          dbg_trace s!"[DEBUG] Translating for statement at loc {forStmt.start_loc}-{forStmt.end_loc}"

          let continueLabel := s!"for_continue_{forStmt.start_loc}"
          let breakLabel := s!"for_break_{forStmt.start_loc}"
          let breakFlagVar := s!"for_break_flag_{forStmt.start_loc}"

          -- Initialize break flag to false
          let initBreakFlag : TSStrataStatement := .cmd (.init breakFlagVar Heap.HMonoTy.bool Heap.HExpr.false)

          -- init phase
          let (_, initStmts) := translate_statement_core (.TS_VariableDeclaration forStmt.init) ctx
          -- guard (test)
          let guard := translate_expr forStmt.test
          -- body (first translate loop body with break support)
          let (ctx1, bodyStmts) :=
              translate_statement_core forStmt.body ctx
                { continueLabel? := some continueLabel, breakLabel? := some breakLabel, breakFlagVar? := some breakFlagVar }
          -- update (translate expression into statements following ExpressionStatement style)
          let (_, updateStmts) :=
            translate_statement_core
              (.TS_ExpressionStatement {
                expression := .TS_AssignmentExpression forStmt.update,
                start_loc := forStmt.start_loc,
                end_loc := forStmt.end_loc,
                loc := forStmt.loc,
                type := "TS_AssignmentExpression"
              }) ctx1

          -- Modify loop condition to include break flag check: (original_condition && !break_flag)
          let breakFlagExpr := Heap.HExpr.lambda (.fvar breakFlagVar none)
          let combinedCondition := Heap.HExpr.deferredIte breakFlagExpr Heap.HExpr.false guard

          -- assemble loop body (body + update)
          let loopBody : Imperative.Block TSStrataExpression TSStrataCommand :=
            { ss := bodyStmts ++ updateStmts }

          -- output: init break flag, init statements, then a loop statement
          (ctx1, [initBreakFlag] ++ initStmts ++ [ .loop combinedCondition none none loopBody])

        | .TS_SwitchStatement switchStmt =>
          -- Handle switch statement: switch discriminant { cases }

          -- Process all cases in their original order, separating regular from default
          let allCases := switchStmt.cases.toList
          let (regularCaseStmts, defaultStmts) := allCases.foldl (fun (regCases, defStmts) case =>
            match case.test with
            | some expr =>
              -- Regular case
              let discrimExpr := translate_expr switchStmt.discriminant
              let caseValue := translate_expr expr
              let testExpr := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Eq" none) discrimExpr) caseValue
              let (caseCtx, stmts) := case.consequent.foldl (fun (accCtx, accStmts) stmt =>
                let (newCtx, newStmts) := translate_statement_core stmt accCtx
                (newCtx, accStmts ++ newStmts)) (ctx, [])
              (regCases ++ [(testExpr, stmts)], defStmts)
            | none =>
              -- Default case
              let (defaultCtx, stmts) := case.consequent.foldl (fun (accCtx, accStmts) stmt =>
                let (newCtx, newStmts) := translate_statement_core stmt accCtx
                (newCtx, accStmts ++ newStmts)) (ctx, [])
              (regCases, stmts)
          ) ([], [])

          -- Build nested if-then-else structure for regular cases
          let rec build_cases (cases: List (Heap.HExpr × List TSStrataStatement)) (defaultStmts: List TSStrataStatement) : TSStrataStatement :=
            match cases with
            | [] =>
              -- No regular cases, just execute default if it exists
              let defaultBlock : Imperative.Block TSStrataExpression TSStrataCommand := { ss := defaultStmts }
              .block "default" defaultBlock
            | [(test, stmts)] =>
              let thenBlock : Imperative.Block TSStrataExpression TSStrataCommand := { ss := stmts }
              let elseBlock : Imperative.Block TSStrataExpression TSStrataCommand := { ss := defaultStmts }
              .ite test thenBlock elseBlock
            | (test, stmts) :: rest =>
              let thenBlock : Imperative.Block TSStrataExpression TSStrataCommand := { ss := stmts }
              let elseBlock := build_cases rest defaultStmts
              let elseBlockWrapped : Imperative.Block TSStrataExpression TSStrataCommand := { ss := [elseBlock] }
              .ite test thenBlock elseBlockWrapped

          let switchStructure := build_cases regularCaseStmts defaultStmts
          (ctx, [switchStructure])

        | .TS_ContinueStatement cont =>
          let tgt :=
            match ct.continueLabel? with
            | some lab => lab
            | none     =>
                dbg_trace "[WARN] `continue` encountered outside of a loop; emitting goto to __unbound_continue";
                "__unbound_continue"
          (ctx, [ .goto tgt ])

        | .TS_BreakStatement brk =>
          -- Handle break statement if loop context fails to handle it
          dbg_trace "[WARN] `break` statement not handled by pattern matching";
          match ct.breakFlagVar? with
          | some flagVar =>
            -- Set break flag to true as fallback
            (ctx, [ .cmd (.set flagVar Heap.HExpr.true) ])
          | none =>
            dbg_trace "[WARN] `break` encountered outside of a loop; using fallback goto";
            let tgt :=
              match ct.breakLabel? with
              | some lab => lab
              | none     => "__unbound_break"
            (ctx, [ .goto tgt ])

        | _ => panic! s!"Unimplemented statement: {repr s}"

-- Translate TypeScript statements to TypeScript-Strata statements
partial def translate_statement (s: TS_Statement) (ctx : TranslationContext) : TranslationContext × List TSStrataStatement :=
  translate_statement_core s ctx {}


-- Translate list of TypeScript statements with context
def translate_program (statements: List TS_Statement) : TranslationContext × List TSStrataStatement :=
  statements.foldl (fun (accCtx, accStmts) stmt =>
    let (newCtx, stmts) := translate_statement stmt accCtx
    (newCtx, accStmts ++ stmts)) (TranslationContext.empty, [])

-- Translate a full Program structure
def translate_full_program (prog: TS_Program) : TranslationContext × List TSStrataStatement :=
  translate_program prog.body.toList

-- Translate a full TS_File structure
def translate_full_ts_program (file: TS_File) : TranslationContext × List TSStrataStatement :=
  translate_full_program file.program

-- Helper to describe a TSStrata statement
def describeTSStrataStatement (stmt: TSStrataStatement) : String :=
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



--#eval translate_expr (.NumericLiteral {value := 42, extra := {raw := "42", rawValue := 42}, type := "NumericLiteral"})

end TSStrata
