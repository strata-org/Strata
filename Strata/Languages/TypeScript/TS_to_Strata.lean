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
  -- | "TS_TSArrayType" => Heap.HMonoTy.addr
  | _ => panic! s!"Unsupported type: {ty}"

def Option_TS_TSTypeKeyword_to_str (i: Option TS_TSTypeKeyword) : String :=
  match i with
  | .some s => match s with
    | .TS_TSNumberKeyword _ => "TS_TSNumberKeyword"
    | .TS_TSBooleanKeyword _ => "TS_TSBooleanKeyword"
    | .TS_TSStringKeyword _ => "TS_TSStringKeyword"
    -- | .TS_TSArrayType _ => "TS_TSArrayType"
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
  -- | .TS_ArrayExpression _ => Heap.HMonoTy.addr   -- Arrays are addresses
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

  -- | .TS_ArrayExpression arr =>
    -- -- Translate [value1, value2, value3] to heap allocation with numeric indices
    -- let fields := arr.elements.toList.mapIdx (fun idx elem =>
      -- (idx, translate_expr elem))
    -- -- Arrays store elements at numeric indices: 0->value1, 1->value2, etc.
    -- Heap.HExpr.allocSimple fields

  | .TS_MemberExpression e =>
    -- Translate obj[index] to heap dereference
    let objExpr := translate_expr e.object
    -- Handle both static and dynamic field access
    match e.property with
    | .TS_NumericLiteral numLit =>
      -- Static field access: obj[5]
      let field := Float.floor numLit.value |>.toUInt64.toNat
      Heap.HExpr.deref objExpr field
    | .TS_IdExpression id =>
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
    -- Handle function calls - translate to expressions for now
    -- For now, create a placeholder that will be handled during call statement processing
    Heap.HExpr.lambda (.fvar s!"call_{call.callee.name}" none)

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

        let funcBody := match funcDecl.body with
          | .TS_BlockStatement blockStmt =>
            (blockStmt.body.toList.map (fun stmt => translate_statement_core stmt ctx ct |>.snd)).flatten
          | _ => panic! s!"Expected block statement as function body, got: {repr funcDecl.body}"

        dbg_trace s!"[DEBUG] Translated function body to {funcBody.length} Strata statements"

        let strataFunc : CallHeapStrataFunction := {
          name := funcDecl.id.name,
          params := funcDecl.params.toList.map (·.name),
          body := funcBody,
          returnType := none  -- We'll infer this later if needed
        }
        let newCtx := ctx.addFunction strataFunc
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
          -- Check if this is a function call assignment
          match d.init with
          | .TS_CallExpression call =>
            -- Handle function call assignment: let x = func(args)
            dbg_trace s!"[DEBUG] Translating TypeScript function call assignment: {d.id.name} = {call.callee.name}(...)"
            let args := call.arguments.toList.map translate_expr
            dbg_trace s!"[DEBUG] Function call has {args.length} arguments"
            let lhs := [d.id.name]  -- Left-hand side variables to store result
            (ctx, [.cmd (.directCall lhs call.callee.name args)])
          | _ =>
            -- Handle simple variable declaration: let x = value
            let value := translate_expr d.init
            let ty := get_var_type d.id.typeAnnotation d.init
            (ctx, [.cmd (.init d.id.name ty value)])

      | .TS_ExpressionStatement expr =>
        match expr.expression with
        | .TS_CallExpression call =>
          -- Handle standalone function call
          dbg_trace s!"[DEBUG] Translating TypeScript standalone function call: {call.callee.name}(...)"
          let args := call.arguments.toList.map translate_expr
          dbg_trace s!"[DEBUG] Function call has {args.length} arguments"
          let lhs := []  -- No left-hand side for standalone calls
          (ctx, [.cmd (.directCall lhs call.callee.name args)])
        | .TS_AssignmentExpression assgn =>
          assert! assgn.operator == "="
          match assgn.left with
          | .TS_Identifier id =>
            -- Handle identifier assignment: x = value
            let value := translate_expr assgn.right
            dbg_trace s!"[DEBUG] Assignment: {id.name} = {repr value}"
            (ctx, [.cmd (.set id.name value)])
          | .TS_MemberExpression member =>
            -- Handle field assignment: obj[field] = value
            let objExpr := translate_expr member.object
            let valueExpr := translate_expr assgn.right

            -- Handle both static and dynamic field assignment
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
          -- init phase
          let (_, initStmts) := translate_statement_core (.TS_VariableDeclaration forStmt.init) ctx
          -- guard (test)
          let guard := translate_expr forStmt.test
          -- body (first translate loop body)
          let (ctx1, bodyStmts) := translate_statement_core forStmt.body ctx
          -- update (translate expression into statements following ExpressionStatement style)
          let (_, updateStmts) :=
            translate_statement_core (.TS_ExpressionStatement { expression := .TS_AssignmentExpression forStmt.update, start_loc := forStmt.start_loc, end_loc := forStmt.end_loc, loc:= forStmt.loc, type := "TS_AssignmentExpression" }) ctx1
          -- assemble loop body (body + update)
          let loopBody : Imperative.Block TSStrataExpression TSStrataCommand :=
            { ss := bodyStmts ++ updateStmts }

          -- output: init statements first, then a loop statement
          (ctx1, initStmts ++ [ .loop guard none none loopBody])

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

      | .TS_SwitchStatement switchStmt =>
        -- Handle switch statement with fallthrough and break semantics
        dbg_trace s!"[DEBUG] Translating switch statement at loc {switchStmt.start_loc}-{switchStmt.end_loc}"

        -- Variables for storing control variables
        let loc := switchStmt.start_loc
        let discriminantVar := s!"switch_discriminant_{loc}" -- Stores the switch expression value
        let fallthroughVar := s!"switch_fallthrough_{loc}" -- Stores fallthrough state
        let breakFlagVar := s!"switch_break_{loc}" -- Stores break state

        -- Initialize control variables
        let initDiscriminant : TSStrataStatement := .cmd (.init discriminantVar (infer_type_from_expr switchStmt.discriminant) (translate_expr switchStmt.discriminant))
        let initFallthrough : TSStrataStatement := .cmd (.init fallthroughVar Heap.HMonoTy.bool Heap.HExpr.false)
        let initBreakFlag : TSStrataStatement := .cmd (.init breakFlagVar Heap.HMonoTy.bool Heap.HExpr.false)

        -- Helper: split statements at break
        let splitAtBreak (stmts : List TS_Statement) : List TS_Statement × Bool :=
          let rec loop acc rest :=
            match rest with
            | [] => (acc.reverse, false)
            | .TS_BreakStatement _ :: _ => (acc.reverse, true)
            | s :: tail => loop (s :: acc) tail
          loop [] stmts

        -- Helper: translate case body
        let translateCaseBody (stmts : List TS_Statement) (caseCtx : TranslationContext) : TranslationContext × List TSStrataStatement :=
          stmts.foldl (fun (c, acc) stmt =>
            let (c2, ss) := translate_statement_core stmt c ct
            (c2, acc ++ ss)) (caseCtx, [])

        -- Helper: build case statements with optional break and fallthrough
        let buildCaseStmts (caseStmts : List TSStrataStatement) (hasBreak : Bool) (isDefault : Bool) : List TSStrataStatement :=
          let setFallthrough := .cmd (.set fallthroughVar Heap.HExpr.true)
          let setBreak := .cmd (.set breakFlagVar Heap.HExpr.true)
          let stmts := if isDefault then caseStmts else setFallthrough :: caseStmts
          if hasBreak then stmts ++ [setBreak] else stmts

        -- Flag references
        let breakFlagRef := Heap.HExpr.lambda (.fvar breakFlagVar none)
        let discriminantRef := Heap.HExpr.lambda (.fvar discriminantVar none)
        let fallthroughRef := Heap.HExpr.lambda (.fvar fallthroughVar none)

        -- Helper: create condition (if break then false else baseCondition)
        let mkCondition (baseCondition : Heap.HExpr) : Heap.HExpr :=
          Heap.HExpr.deferredIte breakFlagRef Heap.HExpr.false baseCondition

        -- Helper: build case condition for regular case
        let mkCaseCondition (testExpr : TS_Expression) : Heap.HExpr :=
          let testVal := translate_expr testExpr
          let matchCond := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Int.Eq" none) discriminantRef) testVal
          let matchOrFallthrough := Heap.HExpr.app (Heap.HExpr.app (Heap.HExpr.deferredOp "Bool.Or" none) fallthroughRef) matchCond
          mkCondition matchOrFallthrough

        -- Recursive case builder
        let rec buildCases (remainingCases : List TS_SwitchCase) (accCtx : TranslationContext) : TranslationContext × TSStrataStatement :=
          let emptyBlock : Imperative.Block TSStrataExpression TSStrataCommand := { ss := [] }

          match remainingCases with
          | [] => (accCtx, .ite Heap.HExpr.false emptyBlock emptyBlock)

          | [singleCase] =>
            -- Last case: no rest to chain
            let (stmtsBeforeBreak, hasBreak) := splitAtBreak singleCase.consequent.toList
            let (caseCtx, caseStmts) := translateCaseBody stmtsBeforeBreak accCtx
            let isDefault := singleCase.test.isNone
            let finalStmts := buildCaseStmts caseStmts hasBreak isDefault

            let condition := match singleCase.test with
              | none => mkCondition Heap.HExpr.true  -- Default: if !break then true
              | some testExpr => mkCaseCondition testExpr

            (caseCtx, .ite condition { ss := finalStmts } emptyBlock)

          | currentCase :: restCases =>
            -- Non-last case: chain with rest
            let (stmtsBeforeBreak, hasBreak) := splitAtBreak currentCase.consequent.toList
            let (caseCtx, caseStmts) := translateCaseBody stmtsBeforeBreak accCtx
            let isDefault := currentCase.test.isNone
            let finalStmts := buildCaseStmts caseStmts hasBreak isDefault
            let (restCtx, restStmt) := buildCases restCases caseCtx

            let condition := match currentCase.test with
              | none => mkCondition Heap.HExpr.true  -- Default: if !break then true
              | some testExpr => mkCaseCondition testExpr

            (restCtx, .ite condition { ss := finalStmts ++ [restStmt] } { ss := [restStmt] })

        let (finalCtx, switchBody) := buildCases switchStmt.cases.toList ctx
        dbg_trace s!"[DEBUG] Switch statement translated with {switchStmt.cases.size} cases (with break support)"
        (finalCtx, [initDiscriminant, initFallthrough, initBreakFlag, switchBody])

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
