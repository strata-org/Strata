/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion
import Strata.DL.SMT.SMT
import Strata.DL.SMT.Factory

/-!
# B3 to SMT Converter

This module converts B3 programs to SMT terms for verification.

## Workflow
1. Parse B3 concrete syntax (CST)
2. Convert CST to B3 abstract syntax (AST) with de Bruijn indices
3. Convert B3 AST to SMT terms
4. Format SMT terms using the SMT encoder

## Key Differences
- B3 uses named identifiers in CST, de Bruijn indices in AST
- SMT uses named variables (TermVar)
- Conversion maintains a context mapping de Bruijn indices to SMT variable names
-/

namespace Strata.B3ToSMT

open Strata
open Strata.B3CST
open Strata.B3AST
open Strata.SMT
open Strata.SMT.Factory

---------------------------------------------------------------------
-- Conversion Context
---------------------------------------------------------------------

structure ConversionContext where
  vars : List String  -- Maps de Bruijn index to variable name

namespace ConversionContext

def empty : ConversionContext := { vars := [] }

def push (ctx : ConversionContext) (name : String) : ConversionContext :=
  { vars := name :: ctx.vars }

def lookup (ctx : ConversionContext) (idx : Nat) : Option String :=
  ctx.vars[idx]?

end ConversionContext

---------------------------------------------------------------------
-- B3AST to SMT Conversion
---------------------------------------------------------------------

/-- Create SMT terms without constant folding to preserve structure -/
partial def binaryOpToSMTRaw : B3AST.BinaryOp M → (Term → Term → Term)
  | .iff _ => fun t1 t2 => Term.app .eq [t1, t2] .bool
  | .implies _ => fun t1 t2 => Term.app .implies [t1, t2] .bool
  | .impliedBy _ => fun t1 t2 => Term.app .implies [t2, t1] .bool
  | .and _ => fun t1 t2 => Term.app .and [t1, t2] .bool
  | .or _ => fun t1 t2 => Term.app .or [t1, t2] .bool
  | .eq _ => fun t1 t2 => Term.app .eq [t1, t2] .bool
  | .neq _ => fun t1 t2 => Term.app .not [Term.app .eq [t1, t2] .bool] .bool
  | .lt _ => fun t1 t2 => Term.app .lt [t1, t2] .bool
  | .le _ => fun t1 t2 => Term.app .le [t1, t2] .bool
  | .ge _ => fun t1 t2 => Term.app .ge [t1, t2] .bool
  | .gt _ => fun t1 t2 => Term.app .gt [t1, t2] .bool
  | .add _ => fun t1 t2 => Term.app .add [t1, t2] .int
  | .sub _ => fun t1 t2 => Term.app .sub [t1, t2] .int
  | .mul _ => fun t1 t2 => Term.app .mul [t1, t2] .int
  | .div _ => fun t1 t2 => Term.app .div [t1, t2] .int
  | .mod _ => fun t1 t2 => Term.app .mod [t1, t2] .int

partial def unaryOpToSMTRaw : B3AST.UnaryOp M → (Term → Term)
  | .not _ => fun t => Term.app .not [t] .bool
  | .neg _ => fun t => Term.app .neg [t] .int

partial def literalToSMT : B3AST.Literal M → Term
  | .intLit _ n => Term.int n
  | .boolLit _ b => Term.bool b
  | .stringLit _ s => Term.string s

partial def expressionToSMT (ctx : ConversionContext) : B3AST.Expression M → Option Term
  | .literal _ lit => some (literalToSMT lit)
  | .id _ idx =>
      match ctx.lookup idx with
      | some name => some (Term.var ⟨name, .int⟩)  -- Default to int type for now
      | none => none
  | .ite _ cond thn els =>
      match expressionToSMT ctx cond, expressionToSMT ctx thn, expressionToSMT ctx els with
      | some c, some t, some e => some (Term.app .ite [c, t, e] t.typeOf)
      | _, _, _ => none
  | .binaryOp _ op lhs rhs =>
      match expressionToSMT ctx lhs, expressionToSMT ctx rhs with
      | some l, some r => some ((binaryOpToSMTRaw op) l r)
      | _, _ => none
  | .unaryOp _ op arg =>
      match expressionToSMT ctx arg with
      | some a => some ((unaryOpToSMTRaw op) a)
      | none => none
  | .functionCall _ fnName args =>
      -- Convert function calls to uninterpreted functions
      let argTerms := args.val.toList.filterMap (expressionToSMT ctx)
      if argTerms.length == args.val.size then
        let uf : UF := {
          id := fnName.val,
          args := argTerms.map (fun t => ⟨"_", t.typeOf⟩),  -- Anonymous args
          out := .int  -- Default to int return type
        }
        some (Term.app (.uf uf) argTerms .int)
      else none
  | .labeledExpr _ _ expr => expressionToSMT ctx expr
  | .letExpr _ _var value body =>
      -- Let expressions: inline the value
      -- Since B3 let uses de Bruijn indices, we need to substitute
      -- For simplicity, we'll convert both value and body, then inline at SMT level
      let ctx' := ctx.push _var.val
      match expressionToSMT ctx value, expressionToSMT ctx' body with
      | some _v, some b =>
          -- TODO: Implement proper let support with substitution or SMT let construct
          some b  -- For now, just return body (incorrect but allows compilation)
      | _, _ => none
  | .quantifierExpr _ qkind var _ty patterns body =>
      -- Quantifiers introduce a new bound variable
      let ctx' := ctx.push var.val
      match expressionToSMT ctx' body with
      | some b =>
          -- Convert patterns to SMT triggers
          let patternTerms := patterns.val.toList.filterMap (fun p =>
            match p with
            | .pattern _ exprs =>
                let terms := exprs.val.toList.filterMap (expressionToSMT ctx')
                if terms.length == exprs.val.size then some terms else none
          )
          -- Create trigger term from patterns
          let trigger := if patternTerms.isEmpty then
            Factory.mkSimpleTrigger var.val .int
          else
            -- Build trigger from pattern expressions
            patternTerms.foldl (fun acc terms =>
              terms.foldl (fun t term => Factory.addTrigger term t) acc
            ) (Term.app .triggers [] .trigger)
          match qkind with
          | .forall _ => some (Factory.quant .all var.val .int trigger b)
          | .exists _ => some (Factory.quant .exist var.val .int trigger b)
      | none => none

---------------------------------------------------------------------
-- Example: Simple B3 Program
---------------------------------------------------------------------

/-- Extract the program OperationF from a parsed DDM program -/
def extractProgramOp (prog : Program) : OperationF SourceRange :=
  match prog.commands.toList with
  | [op] =>
      if op.name.name == "command_program" then
        match op.args.toList with
        | [ArgF.op progOp] => progOp
        | _ => default
      else default
  | _ => default

/-- Convert DDM Program to B3CST -/
def programToB3CST (prog : Program) : B3CST.Program SourceRange :=
  match B3CST.Program.ofAst (extractProgramOp prog) with
  | .ok cstProg => cstProg
  | .error _ => default

/-- Convert B3CST to B3AST -/
def b3CSTToAST (cst : B3CST.Program SourceRange) : B3AST.Program Unit × List (B3.CSTToASTError SourceRange) :=
  let (prog, errors) := B3.programFromCST B3.FromCSTContext.empty cst
  (B3AST.Program.mapMetadata (fun _ => ()) prog, errors)

/-- Format SMT term directly without ANF (A-normal form) -/
partial def formatTermDirect : Term → String
  | Term.prim (.bool b) => if b then "true" else "false"
  | Term.prim (.int i) => toString i
  | Term.prim (.string s) => s!"\"{ s}\""
  | Term.var v => v.id
  | Term.quant qk args trigger body =>
      let qkStr := match qk with | .all => "forall" | .exist => "exists"
      let varDecls := args.map (fun v => s!"({v.id} {formatType v.ty})")
      let varDeclsStr := String.intercalate " " varDecls
      -- Check if trigger has meaningful patterns
      match trigger with
      | Term.app .triggers triggerExprs .trigger =>
          if triggerExprs.isEmpty then
            -- No patterns, simple quantifier
            s!"({qkStr} ({varDeclsStr}) {formatTermDirect body})"
          else
            -- Has patterns, format with :pattern annotation
            let patternStrs := triggerExprs.map (fun t => s!"({formatTermDirect t})")
            let patternStr := String.intercalate " " (patternStrs.map (fun p => s!":pattern {p}"))
            s!"({qkStr} ({varDeclsStr}) (! {formatTermDirect body} {patternStr}))"
      | _ =>
          -- Fallback for non-trigger terms
          s!"({qkStr} ({varDeclsStr}) {formatTermDirect body})"
  | Term.app op args _ =>
      match op with
      | .uf f =>
          let argStrs := args.map formatTermDirect
          if argStrs.isEmpty then
            s!"({f.id})"  -- 0-ary function call needs parentheses
          else
            s!"({f.id} {String.intercalate " " argStrs})"
      | .ite => s!"(ite {formatTermDirect args[0]!} {formatTermDirect args[1]!} {formatTermDirect args[2]!})"
      | .eq => s!"(= {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .add => s!"(+ {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .sub => s!"(- {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .mul => s!"(* {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .div => s!"(div {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .mod => s!"(mod {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .lt => s!"(< {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .le => s!"(<= {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .gt => s!"(> {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .ge => s!"(>= {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .not => s!"(not {formatTermDirect args[0]!})"
      | .and => s!"(and {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .or => s!"(or {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .implies => s!"(=> {formatTermDirect args[0]!} {formatTermDirect args[1]!})"
      | .neg => s!"(- {formatTermDirect args[0]!})"
      | _ => s!"(unsupported-op {args.length})"
  | _ => "(unsupported-term)"
where
  formatType : TermType → String
    | .bool => "Bool"
    | .int => "Int"
    | .real => "Real"
    | .string => "String"
    | .bitvec n => s!"(_ BitVec {n})"
    | _ => "UnknownType"

/-- Convert B3AST program to list of SMT commands -/
def programToSMTCommands (prog : B3AST.Program M) : List String :=
  match prog with
  | .program _ decls =>
      let declList := decls.val.toList
      -- First pass: declare all function signatures
      let functionDecls := declList.filterMap (fun d =>
        match d with
        | .function _ name params _ _ _ =>
            let argTypes := params.val.toList.map (fun _ => "Int")
            let argTypeStr := String.intercalate " " argTypes
            some s!"(declare-fun {name.val} ({argTypeStr}) Int)"
        | _ => none
      )
      -- Second pass: generate axioms for function bodies, axioms, and checks
      let axioms := declList.flatMap (fun d =>
        match d with
        | .function _ name params _ _ body =>
            -- Generate definition axiom if function has a body
            match body.val with
            | some (.functionBody _ whens bodyExpr) =>
                let paramNames := params.val.toList.map (fun p => match p with | .fParameter _ _ n _ => n.val)
                let ctx' := paramNames.foldl (fun acc n => acc.push n) ConversionContext.empty
                match expressionToSMT ctx' bodyExpr with
                | some bodyTerm =>
                    let paramVars := paramNames.map (fun n => Term.var ⟨n, .int⟩)
                    let uf : UF := { id := name.val, args := paramVars.map (fun t => ⟨"_", t.typeOf⟩), out := .int }
                    let funcCall := Term.app (.uf uf) paramVars .int
                    let equality := Term.app .eq [funcCall, bodyTerm] .bool
                    let axiomBody := if whens.val.isEmpty then
                      equality
                    else
                      let whenTerms := whens.val.toList.filterMap (fun w =>
                        match w with | .when _ e => expressionToSMT ctx' e
                      )
                      let antecedent := whenTerms.foldl (fun acc t => Term.app .and [acc, t] .bool) (Term.bool true)
                      Term.app .or [Term.app .not [antecedent] .bool, equality] .bool
                    let axiomTerm := if paramNames.isEmpty then
                      axiomBody
                    else
                      -- Create trigger from the function call (e.g., f(x) not just x)
                      let trigger := Term.app .triggers [funcCall] .trigger
                      paramNames.foldl (fun body pname =>
                        Factory.quant .all pname .int trigger body
                      ) axiomBody
                    [s!"(assert {formatTermDirect axiomTerm})"]
                | none => []
            | none => []
        | .axiom _ _ expr =>
            match expressionToSMT ConversionContext.empty expr with
            | some term => [s!"(assert {formatTermDirect term})"]
            | none => []
        | .checkDecl _ expr =>
            match expressionToSMT ConversionContext.empty expr with
            | some term =>
                [ "(push 1)"
                , s!"(assert (not {formatTermDirect term}))"
                , "(check-sat)"
                , "(pop 1)"
                ]
            | none => []
        | _ => []
      )
      functionDecls ++ axioms

---------------------------------------------------------------------
-- Test
---------------------------------------------------------------------

/-- Format B3 program to string -/
def formatB3Program (prog : Program) : String :=
  let ctx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let state : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a d => a.insert d.name }
  match prog.commands.toList with
  | [op] =>
      if op.name.name == "command_program" then
        match op.args.toList with
        | [ArgF.op progOp] =>
            match B3CST.Program.ofAst progOp with
            | .ok cstProg =>
                let cstAst := cstProg.toAst
                (mformat (ArgF.op cstAst) ctx state).format.pretty
            | .error msg => s!"Parse error: {msg}"
        | _ => "Error: expected program op"
      else s!"Error: expected command_program, got {op.name.name}"
  | _ => "Error: expected single command"

/-- Test B3 to SMT conversion for a given program -/
def testB3ToSMT (prog : Program) : IO Unit := do
  let cst := programToB3CST prog
  let (ast, _errors) := b3CSTToAST cst
  let smtCommands := programToSMTCommands ast
  for cmd in smtCommands do
    IO.println cmd

/--
info: (declare-fun abs (Int) Int)
(assert (forall ((x Int)) (! (= (abs x) (ite (>= x 0) x (- x))) :pattern ((abs x)))))
(push 1)
(assert (not (= (abs (- 5)) 5)))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testB3ToSMT $ #strata program B3CST;
function abs(x : int) : int {
  if x >= 0 then x else -x
}
check abs(-5) == 5
#end

/--
info: (declare-fun isEven (Int) Int)
(declare-fun isOdd (Int) Int)
(assert (forall ((n Int)) (! (= (isEven n) (ite (= n 0) 1 (isOdd (- n 1)))) :pattern ((isEven n)))))
(assert (forall ((n Int)) (! (= (isOdd n) (ite (= n 0) 0 (isEven (- n 1)))) :pattern ((isOdd n)))))
(push 1)
(assert (not (= (isEven 4) 1)))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testB3ToSMT $ #strata program B3CST;
function isEven(n : int) : int {
  if n == 0 then 1 else isOdd(n - 1)
}
function isOdd(n : int) : int {
  if n == 0 then 0 else isEven(n - 1)
}
check isEven(4) == 1
#end

/--
info: (declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (=> (> x 0) (> (f x) 0)) :pattern ((f x)))))
(push 1)
(assert (not (=> (> 5 0) (> (f 5) 0))))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testB3ToSMT $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) x > 0 ==> f(x) > 0
check 5 > 0 ==> f(5) > 0
#end

end Strata.B3ToSMT
