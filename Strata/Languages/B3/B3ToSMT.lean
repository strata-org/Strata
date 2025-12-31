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
  | .implies _ => fun t1 t2 => Term.app .or [Term.app .not [t1] .bool, t2] .bool
  | .impliedBy _ => fun t1 t2 => Term.app .or [Term.app .not [t2] .bool, t1] .bool
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
  | .letExpr _ var value body =>
      -- Let expressions introduce a new variable
      let ctx' := ctx.push var.val
      match expressionToSMT ctx value, expressionToSMT ctx' body with
      | some _, some b => some b  -- Simplified: just return body
      | _, _ => none
  | .quantifierExpr _ qkind var _ty _ body =>
      -- Quantifiers introduce a new bound variable
      let ctx' := ctx.push var.val
      match expressionToSMT ctx' body with
      | some b =>
          let trigger := Factory.mkSimpleTrigger var.val .int  -- Simplified trigger
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
  | Term.app op args _ =>
      match op with
      | .uf f =>
          let argStrs := args.map formatTermDirect
          if argStrs.isEmpty then
            s!"({f.id})"  -- 0-ary function call needs parentheses
          else
            s!"({f.id} {String.intercalate " " argStrs})"
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
      | .neg => s!"(- {formatTermDirect args[0]!})"
      | _ => s!"(unsupported-op {args.length})"
  | _ => "(unsupported-term)"

/-- Convert B3AST declaration to SMT commands (declarations and assertions) -/
def declToSMT (ctx : ConversionContext) : B3AST.Decl M → List String
  | .function _ name params _ _ _ =>
      -- Generate (declare-fun name (arg-types) return-type)
      let argTypes := params.val.toList.map (fun _ => "Int")  -- Simplified: all args are Int
      let argTypeStr := String.intercalate " " argTypes
      [s!"(declare-fun {name.val} ({argTypeStr}) Int)"]
  | .axiom _ _ expr =>
      -- Generate (assert expr)
      match expressionToSMT ctx expr with
      | some term =>
          -- We need to format the term directly without the encoder's ANF
          [s!"(assert {formatTermDirect term})"]
      | none => []
  | _ => []

/-- Convert B3AST program to list of SMT commands -/
def programToSMTCommands (prog : B3AST.Program M) : List String :=
  match prog with
  | .program _ decls =>
      decls.val.toList.flatMap (declToSMT ConversionContext.empty)

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
info: (declare-fun getValue () Int)
(assert (= (+ (getValue) 1) 2))
-/
#guard_msgs in
#eval testB3ToSMT $ #strata program B3CST;
function getValue() : int
axiom getValue() + 1 == 2
#end

end Strata.B3ToSMT
