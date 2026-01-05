/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.DefinitionAST
import Strata.DL.SMT.SMT
import Strata.DL.SMT.Factory

/-!
# B3 AST to SMT Term Conversion

Converts B3 abstract syntax trees to SMT terms for verification.
-/

namespace Strata.B3.Verifier

open Strata
open Strata.B3AST
open Strata.SMT
open Strata.SMT.Factory

---------------------------------------------------------------------
-- Conversion Context
---------------------------------------------------------------------

/-- Errors that can occur during B3 to SMT conversion -/
inductive ConversionError where
  | unsupportedConstruct : String → ConversionError
  | unboundVariable : Nat → ConversionError
  | typeMismatch : String → ConversionError
  | invalidFunctionCall : String → ConversionError
  deriving Inhabited

namespace ConversionError

def toString : ConversionError → String
  | unsupportedConstruct msg => s!"Unsupported construct: {msg}"
  | unboundVariable idx => s!"Unbound variable at index {idx}"
  | typeMismatch msg => s!"Type mismatch: {msg}"
  | invalidFunctionCall msg => s!"Invalid function call: {msg}"

instance : ToString ConversionError where
  toString := ConversionError.toString

end ConversionError

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
-- Operator Conversion
---------------------------------------------------------------------

/-- Placeholder name for UF argument types in SMT encoding.
SMT solvers don't require actual parameter names for uninterpreted functions,
only the types matter for type checking. -/
def UF_ARG_PLACEHOLDER := "_"

/-- Convert B3 binary operators to SMT terms without constant folding -/
partial def binaryOpToSMT : B3AST.BinaryOp M → (Term → Term → Term)
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

/-- Convert B3 unary operators to SMT terms -/
partial def unaryOpToSMT : B3AST.UnaryOp M → (Term → Term)
  | .not _ => fun t => Term.app .not [t] .bool
  | .neg _ => fun t => Term.app .neg [t] .int

/-- Convert B3 literals to SMT terms -/
def literalToSMT : B3AST.Literal M → Term
  | .intLit _ n => Term.int n
  | .boolLit _ b => Term.bool b
  | .stringLit _ s => Term.string s

---------------------------------------------------------------------
-- Expression Conversion
---------------------------------------------------------------------

/-- Convert B3 expressions to SMT terms -/
def expressionToSMT (ctx : ConversionContext) (e : B3AST.Expression M) : Except ConversionError Term :=
  match e with
  | .literal _ lit => .ok (literalToSMT lit)
  | .id _ idx =>
      match ctx.lookup idx with
      | some name => .ok (Term.var ⟨name, .int⟩)
      | none => .error (ConversionError.unboundVariable idx)
  | .ite _ cond thn els => do
      let c ← expressionToSMT ctx cond
      let t ← expressionToSMT ctx thn
      let e ← expressionToSMT ctx els
      return Term.app .ite [c, t, e] t.typeOf
  | .binaryOp _ op lhs rhs => do
      let l ← expressionToSMT ctx lhs
      let r ← expressionToSMT ctx rhs
      return (binaryOpToSMT op) l r
  | .unaryOp _ op arg => do
      let a ← expressionToSMT ctx arg
      return (unaryOpToSMT op) a
  | .functionCall _ fnName args => do
      let argTerms ← args.val.mapM (expressionToSMT ctx)
      let uf : UF := {
        id := fnName.val,
        args := argTerms.toList.map (fun t => ⟨UF_ARG_PLACEHOLDER, t.typeOf⟩),
        out := .int
      }
      return Term.app (.uf uf) argTerms.toList .int
  | .labeledExpr _ _ expr => expressionToSMT ctx expr
  | .letExpr _ _var value body => do
      let ctx' := ctx.push _var.val
      let _v ← expressionToSMT ctx value
      let b ← expressionToSMT ctx' body
      return b
  | .quantifierExpr _ qkind var _ty patterns body => do
      let ctx' := ctx.push var.val
      let b ← expressionToSMT ctx' body
      let patternTerms ← patterns.val.mapM (fun p =>
        match  _: p with
        | .pattern _ exprs =>
            exprs.val.mapM (expressionToSMT ctx')
      )
      let trigger := if patternTerms.toList.isEmpty then
        Factory.mkSimpleTrigger var.val .int
      else
        patternTerms.toList.foldl (fun acc terms =>
          terms.toList.foldl (fun t term => Factory.addTrigger term t) acc
        ) (Term.app .triggers [] .trigger)
      match qkind with
      | .forall _ => return Factory.quant .all var.val .int trigger b
      | .exists _ => return Factory.quant .exist var.val .int trigger b
  termination_by SizeOf.sizeOf e
  decreasing_by
    all_goals (simp_wf <;> try omega)
    . cases args ; simp_all
      rename_i h; have := Array.sizeOf_lt_of_mem h; omega
    . cases exprs; cases patterns; simp_all; subst_vars
      rename_i h1 h2
      have := Array.sizeOf_lt_of_mem h1
      have Hpsz := Array.sizeOf_lt_of_mem h2
      simp at Hpsz; omega

end Strata.B3.Verifier
