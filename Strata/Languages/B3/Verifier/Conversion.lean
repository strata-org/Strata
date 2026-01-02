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
partial def literalToSMT : B3AST.Literal M → Term
  | .intLit _ n => Term.int n
  | .boolLit _ b => Term.bool b
  | .stringLit _ s => Term.string s

---------------------------------------------------------------------
-- Expression Conversion
---------------------------------------------------------------------

/-- Convert B3 expressions to SMT terms -/
partial def expressionToSMT (ctx : ConversionContext) : B3AST.Expression M → Option Term
  | .literal _ lit => some (literalToSMT lit)
  | .id _ idx =>
      match ctx.lookup idx with
      | some name => some (Term.var ⟨name, .int⟩)
      | none => none
  | .ite _ cond thn els =>
      match expressionToSMT ctx cond, expressionToSMT ctx thn, expressionToSMT ctx els with
      | some c, some t, some e => some (Term.app .ite [c, t, e] t.typeOf)
      | _, _, _ => none
  | .binaryOp _ op lhs rhs =>
      match expressionToSMT ctx lhs, expressionToSMT ctx rhs with
      | some l, some r => some ((binaryOpToSMT op) l r)
      | _, _ => none
  | .unaryOp _ op arg =>
      match expressionToSMT ctx arg with
      | some a => some ((unaryOpToSMT op) a)
      | none => none
  | .functionCall _ fnName args =>
      let argTerms := args.val.toList.filterMap (expressionToSMT ctx)
      if argTerms.length == args.val.size then
        let uf : UF := {
          id := fnName.val,
          args := argTerms.map (fun t => ⟨"_", t.typeOf⟩),
          out := .int
        }
        some (Term.app (.uf uf) argTerms .int)
      else none
  | .labeledExpr _ _ expr => expressionToSMT ctx expr
  | .letExpr _ _var value body =>
      let ctx' := ctx.push _var.val
      match expressionToSMT ctx value, expressionToSMT ctx' body with
      | some _v, some b => some b
      | _, _ => none
  | .quantifierExpr _ qkind var _ty patterns body =>
      let ctx' := ctx.push var.val
      match expressionToSMT ctx' body with
      | some b =>
          let patternTerms := patterns.val.toList.filterMap (fun p =>
            match p with
            | .pattern _ exprs =>
                let terms := exprs.val.toList.filterMap (expressionToSMT ctx')
                if terms.length == exprs.val.size then some terms else none
          )
          let trigger := if patternTerms.isEmpty then
            Factory.mkSimpleTrigger var.val .int
          else
            patternTerms.foldl (fun acc terms =>
              terms.foldl (fun t term => Factory.addTrigger term t) acc
            ) (Term.app .triggers [] .trigger)
          match qkind with
          | .forall _ => some (Factory.quant .all var.val .int trigger b)
          | .exists _ => some (Factory.quant .exist var.val .int trigger b)
      | none => none

end Strata.B3.Verifier
