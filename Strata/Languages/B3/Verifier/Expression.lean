/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.DefinitionAST
import Strata.DL.SMT.SMT
import Strata.DL.SMT.Factory
import Strata.Languages.B3.DDMTransform.Conversion

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
-- Type Conversion
---------------------------------------------------------------------

/-- Convert B3 type name to SMT-LIB type name -/
def b3TypeToSMT (typeName : String) : String :=
  match typeName with
  | "int" => "Int"
  | "bool" => "Bool"
  | "real" => "Real"
  | "string" => "String"
  | other => other  -- User-defined types pass through as-is

---------------------------------------------------------------------
-- Conversion Context
---------------------------------------------------------------------

/-- Errors that can occur during B3 to SMT conversion -/
inductive ConversionError (M : Type) where
  | unsupportedConstruct : String → M → ConversionError M
  | unboundVariable : Nat → M → ConversionError M
  | typeMismatch : String → M → ConversionError M
  | invalidFunctionCall : String → M → ConversionError M
  | invalidPattern : String → M → ConversionError M
  deriving Inhabited

namespace ConversionError

def toString [Repr M] : ConversionError M → String
  | unsupportedConstruct msg m => s!"Unsupported construct at {repr m}: {msg}"
  | unboundVariable idx m => s!"Unbound variable at index {idx} at {repr m}"
  | typeMismatch msg m => s!"Type mismatch at {repr m}: {msg}"
  | invalidFunctionCall msg m => s!"Invalid function call at {repr m}: {msg}"
  | invalidPattern msg m => s!"Invalid pattern at {repr m}: {msg}"

instance [Repr M] : ToString (ConversionError M) where
  toString := ConversionError.toString

end ConversionError

---------------------------------------------------------------------
-- Conversion Result with Error Accumulation
---------------------------------------------------------------------

/-- Conversion result that can carry both a term and errors -/
structure ConversionResult (M : Type) where
  term : Term
  errors : List (ConversionError M)

namespace ConversionResult

/-- Create a successful conversion result -/
def ok {M : Type} (term : Term) : ConversionResult M :=
  { term := term, errors := [] }

/-- Create a conversion result with an error and placeholder term -/
def withError {M : Type} (err : ConversionError M) : ConversionResult M :=
  { term := Term.bool false, errors := [err] }

end ConversionResult

structure ConversionContext where
  vars : List String  -- Maps de Bruijn index to variable name
  enableDiagnosis : Bool := true  -- Whether to perform automatic diagnosis on failures

namespace ConversionContext

def empty : ConversionContext := { vars := [], enableDiagnosis := true }

def withoutDiagnosis (ctx : ConversionContext) : ConversionContext :=
  { ctx with enableDiagnosis := false }

def push (ctx : ConversionContext) (name : String) : ConversionContext :=
  { ctx with vars := name :: ctx.vars }

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
def binaryOpToSMT : B3AST.BinaryOp M → (Term → Term → Term)
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
def unaryOpToSMT : B3AST.UnaryOp M → (Term → Term)
  | .not _ => fun t => Term.app .not [t] .bool
  | .neg _ => fun t => Term.app .neg [t] .int

/-- Convert B3 literals to SMT terms -/
def literalToSMT : B3AST.Literal M → Term
  | .intLit _ n => Term.int n
  | .boolLit _ b => Term.bool b
  | .stringLit _ s => Term.string s

---------------------------------------------------------------------
-- Pattern Validation
---------------------------------------------------------------------

/-- Collect bound variable indices from a pattern expression.
Returns error if the expression is not structurally valid as a pattern.
Valid patterns consist only of function applications, bound variables, and literals. -/
def collectPatternBoundVars (expr : B3AST.Expression M) (exprM : M) : Except (ConversionError M) (List Nat) :=
  match expr with
  | .id _ idx => .ok [idx]
  | .literal _ _ => .ok []
  | .functionCall _ _ args => do
      let results ← args.val.toList.mapM (fun arg => collectPatternBoundVars arg exprM)
      return results.flatten
  | _ => .error (ConversionError.invalidPattern "patterns must consist only of function applications, variables, and literals" exprM)
  termination_by SizeOf.sizeOf expr
  decreasing_by
    simp_wf
    cases args
    simp_all
    rename_i h
    have := Array.sizeOf_lt_of_mem h
    omega

/-- Validate pattern expressions for a quantifier -/
def validatePatternExprs (patterns : Array (B3AST.Expression M)) (patternM : M) : Except (ConversionError M) Unit :=
  if patterns.isEmpty then
    .ok ()  -- Empty patterns are OK (solver will auto-generate)
  else do
    -- Check that each pattern expression is a function application (not just a variable or literal)
    for p in patterns do
      match p with
      | .functionCall _ _ _ => pure ()  -- Valid
      | _ => throw (ConversionError.invalidPattern "each pattern expression must be a function application" patternM)

    -- Collect all bound variables from all patterns
    let allBoundVars ← patterns.toList.mapM (fun p => collectPatternBoundVars p patternM)
    let flatVars := allBoundVars.flatten
    -- Check if the bound variable (id 0) appears in at least one pattern
    if !flatVars.contains 0 then
      .error (ConversionError.invalidPattern "bound variable must appear in at least one pattern" patternM)
    else
      .ok ()

---------------------------------------------------------------------
-- Metadata Extraction
---------------------------------------------------------------------

/-- Extract metadata from any B3 expression -/
def getExpressionMetadata : B3AST.Expression M → M
  | .binaryOp m _ _ _ => m
  | .literal m _ => m
  | .id m _ => m
  | .ite m _ _ _ => m
  | .unaryOp m _ _ => m
  | .functionCall m _ _ => m
  | .labeledExpr m _ _ => m
  | .letExpr m _ _ _ => m
  | .quantifierExpr m _ _ _ _ => m

---------------------------------------------------------------------
-- Expression Conversion
---------------------------------------------------------------------

/-- Convert B3 expressions to SMT terms with error accumulation -/
def expressionToSMT (ctx : ConversionContext) (e : B3AST.Expression M) : ConversionResult M :=
  match e with
  | .literal _m lit =>
      ConversionResult.ok (literalToSMT lit)

  | .id m idx =>
      match ctx.lookup idx with
      | some name => ConversionResult.ok (Term.var ⟨name, .int⟩)
      | none => ConversionResult.withError (ConversionError.unboundVariable idx m)

  | .ite _m cond thn els =>
      let condResult := expressionToSMT ctx cond
      let thnResult := expressionToSMT ctx thn
      let elsResult := expressionToSMT ctx els
      let errors := condResult.errors ++ thnResult.errors ++ elsResult.errors
      let term := Term.app .ite [condResult.term, thnResult.term, elsResult.term] thnResult.term.typeOf
      { term := term, errors := errors }

  | .binaryOp _m op lhs rhs =>
      let lhsResult := expressionToSMT ctx lhs
      let rhsResult := expressionToSMT ctx rhs
      let errors := lhsResult.errors ++ rhsResult.errors
      let term := (binaryOpToSMT op) lhsResult.term rhsResult.term
      { term := term, errors := errors }

  | .unaryOp _m op arg =>
      let argResult := expressionToSMT ctx arg
      let term := (unaryOpToSMT op) argResult.term
      { term := term, errors := argResult.errors }

  | .functionCall m fnName args =>
      let argResults := args.val.map (fun arg => match _: arg with | a => expressionToSMT ctx a)
      let errors := argResults.toList.foldl (fun acc r => acc ++ r.errors) []
      let argTerms := argResults.toList.map (·.term)
      let uf : UF := {
        id := fnName.val,
        args := argTerms.map (fun t => ⟨UF_ARG_PLACEHOLDER, t.typeOf⟩),
        out := .int
      }
      let term := Term.app (.uf uf) argTerms .int
      { term := term, errors := errors }

  | .labeledExpr _m _ expr =>
      expressionToSMT ctx expr

  | .letExpr _m _var value body =>
      let ctx' := ctx.push _var.val
      let valueResult := expressionToSMT ctx value
      let bodyResult := expressionToSMT ctx' body
      let errors := valueResult.errors ++ bodyResult.errors
      { term := bodyResult.term, errors := errors }

  | .quantifierExpr m qkind vars patterns body =>
      -- Handle multiple quantified variables
      let varList := vars.val.toList.filterMap (fun v =>
        match _: v with
        | .quantVarDecl _ name ty => some (name.val, ty.val)
      )

      -- Extend context with all variables
      let ctx' := varList.foldl (fun c (name, _) => c.push name) ctx

      -- Convert body
      let bodyResult := expressionToSMT ctx' body

      -- Convert pattern expressions and collect errors
      let patternResults : Array (List Term × List (ConversionError M)) := patterns.val.map (fun p =>
        match _: p with
        | .pattern _ exprs =>
            let results : Array (ConversionResult M) := exprs.val.map (fun e => match _: e with | expr => expressionToSMT ctx' expr)
            (results.toList.map (·.term), results.toList.foldl (fun acc r => acc ++ r.errors) [])
      )
      let patternTermLists : List (List Term) := patternResults.toList.map (·.1)
      let patternErrors : List (ConversionError M) := patternResults.toList.foldl (fun acc r => acc ++ r.2) []

      -- Validate pattern structure
      let patternExprArray := patterns.val.flatMap (fun p =>
        match _: p with
        | .pattern _ exprs => exprs.val
      )
      let validationErrors := match validatePatternExprs patternExprArray m with
        | .ok () => []
        | .error err => [err]

      -- Build trigger from pattern terms
      let allPatternTerms := patternTermLists.foldl (· ++ ·) []
      let trigger := if patterns.val.isEmpty then
        -- No patterns specified in source - don't generate a trigger
        Term.app .triggers [] .trigger
      else if allPatternTerms.isEmpty then
        -- Patterns specified but empty (shouldn't happen) - generate simple trigger for first var
        match varList.head? with
        | some (name, _) => Factory.mkSimpleTrigger name .int
        | none => Term.app .triggers [] .trigger
      else
        -- Patterns specified - use them
        allPatternTerms.foldl (fun acc term => Factory.addTrigger term acc) (Term.app .triggers [] .trigger)

      -- Build quantifier term with all variables
      let qk := match _: qkind with
        | .forall _ => QuantifierKind.all
        | .exists _ => QuantifierKind.exist

      let term := varList.foldr (fun (name, _ty) body =>
        Factory.quant qk name .int trigger body
      ) bodyResult.term

      -- Accumulate all errors
      let allErrors := bodyResult.errors ++ validationErrors ++ patternErrors
      { term := term, errors := allErrors }

  termination_by SizeOf.sizeOf e
  decreasing_by
    all_goals (simp_wf <;> try omega)
    . cases args; simp_all
      rename_i h; have := Array.sizeOf_lt_of_mem h; omega
    . cases exprs; cases patterns; simp_all; subst_vars
      rename_i h1 h2
      have := Array.sizeOf_lt_of_mem h1
      have Hpsz := Array.sizeOf_lt_of_mem h2
      simp at Hpsz; omega

def formatExpression (prog : Program) (expr : B3AST.Expression SourceRange) (ctx: B3.ToCSTContext): String :=
  let (cstExpr, _) := B3.expressionToCST ctx expr
  let ctx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let fmtState : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a (dialect : Dialect) => a.insert dialect.name }
  let formatted := (mformat (ArgF.op cstExpr.toAst) ctx fmtState).format.pretty.trim
  formatted

end Strata.B3.Verifier
