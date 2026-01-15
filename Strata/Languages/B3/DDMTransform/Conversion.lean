/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.DefinitionAST

/-!
# B3 ↔ DDM Bidirectional Conversion

This module provides bidirectional conversion between B3 AST types and B3 CST types.

## B3AST → B3CST Conversion
Converts abstract syntax (de Bruijn indices) to concrete syntax (named identifiers).
Used for formatting and pretty-printing B3 constructs using DDM's formatting system.

## B3CST → B3AST Conversion
Converts concrete syntax (named identifiers) to abstract syntax (de Bruijn indices).
Used for parsing B3 syntax via DDM and converting it back to B3 AST.

## Context Management
A list of variable names is maintained to convert between indices and names.
-/

namespace B3

open Strata
open Strata.B3CST
open Strata.B3AST

---------------------------------------------------------------------
-- Helper Instances
---------------------------------------------------------------------

instance : ToString SourceRange where
  toString _sr := "<source location>"

---------------------------------------------------------------------
-- Conversion Errors
---------------------------------------------------------------------

/-- Errors that can occur during CST→AST conversion (parsing) -/
inductive CSTToASTError (M : Type) where
  | unresolvedIdentifier (name : String) (metadata : M) : CSTToASTError M
  deriving Inhabited

namespace CSTToASTError

def toString [ToString M] : CSTToASTError M → String
  | unresolvedIdentifier name _m => s!"Unresolved identifier '{name}'"

instance [ToString M] : ToString (CSTToASTError M) where
  toString := CSTToASTError.toString

def toFormat [ToString M] : CSTToASTError M → Std.Format
  | unresolvedIdentifier name _m => f!"Unresolved identifier '{name}'"

instance [ToString M] : Std.ToFormat (CSTToASTError M) where
  format := CSTToASTError.toFormat

end CSTToASTError

/-- Errors that can occur during AST→CST conversion (formatting) -/
inductive ASTToCSTError (M : Type) where
  | variableOutOfBounds (index : Nat) (contextSize : Nat) (metadata : M) : ASTToCSTError M
  | unsupportedVariableReference (index : Nat) (metadata : M) : ASTToCSTError M
  deriving Inhabited

namespace ASTToCSTError

def toString [ToString M] : ASTToCSTError M → String
  | variableOutOfBounds idx size _m =>
      s!"Variable index @{idx} is out of bounds (context has {size} variables)"
  | unsupportedVariableReference idx _m =>
      s!"Variable reference @{idx} not yet supported in concrete syntax. " ++
      s!"B3 concrete syntax currently only supports referencing the most recent variable " ++
      s!"or 'old' values in procedure contexts."

instance [ToString M] : ToString (ASTToCSTError M) where
  toString := ASTToCSTError.toString

def toFormat [ToString M] : ASTToCSTError M → Std.Format
  | variableOutOfBounds idx size _m =>
      f!"Variable index @{idx} is out of bounds (context has {size} variables)"
  | unsupportedVariableReference idx _m =>
      f!"Variable reference @{idx} not yet supported in concrete syntax. " ++
      f!"B3 concrete syntax currently only supports referencing the most recent variable " ++
      f!"or 'old' values in procedure contexts."

instance [ToString M] : Std.ToFormat (ASTToCSTError M) where
  format := ASTToCSTError.toFormat

end ASTToCSTError

---------------------------------------------------------------------
-- B3AnnFromCST Typeclass
---------------------------------------------------------------------

/--
Typeclass for creating annotations when converting CST → AST.
Methods extract multiple metadata from a single CST metadata when AST needs more.
-/
class B3AnnFromCST (α : Type) where
  -- Literals: AST needs one extra metadata for the literal wrapper
  annForLiteral : α → α
  -- Literals: AST needs one extra metadata for the literal type (.intLit/.stringLit/.boolLit)
  annForLiteralType : α → α
  -- Unary ops: AST needs one extra metadata for the .unaryOp wrapper
  annForUnaryOp : α → α
  -- Unary ops: AST needs one extra metadata for the op type (.not/.neg)
  annForUnaryOpType : α → α
  -- Binary ops: AST needs one extra metadata for the .binaryOp wrapper
  annForBinaryOp : α → α
  -- Binary ops: AST needs one extra metadata for the op type (.add/.sub/etc)
  annForBinaryOpType : α → α
  -- Function calls: AST needs two extra metadata for fn and args Anns
  annForFunctionCall : α → α
  annForFunctionCallName : α → α
  annForFunctionCallArgs : α → α
  -- Labeled expressions: AST needs one extra metadata for the label Ann
  annForLabeledExpr : α → α
  annForLabeledExprLabel : α → α
  -- Let expressions: AST needs one extra metadata for the var Ann
  annForLetExpr : α → α
  annForLetExprVar : α → α
  -- If-then-else: AST has same metadata count (passthrough)
  annForIte : α → α
  -- Quantifiers: AST needs three extra metadata for kind, vars (Seq), and patterns Anns
  annForQuantifierExpr : α → α
  annForQuantifierKind : α → α
  annForQuantifierVars : α → α
  annForQuantifierPatterns : α → α
  -- Patterns: AST needs one extra metadata for the exprs Ann
  annForPattern : α → α
  annForPatternExprs : α → α

instance : B3AnnFromCST Unit where
  annForLiteral _ := ()
  annForLiteralType _ := ()
  annForUnaryOp _ := ()
  annForUnaryOpType _ := ()
  annForBinaryOp _ := ()
  annForBinaryOpType _ := ()
  annForFunctionCall _ := ()
  annForFunctionCallName _ := ()
  annForFunctionCallArgs _ := ()
  annForLabeledExpr _ := ()
  annForLabeledExprLabel _ := ()
  annForLetExpr _ := ()
  annForLetExprVar _ := ()
  annForIte _ := ()
  annForQuantifierExpr _ := ()
  annForQuantifierKind _ := ()
  annForQuantifierVars _ := ()
  annForQuantifierPatterns _ := ()
  annForPattern _ := ()
  annForPatternExprs _ := ()

instance : B3AnnFromCST M where
  annForLiteral := id
  annForLiteralType := id
  annForUnaryOp := id
  annForUnaryOpType := id
  annForBinaryOp := id
  annForBinaryOpType := id
  annForFunctionCall := id
  annForFunctionCallName := id
  annForFunctionCallArgs := id
  annForLabeledExpr := id
  annForLabeledExprLabel := id
  annForLetExpr := id
  annForLetExprVar := id
  annForIte := id
  annForQuantifierExpr := id
  annForQuantifierKind := id
  annForQuantifierVars := id
  annForQuantifierPatterns := id
  annForPattern := id
  annForPatternExprs := id

-- Helpers for common Ann operations
private def mkAnn {α M: Type} (m: M) (x : α) : Ann α M := ⟨m, x⟩
private def mapAnn {α β M : Type} (f : α → β) (a : Ann α M) : Ann β M := mkAnn a.ann (f a.val)

---------------------------------------------------------------------
-- B3AST → B3CST Conversion (Abstract to Concrete)
---------------------------------------------------------------------

section ToCST

structure ToCSTContext where
  vars : List String
  inProcedure : Bool := false  -- Track if we're in a procedure context (for "old" value support)

namespace ToCSTContext

/--
Check if a variable reference is supported in concrete syntax.
Supported cases:
- Index 0 (most recent variable)
- Variables with unique names (appear only once in context)
- Last occurrence of a variable (for "old" values in inout parameters)
NOT supported:
- Middle occurrences of shadowed variables
- "old" references outside procedure context (not yet implemented in B3)
-/
def isSupported (ctx : ToCSTContext) (idx : Nat) : Bool :=
  match ctx.vars[idx]? with
  | .none => false
  | .some name =>
    if idx == 0 then true  -- Most recent variable always supported
    else if name == "" then false  -- Anonymous variable
    else
      -- Check if this is the last (oldest) occurrence of the name
      let isLastOccurrence := !(ctx.vars.drop (idx + 1)).any (· == name)
      -- Check if this is a middle occurrence (has both earlier and later occurrences)
      let hasEarlierOccurrence := (ctx.vars.take idx).any (· == name)

      if hasEarlierOccurrence && !isLastOccurrence then
        false  -- Middle occurrence - not supported
      else if isLastOccurrence && hasEarlierOccurrence then
        ctx.inProcedure  -- Last occurrence with shadowing - supported only in procedure context
      else
        true  -- Unique name - supported

/-- Helper to resolve variable name disambiguation -/
private def resolveVarName (vars : List String) (name : String) (idx : Nat) : String :=
  let rec go (vars: List String) (pastIndex: Nat) (idx: Nat): String :=
    let default := fun _: Unit => if pastIndex == 0 then
        name  -- No ambiguity
      else
        s!"name@{pastIndex}"
    if idx == 0 then
      default ()
    else
      match vars with
      | [] => default ()
      | otherName :: tail =>
        if name == otherName then
          go tail (pastIndex + 1) (idx - 1)
        else
          go tail pastIndex (idx - 1)
  go vars 0 idx

def lookup (ctx : ToCSTContext) (idx : Nat) (m : M) : String × Bool × List (ASTToCSTError M) :=
  match ctx.vars[idx]? with
  | .some name =>
    if name == "" then (s!"@{idx}", false, []) else
    -- Determine if this is an old value: first occurrence with shadowing
    let isOld :=
      -- Check if there's a later occurrence (lower index) with the same name
      ctx.vars.take idx |>.any (· == name)
    -- Old values in procedure contexts are always supported
    if isOld && ctx.inProcedure then
      (name, true, [])
    else
      -- Check if this reference is supported in concrete syntax
      if !ctx.isSupported idx then
        -- Not supported - return error
        let resolvedName := if isOld then name else resolveVarName ctx.vars name idx
        (resolvedName, isOld, [.unsupportedVariableReference idx m])
      else
        -- Supported - return without error
        if isOld then
          (name, true, [])
        else
          (resolveVarName ctx.vars name idx, false, [])
  | .none =>
    (s!"@{idx}", false, [.variableOutOfBounds idx ctx.vars.length m])

def push (ctx : ToCSTContext) (name : String) : ToCSTContext :=
  { vars := name :: ctx.vars, inProcedure := ctx.inProcedure }

def empty : ToCSTContext := { vars := [] }

end ToCSTContext

def binaryOpToCST [Inhabited (B3CST.Expression M)] : B3AST.BinaryOp M →
    (M → B3CST.Expression M → B3CST.Expression M → B3CST.Expression M)
  | .iff _ => B3CST.Expression.iff
  | .implies _ => B3CST.Expression.implies
  | .impliedBy _ => B3CST.Expression.impliedBy
  | .and _ => B3CST.Expression.and
  | .or _ => B3CST.Expression.or
  | .eq _ => B3CST.Expression.equal
  | .neq _ => B3CST.Expression.not_equal
  | .lt _ => B3CST.Expression.lt
  | .le _ => B3CST.Expression.le
  | .ge _ => B3CST.Expression.ge
  | .gt _ => B3CST.Expression.gt
  | .add _ => B3CST.Expression.add
  | .sub _ => B3CST.Expression.sub
  | .mul _ => B3CST.Expression.mul
  | .div _ => B3CST.Expression.div
  | .mod _ => B3CST.Expression.mod

def unaryOpToCST [Inhabited (B3CST.Expression M)] : B3AST.UnaryOp M →
    (M → B3CST.Expression M → B3CST.Expression M)
  | .not _ => B3CST.Expression.not
  | .neg _ => B3CST.Expression.neg

def literalToCST [Inhabited (B3CST.Expression M)] : B3AST.Literal M → B3CST.Expression M
  | .intLit m n => B3CST.Expression.natLit m n
  | .boolLit m b => if b then B3CST.Expression.btrue m else B3CST.Expression.bfalse m
  | .stringLit m s => B3CST.Expression.strLit m s

mutual

def expressionToCST [Inhabited (B3CST.Expression M)] (ctx : ToCSTContext) (e: B3AST.Expression M) : B3CST.Expression M × List (ASTToCSTError M) :=
  match he: e with
  | .literal _m lit =>
      (literalToCST lit, [])
  | .id m idx =>
      let (name, isOld, errors) := ctx.lookup idx m
      let cstExpr := if isOld then
        B3CST.Expression.old_id m (mkAnn m name)
      else
        B3CST.Expression.id m name
      (cstExpr, errors)
  | .ite m cond thn els =>
      let (cond', e1) := expressionToCST ctx cond
      let (thn', e2) := expressionToCST ctx thn
      let (els', e3) := expressionToCST ctx els
      (B3CST.Expression.ite m cond' thn' els', e1 ++ e2 ++ e3)
  | .binaryOp m op lhs rhs =>
      let (lhs', e1) := expressionToCST ctx lhs
      let (rhs', e2) := expressionToCST ctx rhs
      ((binaryOpToCST op) m lhs' rhs', e1 ++ e2)
  | .unaryOp m op arg =>
      let (arg', errs) := expressionToCST ctx arg
      ((unaryOpToCST op) m arg', errs)
  | .functionCall m fnName args =>
      let (argsConverted, errors) := args.val.toList.foldl (fun (acc, errs) arg =>
        let (arg', e) := expressionToCST ctx arg
        (acc ++ [arg'], errs ++ e)
      ) ([], [])
      (B3CST.Expression.functionCall m (mapAnn (fun x => x) fnName) (mapAnn (fun _ => argsConverted.toArray) args), errors)
  | .labeledExpr m label expr =>
      let (expr', errs) := expressionToCST ctx expr
      (B3CST.Expression.labeledExpr m (mapAnn (fun x => x) label) expr', errs)
  | .letExpr m var value body =>
      let ctx' := ctx.push var.val
      let (value', e1) := expressionToCST ctx value
      let (body', e2) := expressionToCST ctx' body
      (B3CST.Expression.letExpr m (mapAnn (fun x => x) var) value' body', e1 ++ e2)
  | .quantifierExpr m qkind vars patterns body =>
      -- Build context with all variables
      let varList := vars.val.toList
      let ctx' := varList.foldl (fun acc v =>
        match v with
        | .quantVarDecl _ name _ => acc.push name.val
      ) ctx
      let convertPattern (p : Strata.B3AST.Pattern M) (Hp: p ∈ patterns.val.toList) : B3CST.Pattern M × List (ASTToCSTError M) :=
        match p with
        | .pattern pm exprs =>
            let (exprsConverted, errors) := exprs.val.toList.attach.foldl (fun (acc, errs) e =>
              let (e', err) := expressionToCST ctx' e.1
              (acc ++ [e'], errs ++ err)
            ) ([], [])
            (B3CST.Pattern.pattern pm (mkAnn pm exprsConverted.toArray), errors)
      let (patternsConverted, patternErrors) := patterns.val.toList.attach.foldl (fun (acc, errs) p =>
        let (p', e) := convertPattern p.1 p.2
        (acc ++ [p'], errs ++ e)
      ) ([], [])
      let patternsDDM : Ann (Array (B3CST.Pattern M)) M := mkAnn m patternsConverted.toArray
      let (body', bodyErrs) := expressionToCST ctx' body
      -- Convert VarDecl list to CST VarDecl list
      let varDeclsCST := varList.map (fun v =>
        match v with
        | .quantVarDecl vm name ty => B3CST.VarDecl.var_decl vm (mkAnn vm name.val) (mkAnn vm ty.val)
      )
      let result := match qkind with
      | .forall _qm =>
          B3CST.Expression.forall_expr m (mkAnn m varDeclsCST.toArray) patternsDDM body'
      | .exists _qm =>
          B3CST.Expression.exists_expr m (mkAnn m varDeclsCST.toArray) patternsDDM body'
      (result, patternErrors ++ bodyErrs)
  termination_by e
  decreasing_by
  all_goals(simp_wf; try omega)
  . cases args; simp_all; rename_i arg_in;
    have := Array.sizeOf_lt_of_mem arg_in; omega
  . rcases e; rename_i e he
    subst_vars; cases exprs; cases patterns; simp_all
    simp at he
    have := Array.sizeOf_lt_of_mem he
    have := Array.sizeOf_lt_of_mem Hp
    simp_all; omega

def callArgToCST [Inhabited (B3CST.Expression M)] (ctx : ToCSTContext) : Strata.B3AST.CallArg M → B3CST.CallArg M × List (ASTToCSTError M)
  | .callArgExpr m e =>
      let (e', errs) := expressionToCST ctx e
      (B3CST.CallArg.call_arg_expr m e', errs)
  | .callArgOut m id => (B3CST.CallArg.call_arg_out m (mapAnn (fun x => x) id), [])
  | .callArgInout m id => (B3CST.CallArg.call_arg_inout m (mapAnn (fun x => x) id), [])

def buildChoiceBranches [Inhabited (B3CST.Expression M)] : M → List (B3CST.ChoiceBranch M) → B3CST.ChoiceBranches M
  | m, [] => ChoiceBranches.choiceAtom m (ChoiceBranch.choice_branch m (B3CST.Statement.return_statement m))
  | m, [b] => ChoiceBranches.choiceAtom m b
  | m, b :: bs => ChoiceBranches.choicePush m (buildChoiceBranches m bs) b

def stmtToCST [Inhabited (B3CST.Expression M)] [Inhabited (B3CST.Statement M)] (ctx : ToCSTContext) (s: Strata.B3AST.Statement M): B3CST.Statement M × List (ASTToCSTError M) :=
  match _: s with
  | .varDecl m name ty autoinv init =>
    let ctx' := ctx.push name.val
    match ty.val, autoinv.val, init.val with
    | some t, some ai, some i =>
        let (ai', e1) := expressionToCST ctx' ai
        let (i', e2) := expressionToCST ctx' i
        (B3CST.Statement.var_decl_full m (mapAnn (fun x => x) name) (mkAnn m t.val) ai' i', e1 ++ e2)
    | some t, some ai, none =>
        let (ai', errs) := expressionToCST ctx' ai
        (B3CST.Statement.var_decl_with_autoinv m (mapAnn (fun x => x) name) (mkAnn m t.val) ai', errs)
    | some t, none, some i =>
        let (i', errs) := expressionToCST ctx' i
        (B3CST.Statement.var_decl_with_init m (mapAnn (fun x => x) name) (mkAnn m t.val) i', errs)
    | some t, none, none =>
        (B3CST.Statement.var_decl_typed m (mapAnn (fun x => x) name) (mkAnn m t.val), [])
    | none, _, some i =>
        let (i', errs) := expressionToCST ctx' i
        (B3CST.Statement.var_decl_inferred m (mapAnn (fun x => x) name) i', errs)
    | none, _, none =>
        (B3CST.Statement.var_decl_typed m (mapAnn (fun x => x) name) (mkAnn m "unknown"), [])
  | .assign m lhs rhs =>
      let (name, _, e1) := ctx.lookup lhs.val m
      let (rhs', e2) := expressionToCST ctx rhs
      (B3CST.Statement.assign m (mkAnn m name) rhs', e1 ++ e2)
  | .reinit m idx =>
      let (name, _, errs) := ctx.lookup idx.val m
      (B3CST.Statement.reinit_statement m (mkAnn m name), errs)
  | .blockStmt m stmts =>
      let (stmts', _, errors) := stmts.val.toList.foldl (fun (acc, ctx, errs) stmt =>
        let (stmt', e) := stmtToCST ctx stmt
        let ctx' := match stmt with
          | .varDecl _ name _ _ _ => ctx.push name.val
          | _ => ctx
        (acc ++ [stmt'], ctx', errs ++ e)
      ) ([], ctx, [])
      (B3CST.Statement.block m (mkAnn m stmts'.toArray), errors)
  | .call m procName args =>
      let (argsConverted, errors) := args.val.toList.foldl (fun (acc, errs) arg =>
        let (arg', e) := callArgToCST ctx arg
        (acc ++ [arg'], errs ++ e)
      ) ([], [])
      (B3CST.Statement.call_statement m (mapAnn (fun x => x) procName) (mapAnn (fun _ => argsConverted.toArray) args), errors)
  | .check m expr =>
      let (expr', errs) := expressionToCST ctx expr
      (B3CST.Statement.check m expr', errs)
  | .assume m expr =>
      let (expr', errs) := expressionToCST ctx expr
      (B3CST.Statement.assume m expr', errs)
  | .reach m expr =>
      let (expr', errs) := expressionToCST ctx expr
      (B3CST.Statement.reach m expr', errs)
  | .assert m expr =>
      let (expr', errs) := expressionToCST ctx expr
      (B3CST.Statement.assert m expr', errs)
  | .aForall m var ty body =>
      let ctx' := ctx.push var.val
      let (body', errs) := stmtToCST ctx' body
      (B3CST.Statement.aForall_statement m (mapAnn (fun x => x) var) (mapAnn (fun x => x) ty) body', errs)
  | .choose m branches =>
      let (choiceBranches, errors) := branches.val.toList.foldl (fun (acc, errs) s =>
        let (s', e) := stmtToCST ctx s
        (acc ++ [ChoiceBranch.choice_branch m s'], errs ++ e)
      ) ([], [])
      (B3CST.Statement.choose_statement m (buildChoiceBranches m choiceBranches), errors)
  | .ifStmt m cond thenB elseB =>
      let (cond', e1) := expressionToCST ctx cond
      let (then', e2) := stmtToCST ctx thenB
      let (elseBranch, e3) := match _: elseB.val with
        | some e =>
            let (e', err) := stmtToCST ctx e
            (some (Else.else_some m e'), err)
        | none => (none, [])
      (B3CST.Statement.if_statement m cond' then' (mapAnn (fun _ => elseBranch) elseB), e1 ++ e2 ++ e3)
  | .ifCase m cases =>
      let (casesConverted, errors) := cases.val.toList.attach.foldl (fun (acc, errs) c =>
        match _: c.1 with
        | .oneIfCase cm cond body =>
            let (cond', e1) := expressionToCST ctx cond
            let (body', e2) := stmtToCST ctx body
            (acc ++ [IfCaseBranch.if_case_branch cm cond' body'], errs ++ e1 ++ e2)
      ) ([], [])
      (B3CST.Statement.if_case_statement m (mapAnn (fun _ => casesConverted.toArray) cases), errors)
  | .loop m invariants body =>
      let (invs, invErrors) := invariants.val.toList.foldl (fun (acc, errs) e =>
        let (e', err) := expressionToCST ctx e
        (acc ++ [Invariant.invariant m e'], errs ++ err)
      ) ([], [])
      let (body', bodyErrs) := stmtToCST ctx body
      (B3CST.Statement.loop_statement m (mkAnn m invs.toArray) body', invErrors ++ bodyErrs)
  | .labeledStmt m label stmt =>
      let (stmt', errs) := stmtToCST ctx stmt
      (B3CST.Statement.labeled_statement m (mapAnn (fun x => x) label) stmt', errs)
  | .exit m label =>
      (B3CST.Statement.exit_statement m (mapAnn (fun opt => opt.map (fun l => l)) label), [])
  | .returnStmt m => (B3CST.Statement.return_statement m, [])
  | .probe m label => (B3CST.Statement.probe m (mapAnn (fun x => x) label), [])
  termination_by s
  decreasing_by
  all_goals(simp_wf; try omega)
  . cases stmts; simp_all; rename_i hs; have := Array.sizeOf_lt_of_mem hs; omega
  . cases branches; simp_all; rename_i hs; have := Array.sizeOf_lt_of_mem hs; omega
  . cases elseB; simp_all; subst_vars; omega
  . cases c; cases cases; simp_all; subst_vars; rename_i hin
    simp at hin; have hin2 := Array.sizeOf_lt_of_mem hin; simp at hin2; omega

end

def fParameterToCST : Strata.B3AST.FParameter M → B3CST.FParam M
  | .fParameter m injective name ty =>
      let inj := mapAnn (fun b => if b then some (B3CST.Injective.injective_some m) else none) injective
      B3CST.FParam.fparam m inj (mkAnn m name.val) (mkAnn m ty.val)

def pParameterToCST [Inhabited (B3CST.Expression M)] (ctx : ToCSTContext) : Strata.B3AST.PParameter M → B3CST.PParam M × List (ASTToCSTError M)
  | .pParameter m mode name ty autoinv =>
      let modeCST := match mode with
        | .paramModeIn _ => mkAnn m none
        | .paramModeOut _ => mkAnn m (some (B3CST.PParamMode.pmode_out m))
        | .paramModeInout _ => mkAnn m (some (B3CST.PParamMode.pmode_inout m))
      match autoinv.val with
      | some ai =>
          let (ai', errs) := expressionToCST ctx ai
          (B3CST.PParam.pparam_with_autoinv m modeCST (mkAnn m name.val) (mkAnn m ty.val) ai', errs)
      | none => (B3CST.PParam.pparam m modeCST (mkAnn m name.val) (mkAnn m ty.val), [])

def specToCST [Inhabited (B3CST.Expression M)] (ctx : ToCSTContext) : Strata.B3AST.Spec M → B3CST.Spec M × List (ASTToCSTError M)
  | .specRequires m expr =>
      let (expr', errs) := expressionToCST ctx expr
      (B3CST.Spec.spec_requires m expr', errs)
  | .specEnsures m expr =>
      let (expr', errs) := expressionToCST ctx expr
      (B3CST.Spec.spec_ensures m expr', errs)

def declToCST [Inhabited M] [Inhabited (B3CST.Expression M)] [Inhabited (B3CST.Statement M)] (ctx : ToCSTContext) : Strata.B3AST.Decl M → B3CST.Decl M × List (ASTToCSTError M)
  | .typeDecl m name =>
      (B3CST.Decl.type_decl m (mkAnn m name.val), [])
  | .tagger m name forType =>
      (B3CST.Decl.tagger_decl m (mkAnn m name.val) (mkAnn m forType.val), [])
  | .function m name params resultType tag body =>
      let paramNames := params.val.toList.map (fun p => match p with | .fParameter _ _ n _ => n.val)
      let ctx' := paramNames.foldl (fun acc n => acc.push n) ctx
      let paramsCST := mkAnn m (params.val.toList.map fParameterToCST |>.toArray)
      let tagClause := mapAnn (fun opt => opt.map (fun t => B3CST.TagClause.tag_some m (mkAnn m t.val))) tag
      let (bodyCST, errors) := match body.val with
        | some (.functionBody bm whens expr) =>
            let (whensConverted, whenErrors) := whens.val.toList.foldl (fun (acc, errs) w =>
              match w with
              | .when wm e =>
                  let (e', err) := expressionToCST ctx' e
                  (acc ++ [B3CST.WhenClause.when_clause wm e'], errs ++ err)
            ) ([], [])
            let (expr', exprErrs) := expressionToCST ctx' expr
            (some (B3CST.FunctionBody.function_body_some bm (mkAnn bm whensConverted.toArray) expr'), whenErrors ++ exprErrs)
        | none => (none, [])
      (B3CST.Decl.function_decl m (mkAnn m name.val) paramsCST (mkAnn m resultType.val) tagClause (mapAnn (fun _ => bodyCST) body), errors)
  | .axiom m explains expr =>
      let explainsCST := mkAnn m (explains.val.toList.map (fun id => mkAnn m id.val) |>.toArray)
      let (expr', errs) := expressionToCST ctx expr
      if explains.val.isEmpty then
        (B3CST.Decl.axiom_decl m (B3CST.AxiomBody.axiom m expr'), errs)
      else
        (B3CST.Decl.axiom_decl m (B3CST.AxiomBody.explain_axiom m explainsCST expr'), errs)
  | .procedure m name params specs body =>
      -- Build context: inout parameters need two entries (old and current)
      let ctx' := params.val.toList.foldl (fun acc p =>
        match p with
        | .pParameter _ mode pname _ _ =>
          match mode with
          | .paramModeInout _ => acc.push pname.val |>.push pname.val  -- Push twice for inout
          | _ => acc.push pname.val
      ) {ctx with inProcedure := true}  -- Set inProcedure flag for procedure context
      let (paramsConverted, paramErrors) := params.val.toList.foldl (fun (acc, errs) p =>
        let (p', e) := pParameterToCST ctx' p
        (acc ++ [p'], errs ++ e)
      ) ([], [])
      let (specsConverted, specErrors) := specs.val.toList.foldl (fun (acc, errs) s =>
        let (s', e) := specToCST ctx' s
        (acc ++ [s'], errs ++ e)
      ) ([], [])
      let (bodyCST, bodyErrors) := match body.val with
        | some s =>
            let (s', e) := stmtToCST ctx' s
            (some (B3CST.ProcBody.proc_body_some m s'), e)
        | none => (none, [])
      (B3CST.Decl.procedure_decl m (mkAnn m name.val) (mkAnn m paramsConverted.toArray) (mkAnn m specsConverted.toArray) (mapAnn (fun _ => bodyCST) body), paramErrors ++ specErrors ++ bodyErrors)

def programToCST [Inhabited M] [Inhabited (B3CST.Expression M)] [Inhabited (B3CST.Statement M)] (ctx : ToCSTContext) : Strata.B3AST.Program M → B3CST.Program M × List (ASTToCSTError M)
  | .program m decls =>
      let (declsConverted, errors) := decls.val.toList.foldl (fun (acc, errs) d =>
        let (d', e) := declToCST ctx d
        (acc ++ [d'], errs ++ e)
      ) ([], [])
      (.program m (mkAnn m declsConverted.toArray), errors)

end ToCST

---------------------------------------------------------------------
-- B3CST → B3AST Conversion (Concrete to Abstract)
---------------------------------------------------------------------

section FromCST

structure FromCSTContext where
  vars : List String

namespace FromCSTContext

def lookup (ctx : FromCSTContext) (name : String) (m : M) : Nat × List (CSTToASTError M) :=
  match ctx.vars.findIdx? (· == name) with
  | .some idx =>
    (idx, [])
  | .none =>
    (ctx.vars.length, [.unresolvedIdentifier name m])

def lookupLast (ctx : FromCSTContext) (name : String) (m : M) : Nat × List (CSTToASTError M) :=
  let rec findLast (vars : List String) (idx : Nat) (acc : Option Nat) : Option Nat :=
    match vars with
    | [] => acc
    | v :: vs =>
      let newAcc := if v == name then some idx else acc
      findLast vs (idx + 1) newAcc
  match findLast ctx.vars 0 none with
    | some idx => (idx, [])
    | none => (ctx.vars.length, [.unresolvedIdentifier name m])

def push (ctx : FromCSTContext) (name : String) : FromCSTContext :=
  { ctx with vars := name :: ctx.vars }

def empty : FromCSTContext := { vars := [] }

end FromCSTContext

def expressionFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) (e: B3CST.Expression M): Strata.B3AST.Expression M × List (CSTToASTError M) :=
  match he: e with
  | .natLit ann n => (.literal (B3AnnFromCST.annForLiteral ann) (.intLit (B3AnnFromCST.annForLiteralType ann) n), [])
  | .strLit ann s => (.literal (B3AnnFromCST.annForLiteral ann) (.stringLit (B3AnnFromCST.annForLiteralType ann) s), [])
  | .btrue ann => (.literal (B3AnnFromCST.annForLiteral ann) (.boolLit (B3AnnFromCST.annForLiteralType ann) true), [])
  | .bfalse ann => (.literal (B3AnnFromCST.annForLiteral ann) (.boolLit (B3AnnFromCST.annForLiteralType ann) false), [])
  | .id ann name =>
      let (idx, errs) := ctx.lookup name ann
      (.id ann idx, errs)
  | .old_id ann name =>
      let (idx, errs) := ctx.lookupLast name.val ann
      (.id ann idx, errs)
  | .not ann arg =>
      let (arg', errs) := expressionFromCST ctx arg
      (.unaryOp (B3AnnFromCST.annForUnaryOp ann) (.not (B3AnnFromCST.annForUnaryOpType ann)) arg', errs)
  | .neg ann arg =>
      let (arg', errs) := expressionFromCST ctx arg
      (.unaryOp (B3AnnFromCST.annForUnaryOp ann) (.neg (B3AnnFromCST.annForUnaryOpType ann)) arg', errs)
  | .iff ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.iff (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .implies ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.implies (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .impliedBy ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.impliedBy (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .and ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.and (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .or ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.or (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .equal ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.eq (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .not_equal ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.neq (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .lt ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.lt (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .le ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.le (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .ge ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.ge (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .gt ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.gt (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .add ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.add (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .sub ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.sub (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .mul ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.mul (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .div ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.div (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .mod ann lhs rhs =>
      let (lhs', e1) := expressionFromCST ctx lhs
      let (rhs', e2) := expressionFromCST ctx rhs
      (.binaryOp (B3AnnFromCST.annForBinaryOp ann) (.mod (B3AnnFromCST.annForBinaryOpType ann)) lhs' rhs', e1 ++ e2)
  | .functionCall ann fn args =>
      let (argsExprs, errors) := args.val.toList.foldl (fun (acc, errs) arg =>
        let (arg', e) := expressionFromCST ctx arg
        (acc ++ [arg'], errs ++ e)
      ) ([], [])
      (.functionCall (B3AnnFromCST.annForFunctionCall ann) ⟨B3AnnFromCST.annForFunctionCallName ann, fn.val⟩ ⟨B3AnnFromCST.annForFunctionCallArgs ann, argsExprs.toArray⟩, errors)
  | .labeledExpr ann label expr =>
      let (expr', errs) := expressionFromCST ctx expr
      (.labeledExpr (B3AnnFromCST.annForLabeledExpr ann) ⟨B3AnnFromCST.annForLabeledExprLabel ann, label.val⟩ expr', errs)
  | .letExpr ann var value body =>
      let ctx' := ctx.push var.val
      let (value', e1) := expressionFromCST ctx value
      let (body', e2) := expressionFromCST ctx' body
      (.letExpr (B3AnnFromCST.annForLetExpr ann) ⟨B3AnnFromCST.annForLetExprVar ann, var.val⟩ value' body', e1 ++ e2)
  | .ite ann cond thenExpr elseExpr =>
      let (cond', e1) := expressionFromCST ctx cond
      let (then', e2) := expressionFromCST ctx thenExpr
      let (else', e3) := expressionFromCST ctx elseExpr
      (.ite (B3AnnFromCST.annForIte ann) cond' then' else', e1 ++ e2 ++ e3)
  | .forall_expr ann vars patterns body =>
      -- Convert VarDecl array to AST VarDecl array and build context
      let varList := vars.val.toList
      let ctx' := varList.foldl (fun acc v =>
        match v with
        | .var_decl _ name ty => acc.push name.val
      ) ctx
      let convertPattern (p : B3CST.Pattern M) (Hp: p ∈ patterns.val) : Strata.B3AST.Pattern M × List (CSTToASTError M) :=
        match hp: p with
        | .pattern pann exprs =>
            let (exprsConverted, errors) := exprs.val.toList.attach.foldl (fun (acc, errs) e =>
              let (e', err) := expressionFromCST ctx' e.1
              (acc ++ [e'], errs ++ err)
            ) ([], [])
            (.pattern (B3AnnFromCST.annForPattern pann) ⟨B3AnnFromCST.annForPatternExprs pann, exprsConverted.toArray⟩, errors)
      let (patternsConverted, patternErrors) := patterns.val.toList.attach.foldl (fun (acc, errs) p =>
        let (p', e) := convertPattern p.1 (by have hp := p.2; simp at hp; exact hp)
        (acc ++ [p'], errs ++ e)
      ) ([], [])
      let (body', bodyErrs) := expressionFromCST ctx' body
      -- Convert CST VarDecls to AST VarDecls
      let varDeclsAST := varList.map (fun v =>
        match v with
        | .var_decl vann name ty =>
            Strata.B3AST.VarDecl.quantVarDecl vann (mkAnn vann name.val) (mkAnn vann ty.val)
      )
      (.quantifierExpr (B3AnnFromCST.annForQuantifierExpr ann)
        (.forall (B3AnnFromCST.annForQuantifierKind ann))
        ⟨B3AnnFromCST.annForQuantifierVars ann, varDeclsAST.toArray⟩
        ⟨B3AnnFromCST.annForQuantifierPatterns ann, patternsConverted.toArray⟩
        body', patternErrors ++ bodyErrs)
  | .exists_expr ann vars patterns body =>
      -- Convert VarDecl array to AST VarDecl array and build context
      let varList := vars.val.toList
      let ctx' := varList.foldl (fun acc v =>
        match v with
        | .var_decl _ name ty => acc.push name.val
      ) ctx
      let convertPattern (p : B3CST.Pattern M) (Hp: p ∈ patterns.val) : Strata.B3AST.Pattern M × List (CSTToASTError M) :=
        match hp: p with
        | .pattern pann exprs =>
            let (exprsConverted, errors) := exprs.val.toList.attach.foldl (fun (acc, errs) e =>
              let (e', err) := expressionFromCST ctx' e.1
              (acc ++ [e'], errs ++ err)
            ) ([], [])
            (.pattern (B3AnnFromCST.annForPattern pann) ⟨B3AnnFromCST.annForPatternExprs pann, exprsConverted.toArray⟩, errors)
      let (patternsConverted, patternErrors) := patterns.val.toList.attach.foldl (fun (acc, errs) p =>
        let (p', e) := convertPattern p.1 (by have hp := p.2; simp at hp; exact hp)
        (acc ++ [p'], errs ++ e)
      ) ([], [])
      let (body', bodyErrs) := expressionFromCST ctx' body
      -- Convert CST VarDecls to AST VarDecls
      let varDeclsAST := varList.map (fun v =>
        match v with
        | .var_decl vann name ty =>
            Strata.B3AST.VarDecl.quantVarDecl vann (mkAnn vann name.val) (mkAnn vann ty.val)
      )
      (.quantifierExpr (B3AnnFromCST.annForQuantifierExpr ann)
        (.exists (B3AnnFromCST.annForQuantifierKind ann))
        ⟨B3AnnFromCST.annForQuantifierVars ann, varDeclsAST.toArray⟩
        ⟨B3AnnFromCST.annForQuantifierPatterns ann, patternsConverted.toArray⟩
        body', patternErrors ++ bodyErrs)
  | .paren _ expr => expressionFromCST ctx expr
  termination_by e
  decreasing_by
  all_goals(simp_wf; try omega)
  . cases args; simp_all; rename_i harg; have:= Array.sizeOf_lt_of_mem harg; omega
  . cases e; cases exprs; cases patterns; rename_i val_in; subst_vars; simp_all
    rename_i val_in1 _ _; simp at val_in1
    have:= Array.sizeOf_lt_of_mem val_in
    have:= Array.sizeOf_lt_of_mem val_in1
    simp_all; omega
  . cases e; cases exprs; cases patterns; rename_i val_in; subst_vars; simp_all
    rename_i val_in1 _ _; simp at val_in1
    have:= Array.sizeOf_lt_of_mem val_in
    have:= Array.sizeOf_lt_of_mem val_in1
    simp_all; omega

def callArgFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) : B3CST.CallArg M → Strata.B3AST.CallArg M × List (CSTToASTError M)
  | .call_arg_expr m expr =>
      let (expr', errs) := expressionFromCST ctx expr
      (.callArgExpr m expr', errs)
  | .call_arg_out m id => (.callArgOut m (mapAnn (fun x => x) id), [])
  | .call_arg_inout m id => (.callArgInout m (mapAnn (fun x => x) id), [])

@[simp]
def choiceBranchesToList [Inhabited M] : B3CST.ChoiceBranches M → List (B3CST.Statement M)
  | .choiceAtom _ branch =>
      match branch with
      | .choice_branch _ stmt => [stmt]
  | .choicePush _ branches branch =>
      match branch with
      | .choice_branch _ stmt => stmt :: choiceBranchesToList branches

@[simp]
def B3CST.ChoiceBranches.mem [Inhabited M] (stmt: B3CST.Statement M) (bs: B3CST.ChoiceBranches M) : Prop :=
  match bs with
  | .choiceAtom _ (.choice_branch _ s) => stmt = s
  | .choicePush _ branches (.choice_branch _ s) => stmt = s ∨ B3CST.ChoiceBranches.mem stmt branches

def choiceBranchesToList_mem [Inhabited M] {stmt: B3CST.Statement M} {bs: B3CST.ChoiceBranches M} :
    B3CST.ChoiceBranches.mem stmt bs ↔ stmt ∈ choiceBranchesToList bs :=
  match bs with
  | .choiceAtom _ (.choice_branch _ s) => by simp
  | .choicePush _ branches (.choice_branch _ s) => by
    have H := @choiceBranchesToList_mem _ _ stmt branches
    simp; grind

def B3CST.ChoiceBranches.mem_sizeOf [Inhabited M] {stmt: B3CST.Statement M}
{bs: B3CST.ChoiceBranches M} (h: B3CST.ChoiceBranches.mem stmt bs) :
SizeOf.sizeOf stmt < SizeOf.sizeOf bs :=
  match hbs: bs with
  | .choiceAtom _ (.choice_branch _ s) => by simp_all; grind
  | .choicePush _ branches (.choice_branch _ s) => by
    simp_all; rcases h with rfl | h
    · omega
    · have hbs := B3CST.ChoiceBranches.mem_sizeOf h; omega

def stmtFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) (s: B3CST.Statement M): Strata.B3AST.Statement M × List (CSTToASTError M) :=
  match s with
  | .var_decl_full m name ty autoinv init =>
      let ctx' := ctx.push name.val
      let (autoinv', e1) := expressionFromCST ctx' autoinv
      let (init', e2) := expressionFromCST ctx' init
      (.varDecl m (mapAnn (fun x => x) name) (mapAnn (fun t => some (mkAnn m t)) ty) (mkAnn m (some autoinv')) (mkAnn m (some init')), e1 ++ e2)
  | .var_decl_with_autoinv m name ty autoinv =>
      let ctx' := ctx.push name.val
      let (autoinv', errs) := expressionFromCST ctx' autoinv
      (.varDecl m (mapAnn (fun x => x) name) (mapAnn (fun t => some (mkAnn m t)) ty) (mkAnn m (some autoinv')) (mkAnn m none), errs)
  | .var_decl_with_init m name ty init =>
      let ctx' := ctx.push name.val
      let (init', errs) := expressionFromCST ctx' init
      (.varDecl m (mapAnn (fun x => x) name) (mapAnn (fun t => some (mkAnn m t)) ty) (mkAnn m none) (mkAnn m (some init')), errs)
  | .var_decl_typed m name ty =>
      (.varDecl m (mapAnn (fun x => x) name) (mapAnn (fun t => some (mkAnn m t)) ty) (mkAnn m none) (mkAnn m none), [])
  | .var_decl_inferred m name init =>
      let ctx' := ctx.push name.val
      let (init', errs) := expressionFromCST ctx' init
      (.varDecl m (mapAnn (fun x => x) name) (mkAnn m none) (mkAnn m none) (mkAnn m (some init')), errs)
  | .val_decl m name ty init =>
      let ctx' := ctx.push name.val
      let (init', errs) := expressionFromCST ctx' init
      (.varDecl m (mapAnn (fun x => x) name) (mapAnn (fun t => some (mkAnn m t)) ty) (mkAnn m none) (mkAnn m (some init')), errs)
  | .val_decl_inferred m name init =>
      let ctx' := ctx.push name.val
      let (init', errs) := expressionFromCST ctx' init
      (.varDecl m (mapAnn (fun x => x) name) (mkAnn m none) (mkAnn m none) (mkAnn m (some init')), errs)
  | .assign m lhs rhs =>
      let (idx, e1) := ctx.lookup lhs.val m
      let (rhs', e2) := expressionFromCST ctx rhs
      (.assign m (mkAnn m idx) rhs', e1 ++ e2)
  | .reinit_statement m v =>
      let (idx, errs) := ctx.lookup v.val m
      (.reinit m (mkAnn m idx), errs)
  | .check m expr =>
      let (expr', errs) := expressionFromCST ctx expr
      (.check m expr', errs)
  | .assume m expr =>
      let (expr', errs) := expressionFromCST ctx expr
      (.assume m expr', errs)
  | .reach m expr =>
      let (expr', errs) := expressionFromCST ctx expr
      (.reach m expr', errs)
  | .assert m expr =>
      let (expr', errs) := expressionFromCST ctx expr
      (.assert m expr', errs)
  | .return_statement m =>
      (.returnStmt m, [])
  | .block m stmts =>
      let (stmts', _, errors) := stmts.val.toList.foldl (fun (acc, ctx, errs) stmt =>
        let (stmt', e) := stmtFromCST ctx stmt
        let ctx' := match stmt with
          | .var_decl_full _ name _ _ _ => ctx.push name.val
          | .var_decl_with_autoinv _ name _ _ => ctx.push name.val
          | .var_decl_with_init _ name _ _ => ctx.push name.val
          | .var_decl_typed _ name _ => ctx.push name.val
          | .var_decl_inferred _ name _ => ctx.push name.val
          | .val_decl _ name _ _ => ctx.push name.val
          | .val_decl_inferred _ name _ => ctx.push name.val
          | _ => ctx
        (acc ++ [stmt'], ctx', errs ++ e)
      ) ([], ctx, [])
      (.blockStmt m (mkAnn m stmts'.toArray), errors)
  | .if_statement m cond thenB elseB =>
      let (cond', e1) := expressionFromCST ctx cond
      let (then', e2) := stmtFromCST ctx thenB
      let (elseBranch, e3) := match he: elseB.val with
        | some (.else_some _ stmt) =>
            let (stmt', e) := stmtFromCST ctx stmt
            (some stmt', e)
        | none => (none, [])
      (.ifStmt m cond' then' (mapAnn (fun _ => elseBranch) elseB), e1 ++ e2 ++ e3)
  | .loop_statement m invs body =>
      let (invariants, invErrors) := invs.val.toList.foldl (fun (acc, errs) inv =>
        match inv with
        | .invariant _ expr =>
            let (expr', e) := expressionFromCST ctx expr
            (acc ++ [expr'], errs ++ e)
      ) ([], [])
      let (body', bodyErrs) := stmtFromCST ctx body
      (.loop m (mkAnn m invariants.toArray) body', invErrors ++ bodyErrs)
  | .exit_statement m label =>
      (.exit m (mapAnn (fun opt => opt.map (fun l => mkAnn m l.val)) label), [])
  | .labeled_statement m label stmt =>
      let (stmt', errs) := stmtFromCST ctx stmt
      (.labeledStmt m (mapAnn (fun x => x) label) stmt', errs)
  | .probe m label =>
      (.probe m (mapAnn (fun x => x) label), [])
  | .aForall_statement m var ty body =>
      let ctx' := ctx.push var.val
      let (body', errs) := stmtFromCST ctx' body
      (.aForall m (mapAnn (fun x => x) var) (mapAnn (fun x => x) ty) body', errs)
  | .choose_statement m branches =>
      let (stmts, errors) := (choiceBranchesToList branches).attach.foldl (fun (acc, errs) stmt =>
        have hmem : B3CST.ChoiceBranches.mem stmt.1 branches := by
          rw [choiceBranchesToList_mem]; exact stmt.2
        let (stmt', e) := stmtFromCST ctx stmt.1
        (acc ++ [stmt'], errs ++ e)
      ) ([], [])
      (.choose m (mkAnn m stmts.toArray), errors)
  | .if_case_statement m cases =>
      let (casesConverted, errors) := cases.val.toList.attach.foldl (fun (acc, errs) case =>
        match hc: case.1 with
        | .if_case_branch cm cond stmt =>
            let (cond', e1) := expressionFromCST ctx cond
            let (stmt', e2) := stmtFromCST ctx stmt
            (acc ++ [.oneIfCase cm cond' stmt'], errs ++ e1 ++ e2)
      ) ([], [])
      (.ifCase m (mapAnn (fun _ => casesConverted.toArray) cases), errors)
  | .call_statement m procName args =>
      let (argsConverted, errors) := args.val.toList.foldl (fun (acc, errs) arg =>
        let (arg', e) := callArgFromCST ctx arg
        (acc ++ [arg'], errs ++ e)
      ) ([], [])
      (.call m (mapAnn (fun x => x) procName) (mapAnn (fun _ => argsConverted.toArray) args), errors)
  termination_by s
  decreasing_by
  all_goals(simp_wf; try omega)
  . cases stmts; simp_all; rename_i hs; have := Array.sizeOf_lt_of_mem hs; omega
  . cases elseB; simp_all; subst_vars; omega
  . have := B3CST.ChoiceBranches.mem_sizeOf hmem; omega
  . cases case; cases cases; simp_all; subst_vars; rename_i hin; simp at hin
    have := Array.sizeOf_lt_of_mem hin; simp_all; omega

def paramModeFromCST [Inhabited M] : Ann (Option (B3CST.PParamMode M)) M → Strata.B3AST.ParamMode M
  | ⟨m, none⟩ => .paramModeIn m
  | ⟨m, some (.pmode_out _)⟩ => .paramModeOut m
  | ⟨m, some (.pmode_inout _)⟩ => .paramModeInout m

def fParameterFromCST [Inhabited M] : B3CST.FParam M → Strata.B3AST.FParameter M
  | .fparam m injective name ty =>
      let inj := match injective.val with
        | some (.injective_some _) => true
        | none => false
      .fParameter m (mkAnn m inj) (mapAnn (fun x => x) name) (mapAnn (fun x => x) ty)

def pParameterFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) : B3CST.PParam M → Strata.B3AST.PParameter M × List (CSTToASTError M)
  | .pparam m mode name ty =>
      (.pParameter m (paramModeFromCST mode) (mapAnn (fun x => x) name) (mapAnn (fun x => x) ty) (mkAnn m none), [])
  | .pparam_with_autoinv m mode name ty autoinv =>
      let (autoinv', errs) := expressionFromCST ctx autoinv
      (.pParameter m (paramModeFromCST mode) (mapAnn (fun x => x) name) (mapAnn (fun x => x) ty) (mkAnn m (some autoinv')), errs)

def specFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) : B3CST.Spec M → Strata.B3AST.Spec M × List (CSTToASTError M)
  | .spec_requires m expr =>
      let (expr', errs) := expressionFromCST ctx expr
      (.specRequires m expr', errs)
  | .spec_ensures m expr =>
      let (expr', errs) := expressionFromCST ctx expr
      (.specEnsures m expr', errs)

def fparamsToList : Ann (Array (B3CST.FParam M)) M → List (B3CST.FParam M)
  | ⟨_, arr⟩ => arr.toList

def declFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) : B3CST.Decl M → Strata.B3AST.Decl M × List (CSTToASTError M)
  | .type_decl m name =>
      (.typeDecl m (mapAnn (fun x => x) name), [])
  | .tagger_decl m name forType =>
      (.tagger m (mapAnn (fun x => x) name) (mapAnn (fun x => x) forType), [])
  | .function_decl m name params resultType tag body =>
      let paramsAST := fparamsToList params |>.map fParameterFromCST
      let paramNames := paramsAST.map (fun p => match p with | .fParameter _ _ n _ => n.val)
      let ctx' := paramNames.foldl (fun acc n => acc.push n) ctx
      let tagAST := tag.val.map (fun t => match t with | .tag_some _ id => mkAnn m id.val)
      let (bodyAST, errors) := match body.val with
        | some (.function_body_some bm whens expr) =>
            let (whensConverted, whenErrors) := whens.val.toList.foldl (fun (acc, errs) w =>
              match w with
              | .when_clause wm e =>
                  let (e', err) := expressionFromCST ctx' e
                  (acc ++ [B3AST.When.when wm e'], errs ++ err)
            ) ([], [])
            let (expr', exprErrs) := expressionFromCST ctx' expr
            (some (B3AST.FunctionBody.functionBody bm (mkAnn bm whensConverted.toArray) expr'), whenErrors ++ exprErrs)
        | none => (none, [])
      (.function m (mapAnn (fun x => x) name) (mkAnn m paramsAST.toArray) (mapAnn (fun x => x) resultType) (mkAnn m tagAST) (mapAnn (fun _ => bodyAST) body), errors)
  | .axiom_decl m axiomBody =>
      match axiomBody with
      | .axiom _ expr =>
          let (expr', errs) := expressionFromCST ctx expr
          (.axiom m (mkAnn m #[]) expr', errs)
      | .explain_axiom _ names expr =>
          let namesAST := names.val.toList.map (fun n => mkAnn m n.val)
          let (expr', errs) := expressionFromCST ctx expr
          (.axiom m (mkAnn m namesAST.toArray) expr', errs)
  | .procedure_decl m name params specs body =>
      -- Build context for parameters: inout parameters need two entries (old and current)
      let ctx' := params.val.toList.foldl (fun acc p =>
        let (pname, mode) := match p with
          | .pparam _ mode n _ => (n.val, mode.val)
          | .pparam_with_autoinv _ mode n _ _ => (n.val, mode.val)
        match mode with
        | some (.pmode_inout _) => acc.push pname |>.push pname  -- Push twice: old value, then current value
        | _ => acc.push pname  -- Push once for in/out parameters
      ) ctx
      -- Now convert all parameters with the full context (so autoinv can reference all params)
      let (paramsConverted, paramErrors) := params.val.toList.foldl (fun (acc, errs) p =>
        let (p', e) := pParameterFromCST ctx' p
        (acc ++ [p'], errs ++ e)
      ) ([], [])
      let (specsConverted, specErrors) := specs.val.toList.foldl (fun (acc, errs) s =>
        let (s', e) := specFromCST ctx' s
        (acc ++ [s'], errs ++ e)
      ) ([], [])
      let (bodyAST, bodyErrors) := match body.val with
        | some (.proc_body_some _ s) =>
            let (s', e) := stmtFromCST ctx' s
            (some s', e)
        | none => (none, [])
      (.procedure m (mapAnn (fun x => x) name) (mkAnn m paramsConverted.toArray) (mkAnn m specsConverted.toArray) (mapAnn (fun _ => bodyAST) body), paramErrors ++ specErrors ++ bodyErrors)

def programFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) : B3CST.Program M → Strata.B3AST.Program M × List (CSTToASTError M)
  | .program m decls =>
      let (declsConverted, errors) := decls.val.toList.foldl (fun (acc, errs) d =>
        let (d', e) := declFromCST ctx d
        (acc ++ [d'], errs ++ e)
      ) ([], [])
      (.program m (mkAnn m declsConverted.toArray), errors)

end FromCST

end B3
