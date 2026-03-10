/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.DefinitionAST
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 DDM Formatting Test Utilities

Common utilities and helper functions for B3 formatting tests.
Provides string cleanup functions and shared formatting infrastructure used across expression, statement, declaration, and program formatting tests.
-/

namespace B3

open Std (Format)
open Strata
open Strata.B3CST

/--
info: inductive Strata.B3CST.Expression : Type → Type
number of parameters: 1
constructors:
Strata.B3CST.Expression.not : {α : Type} → α → Expression α → Expression α
Strata.B3CST.Expression.natLit : {α : Type} → α → Nat → Expression α
Strata.B3CST.Expression.strLit : {α : Type} → α → String → Expression α
Strata.B3CST.Expression.btrue : {α : Type} → α → Expression α
Strata.B3CST.Expression.bfalse : {α : Type} → α → Expression α
Strata.B3CST.Expression.old_id : {α : Type} → α → Ann String α → Expression α
Strata.B3CST.Expression.id : {α : Type} → α → String → Expression α
Strata.B3CST.Expression.letExpr : {α : Type} → α → Ann String α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.labeledExpr : {α : Type} → α → Ann String α → Expression α → Expression α
Strata.B3CST.Expression.ite : {α : Type} → α → Expression α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.iff : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.implies : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.impliedBy : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.and : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.or : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.equal : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.not_equal : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.le : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.lt : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.ge : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.gt : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.neg : {α : Type} → α → Expression α → Expression α
Strata.B3CST.Expression.add : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.sub : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.mul : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.div : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.mod : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.paren : {α : Type} → α → Expression α → Expression α
Strata.B3CST.Expression.functionCall : {α : Type} → α → Ann String α → Ann (Array (Expression α)) α → Expression α
Strata.B3CST.Expression.forall_expr : {α : Type} →
  α → Ann (Array (VarDecl α)) α → Ann (Array (Pattern α)) α → Expression α → Expression α
Strata.B3CST.Expression.exists_expr : {α : Type} →
  α → Ann (Array (VarDecl α)) α → Ann (Array (Pattern α)) α → Expression α → Expression α
-/
#guard_msgs in
#print B3CST.Expression

/--
info: inductive Strata.B3AST.Expression : Type → Type
number of parameters: 1
constructors:
Strata.B3AST.Expression.literal : {α : Type} → α → B3AST.Literal α → B3AST.Expression α
Strata.B3AST.Expression.id : {α : Type} → α → Nat → B3AST.Expression α
Strata.B3AST.Expression.ite : {α : Type} →
  α → B3AST.Expression α → B3AST.Expression α → B3AST.Expression α → B3AST.Expression α
Strata.B3AST.Expression.binaryOp : {α : Type} →
  α → B3AST.BinaryOp α → B3AST.Expression α → B3AST.Expression α → B3AST.Expression α
Strata.B3AST.Expression.unaryOp : {α : Type} → α → B3AST.UnaryOp α → B3AST.Expression α → B3AST.Expression α
Strata.B3AST.Expression.functionCall : {α : Type} →
  α → Ann String α → Ann (Array (B3AST.Expression α)) α → B3AST.Expression α
Strata.B3AST.Expression.labeledExpr : {α : Type} → α → Ann String α → B3AST.Expression α → B3AST.Expression α
Strata.B3AST.Expression.letExpr : {α : Type} →
  α → Ann String α → B3AST.Expression α → B3AST.Expression α → B3AST.Expression α
Strata.B3AST.Expression.quantifierExpr : {α : Type} →
  α →
    B3AST.QuantifierKind α →
      Ann (Array (B3AST.VarDecl α)) α → Ann (Array (B3AST.Pattern α)) α → B3AST.Expression α → B3AST.Expression α
-/
#guard_msgs in
#print B3AST.Expression

/--
info: inductive Strata.B3CST.Pattern : Type → Type
number of parameters: 1
constructors:
Strata.B3CST.Pattern.pattern : {α : Type} → α → Ann (Array (Expression α)) α → Pattern α
-/
#guard_msgs in
#print B3CST.Pattern

-- Helpers to convert Unit annotations to SourceRange
mutual
  partial def exprFUnitToSourceRange : ExprF Unit → ExprF SourceRange
    | .bvar () idx => .bvar default idx
    | .fvar () idx => .fvar default idx
    | .fn () f => .fn default f
    | .app () f a => .app default (exprFUnitToSourceRange f) (argFUnitToSourceRange a)

  partial def argFUnitToSourceRange : ArgF Unit → ArgF SourceRange
    | .op op => .op { op with ann := default, args := op.args.map argFUnitToSourceRange }
    | .expr e => .expr (exprFUnitToSourceRange e)
    | .type t => .type (typeExprFUnitToSourceRange t)
    | .cat c => .cat (syntaxCatFUnitToSourceRange c)
    | .ident () x => .ident default x
    | .num () x => .num default x
    | .decimal () v => .decimal default v
    | .strlit () s => .strlit default s
    | .bytes () v => .bytes default v
    | .option () ma => .option default (ma.map argFUnitToSourceRange)
    | .seq () sep entries => .seq default sep (entries.map argFUnitToSourceRange)

  partial def typeExprFUnitToSourceRange : TypeExprF Unit → TypeExprF SourceRange
    | .ident () tp a => .ident default tp (a.map typeExprFUnitToSourceRange)
    | .bvar () idx => .bvar default idx
    | .tvar () name => .tvar default name
    | .fvar () idx a => .fvar default idx (a.map typeExprFUnitToSourceRange)
    | .arrow () a r => .arrow default (typeExprFUnitToSourceRange a) (typeExprFUnitToSourceRange r)

  partial def syntaxCatFUnitToSourceRange : SyntaxCatF Unit → SyntaxCatF SourceRange
    | ⟨(), name, args⟩ => ⟨default, name, args.map syntaxCatFUnitToSourceRange⟩
end

-- Create a minimal B3 program to get the dialect context
def b3Program : Program := #strata program B3CST; #end

-- Helper to convert OperationF Unit to OperationF SourceRange
def operationFUnitToSourceRange (op : OperationF Unit) : OperationF SourceRange :=
  { op with ann := default, args := op.args.map argFUnitToSourceRange }

/--
Clean up Unit annotation repr output for better readability.
Step 1: Remove `{ ann := (), val := X }` constructs via brace matching, keeping just u X
Step 2: Reduce excessive indentation (more than 2 spaces difference) to 2 spaces
-/
partial def cleanupUnitRepr (s : String) : String :=
  -- Step 1: Remove { ann := (), val := X } constructs
  let rec removeAnnStructs (chars : List Char) (acc : String) : String :=
    match chars with
    | [] => acc
    | _ =>
        let pattern := "{ ann := (),".toList
        if chars.take pattern.length == pattern then
          -- Found "{ ann := (),", now find matching closing brace for the whole structure
          let rec findClose (cs : List Char) (depth : Nat) (acc : List Char) : Option (List Char × List Char) :=
            match cs with
            | [] => none
            | _ :: [] => none
            | c :: d :: rest =>
                if c == '{' then findClose (d :: rest) (depth + 1) (c :: acc)
                else if c == ' ' && d == '}' then
                  if depth == 0 then some (acc.reverse, rest)
                  else findClose (d :: rest) (depth - 1) (c :: acc)
                else findClose (d :: rest) depth (c :: acc)
          match findClose (chars.drop 1) 0 [] with
          | none => removeAnnStructs (chars.drop 1) (acc ++ String.ofList [chars.head!])
          | some (innerChars, afterClose) =>
              -- innerChars contains everything between { and }, like "ann := (),\n  val := X" or "ann := (), val := X"
              -- Find "val := " and extract everything after it
              let valPattern := "val := ".toList
              let rec findValStart (cs : List Char) : Option (List Char) :=
                match cs with
                | [] => none
                | _ =>
                    if cs.take valPattern.length == valPattern then
                      some (cs.drop valPattern.length)
                    else
                      match cs with
                      | [] => none
                      | _ :: rest => findValStart rest
              match findValStart innerChars with
              | none => removeAnnStructs (chars.drop 1) (acc ++ String.ofList [chars.head!])
              | some valueOnly => removeAnnStructs afterClose (acc ++ "u " ++ String.ofList valueOnly)
        else
          removeAnnStructs (chars.drop 1) (acc ++ String.ofList [chars.head!])

  -- Apply removal 10 times to handle nested structures up to depth 10
  let rec applyNTimes (n : Nat) (str : String) : String :=
    if n == 0 then str
    else applyNTimes (n - 1) (removeAnnStructs str.toList "")

  let step1 := applyNTimes 10 s

  -- Step 2: Remove trailing spaces and normalize indentation using a stack
  let lines := step1.splitOn "\n"
  let rec processLines (lines : List String) (indentStack : List Nat) (acc : List String) : List String :=
    match lines with
    | [] => acc.reverse
    | line :: rest =>
        -- Remove trailing spaces
        let line := line.dropEndWhile ' ' |>.toString
        let indent := line.takeWhile (· == ' ') |>.toString.length
        let content := line.dropWhile (· == ' ')
        if content.isEmpty then
          processLines rest indentStack ("" :: acc)
        else
          -- Update indent stack based on current indent
          let newStack :=
            match indentStack with
            | [] => [indent]
            | prevIndent :: _ =>
                if indent > prevIndent then
                  -- Deeper nesting - push current indent
                  indent :: indentStack
                else if indent == prevIndent then
                  -- Same level - keep stack
                  indentStack
                else
                  -- Dedent - pop stack until we find matching or smaller indent
                  let rec popUntil (stack : List Nat) : List Nat :=
                    match stack with
                    | [] => [indent]
                    | h :: t =>
                        if h <= indent then stack
                        else popUntil t
                  popUntil indentStack
          -- New indent is (stack depth - 1) * 2
          let newIndent := (newStack.length - 1) * 2
          let newLine := String.ofList (List.replicate newIndent ' ') ++ content
          processLines rest newStack (newLine :: acc)

  String.intercalate "\n" (processLines lines [] [])

/-- Remove Strata.B3AST namespace prefixes for expression types -/
def cleanupExprRepr (s : String) : String :=
  let s := s.replace "Strata.B3AST.Expression." "."
  let s := s.replace "Strata.B3AST.QuantifierKind." "."
  let s := s.replace "Strata.B3AST.Literal." "."
  let s := s.replace "Strata.B3AST.UnaryOp." "."
  let s := s.replace "Strata.B3AST.BinaryOp." "."
  let s := s.replace "Strata.B3AST.Pattern." "."
  let s := s.replace "Strata.B3AST.VarDecl." "."
  s

/-- Remove Strata.B3AST namespace prefixes for statement types -/
def cleanupStmtRepr (s : String) : String :=
  let s := cleanupExprRepr s
  let s := s.replace "Strata.B3AST.Statement." "."
  let s := s.replace "Strata.B3AST.CallArg." "."
  let s := s.replace "Strata.B3AST.OneIfCase." "."
  s

/-- Remove Strata.B3AST namespace prefixes for declaration types -/
def cleanupDeclRepr (s : String) : String :=
  let s := cleanupStmtRepr s
  let s := s.replace "Strata.B3AST.Program." "."
  let s := s.replace "Strata.B3AST.Decl." "."
  let s := s.replace "Strata.B3AST.FParameter." "."
  let s := s.replace "Strata.B3AST.PParameter." "."
  let s := s.replace "Strata.B3AST.Spec." "."
  let s := s.replace "Strata.B3AST.ParamMode." "."
  let s := s.replace "Strata.B3AST.FunctionBody." "."
  let s := s.replace "Strata.B3AST.When." "."
  s

end B3
