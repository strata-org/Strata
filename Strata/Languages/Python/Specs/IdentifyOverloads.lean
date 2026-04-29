/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.OverloadTable
public import Strata.Languages.Python.PythonDialect
import Strata.Languages.Core.Factory

/-!
# Overload Resolution for Python Programs

Walks a Python AST and collects which overloaded service modules
are actually used.  Given an `OverloadTable` (from a dispatch
`.pyspec.st.ion` file), the walker finds every `Call` whose
function name appears in the table and whose first argument is
a string literal matching an overload entry, then records the
`pythonModule` of the resolved return type.

The result is a deduplicated set of module names that can be used
to determine which `.pyspec.st.ion` files are needed.
-/

namespace Strata.Python.Specs.IdentifyOverloads

open Strata.Python (stmt expr keyword FunctionOverloads OverloadTable PythonIdent)

/-- State accumulated while walking the AST. -/
public structure ResolveState where
  modules  : Std.HashSet String := {}
  warnings : Array String := #[]

/-- Monad for the overload-resolution walker.
    Reads an `OverloadTable` from the environment and accumulates
    resolved modules and warnings in `ResolveState`. -/
abbrev ResolveM := ReaderT OverloadTable (StateM ResolveState)

/-- Record a warning about an unhandled AST node. -/
def warn (msg : String) : ResolveM Unit :=
  modify fun s =>
    { s with warnings := s.warnings.push msg }

/-- Record a module name from a resolved overload. -/
def recordModule (mod : String) : ResolveM Unit :=
  modify fun s =>
    { s with modules := s.modules.insert mod }

/-! ## Recursive AST Walker -/

mutual

/-- Walk an expression, checking `Call` nodes against
    the overload table and recursing into sub-expressions. -/
partial def walkExpr
    (e : expr SourceRange)
    : ResolveM Unit := do
  match e with
  -- The interesting case: function calls
  | .Call _ f ⟨_, args⟩ ⟨_, kwargs⟩ => do
    -- Check dispatch: use first positional arg, or keyword arg matching the expected param name
    let maybeFuncName :=
          match f with
          | .Attribute _ _ attr _ => some attr.val
          | .Name _ n _ => some n.val
          | _ => none
    if let some funcName := maybeFuncName then
      if let some fnOverloads := (← read)[funcName]? then
        let kwPairs := kwargs.toList.map keyword.nameAndValue
        if let some firstArg := fnOverloads.findDispatchArg args kwPairs then
          if let (.Constant _ (.ConString _ ⟨_, s⟩) _) := firstArg then
            if let some pyId := fnOverloads.entries[s]? then
              recordModule pyId.pythonModule
    -- Recurse into func, args, keyword values
    walkExpr f
    args.forM walkExpr
    kwargs.forM (walkExpr ·.value)

  -- Recurse into sub-expressions for all other forms
  | .BoolOp _ _ ⟨_, values⟩ =>
    values.forM walkExpr
  | .NamedExpr _ target value =>
    walkExpr target
    walkExpr value
  | .BinOp _ left _ right =>
    walkExpr left
    walkExpr right
  | .UnaryOp _ _ operand =>
    walkExpr operand
  | .Lambda _ _ body =>
    walkExpr body
  | .IfExp _ test body orelse =>
    walkExpr test
    walkExpr body
    walkExpr orelse
  | .Dict _ ⟨_, keys⟩ ⟨_, values⟩ => do
    for k in keys do
      match k with
      | .some_expr _ ke => walkExpr ke
      | _ => pure ()
    values.forM walkExpr
  | .Set _ ⟨_, elts⟩ =>
    elts.forM walkExpr
  | .ListComp _ elt ⟨_, gens⟩ =>
    walkExpr elt
    gens.forM walkComprehension
  | .SetComp _ elt ⟨_, gens⟩ =>
    walkExpr elt
    gens.forM walkComprehension
  | .DictComp _ key value ⟨_, gens⟩ =>
    walkExpr key
    walkExpr value
    gens.forM walkComprehension
  | .GeneratorExp _ elt ⟨_, gens⟩ =>
    walkExpr elt
    gens.forM walkComprehension
  | .Await _ value =>
    walkExpr value
  | .Yield _ ⟨_, value⟩ => do
    value.forM walkExpr
  | .YieldFrom _ value =>
    walkExpr value
  | .Compare _ left _ ⟨_, comparators⟩ => do
    walkExpr left
    comparators.forM walkExpr
  | .FormattedValue _ value _ ⟨_, fmtSpec⟩ => do
    walkExpr value
    fmtSpec.forM walkExpr
  | .Interpolation _ value _ _ ⟨_, fmtSpec⟩ => do
    walkExpr value
    fmtSpec.forM walkExpr
  | .JoinedStr _ ⟨_, values⟩ => do
    values.forM walkExpr
  | .TemplateStr _ ⟨_, values⟩ => do
    values.forM walkExpr
  | .Subscript _ value slice _ =>
    walkExpr value
    walkExpr slice
  | .Starred _ value _ =>
    walkExpr value
  | .List _ ⟨_, elts⟩ _ =>
    elts.forM walkExpr
  | .Tuple _ ⟨_, elts⟩ _ =>
    elts.forM walkExpr
  | .Slice _ ⟨_, lower⟩ ⟨_, upper⟩ ⟨_, step⟩ => do
    lower.forM walkExpr
    upper.forM walkExpr
    step.forM walkExpr
  | .Attribute _ value _ _ =>
    walkExpr value
  -- Leaf nodes — no sub-expressions
  | .Constant .. | .Name .. =>
    pure ()

/-- Walk a comprehension's sub-expressions. -/
partial def walkComprehension
    (g : Strata.Python.comprehension SourceRange)
    : ResolveM Unit := do
  match g with
  | .mk_comprehension _ target iter ⟨_, ifs⟩ _ =>
    walkExpr target
    walkExpr iter
    ifs.forM walkExpr

/-- Walk a single statement, recursing into
    sub-expressions and sub-statement bodies. -/
partial def walkStmt
    (s : stmt SourceRange)
    : ResolveM Unit := do
  match s with
  | .FunctionDef _ _ _ ⟨_, body⟩ _ _ _ _ =>
    walkStmts body
  | .AsyncFunctionDef _ _ _ ⟨_, body⟩ _ _ _ _ =>
    walkStmts body
  | .ClassDef _ _ _ _ ⟨_, body⟩ _ _ =>
    walkStmts body
  | .Return _ ⟨_, value⟩ =>
    value.forM walkExpr
  | .Delete _ ⟨_, targets⟩ =>
    targets.forM walkExpr
  | .Assign _ ⟨_, targets⟩ value _ => do
    targets.forM walkExpr
    walkExpr value
  | .AugAssign _ target _ value =>
    walkExpr target
    walkExpr value
  | .AnnAssign _ target _ ⟨_, value⟩ _ => do
    walkExpr target
    value.forM walkExpr
  | .For _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
    walkExpr target
    walkExpr iter
    walkStmts body
    walkStmts orelse
  | .AsyncFor _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
    walkExpr target
    walkExpr iter
    walkStmts body
    walkStmts orelse
  | .While _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
    walkExpr test
    walkStmts body
    walkStmts orelse
  | .If _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
    walkExpr test
    walkStmts body
    walkStmts orelse
  | .With _ ⟨_, items⟩ ⟨_, body⟩ _ => do
    for item in items do
      match item with
      | .mk_withitem _ ctxExpr ⟨_, optVars⟩ =>
        walkExpr ctxExpr
        optVars.forM walkExpr
    walkStmts body
  | .AsyncWith _ ⟨_, items⟩ ⟨_, body⟩ _ => do
    for item in items do
      match item with
      | .mk_withitem _ ctxExpr ⟨_, optVars⟩ =>
        walkExpr ctxExpr
        optVars.forM walkExpr
    walkStmts body
  | .Raise _ ⟨_, exc⟩ ⟨_, cause⟩ => do
    exc.forM walkExpr
    cause.forM walkExpr
  | .Try _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ => do
    walkStmts body
    for h in handlers do
      match h with
      | .ExceptHandler _ ⟨_, exType⟩ _ ⟨_, hBody⟩ =>
        exType.forM walkExpr
        walkStmts hBody
    walkStmts orelse
    walkStmts finalbody
  | .TryStar _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ => do
    walkStmts body
    for h in handlers do
      match h with
      | .ExceptHandler _ ⟨_, exType⟩ _ ⟨_, hBody⟩ =>
        exType.forM walkExpr
        walkStmts hBody
    walkStmts orelse
    walkStmts finalbody
  | .Assert _ test ⟨_, msg⟩ => do
    walkExpr test
    msg.forM walkExpr
  | .Expr _ value =>
    walkExpr value
  | .Match _ subject ⟨_, cases⟩ => do
    walkExpr subject
    for c in cases do
      match c with
      | .mk_match_case _ _pat ⟨_, guard⟩ ⟨_, cBody⟩ =>
        guard.forM walkExpr
        walkStmts cBody
  | .TypeAlias _ _ _ value =>
    walkExpr value
  -- Leaf statements — no sub-expressions to walk
  | .Import .. | .ImportFrom .. | .Global ..
  | .Nonlocal .. | .Pass .. | .Break ..
  | .Continue .. =>
    pure ()

/-- Walk an array of statements. -/
partial def walkStmts
    (stmts : Array (stmt SourceRange))
    : ResolveM Unit := do
  stmts.forM walkStmt

end

/-- Run the walker over the top-level statements and return
    the final state containing collected modules and warnings. -/
public def resolveOverloads
    (overloads : OverloadTable)
    (stmts : Array (stmt SourceRange))
    : ResolveState :=
  (walkStmts stmts |>.run overloads |>.run {}).2

end Strata.Python.Specs.IdentifyOverloads
