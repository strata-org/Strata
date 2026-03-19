/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.PythonDialect
public import Strata.Languages.Python.Specs.OverloadTable
import Strata.Languages.Python.Specs.ToLaurel

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

open Strata.Python (stmt expr)
open Strata.Python.Specs (PythonIdent)
open Strata.Python.Specs.ToLaurel (OverloadTable)

/-- State accumulated while walking the AST. -/
public structure ResolveState where
  modules  : Std.HashSet String := {}
  warnings : Array String := #[]

/-- Monad for the overload-resolution walker. -/
abbrev ResolveM := StateM ResolveState

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
    (tbl : OverloadTable)
    (e : expr SourceRange)
    : ResolveM Unit := do
  match e with
  -- The interesting case: function calls
  | .Call _ f args kwargs => do
    -- Check dispatch
    let funcName := match f with
      | .Attribute _ _ attr _ => attr.val
      | .Name _ n _ => n.val
      | _ => ""
    match tbl.get? funcName with
    | some fnOverloads =>
      if h : args.val.size > 0 then
        match args.val[0] with
        | .Constant _ (.ConString _ s) _ =>
          if let some pyId := fnOverloads.get? s.val then
            recordModule pyId.pythonModule
        | _ => pure ()
    | none => pure ()
    -- Recurse into func, args, keyword values
    walkExpr tbl f
    for arg in args.val do
      walkExpr tbl arg
    for kw in kwargs.val do
      match kw with
      | .mk_keyword _ _ kwVal => walkExpr tbl kwVal

  -- Recurse into sub-expressions for all other forms
  | .BoolOp _ _ values => do
    for v in values.val do walkExpr tbl v
  | .NamedExpr _ target value =>
    walkExpr tbl target
    walkExpr tbl value
  | .BinOp _ left _ right =>
    walkExpr tbl left
    walkExpr tbl right
  | .UnaryOp _ _ operand =>
    walkExpr tbl operand
  | .Lambda _ _ body =>
    walkExpr tbl body
  | .IfExp _ test body orelse =>
    walkExpr tbl test
    walkExpr tbl body
    walkExpr tbl orelse
  | .Dict _ keys values => do
    for k in keys.val do
      match k with
      | .some_expr _ ke => walkExpr tbl ke
      | _ => pure ()
    for v in values.val do walkExpr tbl v
  | .Set _ elts => do
    for e in elts.val do walkExpr tbl e
  | .ListComp _ elt gens =>
    walkExpr tbl elt
    for g in gens.val do walkComprehension tbl g
  | .SetComp _ elt gens =>
    walkExpr tbl elt
    for g in gens.val do walkComprehension tbl g
  | .DictComp _ key value gens =>
    walkExpr tbl key
    walkExpr tbl value
    for g in gens.val do walkComprehension tbl g
  | .GeneratorExp _ elt gens =>
    walkExpr tbl elt
    for g in gens.val do walkComprehension tbl g
  | .Await _ value =>
    walkExpr tbl value
  | .Yield _ value => do
    if let some v := value.val then walkExpr tbl v
  | .YieldFrom _ value =>
    walkExpr tbl value
  | .Compare _ left _ comparators => do
    walkExpr tbl left
    for c in comparators.val do walkExpr tbl c
  | .FormattedValue _ value _ fmtSpec => do
    walkExpr tbl value
    if let some fs := fmtSpec.val then
      walkExpr tbl fs
  | .Interpolation _ value _ _ fmtSpec => do
    walkExpr tbl value
    if let some fs := fmtSpec.val then
      walkExpr tbl fs
  | .JoinedStr _ values => do
    for v in values.val do walkExpr tbl v
  | .TemplateStr _ values => do
    for v in values.val do walkExpr tbl v
  | .Subscript _ value slice _ =>
    walkExpr tbl value
    walkExpr tbl slice
  | .Starred _ value _ =>
    walkExpr tbl value
  | .List _ elts _ => do
    for e in elts.val do walkExpr tbl e
  | .Tuple _ elts _ => do
    for e in elts.val do walkExpr tbl e
  | .Slice _ lower upper step => do
    if let some l := lower.val then walkExpr tbl l
    if let some u := upper.val then walkExpr tbl u
    if let some s := step.val then walkExpr tbl s
  | .Attribute _ value _ _ =>
    walkExpr tbl value
  -- Leaf nodes — no sub-expressions
  | .Constant .. | .Name .. =>
    pure ()

/-- Walk a comprehension's sub-expressions. -/
partial def walkComprehension
    (tbl : OverloadTable)
    (g : Strata.Python.comprehension SourceRange)
    : ResolveM Unit := do
  match g with
  | .mk_comprehension _ target iter ifs _ =>
    walkExpr tbl target
    walkExpr tbl iter
    for cond in ifs.val do walkExpr tbl cond

/-- Walk a single statement, recursing into
    sub-expressions and sub-statement bodies. -/
partial def walkStmt
    (tbl : OverloadTable)
    (s : stmt SourceRange)
    : ResolveM Unit := do
  match s with
  | .FunctionDef _ _ _ body _ _ _ _ =>
    walkStmts tbl body.val
  | .AsyncFunctionDef _ _ _ body _ _ _ _ =>
    walkStmts tbl body.val
  | .ClassDef _ _ _ _ body _ _ =>
    walkStmts tbl body.val
  | .Return _ value => do
    if let some v := value.val then walkExpr tbl v
  | .Delete _ targets => do
    for t in targets.val do walkExpr tbl t
  | .Assign _ targets value _ => do
    for t in targets.val do walkExpr tbl t
    walkExpr tbl value
  | .AugAssign _ target _ value =>
    walkExpr tbl target
    walkExpr tbl value
  | .AnnAssign _ target _ value _ => do
    walkExpr tbl target
    if let some v := value.val then walkExpr tbl v
  | .For _ target iter body orelse _ =>
    walkExpr tbl target
    walkExpr tbl iter
    walkStmts tbl body.val
    walkStmts tbl orelse.val
  | .AsyncFor _ target iter body orelse _ =>
    walkExpr tbl target
    walkExpr tbl iter
    walkStmts tbl body.val
    walkStmts tbl orelse.val
  | .While _ test body orelse =>
    walkExpr tbl test
    walkStmts tbl body.val
    walkStmts tbl orelse.val
  | .If _ test body orelse =>
    walkExpr tbl test
    walkStmts tbl body.val
    walkStmts tbl orelse.val
  | .With _ items body _ => do
    for item in items.val do
      match item with
      | .mk_withitem _ ctxExpr optVars =>
        walkExpr tbl ctxExpr
        if let some v := optVars.val then
          walkExpr tbl v
    walkStmts tbl body.val
  | .AsyncWith _ items body _ => do
    for item in items.val do
      match item with
      | .mk_withitem _ ctxExpr optVars =>
        walkExpr tbl ctxExpr
        if let some v := optVars.val then
          walkExpr tbl v
    walkStmts tbl body.val
  | .Raise _ exc cause => do
    if let some e := exc.val then walkExpr tbl e
    if let some c := cause.val then walkExpr tbl c
  | .Try _ body handlers orelse finalbody => do
    walkStmts tbl body.val
    for h in handlers.val do
      match h with
      | .ExceptHandler _ exType _ hBody =>
        if let some t := exType.val then
          walkExpr tbl t
        walkStmts tbl hBody.val
    walkStmts tbl orelse.val
    walkStmts tbl finalbody.val
  | .TryStar _ body handlers orelse finalbody => do
    walkStmts tbl body.val
    for h in handlers.val do
      match h with
      | .ExceptHandler _ exType _ hBody =>
        if let some t := exType.val then
          walkExpr tbl t
        walkStmts tbl hBody.val
    walkStmts tbl orelse.val
    walkStmts tbl finalbody.val
  | .Assert _ test msg => do
    walkExpr tbl test
    if let some m := msg.val then walkExpr tbl m
  | .Expr _ value =>
    walkExpr tbl value
  | .Match _ subject cases => do
    walkExpr tbl subject
    for c in cases.val do
      match c with
      | .mk_match_case _ _pat guard cBody =>
        if let some g := guard.val then
          walkExpr tbl g
        walkStmts tbl cBody.val
  | .TypeAlias _ _ _ value =>
    walkExpr tbl value
  -- Leaf statements — no sub-expressions to walk
  | .Import .. | .ImportFrom .. | .Global ..
  | .Nonlocal .. | .Pass .. | .Break ..
  | .Continue .. =>
    pure ()

/-- Walk an array of statements. -/
partial def walkStmts
    (tbl : OverloadTable)
    (stmts : Array (stmt SourceRange))
    : ResolveM Unit := do
  for s in stmts do walkStmt tbl s

end

/-- Run the walker over the top-level statements and return
    the final state containing collected modules and warnings. -/
public def resolveOverloads
    (overloads : OverloadTable)
    (stmts : Array (stmt SourceRange))
    : ResolveState :=
  (walkStmts overloads stmts |>.run {}).2

end Strata.Python.Specs.IdentifyOverloads
