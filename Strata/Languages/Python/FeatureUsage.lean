/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.PythonDialect

/-!
# Feature Usage Analysis for Python Programs

Walks a Python DDM AST and collects every constructor encountered,
grouped by syntactic category (statement, expression, constant,
operator, etc.).  The result is a frequency map that can be printed
to stdout to understand which Python features a file uses.
-/

namespace Strata.Python.FeatureUsage

open Strata.Python (stmt expr constant operator unaryop boolop cmpop
                    pattern keyword comprehension withitem match_case
                    excepthandler opt_expr)

/-! ## State -/

/-- Accumulated feature counts and warnings. -/
public structure FeatureState where
  stmtCounts     : Std.HashMap String Nat := {}
  exprCounts     : Std.HashMap String Nat := {}
  constantCounts : Std.HashMap String Nat := {}
  operatorCounts : Std.HashMap String Nat := {}
  unaryopCounts  : Std.HashMap String Nat := {}
  boolopCounts   : Std.HashMap String Nat := {}
  cmpopCounts    : Std.HashMap String Nat := {}
  patternCounts  : Std.HashMap String Nat := {}
  warnings       : Array String := #[]

abbrev FeatureM := StateM FeatureState

/-- Increment a counter in a HashMap by 1. -/
private def bump (get : FeatureState → Std.HashMap String Nat)
    (set : FeatureState → Std.HashMap String Nat → FeatureState)
    (key : String) : FeatureM Unit :=
  modify fun s =>
    let m := get s
    set s (m.insert key (m.getD key 0 + 1))

private def bumpStmt     := bump (·.stmtCounts)     (fun s m => { s with stmtCounts     := m })
private def bumpExpr     := bump (·.exprCounts)     (fun s m => { s with exprCounts     := m })
private def bumpConstant := bump (·.constantCounts) (fun s m => { s with constantCounts := m })
private def bumpOperator := bump (·.operatorCounts) (fun s m => { s with operatorCounts := m })
private def bumpUnaryop  := bump (·.unaryopCounts)  (fun s m => { s with unaryopCounts  := m })
private def bumpBoolop   := bump (·.boolopCounts)   (fun s m => { s with boolopCounts   := m })
private def bumpCmpop    := bump (·.cmpopCounts)    (fun s m => { s with cmpopCounts    := m })
private def bumpPattern  := bump (·.patternCounts)  (fun s m => { s with patternCounts  := m })

private def warn (msg : String) : FeatureM Unit :=
  modify fun s => { s with warnings := s.warnings.push msg }

/-! ## Leaf visitors -/

private def visitConstant (c : constant SourceRange) : FeatureM Unit :=
  match c with
  | .ConTrue ..    => bumpConstant "ConTrue"
  | .ConFalse ..   => bumpConstant "ConFalse"
  | .ConPos ..     => bumpConstant "ConPos"
  | .ConNeg ..     => bumpConstant "ConNeg"
  | .ConString ..  => bumpConstant "ConString"
  | .ConFloat ..   => bumpConstant "ConFloat"
  | .ConComplex .. => bumpConstant "ConComplex"
  | .ConNone ..    => bumpConstant "ConNone"
  | .ConEllipsis ..=> bumpConstant "ConEllipsis"
  | .ConBytes ..   => bumpConstant "ConBytes"

private def visitOperator (op : operator SourceRange) : FeatureM Unit :=
  match op with
  | .Add ..      => bumpOperator "Add"
  | .Sub ..      => bumpOperator "Sub"
  | .Mult ..     => bumpOperator "Mult"
  | .Div ..      => bumpOperator "Div"
  | .FloorDiv .. => bumpOperator "FloorDiv"
  | .Mod ..      => bumpOperator "Mod"
  | .Pow ..      => bumpOperator "Pow"
  | .LShift ..   => bumpOperator "LShift"
  | .RShift ..   => bumpOperator "RShift"
  | .BitOr ..    => bumpOperator "BitOr"
  | .BitXor ..   => bumpOperator "BitXor"
  | .BitAnd ..   => bumpOperator "BitAnd"
  | .MatMult ..  => bumpOperator "MatMult"

private def visitUnaryOp (op : unaryop SourceRange) : FeatureM Unit :=
  match op with
  | .Invert .. => bumpUnaryop "Invert"
  | .Not ..    => bumpUnaryop "Not"
  | .UAdd ..   => bumpUnaryop "UAdd"
  | .USub ..   => bumpUnaryop "USub"

private def visitBoolOp (op : boolop SourceRange) : FeatureM Unit :=
  match op with
  | .And .. => bumpBoolop "And"
  | .Or ..  => bumpBoolop "Or"

private def visitCmpOp (op : cmpop SourceRange) : FeatureM Unit :=
  match op with
  | .Eq ..    => bumpCmpop "Eq"
  | .NotEq .. => bumpCmpop "NotEq"
  | .Lt ..    => bumpCmpop "Lt"
  | .LtE ..   => bumpCmpop "LtE"
  | .Gt ..    => bumpCmpop "Gt"
  | .GtE ..   => bumpCmpop "GtE"
  | .Is ..    => bumpCmpop "Is"
  | .IsNot .. => bumpCmpop "IsNot"
  | .In ..    => bumpCmpop "In"
  | .NotIn .. => bumpCmpop "NotIn"

/-! ## Expression visitor -/

partial def visitExpr (e : expr SourceRange) : FeatureM Unit := do
  match e with
  | .BoolOp _ op ⟨_, values⟩ =>
    bumpExpr "BoolOp"
    visitBoolOp op
    values.forM visitExpr
  | .NamedExpr _ target value =>
    bumpExpr "NamedExpr"
    visitExpr target
    visitExpr value
  | .BinOp _ left op right =>
    bumpExpr "BinOp"
    visitOperator op
    visitExpr left
    visitExpr right
  | .UnaryOp _ op operand =>
    bumpExpr "UnaryOp"
    visitUnaryOp op
    visitExpr operand
  | .Lambda _ _ body =>
    bumpExpr "Lambda"
    visitExpr body
  | .IfExp _ test body orelse =>
    bumpExpr "IfExp"
    visitExpr test
    visitExpr body
    visitExpr orelse
  | .Dict _ ⟨_, keys⟩ ⟨_, values⟩ =>
    bumpExpr "Dict"
    for k in keys do
      match k with
      | .some_expr _ ke => visitExpr ke
      | _ => pure ()
    values.forM visitExpr
  | .Set _ ⟨_, elts⟩ =>
    bumpExpr "Set"
    elts.forM visitExpr
  | .ListComp _ elt ⟨_, gens⟩ =>
    bumpExpr "ListComp"
    visitExpr elt
    gens.forM visitComprehension
  | .SetComp _ elt ⟨_, gens⟩ =>
    bumpExpr "SetComp"
    visitExpr elt
    gens.forM visitComprehension
  | .DictComp _ key value ⟨_, gens⟩ =>
    bumpExpr "DictComp"
    visitExpr key
    visitExpr value
    gens.forM visitComprehension
  | .GeneratorExp _ elt ⟨_, gens⟩ =>
    bumpExpr "GeneratorExp"
    visitExpr elt
    gens.forM visitComprehension
  | .Await _ value =>
    bumpExpr "Await"
    visitExpr value
  | .Yield _ ⟨_, value⟩ =>
    bumpExpr "Yield"
    value.forM visitExpr
  | .YieldFrom _ value =>
    bumpExpr "YieldFrom"
    visitExpr value
  | .Compare _ left ⟨_, ops⟩ ⟨_, comparators⟩ =>
    bumpExpr "Compare"
    visitExpr left
    ops.forM visitCmpOp
    comparators.forM visitExpr
  | .Call _ f ⟨_, args⟩ ⟨_, kwargs⟩ =>
    bumpExpr "Call"
    visitExpr f
    args.forM visitExpr
    kwargs.forM fun kw => visitKeyword kw
  | .FormattedValue _ value _ ⟨_, fmtSpec⟩ =>
    bumpExpr "FormattedValue"
    visitExpr value
    fmtSpec.forM visitExpr
  | .Interpolation _ value _ _ ⟨_, fmtSpec⟩ =>
    bumpExpr "Interpolation"
    visitExpr value
    fmtSpec.forM visitExpr
  | .JoinedStr _ ⟨_, values⟩ =>
    bumpExpr "JoinedStr"
    values.forM visitExpr
  | .TemplateStr _ ⟨_, values⟩ =>
    bumpExpr "TemplateStr"
    values.forM visitExpr
  | .Constant _ c _ =>
    bumpExpr "Constant"
    visitConstant c
  | .Attribute _ value _ _ =>
    bumpExpr "Attribute"
    visitExpr value
  | .Subscript _ value slice _ =>
    bumpExpr "Subscript"
    visitExpr value
    visitExpr slice
  | .Starred _ value _ =>
    bumpExpr "Starred"
    visitExpr value
  | .Name .. =>
    bumpExpr "Name"
  | .List _ ⟨_, elts⟩ _ =>
    bumpExpr "List"
    elts.forM visitExpr
  | .Tuple _ ⟨_, elts⟩ _ =>
    bumpExpr "Tuple"
    elts.forM visitExpr
  | .Slice _ ⟨_, lower⟩ ⟨_, upper⟩ ⟨_, step⟩ =>
    bumpExpr "Slice"
    lower.forM visitExpr
    upper.forM visitExpr
    step.forM visitExpr
where
  visitComprehension (g : comprehension SourceRange) : FeatureM Unit := do
    match g with
    | .mk_comprehension _ target iter ⟨_, ifs⟩ _ =>
      visitExpr target
      visitExpr iter
      ifs.forM visitExpr
  visitKeyword (kw : keyword SourceRange) : FeatureM Unit := do
    match kw with
    | .mk_keyword _ _ value => visitExpr value

/-! ## Pattern visitor -/

partial def visitPattern (p : pattern SourceRange) : FeatureM Unit := do
  match p with
  | .MatchValue _ value =>
    bumpPattern "MatchValue"
    visitExpr value
  | .MatchSingleton _ c =>
    bumpPattern "MatchSingleton"
    visitConstant c
  | .MatchSequence _ ⟨_, pats⟩ =>
    bumpPattern "MatchSequence"
    pats.forM visitPattern
  | .MatchMapping _ ⟨_, keys⟩ ⟨_, pats⟩ _ =>
    bumpPattern "MatchMapping"
    keys.forM visitExpr
    pats.forM visitPattern
  | .MatchClass _ cls ⟨_, pats⟩ ⟨_, kwAttrs⟩ ⟨_, kwPats⟩ =>
    bumpPattern "MatchClass"
    visitExpr cls
    pats.forM visitPattern
    kwPats.forM visitPattern
  | .MatchStar _ _ =>
    bumpPattern "MatchStar"
  | .MatchAs _ ⟨_, pat⟩ _ =>
    bumpPattern "MatchAs"
    pat.forM visitPattern
  | .MatchOr _ ⟨_, pats⟩ =>
    bumpPattern "MatchOr"
    pats.forM visitPattern

/-! ## Statement visitor -/

partial def visitStmt (s : stmt SourceRange) : FeatureM Unit := do
  match s with
  | .FunctionDef _ _ _ ⟨_, body⟩ _ _ _ _ =>
    bumpStmt "FunctionDef"
    body.forM visitStmt
  | .AsyncFunctionDef _ _ _ ⟨_, body⟩ _ _ _ _ =>
    bumpStmt "AsyncFunctionDef"
    body.forM visitStmt
  | .ClassDef _ _ _ _ ⟨_, body⟩ _ _ =>
    bumpStmt "ClassDef"
    body.forM visitStmt
  | .Return _ ⟨_, value⟩ =>
    bumpStmt "Return"
    value.forM visitExpr
  | .Delete _ ⟨_, targets⟩ =>
    bumpStmt "Delete"
    targets.forM visitExpr
  | .Assign _ ⟨_, targets⟩ value _ =>
    bumpStmt "Assign"
    targets.forM visitExpr
    visitExpr value
  | .AugAssign _ target op value =>
    bumpStmt "AugAssign"
    visitExpr target
    visitOperator op
    visitExpr value
  | .AnnAssign _ target _ ⟨_, value⟩ _ =>
    bumpStmt "AnnAssign"
    visitExpr target
    value.forM visitExpr
  | .For _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
    bumpStmt "For"
    visitExpr target
    visitExpr iter
    body.forM visitStmt
    orelse.forM visitStmt
  | .AsyncFor _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
    bumpStmt "AsyncFor"
    visitExpr target
    visitExpr iter
    body.forM visitStmt
    orelse.forM visitStmt
  | .While _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
    bumpStmt "While"
    visitExpr test
    body.forM visitStmt
    orelse.forM visitStmt
  | .If _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
    bumpStmt "If"
    visitExpr test
    body.forM visitStmt
    orelse.forM visitStmt
  | .With _ ⟨_, items⟩ ⟨_, body⟩ _ =>
    bumpStmt "With"
    for item in items do
      match item with
      | .mk_withitem _ ctxExpr ⟨_, optVars⟩ =>
        visitExpr ctxExpr
        optVars.forM visitExpr
    body.forM visitStmt
  | .AsyncWith _ ⟨_, items⟩ ⟨_, body⟩ _ =>
    bumpStmt "AsyncWith"
    for item in items do
      match item with
      | .mk_withitem _ ctxExpr ⟨_, optVars⟩ =>
        visitExpr ctxExpr
        optVars.forM visitExpr
    body.forM visitStmt
  | .Raise _ ⟨_, exc⟩ ⟨_, cause⟩ =>
    bumpStmt "Raise"
    exc.forM visitExpr
    cause.forM visitExpr
  | .Try _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ =>
    bumpStmt "Try"
    body.forM visitStmt
    for h in handlers do
      match h with
      | .ExceptHandler _ ⟨_, exType⟩ _ ⟨_, hBody⟩ =>
        exType.forM visitExpr
        hBody.forM visitStmt
    orelse.forM visitStmt
    finalbody.forM visitStmt
  | .TryStar _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ =>
    bumpStmt "TryStar"
    body.forM visitStmt
    for h in handlers do
      match h with
      | .ExceptHandler _ ⟨_, exType⟩ _ ⟨_, hBody⟩ =>
        exType.forM visitExpr
        hBody.forM visitStmt
    orelse.forM visitStmt
    finalbody.forM visitStmt
  | .Assert _ test ⟨_, msg⟩ =>
    bumpStmt "Assert"
    visitExpr test
    msg.forM visitExpr
  | .Import .. =>
    bumpStmt "Import"
  | .ImportFrom .. =>
    bumpStmt "ImportFrom"
  | .Global .. =>
    bumpStmt "Global"
  | .Nonlocal .. =>
    bumpStmt "Nonlocal"
  | .Expr _ value =>
    bumpStmt "Expr"
    visitExpr value
  | .Pass .. =>
    bumpStmt "Pass"
  | .Break .. =>
    bumpStmt "Break"
  | .Continue .. =>
    bumpStmt "Continue"
  | .Match _ subject ⟨_, cases⟩ =>
    bumpStmt "Match"
    visitExpr subject
    for c in cases do
      match c with
      | .mk_match_case _ pat ⟨_, guard⟩ ⟨_, cBody⟩ =>
        visitPattern pat
        guard.forM visitExpr
        cBody.forM visitStmt
  | .TypeAlias _ _ _ value =>
    bumpStmt "TypeAlias"
    visitExpr value

/-! ## Entry point and formatting -/

/-- Run the feature analysis over an array of top-level statements. -/
public def analyzeFeatures (stmts : Array (stmt SourceRange)) : FeatureState :=
  (stmts.forM visitStmt |>.run {}).2

/-- Format a HashMap as sorted lines of "  Name: Count". -/
private def formatCounts (m : Std.HashMap String Nat) : String :=
  let entries := m.toList.mergeSort (·.1 < ·.1)
  entries.foldl (init := "") fun acc (k, v) =>
    acc ++ s!"  {k}: {v}\n"

/-- Format the full feature report. -/
public def formatReport (s : FeatureState) : String :=
  let sections := #[
    ("Statement Features", s.stmtCounts),
    ("Expression Features", s.exprCounts),
    ("Constant Features", s.constantCounts),
    ("Operator Features", s.operatorCounts),
    ("UnaryOp Features", s.unaryopCounts),
    ("BoolOp Features", s.boolopCounts),
    ("CmpOp Features", s.cmpopCounts),
    ("Pattern Features", s.patternCounts)
  ]
  let body := sections.foldl (init := "") fun acc (title, counts) =>
    if counts.isEmpty then acc
    else acc ++ s!"=== {title} ===\n{formatCounts counts}\n"
  let warnSection := if s.warnings.isEmpty then ""
    else "=== Warnings ===\n" ++
      s.warnings.foldl (init := "") fun acc w => acc ++ s!"  {w}\n"
  body ++ warnSection

end Strata.Python.FeatureUsage
