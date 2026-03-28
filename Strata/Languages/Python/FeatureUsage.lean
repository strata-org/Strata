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
  stmtCounts      : Std.HashMap String Nat := {}
  exprCounts      : Std.HashMap String Nat := {}
  constantCounts  : Std.HashMap String Nat := {}
  operatorCounts  : Std.HashMap String Nat := {}
  unaryopCounts   : Std.HashMap String Nat := {}
  boolopCounts    : Std.HashMap String Nat := {}
  cmpopCounts     : Std.HashMap String Nat := {}
  patternCounts   : Std.HashMap String Nat := {}
  unresolvedNames : Std.HashMap String Nat := {}
  decoratorNames  : Std.HashMap String Nat := {}
  /-- Constructs that the SSA translator would degrade on. -/
  ssaUnsupported  : Std.HashMap String Nat := {}
  warnings        : Array String := #[]
  /-- Stack of defined-name sets. Top = current scope. -/
  scopeStack      : Array (Std.HashSet String) := #[{}]

abbrev FeatureM := StateM FeatureState

/-- Increment a counter in a HashMap by 1. -/
private def bump (get : FeatureState → Std.HashMap String Nat)
    (set : FeatureState → Std.HashMap String Nat → FeatureState)
    (key : String) : FeatureM Unit :=
  modify fun s =>
    let m := get s
    set s (m.insert key (m.getD key 0 + 1))

private def bumpStmt       := bump (·.stmtCounts)      (fun s m => { s with stmtCounts      := m })
private def bumpExpr       := bump (·.exprCounts)      (fun s m => { s with exprCounts      := m })
private def bumpConstant   := bump (·.constantCounts)  (fun s m => { s with constantCounts  := m })
private def bumpOperator   := bump (·.operatorCounts)  (fun s m => { s with operatorCounts  := m })
private def bumpUnaryop    := bump (·.unaryopCounts)   (fun s m => { s with unaryopCounts   := m })
private def bumpBoolop     := bump (·.boolopCounts)    (fun s m => { s with boolopCounts    := m })
private def bumpCmpop      := bump (·.cmpopCounts)     (fun s m => { s with cmpopCounts     := m })
private def bumpPattern    := bump (·.patternCounts)   (fun s m => { s with patternCounts   := m })
private def bumpUnresolved := bump (·.unresolvedNames) (fun s m => { s with unresolvedNames := m })
private def bumpDecorator  := bump (·.decoratorNames)  (fun s m => { s with decoratorNames  := m })
private def bumpSSAUnsup  := bump (·.ssaUnsupported)  (fun s m => { s with ssaUnsupported  := m })

/-- Bump an expression counter AND flag it as SSA-unsupported. -/
private def bumpUnsupExpr (name : String) : FeatureM Unit := do
  bumpExpr name; bumpSSAUnsup name

/-- Bump a statement counter AND flag it as SSA-unsupported. -/
private def bumpUnsupStmt (name : String) : FeatureM Unit := do
  bumpStmt name; bumpSSAUnsup name

private def warn (msg : String) : FeatureM Unit :=
  modify fun s => { s with warnings := s.warnings.push msg }

/-! ## Scope tracking for unresolved name analysis -/

/-- Add a name to the current (top-of-stack) scope. -/
private def defineName (name : String) : FeatureM Unit :=
  modify fun s =>
    let stack := s.scopeStack
    if h : stack.size > 0 then
      let top := stack[stack.size - 1]
      { s with scopeStack := stack.set (stack.size - 1) (top.insert name) }
    else s

/-- Check if a name is defined in any scope on the stack. -/
private def isNameDefined (name : String) : FeatureM Bool := do
  let s ← get
  return s.scopeStack.any (·.contains name)

/-- Push a new scope (entering a function/class body). -/
private def pushScope : FeatureM Unit :=
  modify fun s => { s with scopeStack := s.scopeStack.push {} }

/-- Pop the current scope (leaving a function/class body). -/
private def popScope : FeatureM Unit :=
  modify fun s => { s with scopeStack := s.scopeStack.pop }

/-- Extract a human-readable name from a decorator expression. -/
private def decoratorName (d : expr SourceRange) : Option String :=
  match d with
  | .Name _ ⟨_, name⟩ _ => some name
  | .Attribute _ _ ⟨_, attr⟩ _ => some attr
  | .Call _ f _ _ =>
    match f with
    | .Name _ ⟨_, name⟩ _ => some name
    | .Attribute _ _ ⟨_, attr⟩ _ => some attr
    | _ => none
  | _ => none

/-- Record all decorators in a decorator list. -/
private def visitDecorators (decorators : Array (expr SourceRange)) : FeatureM Unit :=
  for d in decorators do
    match decoratorName d with
    | some name => bumpDecorator name
    | none => warn s!"Unrecognized decorator expression"

/-- Extract names from a target expression (handles Name, Tuple, List unpacking). -/
private def extractNames (e : expr SourceRange) : Array String :=
  match e with
  | .Name _ ⟨_, name⟩ _ => #[name]
  | .Tuple _ ⟨_, elts⟩ _ => elts.flatMap extractNames
  | .List _ ⟨_, elts⟩ _ => elts.flatMap extractNames
  | _ => #[]

/-- Extract a single name from a Name expression. -/
private def extractName (e : expr SourceRange) : Option String :=
  match e with
  | .Name _ ⟨_, name⟩ _ => some name
  | _ => none

/-- Extract parameter names from an arguments node and define them in current scope. -/
private def defineParams (args : arguments SourceRange) : FeatureM Unit :=
  match args with
  | .mk_arguments _ posonlyargs posargs vararg kwonlyargs _ kwarg _ => do
    -- positional-only args
    for a in posonlyargs.val do
      match a with
      | .mk_arg _ ⟨_, name⟩ _ _ => defineName name
    -- regular positional args
    for a in posargs.val do
      match a with
      | .mk_arg _ ⟨_, name⟩ _ _ => defineName name
    -- *args
    match vararg.val with
    | some (.mk_arg _ ⟨_, name⟩ _ _) => defineName name
    | none => pure ()
    -- keyword-only args
    for a in kwonlyargs.val do
      match a with
      | .mk_arg _ ⟨_, name⟩ _ _ => defineName name
    -- **kwargs
    match kwarg.val with
    | some (.mk_arg _ ⟨_, name⟩ _ _) => defineName name
    | none => pure ()

/-- Pre-collect all names defined in a statement list (shallow — does not
    recurse into function/class bodies). Used to handle forward references
    within a scope (e.g., function called before its def). -/
partial def preCollectDefined (stmts : Array (stmt SourceRange)) : FeatureM Unit :=
  for s in stmts do
    match s with
    | .FunctionDef _ ⟨_, name⟩ _ _ _ _ _ _ => defineName name
    | .AsyncFunctionDef _ ⟨_, name⟩ _ _ _ _ _ _ => defineName name
    | .ClassDef _ ⟨_, name⟩ _ _ _ _ _ => defineName name
    | .Assign _ ⟨_, targets⟩ _ _ =>
      for t in targets do
        (extractNames t).forM defineName
    | .AnnAssign _ target _ _ _ =>
      (extractNames target).forM defineName
    | .AugAssign _ target _ _ =>
      (extractNames target).forM defineName
    | .For _ target _ _ _ _ =>
      (extractNames target).forM defineName
    | .AsyncFor _ target _ _ _ _ =>
      (extractNames target).forM defineName
    | .Import _ ⟨_, aliases⟩ =>
      for a in aliases do
        defineName (a.asname.getD a.name)
    | .ImportFrom _ _ ⟨_, aliases⟩ _ =>
      for a in aliases do
        defineName (a.asname.getD a.name)
    | .With _ ⟨_, items⟩ _ _ =>
      for item in items do
        match item with
        | .mk_withitem _ _ ⟨_, optVars⟩ =>
          match optVars with
          | some e => (extractNames e).forM defineName
          | none => pure ()
    | _ => pure ()

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
    bumpUnsupExpr "NamedExpr"
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
    bumpUnsupExpr "Lambda"
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
    bumpUnsupExpr "ListComp"
    pushScope
    gens.forM visitComprehension
    visitExpr elt
    popScope
  | .SetComp _ elt ⟨_, gens⟩ =>
    bumpUnsupExpr "SetComp"
    pushScope
    gens.forM visitComprehension
    visitExpr elt
    popScope
  | .DictComp _ key value ⟨_, gens⟩ =>
    bumpUnsupExpr "DictComp"
    pushScope
    gens.forM visitComprehension
    visitExpr key
    visitExpr value
    popScope
  | .GeneratorExp _ elt ⟨_, gens⟩ =>
    bumpUnsupExpr "GeneratorExp"
    pushScope
    gens.forM visitComprehension
    visitExpr elt
    popScope
  | .Await _ value =>
    bumpUnsupExpr "Await"
    visitExpr value
  | .Yield _ ⟨_, value⟩ =>
    bumpUnsupExpr "Yield"
    value.forM visitExpr
  | .YieldFrom _ value =>
    bumpUnsupExpr "YieldFrom"
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
  | .Name _ ⟨_, name⟩ (.Load _) =>
    bumpExpr "Name"
    let defined ← isNameDefined name
    if !defined then
      bumpUnresolved name
  | .Name _ ⟨_, _⟩ _ =>
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
      -- Define the comprehension variable in current scope
      match extractName target with
      | some name => defineName name
      | none => pure ()
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
  | .MatchClass _ cls ⟨_, pats⟩ ⟨_, _kwAttrs⟩ ⟨_, kwPats⟩ =>
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
  | .FunctionDef _ ⟨_, name⟩ args ⟨_, body⟩ ⟨_, decorators⟩ _ _ _ =>
    bumpStmt "FunctionDef"
    defineName name
    visitDecorators decorators
    -- Enter new scope with params, pre-collect body definitions
    pushScope
    defineParams args
    preCollectDefined body
    body.forM visitStmt
    popScope
  | .AsyncFunctionDef _ ⟨_, name⟩ args ⟨_, body⟩ ⟨_, decorators⟩ _ _ _ =>
    bumpUnsupStmt "AsyncFunctionDef"
    defineName name
    visitDecorators decorators
    pushScope
    defineParams args
    preCollectDefined body
    body.forM visitStmt
    popScope
  | .ClassDef _ ⟨_, name⟩ _ _ ⟨_, body⟩ ⟨_, decorators⟩ _ =>
    bumpStmt "ClassDef"
    defineName name
    visitDecorators decorators
    pushScope
    preCollectDefined body
    body.forM visitStmt
    popScope
  | .Return _ ⟨_, value⟩ =>
    bumpStmt "Return"
    value.forM visitExpr
  | .Delete _ ⟨_, targets⟩ =>
    bumpStmt "Delete"
    targets.forM visitExpr
  | .Assign _ ⟨_, targets⟩ value _ =>
    bumpStmt "Assign"
    for t in targets do
      (extractNames t).forM defineName
    targets.forM visitExpr
    visitExpr value
  | .AugAssign _ target op value =>
    bumpStmt "AugAssign"
    (extractNames target).forM defineName
    visitExpr target
    visitOperator op
    visitExpr value
  | .AnnAssign _ target _ ⟨_, value⟩ _ =>
    bumpStmt "AnnAssign"
    (extractNames target).forM defineName
    visitExpr target
    value.forM visitExpr
  | .For _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
    bumpStmt "For"
    (extractNames target).forM defineName
    visitExpr target
    visitExpr iter
    body.forM visitStmt
    orelse.forM visitStmt
  | .AsyncFor _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
    bumpUnsupStmt "AsyncFor"
    (extractNames target).forM defineName
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
        match optVars with
        | some e =>
          (extractNames e).forM defineName
          visitExpr e
        | none => pure ()
    body.forM visitStmt
  | .AsyncWith _ ⟨_, items⟩ ⟨_, body⟩ _ =>
    bumpUnsupStmt "AsyncWith"
    for item in items do
      match item with
      | .mk_withitem _ ctxExpr ⟨_, optVars⟩ =>
        visitExpr ctxExpr
        match optVars with
        | some e =>
          (extractNames e).forM defineName
          visitExpr e
        | none => pure ()
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
      | .ExceptHandler _ ⟨_, exType⟩ errname ⟨_, hBody⟩ =>
        exType.forM visitExpr
        -- Define the handler variable (e.g., `as e`)
        match errname.val with
        | some ⟨_, name⟩ => defineName name
        | none => pure ()
        hBody.forM visitStmt
    orelse.forM visitStmt
    finalbody.forM visitStmt
  | .TryStar _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ =>
    bumpStmt "TryStar"
    body.forM visitStmt
    for h in handlers do
      match h with
      | .ExceptHandler _ ⟨_, exType⟩ errname ⟨_, hBody⟩ =>
        exType.forM visitExpr
        match errname.val with
        | some ⟨_, name⟩ => defineName name
        | none => pure ()
        hBody.forM visitStmt
    orelse.forM visitStmt
    finalbody.forM visitStmt
  | .Assert _ test ⟨_, msg⟩ =>
    bumpStmt "Assert"
    visitExpr test
    msg.forM visitExpr
  | .Import _ ⟨_, aliases⟩ =>
    bumpStmt "Import"
    for a in aliases do
      defineName (a.asname.getD a.name)
  | .ImportFrom _ _ ⟨_, aliases⟩ _ =>
    bumpStmt "ImportFrom"
    for a in aliases do
      defineName (a.asname.getD a.name)
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
  let action : FeatureM Unit := do
    -- Pre-collect module-level names so forward references resolve
    preCollectDefined stmts
    stmts.forM visitStmt
  (action |>.run {}).2

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
    ("Pattern Features", s.patternCounts),
    ("Unresolved Names", s.unresolvedNames),
    ("Decorator Names", s.decoratorNames),
    ("SSA Unsupported Constructs", s.ssaUnsupported)
  ]
  let body := sections.foldl (init := "") fun acc (title, counts) =>
    if counts.isEmpty then acc
    else acc ++ s!"=== {title} ===\n{formatCounts counts}\n"
  let warnSection := if s.warnings.isEmpty then ""
    else "=== Warnings ===\n" ++
      s.warnings.foldl (init := "") fun acc w => acc ++ s!"  {w}\n"
  body ++ warnSection

end Strata.Python.FeatureUsage
