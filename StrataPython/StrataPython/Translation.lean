/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
public import StrataPython.PythonDialect
public import StrataPython.Resolution
import StrataDDM.Util.SourceRange

/-!
# Pass 2: Translation

Structural recursion over the resolved Python AST. Pattern matches on
NodeInfo and emits Laurel constructs. Never constructs Laurel.Identifier
from strings — only forwards what Resolution provided.

Input:  ResolvedPythonProgram
Output: Laurel.Program
-/

namespace StrataPython.Translation

open Strata (Uri FileRange)
open Strata.Laurel
open StrataDDM
open StrataPython
open StrataPython.Resolution

public section

-- ═══════════════════════════════════════════════════════════════════════════════
-- Error
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Errors that can occur during translation. -/
inductive TransError where
  /-- A Python construct with no Laurel equivalent. -/
  | unsupportedConstruct (msg : String)
  /-- A bug in the translator (should never occur on well-resolved input). -/
  | internalError (msg : String)
  /-- An error in the user's Python code detected during translation. -/
  | userError (range : SourceRange) (msg : String)
  deriving Repr

instance : ToString TransError where
  toString
    | .unsupportedConstruct msg => s!"Translation: unsupported construct: {msg}"
    | .internalError msg => s!"Translation: internal error: {msg}"
    | .userError _range msg => s!"User code error: {msg}"

-- ═══════════════════════════════════════════════════════════════════════════════
-- Monad (State for fresh counter + loop labels)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Mutable state threaded through translation: fresh name counter, source file path,
    and a stack of loop break/continue labels for translating `break`/`continue`. -/
structure TransState where
  /-- Counter for generating unique temporary names. -/
  freshCounter : Nat := 0
  /-- Path of the source file being translated (used for metadata). -/
  filePath : System.FilePath := ""
  /-- Stack of (break_label, continue_label) pairs for enclosing loops. -/
  loopLabels : List (Identifier × Identifier) := []
  deriving Inhabited

abbrev BaseM := StateT TransState (Except TransError)

/-- Writer monad for translation. Produces a value plus a list of emitted Laurel statements.
    Allows expressions that need prefix statements (e.g., `classNew` emits `New` + `__init__`)
    to `tell` those statements and return just the expression value. -/
structure TransM (α : Type) where
  /-- Run the writer, producing the value and accumulated statement list. -/
  run : BaseM (α × List StmtExprMd)

instance : Monad TransM where
  pure a := ⟨pure (a, [])⟩
  bind ma f := ⟨do
    let (a, w1) ← ma.run
    let (b, w2) ← (f a).run
    pure (b, w1 ++ w2)⟩

instance : MonadLift BaseM TransM where
  monadLift ma := ⟨do let a ← ma; pure (a, [])⟩

instance : MonadExceptOf TransError TransM where
  throw e := ⟨throw e⟩
  tryCatch ma f := ⟨tryCatch ma.run (fun e => (f e).run)⟩

def tell (stmts : List StmtExprMd) : TransM Unit := ⟨pure ((), stmts)⟩

def listen (ma : TransM α) : TransM (α × List StmtExprMd) := ⟨do
  let (a, stmts) ← ma.run
  pure ((a, stmts), stmts)⟩

def pass (ma : TransM (α × (List StmtExprMd → List StmtExprMd))) : TransM α := ⟨do
  let ((a, f), stmts) ← ma.run
  pure (a, f stmts)⟩

def collect (ma : TransM α) : TransM (α × List StmtExprMd) :=
  liftM (α := α × List StmtExprMd) ma.run

-- ═══════════════════════════════════════════════════════════════════════════════
-- Smart Constructors
-- ═══════════════════════════════════════════════════════════════════════════════

private def sourceRangeToMd (filePath : System.FilePath) (sr : SourceRange) : Option FileRange :=
  some { file := .file filePath.toString, range := sr }

def mkExpr (sr : SourceRange) (expr : StmtExpr) : TransM StmtExprMd := do
  pure { val := expr, source := sourceRangeToMd (← get).filePath sr }

private def defaultMd : Option FileRange := none
def mkExprDefault (expr : StmtExpr) : StmtExprMd := { val := expr, source := defaultMd }
def mkTypeDefault (ty : HighType) : HighTypeMd := { val := ty, source := defaultMd }

/-- Default-source local-variable declaration (see `mkLocalDecl`). -/
def mkLocalDeclDefault (id : Identifier) (ty : HighTypeMd) (init : Option StmtExprMd) : StmtExprMd :=
  match init with
  | some v => mkExprDefault (.Assign [{ val := .Declare { name := id, type := ty }, source := defaultMd }] v)
  | none => mkExprDefault (.Var (.Declare { name := id, type := ty }))

/-- Wrap a `Variable` as a `.Var` statement-expression with source location. -/
def mkVar (sr : SourceRange) (v : Variable) : TransM StmtExprMd := mkExpr sr (.Var v)

/-- Extract the `Variable` from a `.Var` statement-expression (assignment targets are
    always translated to `.Var` nodes). Preserves the source location. -/
def toVarTarget (e : StmtExprMd) : VariableMd :=
  match e.val with
  | .Var v => { val := v, source := e.source }
  | _ => { val := .Local default, source := e.source }

/-- Build a local-variable declaration. With an initializer this lowers to an
    `Assign` to a `Declare` target (the canonical "declare + initialize" form
    consumed by `LaurelToCoreSchemaPass`); without one it is a bare `Var (Declare …)`. -/
def mkLocalDecl (sr : SourceRange) (id : Identifier) (ty : HighTypeMd)
    (init : Option StmtExprMd) : TransM StmtExprMd := do
  match init with
  | some v => do
    let target : VariableMd := { val := .Declare { name := id, type := ty }, source := sourceRangeToMd (← get).filePath sr }
    mkExpr sr (.Assign [target] v)
  | none => mkExpr sr (.Var (.Declare { name := id, type := ty }))

def freshId (pfx : String) : TransM Identifier := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }
  pure { text := s!"{pfx}_{s.freshCounter}", uniqueId := none }

def pushLoopLabel (pfx : String) : TransM (Identifier × Identifier) := do
  let s ← get
  let bk : Identifier := { text := s!"{pfx}_break_{s.freshCounter}", uniqueId := none }
  let ct : Identifier := { text := s!"{pfx}_continue_{s.freshCounter}", uniqueId := none }
  set { s with freshCounter := s.freshCounter + 1, loopLabels := (bk, ct) :: s.loopLabels }
  pure (bk, ct)

def popLoopLabel : TransM Unit := modify fun s => { s with loopLabels := s.loopLabels.tail! }
def currentBreakLabel : TransM (Option Identifier) := do return (← get).loopLabels.head?.map (·.1)
def currentContinueLabel : TransM (Option Identifier) := do return (← get).loopLabels.head?.map (·.2)

-- ═══════════════════════════════════════════════════════════════════════════════
-- PythonType → HighType
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Map a resolved Python type annotation to a Laurel `HighType`.

Base names map to Core types: `int`/`bool`/`str`/`float`/`None` to their
scalars, `Any`/`object` to `Any`, and the container names `dict`/`list` to the
homogeneous Core encodings `DictStrAny`/`ListAny`. A bare name that matches none
of these is a user-defined class (`.UserDefined`), which Translation emits as a
`Composite`.

Subscripted generics carry the same meaning as their base: the parameterized
containers (`dict[...]`, `list[...]`, and the `typing` aliases `Dict`/`List`/
`Tuple`/`Set`) map to the container encodings, and the type-level operators
(`Optional`/`Union`/`Literal`/`Unpack`/`NotRequired`/`Required`/`Type`) erase to
`Any`. A subscripted name with no concrete encoding is a user-defined generic
class (`.UserDefined`). The lowercase `dict`/`list` subscript cases must agree
with the bare-name cases — otherwise `body: dict[str, Any]` is typed `Composite`
while its dict-literal value is `DictStrAny`, and Core fails to unify the two. -/
def pythonTypeToHighType : PythonType → HighType
  | .Name _ n _ => match n.val with
    | "int" => .TInt
    | "bool" => .TBool
    | "str" => .TString
    -- Python `float` is a real: a float literal lowers to `LiteralDecimal : TReal`
    -- and the prelude boxes via `from_float : real`. Annotating `float` as `TReal`
    -- keeps annotation and literal in one domain (no `real`↔`float64` reconciliation).
    | "float" => .TReal
    | "None" => .TVoid
    | "Any" | "object" => .TCore "Any"
    | "dict" => .TCore "DictStrAny"
    | "list" => .TCore "ListAny"
    | name => .UserDefined { text := name, uniqueId := none }
  | .Constant _ (.ConNone _) _ => .TVoid
  | .BinOp _ _ (.BitOr _) _ => .TCore "Any"
  | .Subscript _ (.Name _ n _) _ _ => match n.val with
    | "dict" | "Dict" => .TCore "DictStrAny"
    | "list" | "List" | "tuple" | "Tuple" | "set" | "Set" | "frozenset" => .TCore "ListAny"
    | "Optional" | "Union" | "Type"
    | "Literal" | "Unpack" | "NotRequired" | "Required" => .TCore "Any"
    | other => .UserDefined { text := other, uniqueId := none }
  | _ => .TCore "Any"

-- ═══════════════════════════════════════════════════════════════════════════════
-- Runtime Constants (extracted from runtime program interface)
-- ═══════════════════════════════════════════════════════════════════════════════

private def rt (name : String) : Identifier := { text := name, uniqueId := none }

private def rtListAnyCons := rt "ListAny_cons"
private def rtListAnyNil := rt "ListAny_nil"
private def rtFromListAny := rt "from_ListAny"
private def rtDictStrAnyCons := rt "DictStrAny_cons"
private def rtDictStrAnyEmpty := rt "DictStrAny_empty"
private def rtFromDictStrAny := rt "from_DictStrAny"
private def rtFromNone := rt "from_None"
private def rtAnyGet := rt "Any_get"
private def rtAnySets := rt "Any_sets"
private def rtFromSlice := rt "from_Slice"
private def rtAnyAsInt := rt "Any..as_int!"
private def rtOptSome := rt "OptSome"
private def rtOptNone := rt "OptNone"
private def rtPAdd := rt "PAdd"
private def rtPIn := rt "PIn"
private def rtIsError := rt "isError"
private def rtToStringAny := rt "to_string_any"
private def rtLaurelResult := rt "LaurelResult"
private def rtMaybeExcept := rt "maybe_except"

-- ═══════════════════════════════════════════════════════════════════════════════
-- ═══════════════════════════════════════════════════════════════════════════════
-- The Structural Recursion
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Runtime comparison-operator function name for a resolved cmpop, given its RHS operand.
    `is`/`is not` are UNINTERPRETED (`PIs`/`PIsNot` have no model) EXCEPT against `None`:
    Python's `is None`/`is not None` are identity checks, but in the `Any` value model None
    is a singleton so identity coincides with equality — so we lower them to the MODELED
    `PEq`/`PNEq` (which handle None via `isfrom_None`). Without this, `if x is None` is
    inconclusive. Non-None `is` stays `PIs` (uninterpreted, sound-but-inconclusive — NOT an
    error: matches the elaborator's tolerance and keeps unusual `is` usages analyzable). -/
def cmpopResolvedToLaurel (op : StrataPython.cmpop ResolvedAnn) (rhs : StrataPython.expr ResolvedAnn) : String :=
  let rhsIsNone := match rhs with | .Constant _ (.ConNone _) _ => true | _ => false
  match op with
  | .Eq _ => "PEq" | .NotEq _ => "PNEq" | .Lt _ => "PLt" | .LtE _ => "PLe"
  | .Gt _ => "PGt" | .GtE _ => "PGe" | .In _ => "PIn" | .NotIn _ => "PNotIn"
  | .Is _ => if rhsIsNone then "PEq" else "PIs"
  | .IsNot _ => if rhsIsNone then "PNEq" else "PIsNot"

/-- Parse a Python float literal string (e.g. "0.0", "1.5", "1e10", "1_000.5") into a
    `Decimal { mantissa, exponent }`. Returns `none` for inf/nan (unrepresentable). Mirrors
    the proven PythonToLaurel `parseFloatString`. A Python float MUST become a `LiteralDecimal`
    (which types as `TReal`, matching `from_float : real`), NOT a `LiteralString` — the latter
    was a v2 workaround from before kbd had a decimal literal, and mis-types ("real with string"). -/
private def parseFloatString (s : String) : Option Decimal := do
  let lower := s.toLower
  if lower == "inf" || lower == "-inf" || lower == "nan" then none
  else
  let s := s.replace "_" ""
  let (coeffStr, expPart) :=
    match s.splitOn "e" with
    | [c, e] => (c, (if e.startsWith "+" then e.drop 1 else e).toInt?)
    | _ => match s.splitOn "E" with
      | [c, e] => (c, (if e.startsWith "+" then e.drop 1 else e).toInt?)
      | _ => (s, some 0)
  let sciExp ← expPart
  match coeffStr.splitOn "." with
  | [intPart, fracPart] =>
    let digits := intPart ++ fracPart
    let mantissa ← digits.toInt?
    some { mantissa, exponent := sciExp - fracPart.length }
  | [intPart] =>
    let mantissa ← intPart.toInt?
    some { mantissa, exponent := sciExp }
  | _ => none

mutual

partial def translateExpr (e : StrataPython.expr ResolvedAnn) : TransM StmtExprMd := do
  let sr := e.ann.sr
  match e with
  | .Constant _ (.ConPos _ n) _ => mkExpr sr (.LiteralInt n.val)
  | .Constant _ (.ConNeg _ n) _ => mkExpr sr (.LiteralInt (-n.val))
  | .Constant _ (.ConString _ s) _ => mkExpr sr (.LiteralString s.val)
  | .Constant _ (.ConTrue _) _ => mkExpr sr (.LiteralBool true)
  | .Constant _ (.ConFalse _) _ => mkExpr sr (.LiteralBool false)
  | .Constant _ (.ConNone _) _ => mkExpr sr (.StaticCall rtFromNone [])
  | .Constant _ (.ConFloat _ f) _ =>
    match parseFloatString f.val with
    | some d => mkExpr sr (.LiteralDecimal d)
    | none => mkExpr sr .Hole  -- inf/nan: unrepresentable as Decimal → sound hole

  | .Constant _ _ _ => mkExpr sr .Hole
  | .Name ann _ _ => match ann.info with
    | .variable name => mkExpr sr (.Var (.Local name.toLaurel))
    | .unresolved => mkExpr sr (.Hole (deterministic := false))
    | .irrelevant => mkExpr sr (.Hole (deterministic := false))
    | _ => panic! "Resolution bug: invalid NodeInfo on Name node"
  | .Call ann func args kwargs => match ann.info with
    | .funcCall sig => do
        -- Prepend the receiver ONLY for instance methods (sig has a receiver slot).
        -- A `.static` sig is a module/free function: its `.Attribute` base (e.g. the
        -- module `boto3` in `boto3.client(...)`) is NOT an argument and must be dropped.
        let receiver ← match sig.params, func with
          | .instance _ _, .Attribute _ obj _ _ => pure [← translateExpr obj]
          | _, _ => pure []
        let posArgs ← args.val.toList.mapM translateExpr
        let kwargPairs ← kwargs.val.toList.filterMapM fun kw => match kw with
          | .mk_keyword _ kwName kwExpr => do
            let val ← translateExpr kwExpr
            match kwName.val with | some n => pure (some (n.val, val)) | none => pure none
        mkExpr sr (.StaticCall sig.laurelName (← sig.matchArgs (receiver ++ posArgs) kwargPairs translateExpr (mkKwargs := (do return some (← mkExpr sr (.Hole (deterministic := false)))))))
    | .classNew cls initSig => do
        let tmp ← freshId "new"
        let tmpRef ← mkExpr sr (.Var (.Local tmp))
        let assignNew ← mkExpr sr (.Assign [toVarTarget tmpRef] (← mkExpr sr (.New cls.toLaurel)))
        let posArgs ← args.val.toList.mapM translateExpr
        let kwargPairs ← kwargs.val.toList.filterMapM fun kw => match kw with
          | .mk_keyword _ kwName kwExpr => do
            let val ← translateExpr kwExpr
            match kwName.val with | some n => pure (some (n.val, val)) | none => pure none
        let initCall ← mkExpr sr (.StaticCall initSig.laurelName (← initSig.matchArgs ([tmpRef] ++ posArgs) kwargPairs translateExpr (mkKwargs := (do return some (← mkExpr sr (.Hole (deterministic := false)))))))
        tell [assignNew, initCall]
        pure tmpRef
    | .unresolved => mkExpr sr (.Hole (deterministic := false))
    | _ => mkExpr sr (.Hole (deterministic := false))
  | .BinOp ann left _ right => match ann.info with
    | .funcCall sig => do
        let l ← translateExpr left; let r ← translateExpr right
        mkExpr sr (.StaticCall sig.laurelName (← sig.matchArgs [l, r] [] translateExpr))
    | _ => mkExpr sr .Hole
  | .BoolOp ann _ operands => match ann.info with
    | .funcCall sig => do
        let exprs ← operands.val.toList.mapM translateExpr
        match exprs with
        | [] => mkExpr sr .Hole
        | first :: rest => rest.foldlM (fun acc e => do
            let args ← sig.matchArgs [acc, e] [] translateExpr
            mkExpr sr (.StaticCall sig.laurelName args)) first
    | _ => mkExpr sr .Hole
  | .UnaryOp ann _ operand => match ann.info with
    | .funcCall sig => do
        mkExpr sr (.StaticCall sig.laurelName (← sig.matchArgs [← translateExpr operand] [] translateExpr))
    | _ => mkExpr sr .Hole
  | .Compare ann left ops comparators => match ann.info with
    | .funcCall sig => do
        if comparators.val.size == 1 then
          -- Use the None-aware op name (`is None`→PEq), NOT sig.laurelName (which is the
          -- uninterpreted PIs/PIsNot for `is`/`is not`). matchArgs still wraps the operands.
          let opName := cmpopResolvedToLaurel (ops.val[0]!) (comparators.val[0]!)
          let l ← translateExpr left; let r ← translateExpr comparators.val[0]!
          mkExpr sr (.StaticCall (rt opName) (← sig.matchArgs [l, r] [] translateExpr))
        else do
          -- Chained comparison `e0 op0 e1 op1 e2 ...` lowers to
          -- `(e0 op0 e1) and (e1 op1 e2) and ...`. Each operand is translated once;
          -- each pairwise op uses its own runtime fn (PLt/PLe/PEq/...) named by the
          -- resolved cmpop (None-aware). The conjunction uses `PAnd`. Operands are
          -- Any-valued; the elaborator coerces them to the op params.
          let operandExprs := #[left] ++ comparators.val
          -- build operand translations once
          let mut translated : Array StmtExprMd := #[]
          for e in operandExprs do translated := translated.push (← translateExpr e)
          -- fold pairwise comparisons joined by PAnd
          let mut acc : Option StmtExprMd := none
          for i in [0:ops.val.size] do
            let opName := cmpopResolvedToLaurel (ops.val[i]!) (comparators.val[i]!)
            let li := translated[i]!
            let ri := translated[i+1]!
            let cmp ← mkExpr sr (.StaticCall (rt opName) [li, ri])
            acc := some (← match acc with
              | none => pure cmp
              | some prev => mkExpr sr (.StaticCall (rt "PAnd") [prev, cmp]))
          match acc with
          | some result => pure result
          | none => mkExpr sr .Hole  -- unreachable: comparators non-empty
    | _ => mkExpr sr .Hole
  | .Attribute ann obj _ _ => match ann.info with
    | .attribute name => do mkExpr sr (.Var (.Field (← translateExpr obj) name.toLaurel))
    | _ => mkExpr sr .Hole
  | .Subscript _ container slice _ => do
      let c ← translateExpr container
      let idx ← match slice with
        | .Slice _ start stop _ => do
          let s ← match start.val with
            | some e => translateExpr e
            | none => mkExpr sr (.LiteralInt 0)
          let e ← match stop.val with
            | some e => mkExpr sr (.StaticCall rtOptSome [← translateExpr e])
            | none => mkExpr sr (.StaticCall rtOptNone [])
          mkExpr sr (.StaticCall rtFromSlice [s, e])
        | _ => translateExpr slice
      mkExpr sr (.StaticCall rtAnyGet [c, idx])
  | .List _ elts _ => do
      let es ← elts.val.toList.mapM translateExpr
      let nil ← mkExpr sr (.StaticCall rtListAnyNil [])
      es.foldrM (fun e acc => mkExpr sr (.StaticCall rtListAnyCons [e, acc])) nil
  | .Tuple _ elts _ => do
      let es ← elts.val.toList.mapM translateExpr
      let nil ← mkExpr sr (.StaticCall rtListAnyNil [])
      es.foldrM (fun e acc => mkExpr sr (.StaticCall rtListAnyCons [e, acc])) nil
  | .Dict _ keys vals => do
      let ks ← keys.val.toList.mapM (fun k => match k with
        | .some_expr _ e => translateExpr e | .missing_expr _ => mkExpr sr .Hole)
      let vs ← vals.val.toList.mapM translateExpr
      let empty ← mkExpr sr (.StaticCall rtDictStrAnyEmpty [])
      (List.zip ks vs).foldrM (fun (k, v) acc =>
        mkExpr sr (.StaticCall rtDictStrAnyCons [k, v, acc])) empty
  | .IfExp _ test body orelse => do
      mkExpr sr (.IfThenElse (← translateExpr test) (← translateExpr body) (some (← translateExpr orelse)))
  | .JoinedStr _ values => do
      if values.val.isEmpty then mkExpr sr (.LiteralString "")
      else do
        let parts ← values.val.toList.mapM translateExpr
        let init ← mkExpr sr (.LiteralString "")
        parts.foldlM (fun acc p => mkExpr sr (.StaticCall rtPAdd [acc, p])) init
  | .FormattedValue _ value _ _ => do
      mkExpr sr (.StaticCall rtToStringAny [← translateExpr value])
  | _ => mkExpr sr .Hole

where
  ann (e : StrataPython.expr ResolvedAnn) : ResolvedAnn := match e with
    | .Name a .. => a | .Constant a .. => a | .BinOp a .. => a | .Compare a .. => a
    | .BoolOp a .. => a | .UnaryOp a .. => a | .Call a .. => a | .Attribute a .. => a
    | .Subscript a .. => a | .List a .. => a | .Tuple a .. => a | .Dict a .. => a
    | .Set a .. => a | .IfExp a .. => a | .JoinedStr a .. => a | .FormattedValue a .. => a
    | .Lambda a .. => a | .ListComp a .. => a | .SetComp a .. => a | .DictComp a .. => a
    | .GeneratorExp a .. => a | .NamedExpr a .. => a | .Slice a .. => a | .Starred a .. => a
    | .Await a .. => a | .Yield a .. => a | .YieldFrom a .. => a | .TemplateStr a .. => a
    | .Interpolation a .. => a

-- ═══════════════════════════════════════════════════════════════════════════════
-- Statement Translation
-- ═══════════════════════════════════════════════════════════════════════════════

partial def translateStmtList (stmts : List (StrataPython.stmt ResolvedAnn)) : TransM Unit :=
  stmts.forM translateStmt

partial def execWriter (stmts : List (StrataPython.stmt ResolvedAnn)) : TransM (List StmtExprMd) := do
  let (_, s) ← collect (translateStmtList stmts)
  pure s

partial def translateAssign (sr : SourceRange) (target : StrataPython.expr ResolvedAnn)
    (value : StrataPython.expr ResolvedAnn) : TransM Unit := do
  match value with
  | .Call ann _ args kwargs => match ann.info with
    | .classNew cls initSig => do
        let targetExpr ← translateExpr target
        let assignNew ← mkExpr sr (.Assign [toVarTarget targetExpr] (← mkExpr sr (.New cls.toLaurel)))
        let posArgs ← args.val.toList.mapM translateExpr
        let kwargPairs ← kwargs.val.toList.filterMapM fun kw => match kw with
          | .mk_keyword _ kwName kwExpr => do
            let val ← translateExpr kwExpr
            match kwName.val with | some n => pure (some (n.val, val)) | none => pure none
        let initCall ← mkExpr sr (.StaticCall initSig.laurelName (← initSig.matchArgs ([targetExpr] ++ posArgs) kwargPairs translateExpr (mkKwargs := (do return some (← mkExpr sr (.Hole (deterministic := false)))))))
        tell [assignNew, initCall]
    | _ => tell [← mkExpr sr (.Assign [toVarTarget (← translateExpr target)] (← translateExpr value))]
  | _ => tell [← mkExpr sr (.Assign [toVarTarget (← translateExpr target)] (← translateExpr value))]

partial def translateStmt (s : StrataPython.stmt ResolvedAnn) : TransM Unit := do
  let sr := s.ann.sr
  match s with
  | .Assign _ targets value _ => do
      if targets.val.size != 1 then
        -- Multiple assignment targets: translate each target as a separate assign
        -- (sound: Python chained assignment `a = b = expr` assigns the same value to all targets)
        let rhsExpr ← translateExpr value
        for target in targets.val.toList do
          tell [← mkExpr sr (.Assign [toVarTarget (← translateExpr target)] rhsExpr)]
      else
      let target := targets.val[0]!
      match target with
      | .Tuple _ elts _ => do
          let rhsExpr ← translateExpr value
          let tmp ← freshId "unpack"
          let tmpDecl ← mkLocalDecl sr tmp (mkTypeDefault (.TCore "Any")) (some rhsExpr)
          let tmpRef ← mkExpr sr (.Var (.Local tmp))
          tell [tmpDecl]
          unpackTargets sr elts.val.toList tmpRef
      | .Subscript .. => do
          subscriptWriteBack sr target (← translateExpr value)
      | _ => translateAssign sr target value

  | .AnnAssign _ target _ value _ => do
      match value.val with
      | some val => translateAssign sr target val
      | none => pure ()

  | .AugAssign ann target _ value => match ann.info with
    | .funcCall sig => do
        let t ← translateExpr target; let v ← translateExpr value
        let newVal ← mkExpr sr (.StaticCall sig.laurelName (← sig.matchArgs [t, v] [] translateExpr))
        match target with
        | .Subscript .. => subscriptWriteBack sr target newVal
        | _ => tell [← mkExpr sr (.Assign [toVarTarget t] newVal)]
    | _ => tell [← mkExpr sr .Hole]

  | .If _ test body orelse => do
      let cond ← translateExpr test
      let thn ← mkExpr sr (.Block (← execWriter body.val.toList) none)
      let els ← if orelse.val.isEmpty then pure none
        else pure (some (← mkExpr sr (.Block (← execWriter orelse.val.toList) none)))
      tell [← mkExpr sr (.IfThenElse cond thn els)]

  | .While _ test body _ => do
      let (bk, ct) ← pushLoopLabel "loop"
      let cond ← translateExpr test
      let inner ← mkExpr sr (.Block (← execWriter body.val.toList) (some ct.text))
      let outer ← mkExpr sr (.Block [← mkExpr sr (.While cond [] none inner)] (some bk.text))
      popLoopLabel; tell [outer]

  | .For _ target iter body _ _ => do
      let (bk, ct) ← pushLoopLabel "for"
      let iterExpr ← translateExpr iter
      let bodyStmts ← execWriter body.val.toList
      let (havocStmts, assumeTarget) ← match target with
        | .Tuple _ elts _ => do
          let tmp ← freshId "for_iter"
          let tmpRef ← mkExpr sr (.Var (.Local tmp))
          let decl ← mkLocalDecl sr tmp (mkTypeDefault (.TCore "Any")) none
          let havoc ← mkExpr sr (.Assign [toVarTarget tmpRef] (← mkExpr sr (.Hole (deterministic := false))))
          let (_, unpacks) ← collect (unpackTargets sr elts.val.toList tmpRef)
          pure ([decl, havoc] ++ unpacks, tmpRef)
        | _ => do
          let tgt ← translateExpr target
          let havoc ← mkExpr sr (.Assign [toVarTarget tgt] (← mkExpr sr (.Hole (deterministic := false))))
          pure ([havoc], tgt)
      let assume ← mkExpr sr (.Assume (← mkExpr sr (.StaticCall rtPIn [assumeTarget, iterExpr])))
      let inner ← mkExpr sr (.Block (havocStmts ++ [assume] ++ bodyStmts) (some ct.text))
      let outer ← mkExpr sr (.Block [inner] (some bk.text))
      popLoopLabel; tell [outer]

  | .Return _ value => do
      match value.val with
      | some expr => do
        let e ← translateExpr expr
        tell [← mkExpr sr (.Assign [{ val := .Local rtLaurelResult, source := sourceRangeToMd (← get).filePath sr }] e), ← mkExpr sr (.Exit "$body")]
      | none => tell [← mkExpr sr (.Exit "$body")]

  | .Assert _ test _ => tell [← mkExpr sr (.Assert ({ condition := ← translateExpr test } : Condition))]
  | .Expr _ (.Constant _ (.ConString _ _) _) => pure ()
  | .Expr _ value => tell [← translateExpr value]
  | .Pass _ => pure ()
  | .Break _ => tell [← mkExpr sr (.Exit ((← currentBreakLabel).map (·.text) |>.getD "break"))]
  | .Continue _ => tell [← mkExpr sr (.Exit ((← currentContinueLabel).map (·.text) |>.getD "continue"))]

  | .Try _ body handlers _ _ => translateTryExcept sr body handlers
  | .TryStar _ body handlers _ _ => translateTryExcept sr body handlers

  | .With _ items body _ => do
      let (pre, post) ← items.val.toList.foldlM (fun acc item => do
        let (pre, post) := acc
        match item with
        | .mk_withitem ann ctxExpr optVars => do
          let mgr ← translateExpr ctxExpr
          match ann.info with
          | .withCtx enterSig exitSig =>
            let enterCall ← mkExpr sr (.StaticCall enterSig.laurelName [mgr])
            let exitCall ← mkExpr sr (.StaticCall exitSig.laurelName [mgr])
            match optVars.val with
            | some varExpr =>
              pure (pre ++ [← mkExpr sr (.Assign [toVarTarget (← translateExpr varExpr)] enterCall)], post ++ [exitCall])
            | none => pure (pre ++ [enterCall], post ++ [exitCall])
          | _ =>
            let enter ← mkExpr sr (.Hole (deterministic := false))
            let exit ← mkExpr sr (.Hole (deterministic := false))
            match optVars.val with
            | some varExpr =>
              pure (pre ++ [← mkExpr sr (.Assign [toVarTarget (← translateExpr varExpr)] enter)], post ++ [exit])
            | none => pure (pre ++ [enter], post ++ [exit])
      ) (([] : List StmtExprMd), ([] : List StmtExprMd))
      let bodyStmts ← execWriter body.val.toList
      tell (pre ++ bodyStmts ++ post)

  | .Raise _ exc _ => do
      match exc.val with
      | some excExpr => do
        let errorExpr ← translateExpr excExpr
        tell [← mkExpr sr (.Assign [{ val := .Local rtMaybeExcept, source := sourceRangeToMd (← get).filePath sr }] errorExpr)]
      | none => tell [← mkExpr sr (.Assign [{ val := .Local rtMaybeExcept, source := sourceRangeToMd (← get).filePath sr }] (← mkExpr sr .Hole))]

  | .Import _ _ => pure ()
  | .ImportFrom _ _ _ _ => pure ()
  | .Global _ _ => pure ()
  | .Nonlocal _ _ => pure ()
  | .Delete _ _ => pure ()
  | .AsyncFor _ _ _ _ _ _ => tell [← mkExpr sr .Hole]
  | .AsyncWith _ _ _ _ => tell [← mkExpr sr .Hole]
  | .Match _ _ _ => tell [← mkExpr sr .Hole]
  | .TypeAlias _ _ _ _ => pure ()
  | .FunctionDef _ _ _ _ _ _ _ _ => pure ()
  | .AsyncFunctionDef _ _ _ _ _ _ _ _ => pure ()
  | .ClassDef _ _ _ _ _ _ _ => pure ()

where
  ann (s : StrataPython.stmt ResolvedAnn) : ResolvedAnn := match s with
    | .FunctionDef a .. => a | .AsyncFunctionDef a .. => a | .ClassDef a .. => a
    | .Return a .. => a | .Delete a .. => a | .Assign a .. => a | .AugAssign a .. => a
    | .AnnAssign a .. => a | .For a .. => a | .AsyncFor a .. => a | .While a .. => a
    | .If a .. => a | .With a .. => a | .AsyncWith a .. => a | .Raise a .. => a
    | .Try a .. => a | .TryStar a .. => a | .Assert a .. => a | .Import a .. => a
    | .ImportFrom a .. => a | .Global a .. => a | .Nonlocal a .. => a | .Expr a .. => a
    | .Pass a => { sr := a.sr, info := .irrelevant } | .Break a => { sr := a.sr, info := .irrelevant }
    | .Continue a => { sr := a.sr, info := .irrelevant } | .Match a .. => a | .TypeAlias a .. => a

partial def unpackTargets (sr : SourceRange) (elts : List (StrataPython.expr ResolvedAnn))
    (sourceRef : StmtExprMd) : TransM Unit := do
  for (elt, idx) in elts.zipIdx do
    let getExpr ← mkExpr sr (.StaticCall rtAnyGet [sourceRef, ← mkExpr sr (.LiteralInt ↑idx)])
    match elt with
    | .Tuple _ innerElts _ => do
      let innerTmp ← freshId "unpack"
      let innerRef ← mkExpr sr (.Var (.Local innerTmp))
      let innerDecl ← mkLocalDecl sr innerTmp (mkTypeDefault (.TCore "Any")) (some getExpr)
      tell [innerDecl]
      unpackTargets sr innerElts.val.toList innerRef
    | _ => do
      let tgt ← translateExpr elt
      tell [← mkExpr sr (.Assign [toVarTarget tgt] getExpr)]

partial def collectSubscriptChain (expr : StrataPython.expr ResolvedAnn) : TransM (StrataPython.expr ResolvedAnn × List (StrataPython.expr ResolvedAnn)) := do
  match expr with
  | .Subscript _ container slice _ =>
    let (root, innerIndices) ← collectSubscriptChain container
    pure (root, innerIndices ++ [slice])
  | other => pure (other, [])

/-- Write `rhs` back into the subscript target `a[i]...[j]` via `Any_sets`, then
    assign the updated container to its root. Used by both plain and augmented
    subscript assignment — a subscript is not an lvalue identifier. -/
partial def subscriptWriteBack (sr : SourceRange) (target : StrataPython.expr ResolvedAnn)
    (rhs : StmtExprMd) : TransM Unit := do
  let (root, indices) ← collectSubscriptChain target
  let rootExpr ← translateExpr root
  let idxList ← indices.foldrM (fun idx acc => do
    let idxExpr ← match idx with
      | .Slice _ start stop _ => do
        let s' ← match start.val with
          | some e => mkExpr sr (.StaticCall rtAnyAsInt [← translateExpr e])
          | none => mkExpr sr (.LiteralInt 0)
        let e' ← match stop.val with
          | some e => mkExpr sr (.StaticCall rtOptSome [← mkExpr sr (.StaticCall rtAnyAsInt [← translateExpr e])])
          | none => mkExpr sr (.StaticCall rtOptNone [])
        mkExpr sr (.StaticCall rtFromSlice [s', e'])
      | _ => translateExpr idx
    mkExpr sr (.StaticCall rtListAnyCons [idxExpr, acc])
  ) (← mkExpr sr (.StaticCall rtListAnyNil []))
  let setsCall ← mkExpr sr (.StaticCall rtAnySets [idxList, rootExpr, rhs])
  tell [← mkExpr sr (.Assign [toVarTarget rootExpr] setsCall)]

/-- Wrap each body statement with an isError check that exits to the catcher block. -/
private partial def wrapBodyWithErrorChecks (sr : SourceRange) (catchersLabel : String)
    (bodyStmts : List StmtExprMd) : TransM (List StmtExprMd) :=
  bodyStmts.foldlM (fun acc stmt => do
    let ref ← mkExpr sr (.Var (.Local rtMaybeExcept))
    let check ← mkExpr sr (.StaticCall rtIsError [ref])
    let ifCheck ← mkExpr sr (.IfThenElse check (← mkExpr sr (.Exit catchersLabel)) none)
    pure (acc ++ [stmt, ifCheck])) []

/-- Translate exception handlers to their statement lists. -/
private partial def translateHandlers (handlers : List (StrataPython.excepthandler ResolvedAnn))
    : TransM (List StmtExprMd) := do
  let lists ← handlers.mapM fun handler => match handler with
    | .ExceptHandler _ _ _ handlerBody => execWriter handlerBody.val.toList
  pure lists.flatten

partial def translateTryExcept (sr : SourceRange)
    (body : Ann (Array (StrataPython.stmt ResolvedAnn)) ResolvedAnn)
    (handlers : Ann (Array (StrataPython.excepthandler ResolvedAnn)) ResolvedAnn) : TransM Unit := do
  let tryLabel     := s!"try_end_{sr.start.byteIdx}"
  let catchersLabel := s!"exception_handlers_{sr.start.byteIdx}"
  let bodyStmts   ← execWriter body.val.toList
  let withChecks  ← wrapBodyWithErrorChecks sr catchersLabel bodyStmts
  let exitTry     ← mkExpr sr (.Exit tryLabel)
  let catchers    ← mkExpr sr (.Block (withChecks ++ [exitTry]) (some catchersLabel))
  let handlerStmts ← translateHandlers handlers.val.toList
  tell [← mkExpr sr (.Block ([catchers] ++ handlerStmts) (some tryLabel))]

-- ═══════════════════════════════════════════════════════════════════════════════
-- Function / Class / Module — reads NodeInfo directly
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Rewrite identifiers in a precondition expression: each declared parameter name
    `x` becomes the input name `$in_x`. Laurel `requires` clauses are evaluated in
    the procedure's INPUT scope (where params are named `$in_x`), not the body scope
    (where they are copied to locals `x`). -/
partial def renameParamsToInputs (paramNames : List String) (e : StmtExprMd) : StmtExprMd :=
  let rw := renameParamsToInputs paramNames
  let rwOpt := fun (o : Option StmtExprMd) => o.map rw
  let rwList := fun (l : List StmtExprMd) => l.map rw
  let rwVar := fun (v : VariableMd) => match v.val with
    | .Local name =>
      if paramNames.contains name.text then { v with val := .Local { name with text := s!"$in_{name.text}" } } else v
    | .Field t fn => { v with val := .Field (rw t) fn }
    | .Declare _ => v
  let rwVarList := fun (l : List VariableMd) => l.map rwVar
  let val := match e.val with
    | .Var v => .Var (rwVar { val := v, source := e.source }).val
    | .IfThenElse c t el => .IfThenElse (rw c) (rw t) (rwOpt el)
    | .Block ss l => .Block (rwList ss) l
    | .Assign ts v => .Assign (rwVarList ts) (rw v)
    | .PureFieldUpdate t fn nv => .PureFieldUpdate (rw t) fn (rw nv)
    | .StaticCall c args => .StaticCall c (rwList args)
    | .PrimitiveOp op args => .PrimitiveOp op (rwList args)
    | .ReferenceEquals l r => .ReferenceEquals (rw l) (rw r)
    | .AsType t ty => .AsType (rw t) ty
    | .IsType t ty => .IsType (rw t) ty
    | .InstanceCall t c args => .InstanceCall (rw t) c (rwList args)
    | .Old v => .Old (rw v)
    | .Fresh v => .Fresh (rw v)
    | .Assert c => .Assert (c.mapCondition rw)
    | .Assume c => .Assume (rw c)
    | .Return v => .Return (rwOpt v)
    | other => other
  { e with val }

private partial def buildProcInputs (sig : FuncSig) : List Parameter :=
  sig.laurelDeclInputs.map fun (lId, pTy) =>
    { name := { text := s!"$in_{lId.text}", uniqueId := none }, type := mkTypeDefault (pythonTypeToHighType pTy) }

private partial def buildProcOutputs (sig : FuncSig) : List Parameter :=
  -- LaurelResult is typed by the USER-DECLARED return type (v2 verbatim). The frontend
  -- trusts the annotation; the coercion mechanism reconciles the body's Any-valued
  -- expressions with the declared type at the `return e` assignment. (Do NOT type it
  -- `Any` and recover via postconditions — that compensates for a deviation v2 never made.)
  -- EXCEPTION (kbd-forced): a `-> None` return maps to `.TVoid`, which kbd's Laurel→Core
  -- renders as a `bool` PLACEHOLDER (LaurelToCoreSchemaPass). But `return None` assigns
  -- `from_None : Any` to LaurelResult, so the body needs an `Any` slot — `bool := Any`
  -- fails kbd's Core type-checker ("unify bool with Any"). Python `None` IS a value
  -- (`from_None`) in the Any model, so type the result `Any`. (v2's Core accepted void
  -- here; kbd's stricter placeholder does not — same class of kbd adaptation as others.)
  let retHigh := pythonTypeToHighType sig.returnType
  let resultTy := match retHigh with | .TVoid => HighType.TCore "Any" | t => t
  [{ name := rtLaurelResult, type := mkTypeDefault resultTy },
   { name := rtMaybeExcept, type := mkTypeDefault (.TCore "Error") }]

private partial def buildParamCopies (sig : FuncSig) : List StmtExprMd :=
  sig.laurelDeclInputs.map fun (lId, pTy) =>
    mkLocalDeclDefault lId (mkTypeDefault (pythonTypeToHighType pTy))
      (some (mkExprDefault (.Var (.Local { text := s!"$in_{lId.text}", uniqueId := none }))))

private partial def buildLocalDecls (sig : FuncSig) : List StmtExprMd :=
  sig.laurelLocals.map fun (lId, lTy) =>
    mkLocalDeclDefault lId (mkTypeDefault (pythonTypeToHighType lTy)) none

private partial def splitPreconditions (body : List (StrataPython.stmt ResolvedAnn))
    : List (StrataPython.stmt ResolvedAnn) × List (StrataPython.stmt ResolvedAnn) :=
  body.span fun s => match s with | .Assert _ _ _ => true | _ => false

partial def translateFunction (sig : FuncSig) (body : Array (StrataPython.stmt ResolvedAnn))
    (sr : SourceRange) : TransM Procedure := do
  let inputs := buildProcInputs sig
  let outputs := buildProcOutputs sig
  let paramCopies := buildParamCopies sig
  let localDecls := buildLocalDecls sig
  let (preAsserts, restBody) := splitPreconditions body.toList
  let paramNames := sig.laurelDeclInputs.map (·.1.text)
  let preconditions ← preAsserts.mapM fun s => match s with
    | .Assert _ test _ => do pure ({ condition := renameParamsToInputs paramNames (← translateExpr test) } : Condition)
    | _ => throw (.internalError "non-Assert statement in precondition prefix")
  let bodyStmts ← execWriter restBody
  let bodyBlock ← mkExpr sr (.Block (paramCopies ++ localDecls ++ bodyStmts) none)
  -- kbd has no Procedure.md field: the source range lives on the proc name's
  -- `.source`. splitProcNames reads it (via getFileRange) to tell user procs from
  -- prelude; without it every user proc looks like prelude and nothing is verified.
  let procName := { sig.laurelName with source := sourceRangeToMd (← get).filePath sr }
  pure {
    name := procName
    inputs, outputs, preconditions
    decreases := none
    isFunctional := false
    -- v2 used `.Transparent bodyBlock` with no postconditions. The only kbd-forced
    -- change is the modifies clause: field-mutating procs need `modifies *`
    -- (wildcardModifies) so modifiesClausesTransformPass emits no frame condition;
    -- empty modifies would impose a "heap unchanged" obligation contradicting the writes.
    -- Postconditions stay EMPTY — the declared return type lives on the output param.
    body := .Opaque [] (some bodyBlock) [← mkExpr sr .All]
  }

partial def translateClass (name : PythonIdentifier) (attributes : List (PythonIdentifier × PythonType))
    (_methods : List FuncSig) (body : Array (StrataPython.stmt ResolvedAnn))
    : TransM (TypeDefinition × List Procedure) := do
  -- Composite fields keep their USER-DECLARED type. The Python frontend trusts user
  -- annotations; the coercion mechanism handles impedance (e.g. boxing to `Any` where a
  -- value context demands it). The box protocol stores/loads each field at its declared
  -- type (`Box..<T>`), so a field read synthesizes that type — `e ⇒ &{…l:A_l…} ⊢ e.l ⇒ A_l`.
  let laurelFields := attributes.map fun (fId, fTy) =>
    ({ name := fId.toLaurel, isMutable := true, type := mkTypeDefault (pythonTypeToHighType fTy) } : Field)
  let procResults ← body.toList.mapM fun stmt => match stmt with
    | .FunctionDef ann _ _ fbody _ _ _ _ => match ann.info with
      | .funcDecl sig => do pure (some (← translateFunction sig fbody.val ann.sr))
      | _ => pure none
    | .AsyncFunctionDef ann _ _ fbody _ _ _ _ => match ann.info with
      | .funcDecl sig => do pure (some (← translateFunction sig fbody.val ann.sr))
      | _ => pure none
    | _ => pure none
  let procs := procResults.filterMap id
  -- Synthesize a default `Class@__init__` if the class defines none. Every `C(...)`
  -- instantiation (classNew) emits a call to `C@__init__`; without a definition that
  -- call fails to elaborate (lookupFuncSig miss) and takes the whole caller down. The
  -- default ctor takes only `self : Class`, has empty body + the standard Any/Error
  -- outputs. (Proven PythonToLaurel synthesizes the same default.)
  let initName := s!"{name.toLaurel.text}@__init__"
  let hasInit := procs.any (fun p => p.name.text == initName)
  let procs := if hasInit then procs else
    -- The default init takes NO inputs: Resolution's synthesized `initSig` for a class
    -- with no `__init__` has no receiver slot, so `classNew` emits `Class@__init__()`
    -- with zero args. The proc decl must match that arity (a `self` input would make the
    -- Core call-arity check fail: "input length and args length mismatch").
    let defaultInit : Procedure := {
      name := { text := initName, uniqueId := none }
      inputs := []
      outputs := [{ name := rtLaurelResult, type := mkTypeDefault (.TCore "Any") },
                  { name := rtMaybeExcept, type := mkTypeDefault (.TCore "Error") }]
      preconditions := []
      decreases := none
      isFunctional := false
      body := .Opaque [] (some (mkExprDefault (.Block [] none))) [mkExprDefault .All] }
    procs ++ [defaultInit]
  let ct : CompositeType := { name := name.toLaurel, extending := [], fields := laurelFields, instanceProcedures := [] }
  pure (.Composite ct, procs)

partial def translateModule (program : ResolvedPythonProgram) : TransM Strata.Laurel.Program := do
  let init : List Procedure × List TypeDefinition × List (StrataPython.stmt ResolvedAnn) := ([], [], [])
  let (procedures, types, otherStmts) ← program.stmts.toList.foldlM (fun (procs, tys, others) stmt => do
    match stmt with
    | .FunctionDef ann _ _ body _ _ _ _ => match ann.info with
      | .funcDecl sig =>
        let proc ← translateFunction sig body.val ann.sr
        pure (procs ++ [proc], tys, others)
      | _ => pure (procs, tys, others)
    | .AsyncFunctionDef ann _ _ body _ _ _ _ => match ann.info with
      | .funcDecl sig =>
        let proc ← translateFunction sig body.val ann.sr
        pure (procs ++ [proc], tys, others)
      | _ => pure (procs, tys, others)
    | .ClassDef ann _ _ _ body _ _ => match ann.info with
      | .classDecl name fields methods =>
        let (td, ms) ← translateClass name fields methods body.val
        pure (procs ++ ms, tys ++ [td], others)
      | _ => pure (procs, tys, others)
    | other => pure (procs, tys, others ++ [other])
  ) init
  let procedures ← if otherStmts.isEmpty then pure procedures
    else do
      let sr : SourceRange := default
      let nameId := rt "__name__"
      let nameDecl ← mkLocalDecl sr nameId (mkTypeDefault .TString) (some (mkExprDefault (.LiteralString "__main__")))
      let localDecls := program.moduleLocals.map fun (lId, lTy) =>
        mkLocalDeclDefault lId.toLaurel (mkTypeDefault (pythonTypeToHighType lTy)) none
      let bodyStmts ← execWriter otherStmts
      let bodyBlock ← mkExpr sr (.Block ([nameDecl] ++ localDecls ++ bodyStmts) none)
      let mainOutputs : List Parameter :=
        [{ name := rtLaurelResult, type := mkTypeDefault (.TCore "Any") },
         { name := rtMaybeExcept, type := mkTypeDefault (.TCore "Error") }]
      let mainName := { (rt "__main__") with source := sourceRangeToMd (← get).filePath sr }
      let mainProc : Procedure := { name := mainName, inputs := [], outputs := mainOutputs, preconditions := [], decreases := none, isFunctional := false, body := .Opaque [] (some bodyBlock) [← mkExpr sr .All] }
      pure (procedures ++ [mainProc])
  return { staticProcedures := procedures, staticFields := [], types, constants := [] }

end -- mutual

-- ═══════════════════════════════════════════════════════════════════════════════
-- Runner
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Entry point: translates a resolved Python program to a Laurel program.
    Returns the Laurel program and final translator state, or a `TransError`. -/
def runTranslation (program : ResolvedPythonProgram)
    (filePath : String := "")
    : Except TransError (Strata.Laurel.Program × TransState) :=
  (translateModule program).run.run { filePath := filePath } |>.map fun ((prog, _stmts), state) => (prog, state)

end -- public section
end StrataPython.Translation
