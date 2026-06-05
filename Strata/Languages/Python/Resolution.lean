/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Python.PythonDialect
import Strata.DDM.Util.SourceRange
import Strata.Languages.Python.ReadPython

/-!
# Pass 1: Name Resolution

Resolution is a fold over the Python AST that threads a growing context
as accumulator. Its job is to **disambiguate** what each AST node means
and attach the result as a `NodeInfo` annotation. The process of
disambiguation produces Laurel-ready identifiers and auxiliary data
(FuncSig, field lists) that Translation uses mechanically.

**Input:**  `Array (Python.stmt SourceRange)` (raw, unscoped)
**Output:** `ResolvedPythonProgram` (scoped, every node annotated with NodeInfo)

The output AST is the scoping derivation for the Python program —
every node carries proof of what it refers to.

## Phase Distinction

All Resolution types are purely Python-level. No `Laurel.Identifier` is
stored anywhere. Translation obtains Laurel identifiers by calling accessor
functions on the Python-level structures. This makes the phase boundary
explicit and prevents mixing.

## What Resolution Does

At the top level (module scope), each declaration extends the context:
- `def f(...)` → extends context, annotates FunctionDef with `.funcDecl sig`
- `class C` → extends context with class + methods, annotates with `.classDecl`
- `import M` → extends context internally (module tracked in Ctx only)
- `x : T = ...` → extends context with variable

At each reference, Resolution annotates with the appropriate `NodeInfo`:
- Name use (variable/function/class) → `.variable name`
- Call (function) → `.funcCall sig`
- Call (class) → `.classNew className initSig`
- Call (method) → `.funcCall sig` (sig has `className = some _`)
- Attribute access → `.attribute name` (bare field name; Elaboration resolves based on receiver type)
- BinOp/Compare/UnaryOp → `.funcCall sig` (operator runtime procedure)
- Unresolvable → `.unresolved`
- Non-reference → `.irrelevant`

## What Resolution Does NOT

- Determine effects (Elaboration does that)
- Map PythonType → HighType (Translation does that)
- Emit Laurel constructs (Translation does that)
- Resolve field access to class (Elaboration does that via synthesized receiver type)
-/

namespace Strata.Python.Resolution

open Strata.Laurel

public section

/-! ## Core Types

`PythonIdentifier` is a newtype with a private constructor. The only ways to
create one are from the AST (`.fromAst`), from an import path (`.fromImport`),
or for builtins (`.builtin`). This prevents fabrication of identifiers like
`"ClassName@method"` — all identifiers trace back to source or builtins. -/

abbrev PythonExpr := Python.expr SourceRange
abbrev PythonStmt := Python.stmt SourceRange
abbrev PythonProgram := Array PythonStmt
abbrev PythonType := PythonExpr
/-- A Python identifier with a private constructor. Can only be created via `.fromAst`,
    `.fromImport`, or `.builtin` — preventing fabrication of identifiers from arbitrary strings. -/
structure PythonIdentifier where
  private mk ::
  private val : String
  deriving BEq, Hashable, Inhabited, Repr

def PythonIdentifier.fromAst (n : Ann String SourceRange) : PythonIdentifier :=
  ⟨n.val⟩

def PythonIdentifier.fromImport (modName : Ann String SourceRange) : PythonIdentifier :=
  match modName.val.splitOn "." with
  | first :: _ => ⟨first⟩
  | [] => ⟨modName.val⟩

def PythonIdentifier.builtin (name : String) : PythonIdentifier :=
  ⟨name⟩

/-! ## Intermediate Types (mutually recursive)

These types are mutually recursive because `ParamList` stores resolved default
expressions (`Python.expr ResolvedAnn`) which depend on `ResolvedAnn` which
depends on `NodeInfo` which depends on `FuncSig` which depends on `ParamList`.

**FuncParams** distinguishes instance methods (with explicit receiver) from
static functions. The receiver is NOT in `ParamList` — it's separated so that
`matchArgs` can handle it correctly (receiver gets its own slot in the zip-fold).

**FuncSig** carries the Python-level function signature. `params` and `locals`
are private — Translation accesses them only via `matchArgs`, `laurelDeclInputs`,
and `laurelLocals` accessors.

**NodeInfo** is the output annotation on each AST node. Pattern matching on it
determines Translation's action. Complements:
- `funcDecl` / `funcCall` — declaration and use site of a function
- `classDecl` / `classNew` — declaration and instantiation site of a class
- `withCtx` — resolved `__enter__`/`__exit__` sigs on a with-item
- Operators are `funcCall` with correct arity (2 for binary, 1 for unary) -/

mutual

/-- The parameter list of a function/method, split into required, optional (with defaults),
    and keyword-only parameters. Defaults are resolved expressions (carry `ResolvedAnn`). -/
structure ParamList where
  /-- Parameters with no default value — must be provided at every call site. -/
  required : List (PythonIdentifier × PythonType)
  /-- Parameters with default values — may be omitted at call sites. -/
  optional : List (PythonIdentifier × PythonType × Python.expr ResolvedAnn)
  /-- Keyword-only parameters (after `*` in Python). Default is optional. -/
  kwonly : List (PythonIdentifier × PythonType × Option (Python.expr ResolvedAnn))

/-- Distinguishes instance methods (with explicit receiver) from static functions.
    The receiver is NOT in `ParamList` — it gets its own slot in `matchArgs`. -/
inductive FuncParams where
  /-- Instance method: first Python param is the receiver (typically `self`). -/
  | instance (receiver : PythonIdentifier) (params : ParamList)
  /-- Static function or top-level function: no receiver. -/
  | static (params : ParamList)

/-- The complete signature of a Python function or method. Carries everything Translation
    needs to emit a Laurel procedure declaration and match call-site arguments. -/
structure FuncSig where
  /-- The Python name of the function/method. -/
  name : PythonIdentifier
  /-- If this is a method, the class it belongs to. `none` for top-level functions. -/
  className : Option PythonIdentifier
  /-- Instance vs static params (receiver separated from ParamList). -/
  params : FuncParams
  /-- The declared return type annotation (defaults to Any if absent). -/
  returnType : PythonType
  /-- All local variables in the function body (computed by `computeLocals`). -/
  locals : List (PythonIdentifier × PythonType)
  /-- Overload index for disambiguated naming. `none` for non-overloaded functions. -/
  overloadIndex : Option Nat := none
  /-- The `**kwargs` parameter name, if present. A declared input (Any-typed) but not
      matched positionally by `matchArgs`. -/
  kwargName : Option PythonIdentifier := none

/-- The resolution annotation on each Python AST node.
    Each variant carries exactly what Translation needs to emit Laurel. -/
inductive NodeInfo where
  /-- A variable reference (local, param, or global). -/
  | variable (name : PythonIdentifier)
  /-- A function/method call site with the callee's full signature. -/
  | funcCall (sig : FuncSig)
  /-- A function/method declaration site with its signature. -/
  | funcDecl (sig : FuncSig)
  /-- A class instantiation (`ClassName(...)`) with class name and `__init__` sig. -/
  | classNew (className : PythonIdentifier) (initSig : FuncSig)
  /-- A class declaration with its fields and method signatures. -/
  | classDecl (name : PythonIdentifier) (attributes : List (PythonIdentifier × PythonType)) (methods : List FuncSig)
  /-- An attribute access (bare field name; Elaboration resolves via receiver type). -/
  | attribute (name : PythonIdentifier)
  /-- A `with` item with resolved `__enter__` and `__exit__` signatures. -/
  | withCtx (enterSig : FuncSig) (exitSig : FuncSig)
  /-- A reference that could not be resolved (unknown name/module). -/
  | unresolved
  /-- A non-reference node (literals, operators as nodes, etc.). -/
  | irrelevant

/-- The annotation type on resolved AST nodes: source range plus resolution info. -/
structure ResolvedAnn where
  /-- Original source location. -/
  sr : SourceRange
  /-- What Resolution determined about this node. -/
  info : NodeInfo

end

abbrev ResolvedPythonStmt := Python.stmt ResolvedAnn
abbrev ResolvedPythonExpr := Python.expr ResolvedAnn

instance : Inhabited ParamList where default := { required := [], optional := [], kwonly := [] }
instance : Inhabited FuncParams where default := .static default
instance : Inhabited FuncSig where default := { name := default, className := none, params := default, returnType := .Name SourceRange.none ⟨SourceRange.none, "Any"⟩ (.Load SourceRange.none), locals := [] }
instance : Inhabited NodeInfo where default := .irrelevant
instance : Inhabited ResolvedAnn where default := { sr := .none, info := .irrelevant }

/-- The output of Resolution: fully-annotated AST plus module-level local list. -/
structure ResolvedPythonProgram where
  /-- The resolved top-level statements. -/
  stmts : Array ResolvedPythonStmt
  /-- Module-level local variables (assignment targets at module scope). -/
  moduleLocals : List (PythonIdentifier × PythonType)

/-! ## Internal Context

Resolution's working state — NOT exposed to Translation. `Ctx` maps
`PythonIdentifier` keys to `CtxEntry` values. Keys are bare Python names
from the AST (no fabricated compound keys like "ClassName@method").

Method lookup goes through `CtxEntry.class_`'s method list, not through
top-level keys. This prevents name collision between methods of different
classes with the same name.

Within a class body, the context is extended with:
- `self` typed as the enclosing class (enables method resolution on `self`)
- All methods registered under their bare Python names (enables `self.method()` lookup)

Within a function body, the context is extended with:
- Parameters (a param with no annotation does NOT override a more specific
  type already in context, e.g. `self` typed by the enclosing class)
- Locals (Python's scoping rule: any assignment target in the body is function-local)
- FunctionDef/ClassDef names are NOT included in locals (they're declarations) -/

/-- An entry in Resolution's context. Determines what a `PythonIdentifier` key refers to. -/
inductive CtxEntry where
  /-- A function or method with its full signature. -/
  | function (sig : FuncSig)
  /-- A class with its field list and method signatures.
      `methods` holds eagerly-resolved sigs (user classes); `methodAsts` holds raw
      method statements for lazy on-demand resolution (imported classes). -/
  | class_ (name : PythonIdentifier) (fields : List (PythonIdentifier × PythonType))
      (methods : List (PythonIdentifier × FuncSig))
      (methodAsts : List (PythonIdentifier × PythonStmt) := [])
  /-- A variable with its type annotation. -/
  | variable (ty : PythonType)
  /-- An overloaded function: signatures under the same name, matched in order.
      Each carries its index, sig, and raw AST (for on-demand body resolution). -/
  | overloadedFunction (overloads : List (Nat × FuncSig × Option PythonStmt))
  /-- An imported module with its resolved context. -/
  | module_ (moduleCtx : Std.DHashMap.Raw PythonIdentifier (fun _ => CtxEntry))
  /-- An imported name whose type/kind is unknown. -/
  | unresolved
  deriving Inhabited

abbrev Ctx := Std.HashMap PythonIdentifier CtxEntry

/-- An imported module with its source path (for cache filename) and resolved program. -/
structure ImportedModule where
  sourcePath : System.FilePath
  program : ResolvedPythonProgram

/-- State for the resolution monad: collects resolved imported module programs. -/
structure ResolveState where
  importedModules : Array ImportedModule := #[]
  resolvedPaths : Std.HashMap String Ctx := {}
  /-- Imported class methods resolved on demand (qualified name → resolved FunctionDef stmt).
      The pipeline translates only these, not whole imported modules. -/
  demandedMethods : Std.HashMap String ResolvedPythonStmt := {}
  /-- Imported top-level functions / overloads resolved on demand
      (disambiguated name → resolved FunctionDef stmt). -/
  demandedFunctions : Std.HashMap String ResolvedPythonStmt := {}
  /-- Imported classes whose methods/inits were demanded (class name → (id, fields)).
      The pipeline emits a Composite type definition for each. -/
  demandedClasses : Std.HashMap String (PythonIdentifier × List (PythonIdentifier × PythonType)) := {}

/-- The resolution monad. Reader carries baseDir, State collects imported module programs. -/
abbrev ResolveM := ReaderT System.FilePath (StateT ResolveState (EIO String))

-- ═══════════════════════════════════════════════════════════════════════════════
-- Annotation Extraction
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Extract a PythonType from an optional annotation. No annotation defaults to Any. -/
def annotationToPythonType (ann : Option PythonExpr) : PythonType :=
  match ann with
  | some expr => expr
  | none => .Name SourceRange.none ⟨SourceRange.none, "Any"⟩ (.Load SourceRange.none)

-- ═══════════════════════════════════════════════════════════════════════════════
-- Function Locals (Python scoping: assignment anywhere in body → function-local)
-- ═══════════════════════════════════════════════════════════════════════════════

mutual
/-- Collects walrus operator (`:=`) targets from comprehension iterables and filters. -/
partial def collectWalrusFromComprehensions (comps : List (Python.comprehension SourceRange)) : List PythonIdentifier :=
  comps.flatMap fun comp =>
    match comp with
    | .mk_comprehension _ _target iter ifs _isAsync =>
        collectWalrusNames iter ++ ifs.val.toList.flatMap collectWalrusNames

/-- Extracts assigned names from an assignment target (handles tuple/list unpacking, starred). -/
partial def collectNamesFromTarget (target : PythonExpr) : List PythonIdentifier :=
  match target with
  | .Name _ n _ => [PythonIdentifier.fromAst n]
  | .Tuple _ elems _ => elems.val.toList.flatMap collectNamesFromTarget
  | .List _ elems _ => elems.val.toList.flatMap collectNamesFromTarget
  | .Starred _ inner _ => collectNamesFromTarget inner
  | .Subscript _ _ _ _ => []
  | .Attribute _ _ _ _ => []
  | e => collectWalrusNames e

/-- Recursively finds all walrus operator (`:=`) targets within an expression tree. -/
partial def collectWalrusNames (expr : PythonExpr) : List PythonIdentifier :=
  match expr with
  | .NamedExpr _ target _ => collectNamesFromTarget target
  | .BinOp _ left _ right => collectWalrusNames left ++ collectWalrusNames right
  | .BoolOp _ _ operands => operands.val.toList.flatMap collectWalrusNames
  | .UnaryOp _ _ operand => collectWalrusNames operand
  | .Compare _ left _ comparators => collectWalrusNames left ++ comparators.val.toList.flatMap collectWalrusNames
  | .Call _ func args kwargs =>
      collectWalrusNames func ++ args.val.toList.flatMap collectWalrusNames ++
      kwargs.val.toList.flatMap fun kw => match kw with | .mk_keyword _ _ val => collectWalrusNames val
  | .IfExp _ test body orelse => collectWalrusNames test ++ collectWalrusNames body ++ collectWalrusNames orelse
  | .Dict _ keys vals => keys.val.toList.flatMap (fun k => match k with | .some_expr _ e => collectWalrusNames e | .missing_expr _ => []) ++ vals.val.toList.flatMap collectWalrusNames
  | .Set _ elts => elts.val.toList.flatMap collectWalrusNames
  | .ListComp _ elt generators => collectWalrusNames elt ++ collectWalrusFromComprehensions generators.val.toList
  | .SetComp _ elt generators => collectWalrusNames elt ++ collectWalrusFromComprehensions generators.val.toList
  | .DictComp _ key value generators => collectWalrusNames key ++ collectWalrusNames value ++ collectWalrusFromComprehensions generators.val.toList
  | .GeneratorExp _ elt generators => collectWalrusNames elt ++ collectWalrusFromComprehensions generators.val.toList
  | .Await _ inner => collectWalrusNames inner
  | .Yield _ valOpt => match valOpt.val with | some v => collectWalrusNames v | none => []
  | .YieldFrom _ inner => collectWalrusNames inner
  | .FormattedValue _ value _ _ => collectWalrusNames value
  | .JoinedStr _ values => values.val.toList.flatMap collectWalrusNames
  | .Subscript _ obj slice _ => collectWalrusNames obj ++ collectWalrusNames slice
  | .Attribute _ obj _ _ => collectWalrusNames obj
  | .Starred _ inner _ => collectWalrusNames inner
  | .Tuple _ elems _ => elems.val.toList.flatMap collectWalrusNames
  | .List _ elems _ => elems.val.toList.flatMap collectWalrusNames
  | .Slice _ start stop step =>
      (match start.val with | some e => collectWalrusNames e | none => []) ++
      (match stop.val with | some e => collectWalrusNames e | none => []) ++
      (match step.val with | some e => collectWalrusNames e | none => [])
  | .Name _ _ _ => []
  | .Constant _ _ _ => []
  | .Lambda _ _ _ => []
  | .TemplateStr _ _ => []
  | .Interpolation _ _ _ _ _ => []
end

/-- Collects all local variable bindings from a statement (assignment targets, for targets,
    except-as names, with-as names, walrus targets). Recurses into sub-blocks but NOT into
    nested FunctionDef/ClassDef (those introduce their own scope). -/
partial def collectLocalsFromStmt (s : PythonStmt) : List (PythonIdentifier × PythonType) :=
  match s with
  | .Assign _ targets value _ =>
      let targetNames := targets.val.toList.flatMap fun target =>
        (collectNamesFromTarget target).map fun n => (n, annotationToPythonType none)
      let rhsWalrus := (collectWalrusNames value).map fun n => (n, annotationToPythonType none)
      targetNames ++ rhsWalrus
  | .AnnAssign _ target annotation valueOpt _ =>
      let targetNames := (collectNamesFromTarget target).map fun n => (n, annotation)
      let rhsWalrus := match valueOpt.val with
        | some v => (collectWalrusNames v).map fun n => (n, annotationToPythonType none)
        | none => []
      targetNames ++ rhsWalrus
  | .AugAssign _ target _ value =>
      let targetNames := (collectNamesFromTarget target).map fun n => (n, annotationToPythonType none)
      let rhsWalrus := (collectWalrusNames value).map fun n => (n, annotationToPythonType none)
      targetNames ++ rhsWalrus
  | .If _ test bodyStmts elseStmts =>
      (collectWalrusNames test).map (fun n => (n, annotationToPythonType none)) ++
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      elseStmts.val.toList.flatMap collectLocalsFromStmt
  | .For _ target iter bodyStmts orelse _ =>
      let targetNames := (collectNamesFromTarget target).map fun n => (n, annotationToPythonType none)
      let iterWalrus := (collectWalrusNames iter).map fun n => (n, annotationToPythonType none)
      targetNames ++ iterWalrus ++
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      orelse.val.toList.flatMap collectLocalsFromStmt
  | .While _ cond bodyStmts orelse =>
      (collectWalrusNames cond).map (fun n => (n, annotationToPythonType none)) ++
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      orelse.val.toList.flatMap collectLocalsFromStmt
  | .Try _ bodyStmts handlers orelse finalbody =>
      let handlerLocals := handlers.val.toList.flatMap fun h =>
        match h with
        | .ExceptHandler _ _ maybeName handlerBody =>
            let errorVar := match maybeName.val with
              | some n => [(PythonIdentifier.fromAst n, annotationToPythonType none)]
              | none => []
            errorVar ++ handlerBody.val.toList.flatMap collectLocalsFromStmt
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      handlerLocals ++
      orelse.val.toList.flatMap collectLocalsFromStmt ++
      finalbody.val.toList.flatMap collectLocalsFromStmt
  | .TryStar _ bodyStmts handlers orelse finalbody =>
      let handlerLocals := handlers.val.toList.flatMap fun h =>
        match h with
        | .ExceptHandler _ _ maybeName handlerBody =>
            let errorVar := match maybeName.val with
              | some n => [(PythonIdentifier.fromAst n, annotationToPythonType none)]
              | none => []
            errorVar ++ handlerBody.val.toList.flatMap collectLocalsFromStmt
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      handlerLocals ++
      orelse.val.toList.flatMap collectLocalsFromStmt ++
      finalbody.val.toList.flatMap collectLocalsFromStmt
  | .With _ items bodyStmts _ =>
      let itemLocals := items.val.toList.flatMap fun item =>
        match item with
        | .mk_withitem _ ctxExpr optVars =>
            let ctxWalrus := (collectWalrusNames ctxExpr).map fun n => (n, annotationToPythonType none)
            let varNames := match optVars.val with
              | some varExpr => (collectNamesFromTarget varExpr).map fun n => (n, annotationToPythonType none)
              | none => []
            ctxWalrus ++ varNames
      itemLocals ++ bodyStmts.val.toList.flatMap collectLocalsFromStmt
  | .AsyncWith _ items bodyStmts _ =>
      let itemLocals := items.val.toList.flatMap fun item =>
        match item with
        | .mk_withitem _ ctxExpr optVars =>
            let ctxWalrus := (collectWalrusNames ctxExpr).map fun n => (n, annotationToPythonType none)
            let varNames := match optVars.val with
              | some varExpr => (collectNamesFromTarget varExpr).map fun n => (n, annotationToPythonType none)
              | none => []
            ctxWalrus ++ varNames
      itemLocals ++ bodyStmts.val.toList.flatMap collectLocalsFromStmt
  | .AsyncFor _ target iter bodyStmts orelse _ =>
      let targetNames := (collectNamesFromTarget target).map fun n => (n, annotationToPythonType none)
      let iterWalrus := (collectWalrusNames iter).map fun n => (n, annotationToPythonType none)
      targetNames ++ iterWalrus ++
      bodyStmts.val.toList.flatMap collectLocalsFromStmt ++
      orelse.val.toList.flatMap collectLocalsFromStmt
  | .Match _ subject cases =>
      let subjectW := (collectWalrusNames subject).map fun n => (n, annotationToPythonType none)
      let caseLocals := cases.val.toList.flatMap fun c =>
        match c with
        | .mk_match_case _ _pattern guardOpt caseBody =>
            -- TODO: extract pattern bindings from _pattern (requires walking Python.pattern)
            let guardW := match guardOpt.val with
              | some g => (collectWalrusNames g).map fun n => (n, annotationToPythonType none)
              | none => []
            guardW ++ caseBody.val.toList.flatMap collectLocalsFromStmt
      subjectW ++ caseLocals
  | .FunctionDef _ _ _ _ _ _ _ _ => []
  | .AsyncFunctionDef _ _ _ _ _ _ _ _ => []
  | .ClassDef _ _ _ _ _ _ _ => []
  | .Return _ valOpt =>
      match valOpt.val with
      | some v => (collectWalrusNames v).map (fun n => (n, annotationToPythonType none))
      | none => []
  | .Delete _ targets =>
      targets.val.toList.flatMap fun t => (collectWalrusNames t).map fun n => (n, annotationToPythonType none)
  | .Raise _ excOpt causeOpt =>
      let excW := match excOpt.val with | some e => collectWalrusNames e | none => []
      let causeW := match causeOpt.val with | some e => collectWalrusNames e | none => []
      (excW ++ causeW).map fun n => (n, annotationToPythonType none)
  | .Assert _ test msgOpt =>
      let testW := collectWalrusNames test
      let msgW := match msgOpt.val with | some e => collectWalrusNames e | none => []
      (testW ++ msgW).map fun n => (n, annotationToPythonType none)
  | .Pass _ => []
  | .Break _ => []
  | .Continue _ => []
  | .Import _ aliases =>
      aliases.val.toList.filterMap fun alias =>
        match alias with
        | .mk_alias _ modName asName =>
            let id := match asName.val with
              | some aliasName => PythonIdentifier.fromAst aliasName
              | none => PythonIdentifier.fromImport modName
            some (id, annotationToPythonType none)
  | .ImportFrom _ _ imports _ =>
      imports.val.toList.filterMap fun imp =>
        match imp with
        | .mk_alias _ impName asName =>
            let id := match asName.val with
              | some aliasName => PythonIdentifier.fromAst aliasName
              | none => PythonIdentifier.fromAst impName
            some (id, annotationToPythonType none)
  | .Global _ _ => []
  | .Nonlocal _ _ => []
  | .Expr _ value =>
      (collectWalrusNames value).map (fun n => (n, annotationToPythonType none))
  | .TypeAlias _ nameExpr _ _ =>
      (collectNamesFromTarget nameExpr).map fun n => (n, annotationToPythonType none)

/-- Collects names declared `global` or `nonlocal` in a function body (including nested blocks).
    These are excluded from locals — they refer to enclosing/global scope. -/
partial def collectGlobalNonlocalNames (s : PythonStmt) : List PythonIdentifier :=
  match s with
  | .Global _ names => names.val.toList.map PythonIdentifier.fromAst
  | .Nonlocal _ names => names.val.toList.map PythonIdentifier.fromAst
  | .If _ _ body orelse =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames
  | .For _ _ _ body orelse _ =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames
  | .AsyncFor _ _ _ body orelse _ =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames
  | .While _ _ body orelse =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames
  | .Try _ body handlers orelse finalbody =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      handlers.val.toList.flatMap (fun h => match h with
        | .ExceptHandler _ _ _ hBody => hBody.val.toList.flatMap collectGlobalNonlocalNames) ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames ++
      finalbody.val.toList.flatMap collectGlobalNonlocalNames
  | .TryStar _ body handlers orelse finalbody =>
      body.val.toList.flatMap collectGlobalNonlocalNames ++
      handlers.val.toList.flatMap (fun h => match h with
        | .ExceptHandler _ _ _ hBody => hBody.val.toList.flatMap collectGlobalNonlocalNames) ++
      orelse.val.toList.flatMap collectGlobalNonlocalNames ++
      finalbody.val.toList.flatMap collectGlobalNonlocalNames
  | .With _ _ body _ => body.val.toList.flatMap collectGlobalNonlocalNames
  | .AsyncWith _ _ body _ => body.val.toList.flatMap collectGlobalNonlocalNames
  | .Match _ _ cases =>
      cases.val.toList.flatMap fun c => match c with
        | .mk_match_case _ _ _ caseBody => caseBody.val.toList.flatMap collectGlobalNonlocalNames
  | _ => []

/-- Python scoping: any assignment target in a function body is local to that function.
    Collects all such names (excluding params, globals, nonlocals, and nested def/class names),
    deduplicates preserving first-occurrence order. Used by `extractFuncSig` to populate `FuncSig.locals`. -/
def computeLocals (body : PythonProgram) (paramNames : List PythonIdentifier)
    : List (PythonIdentifier × PythonType) :=
  let allPairs := body.toList.flatMap collectLocalsFromStmt
  let globalNonlocal := body.toList.flatMap collectGlobalNonlocalNames
  let excluded : Std.HashSet PythonIdentifier := (paramNames ++ globalNonlocal).foldl (fun s n => s.insert n) {}
  let (_, result) := allPairs.foldl (init := (excluded, ([] : List (PythonIdentifier × PythonType)))) fun acc pair =>
    let (seen, result) := acc
    let (name, ty) := pair
    if seen.contains name then (seen, result)
    else (seen.insert name, result ++ [(name, ty)])
  result

-- ═══════════════════════════════════════════════════════════════════════════════
-- Extract FuncSig from a Python FunctionDef
-- ═══════════════════════════════════════════════════════════════════════════════

private def argToParam (arg : Python.arg SourceRange) : PythonIdentifier × PythonType :=
  match arg with
  | .mk_arg _ argName annotation _ => (PythonIdentifier.fromAst argName, annotationToPythonType annotation.val)

private def extractAllParamNames (args : Python.arguments SourceRange) : List PythonIdentifier :=
  match args with
  | .mk_arguments _ posonlyargs argList vararg kwonlyargs _ kwarg _ =>
      let names := (posonlyargs.val.toList ++ argList.val.toList ++ kwonlyargs.val.toList).map fun arg =>
        match arg with | .mk_arg _ argName _ _ => PythonIdentifier.fromAst argName
      let vaName := match vararg.val with | some (.mk_arg _ n _ _) => [PythonIdentifier.fromAst n] | none => []
      let kwName := match kwarg.val with | some (.mk_arg _ n _ _) => [PythonIdentifier.fromAst n] | none => []
      names ++ vaName ++ kwName

private def hasStaticmethodDecorator (decorators : Array PythonExpr) : Bool :=
  decorators.any fun d => match d with
    | .Name _ n _ => n.val == "staticmethod"
    | _ => false

private def hasOverloadDecorator (decorators : Array PythonExpr) : Bool :=
  decorators.any fun d => match d with
    | .Name _ n _ => n.val == "overload"
    | _ => false

/-- Check if a call argument matches a parameter's type for overload resolution.
    A Literal["value"] parameter matches a string constant with the same value.
    All other parameter types match any argument (broad matching). -/
private def argMatchesParam (arg : PythonExpr) (paramTy : PythonType) : Bool :=
  match paramTy with
  | .Subscript _ (.Name _ tName _) (.Constant _ (.ConString _ litVal) _) _ =>
    if tName.val == "Literal" then
      match arg with
      | .Constant _ (.ConString _ argVal) _ => argVal == litVal
      | _ => false
    else true
  | _ => true

/-- Check if call arguments match an overload's parameter signature. -/
private def matchOverload (sig : FuncSig) (args : Array PythonExpr) : Bool :=
  match sig.params with
  | .static pl =>
    let params := pl.required
    params.zip args.toList |>.all fun ((_, paramTy), arg) => argMatchesParam arg paramTy
  | .instance _ pl =>
    let params := pl.required
    params.zip args.toList |>.all fun ((_, paramTy), arg) => argMatchesParam arg paramTy

/-! ## Python Name → Laurel Name Mapping

The builtin mapping (`len` → `Any_len_to_Any`), method qualification
(`get_x` → `Account@get_x`), and module qualification
(`timedelta` → `datetime_timedelta`) are encoded in accessor functions.
Translation calls these accessors — it never fabricates Laurel identifiers
from strings or applies naming conventions itself.

`PythonIdentifier.toLaurel` is identity — bare name to Laurel.Identifier.
`FuncSig.laurelName` applies the builtin mapping for top-level functions and
`ClassName@method` qualification for class methods. -/

def pythonNameToLaurel : String → String
  | "len" => "Any_len_to_Any"
  | "str" => "to_string_any"
  | "int" => "to_int_any"
  | "float" => "to_float_any"
  | "bool" => "Any_to_bool"
  | "abs" => "Any_abs_to_Any"
  | "print" => "print"
  | "repr" => "to_string_any"
  | "type" => "Any_type_to_Any"
  | "isinstance" => "Any_isinstance_to_bool"
  | "hasattr" => "Any_hasattr_to_bool"
  | "getattr" => "Any_getattr_to_Any"
  | "setattr" => "Any_setattr_to_Any"
  | "sorted" => "Any_sorted_to_Any"
  | "reversed" => "Any_reversed_to_Any"
  | "enumerate" => "Any_enumerate_to_Any"
  | "zip" => "Any_zip_to_Any"
  | "range" => "Any_range_to_Any"
  | "list" => "Any_list_to_Any"
  | "dict" => "Any_dict_to_Any"
  | "set" => "Any_set_to_Any"
  | "tuple" => "Any_tuple_to_Any"
  | "min" => "Any_min_to_Any"
  | "max" => "Any_max_to_Any"
  | "sum" => "Any_sum_to_Any"
  | "any" => "Any_any_to_bool"
  | "all" => "Any_all_to_bool"
  | "ord" => "Any_ord_to_Any"
  | "chr" => "Any_chr_to_Any"
  | "map" => "Any_map_to_Any"
  | "filter" => "Any_filter_to_Any"
  | "timedelta" => "timedelta_func"
  | other => other

def operatorToLaurel : Python.operator SourceRange → String
  | .Add _ => "PAdd" | .Sub _ => "PSub" | .Mult _ => "PMul" | .Div _ => "PDiv"
  | .FloorDiv _ => "PFloorDiv" | .Mod _ => "PMod" | .Pow _ => "PPow"
  | .BitAnd _ => "PBitAnd" | .BitOr _ => "PBitOr" | .BitXor _ => "PBitXor"
  | .LShift _ => "PLShift" | .RShift _ => "PRShift" | .MatMult _ => "PMatMul"

def cmpopToLaurel : Python.cmpop SourceRange → String
  | .Eq _ => "PEq" | .NotEq _ => "PNEq" | .Lt _ => "PLt" | .LtE _ => "PLe"
  | .Gt _ => "PGt" | .GtE _ => "PGe" | .In _ => "PIn" | .NotIn _ => "PNotIn"
  | .Is _ => "PIs" | .IsNot _ => "PIsNot"

def unaryopToLaurel : Python.unaryop SourceRange → String
  | .Not _ => "PNot" | .USub _ => "PNeg" | .UAdd _ => "PPos" | .Invert _ => "PInvert"

def boolopToLaurel : Python.boolop SourceRange → String
  | .And _ => "PAnd" | .Or _ => "POr"

/-! ## Accessor Functions (Python → Laurel)

Translation calls these to obtain `Laurel.Identifier` values on demand.
They encode the naming conventions in one place. Translation never
fabricates identifiers from raw strings — it calls these accessors. -/

/-- Identity: bare Python name → Laurel.Identifier. No mapping applied.
    Used for variable names, param names, field names, local names. -/
def PythonIdentifier.toLaurel (id : PythonIdentifier) : Laurel.Identifier :=
  { text := id.val, uniqueId := none }

/-- Produces the Laurel procedure name. Applies builtin mapping for top-level
    functions (`len` → `Any_len_to_Any`) and class qualification for methods
    (`get_x` with `className = some "Account"` → `Account@get_x`). -/
def FuncSig.laurelName (sig : FuncSig) : Laurel.Identifier :=
  let baseName := match sig.className with
    | some cls => s!"{cls.val}@{sig.name.val}"
    | none => pythonNameToLaurel sig.name.val
  let name := match sig.overloadIndex with
    | some idx => s!"{baseName}${idx}"
    | none => baseName
  { text := name, uniqueId := none }

private def ParamList.allParams (pl : ParamList) : List (PythonIdentifier × PythonType) :=
  pl.required ++ pl.optional.map (fun (n, ty, _) => (n, ty)) ++ pl.kwonly.map (fun (n, ty, _) => (n, ty))

/-- All procedure inputs as `(Laurel.Identifier × PythonType)`. For instance
    methods, includes the receiver as first element (typed Any). For static
    functions, just the params. Translation uses this to declare procedure inputs.
    Inputs are named `$in_X` at the Laurel level (body uses mutable local `X`). -/
def FuncSig.laurelDeclInputs (sig : FuncSig) : List (Laurel.Identifier × PythonType) :=
  let anyTy : PythonType := .Name SourceRange.none ⟨SourceRange.none, "Any"⟩ (.Load SourceRange.none)
  let base := match sig.params with
    | .instance recv pl =>
      ({ text := recv.val, uniqueId := none }, anyTy) :: pl.allParams.map fun (id, ty) => ({ text := id.val, uniqueId := none }, ty)
    | .static pl =>
      pl.allParams.map fun (id, ty) => ({ text := id.val, uniqueId := none }, ty)
  match sig.kwargName with
  | some kw => base ++ [({ text := kw.val, uniqueId := none }, anyTy)]
  | none => base

/-- Zip-fold arg matching. Each param slot is filled in order:
    1. If a positional arg remains → consume it
    2. Else if a kwarg matches by name → use it
    3. Else if a default exists → translate it via `translateDefault`
    4. Else → panic (Resolution bug: required param without arg)

    Includes receiver slot for instance methods. Lives in Resolution
    because it accesses private `ParamList` fields and resolved defaults. -/
def FuncSig.matchArgs [Monad m] [Inhabited (m α)] (sig : FuncSig) (posArgs : List α) (kwargs : List (String × α))
    (translateDefault : ResolvedPythonExpr → m α) (mkKwargs : m (Option α) := pure none) : m (List α) := do
  let (receiverSlot, pl) := match sig.params with
    | .instance recv pl => ([(recv.val, (none : Option ResolvedPythonExpr))], pl)
    | .static pl => ([], pl)
  let slots : List (String × Option ResolvedPythonExpr) :=
    receiverSlot ++
    pl.required.map (fun (id, _) => (id.val, none)) ++
    pl.optional.map (fun (id, _, dflt) => (id.val, some dflt)) ++
    pl.kwonly.map (fun (id, _, dflt) => (id.val, dflt))
  let (result, _) ← slots.foldlM (fun (acc, pos) (pName, dflt) => do
    match pos with
    | a :: rest => pure (acc ++ [a], rest)
    | [] =>
      let v ← match kwargs.find? (fun (k, _) => k == pName) with
        | some (_, v) => pure v
        | none => match dflt with
          | some d => translateDefault d
          | none => panic! "Resolution bug: required param without arg"
      pure (acc ++ [v], [])
  ) ([], posArgs)
  -- Append a value for the `**kwargs` declared input, if present.
  if sig.kwargName.isSome then
    let kwOpt ← mkKwargs
    match kwOpt with
    | some kw => return (result ++ [kw])
    | none => return result
  else
    return result

/-- Locals as `(Laurel.Identifier × PythonType)` for `LocalVariable` declarations. -/
def FuncSig.laurelLocals (sig : FuncSig) : List (Laurel.Identifier × PythonType) :=
  sig.locals.map fun (id, ty) => ({ text := id.val, uniqueId := none }, ty)

/-- The receiver's Laurel.Identifier, if this is an instance method. -/
def FuncSig.laurelReceiver (sig : FuncSig) : Option Laurel.Identifier :=
  match sig.params with
  | .instance recv _ => some { text := recv.val, uniqueId := none }
  | .static _ => none

-- ═══════════════════════════════════════════════════════════════════════════════
-- Initial Context: Python Builtins
-- ═══════════════════════════════════════════════════════════════════════════════

private def anyType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "Any"⟩ (.Load SourceRange.none)
private def intType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "int"⟩ (.Load SourceRange.none)
private def strType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "str"⟩ (.Load SourceRange.none)
private def boolType : PythonType := .Name SourceRange.none ⟨SourceRange.none, "bool"⟩ (.Load SourceRange.none)

private def mkBuiltinSig (pythonName : String) (params : List (String × PythonType)) (retTy : PythonType) : FuncSig :=
  let required := params.map fun (n, ty) => (PythonIdentifier.builtin n, ty)
  { name := .builtin pythonName, className := none,
    params := .static { required, optional := [], kwonly := [] },
    returnType := retTy, locals := [] }

/-- The initial context: all Python builtins with their FuncSig (correct arity, param names,
    return types). Resolution starts from this and extends with user-defined declarations. -/
def builtinContext : Ctx :=
  let entries : List (PythonIdentifier × CtxEntry) := [
    (.builtin "len", .function (mkBuiltinSig "len" [("obj", anyType)] intType)),
    (.builtin "str", .function (mkBuiltinSig "str" [("obj", anyType)] strType)),
    (.builtin "int", .function (mkBuiltinSig "int" [("obj", anyType)] intType)),
    (.builtin "float", .function (mkBuiltinSig "float" [("obj", anyType)] anyType)),
    (.builtin "bool", .function (mkBuiltinSig "bool" [("obj", anyType)] boolType)),
    (.builtin "print", .function (mkBuiltinSig "print" [("obj", anyType)] anyType)),
    (.builtin "repr", .function (mkBuiltinSig "repr" [("obj", anyType)] strType)),
    (.builtin "type", .function (mkBuiltinSig "type" [("obj", anyType)] anyType)),
    (.builtin "isinstance", .function (mkBuiltinSig "isinstance" [("obj", anyType), ("cls", anyType)] boolType)),
    (.builtin "hasattr", .function (mkBuiltinSig "hasattr" [("obj", anyType), ("name", strType)] boolType)),
    (.builtin "getattr", .function (mkBuiltinSig "getattr" [("obj", anyType), ("name", strType)] anyType)),
    (.builtin "setattr", .function (mkBuiltinSig "setattr" [("obj", anyType), ("name", strType), ("value", anyType)] anyType)),
    (.builtin "sorted", .function (mkBuiltinSig "sorted" [("iterable", anyType)] anyType)),
    (.builtin "reversed", .function (mkBuiltinSig "reversed" [("seq", anyType)] anyType)),
    (.builtin "enumerate", .function (mkBuiltinSig "enumerate" [("iterable", anyType)] anyType)),
    (.builtin "zip", .function (mkBuiltinSig "zip" [("a", anyType), ("b", anyType)] anyType)),
    (.builtin "range", .function (mkBuiltinSig "range" [("stop", anyType)] anyType)),
    (.builtin "list", .function (mkBuiltinSig "list" [("iterable", anyType)] anyType)),
    (.builtin "dict", .function (mkBuiltinSig "dict" [("iterable", anyType)] anyType)),
    (.builtin "set", .function (mkBuiltinSig "set" [("iterable", anyType)] anyType)),
    (.builtin "tuple", .function (mkBuiltinSig "tuple" [("iterable", anyType)] anyType)),
    (.builtin "min", .function (mkBuiltinSig "min" [("a", anyType), ("b", anyType)] anyType)),
    (.builtin "max", .function (mkBuiltinSig "max" [("a", anyType), ("b", anyType)] anyType)),
    (.builtin "sum", .function (mkBuiltinSig "sum" [("iterable", anyType)] anyType)),
    (.builtin "any", .function (mkBuiltinSig "any" [("iterable", anyType)] boolType)),
    (.builtin "all", .function (mkBuiltinSig "all" [("iterable", anyType)] boolType)),
    (.builtin "abs", .function (mkBuiltinSig "abs" [("x", anyType)] anyType)),
    (.builtin "ord", .function (mkBuiltinSig "ord" [("c", strType)] intType)),
    (.builtin "chr", .function (mkBuiltinSig "chr" [("i", intType)] strType)),
    (.builtin "map", .function (mkBuiltinSig "map" [("func", anyType), ("iterable", anyType)] anyType)),
    (.builtin "filter", .function (mkBuiltinSig "filter" [("func", anyType), ("iterable", anyType)] anyType))
  ]
  entries.foldl (fun ctx (name, info) => ctx.insert name info) {}

-- ═══════════════════════════════════════════════════════════════════════════════
-- Spine type resolution (chases .Name and .Attribute chains)
-- ═══════════════════════════════════════════════════════════════════════════════

-- typeOfExpr and resolveMethodCall moved into the mutual block below

-- resolveMethodCall moved into the mutual block below

-- ═══════════════════════════════════════════════════════════════════════════════
-- AST Annotation Mapping (f : SourceRange → ResolvedAnn through the tree)
-- ═══════════════════════════════════════════════════════════════════════════════

private def mapAnnVal (f : α → β) (a : Ann T α) : Ann T β := ⟨f a.ann, a.val⟩
private def mapAnnOpt (f : α → β) (mapT : T₁ → T₂) (a : Ann (Option T₁) α) : Ann (Option T₂) β :=
  ⟨f a.ann, a.val.map mapT⟩
private def mapAnnArr (f : α → β) (mapT : T₁ → T₂) (a : Ann (Array T₁) α) : Ann (Array T₂) β :=
  ⟨f a.ann, a.val.map mapT⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- The Fold: resolve
--
-- Threads Ctx as accumulator. Declarations extend it. References look up from it.
-- Non-reference nodes get .none. Reference nodes get their lookup result.
-- ═══════════════════════════════════════════════════════════════════════════════

mutual

/-- Extracts a `ParamList` from Python's `arguments` AST node. Resolves default expressions
    via `resolveExpr` so they carry `ResolvedAnn` annotations for later Translation use. -/
partial def extractParamList (ctx : Ctx) (f : SourceRange → ResolvedAnn) (args : Python.arguments SourceRange) : ResolveM ParamList := do
  match args with
  | .mk_arguments _ posonlyargs argList _ kwonlyargs kwDefaults kwarg defaults =>
      let posAndRegular := posonlyargs.val.toList ++ argList.val.toList
      let allPosParams := posAndRegular.map argToParam
      let defaultCount := defaults.val.size
      let requiredCount := allPosParams.length - defaultCount
      let required := allPosParams.take requiredCount
      let optionalParams := allPosParams.drop requiredCount
      let mut optional : List (PythonIdentifier × PythonType × ResolvedPythonExpr) := []
      for ((n, ty), dflt) in optionalParams.zip (defaults.val.toList) do
        optional := optional ++ [(n, ty, ← resolveExpr ctx f dflt)]
      let kwParams := kwonlyargs.val.toList.map argToParam
      let mut kwonly : List (PythonIdentifier × PythonType × Option ResolvedPythonExpr) := []
      for ((n, ty), optExpr) in kwParams.zip (kwDefaults.val.toList) do
        match optExpr with
        | .some_expr _ e => kwonly := kwonly ++ [(n, ty, some (← resolveExpr ctx f e))]
        | .missing_expr _ => kwonly := kwonly ++ [(n, ty, none)]
      let _ := kwarg  -- `**kwargs` registered separately by resolveFunctionBody
      return { required, optional, kwonly }

/-- Builds a complete `FuncSig` for a function/method definition. Determines instance vs static
    (if `className` is set and no `@staticmethod`, first param becomes receiver), computes locals,
    and stores the resolved param list. This is the single point where FuncSig is created. -/
partial def extractFuncSig (ctx : Ctx) (f : SourceRange → ResolvedAnn)
    (pythonName : PythonIdentifier) (className : Option PythonIdentifier)
    (args : Python.arguments SourceRange) (decorators : Array PythonExpr)
    (returns : Ann (Option PythonExpr) SourceRange)
    (body : PythonProgram) : ResolveM FuncSig := do
  let paramList ← extractParamList ctx f args
  let retTy := annotationToPythonType returns.val
  let allParamNames := extractAllParamNames args
  let locals := computeLocals body allParamNames
  let funcParams :=
    if className.isNone || hasStaticmethodDecorator decorators then
      .static paramList
    else match paramList.required with
      | (recv, _) :: rest => .instance recv { paramList with required := rest }
      | [] => .static paramList
  let kwargName := match args with
    | .mk_arguments _ _ _ _ _ _ kwarg _ => match kwarg.val with
      | some (.mk_arg _ n _ _) => some (PythonIdentifier.fromAst n)
      | none => none
  return { name := pythonName, className, params := funcParams, returnType := retTy, locals, kwargName }

/-- Builds the body context for resolving statements inside a function. Extends ctx with
    all params (including vararg/kwarg) and locals. Used by `resolveFuncDef` to create the
    scope in which the function body is resolved. -/
partial def resolveFunctionBody (ctx : Ctx) (f : SourceRange → ResolvedAnn) (args : Python.arguments SourceRange) (body : PythonProgram) : ResolveM Ctx := do
  let pl ← extractParamList ctx f args
  let allParams := pl.required ++ pl.optional.map (fun (n, ty, _) => (n, ty)) ++ pl.kwonly.map (fun (n, ty, _) => (n, ty))
  let varargKwarg : List (PythonIdentifier × PythonType) := match args with
    | .mk_arguments _ _ _ vararg _ _ kwarg _ =>
      let va := match vararg.val with | some a => [argToParam a] | none => []
      let kw := match kwarg.val with | some a => [argToParam a] | none => []
      va ++ kw
  let allParamNames := extractAllParamNames args
  let locals := computeLocals body allParamNames
  let bodyCtx := allParams.foldl (fun c (n, ty) => c.insert n (CtxEntry.variable ty)) ctx
  let bodyCtx := varargKwarg.foldl (fun c (n, ty) => c.insert n (CtxEntry.variable ty)) bodyCtx
  return locals.foldl (fun c (n, ty) => c.insert n (CtxEntry.variable ty)) bodyCtx

partial def resolveExprCtx (f : SourceRange → ResolvedAnn) : Python.expr_context SourceRange → Python.expr_context ResolvedAnn
  | .Load a => .Load (f a) | .Store a => .Store (f a) | .Del a => .Del (f a)

partial def resolveConstant (f : SourceRange → ResolvedAnn) : Python.constant SourceRange → Python.constant ResolvedAnn
  | .ConTrue a => .ConTrue (f a) | .ConFalse a => .ConFalse (f a)
  | .ConPos a n => .ConPos (f a) (mapAnnVal f n) | .ConNeg a n => .ConNeg (f a) (mapAnnVal f n)
  | .ConString a s => .ConString (f a) (mapAnnVal f s) | .ConFloat a s => .ConFloat (f a) (mapAnnVal f s)
  | .ConComplex a r i => .ConComplex (f a) (mapAnnVal f r) (mapAnnVal f i)
  | .ConNone a => .ConNone (f a) | .ConEllipsis a => .ConEllipsis (f a)
  | .ConBytes a b => .ConBytes (f a) (mapAnnVal f b)

partial def resolveInt (f : SourceRange → ResolvedAnn) : Python.int SourceRange → Python.int ResolvedAnn
  | .IntPos a n => .IntPos (f a) (mapAnnVal f n) | .IntNeg a n => .IntNeg (f a) (mapAnnVal f n)

partial def resolveOperator (f : SourceRange → ResolvedAnn) : Python.operator SourceRange → Python.operator ResolvedAnn
  | .Add a => .Add (f a) | .Sub a => .Sub (f a) | .Mult a => .Mult (f a) | .Div a => .Div (f a)
  | .FloorDiv a => .FloorDiv (f a) | .Mod a => .Mod (f a) | .Pow a => .Pow (f a)
  | .BitAnd a => .BitAnd (f a) | .BitOr a => .BitOr (f a) | .BitXor a => .BitXor (f a)
  | .LShift a => .LShift (f a) | .RShift a => .RShift (f a) | .MatMult a => .MatMult (f a)

partial def resolveBoolop (f : SourceRange → ResolvedAnn) : Python.boolop SourceRange → Python.boolop ResolvedAnn
  | .And a => .And (f a) | .Or a => .Or (f a)

partial def resolveUnaryop (f : SourceRange → ResolvedAnn) : Python.unaryop SourceRange → Python.unaryop ResolvedAnn
  | .Not a => .Not (f a) | .USub a => .USub (f a) | .UAdd a => .UAdd (f a) | .Invert a => .Invert (f a)

partial def resolveCmpop (f : SourceRange → ResolvedAnn) : Python.cmpop SourceRange → Python.cmpop ResolvedAnn
  | .Eq a => .Eq (f a) | .NotEq a => .NotEq (f a) | .Lt a => .Lt (f a) | .LtE a => .LtE (f a)
  | .Gt a => .Gt (f a) | .GtE a => .GtE (f a) | .Is a => .Is (f a) | .IsNot a => .IsNot (f a)
  | .In a => .In (f a) | .NotIn a => .NotIn (f a)

partial def resolveOptExpr (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.opt_expr SourceRange → ResolveM (Python.opt_expr ResolvedAnn)
  | .some_expr a e => do return .some_expr (f a) (← resolveExpr ctx f e)
  | .missing_expr a => return .missing_expr (f a)

partial def resolveKeyword (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.keyword SourceRange → ResolveM (Python.keyword ResolvedAnn)
  | .mk_keyword a arg val => do return .mk_keyword (f a) (mapAnnOpt f (mapAnnVal f) arg) (← resolveExpr ctx f val)

partial def resolveArg (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.arg SourceRange → ResolveM (Python.arg ResolvedAnn)
  | .mk_arg a name ann tc => do
    let rAnn ← match ann.val with
      | some e => pure (some (← resolveExpr ctx f e))
      | none => pure none
    return .mk_arg (f a) (mapAnnVal f name) ⟨f ann.ann, rAnn⟩ (mapAnnOpt f (mapAnnVal f) tc)

partial def resolveArguments (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.arguments SourceRange → ResolveM (Python.arguments ResolvedAnn)
  | .mk_arguments a posonlyargs args vararg kwonlyargs kwDefaults kwarg defaults => do
      let mut rPosonlyargs : Array (Python.arg ResolvedAnn) := #[]
      for arg in posonlyargs.val do rPosonlyargs := rPosonlyargs.push (← resolveArg ctx f arg)
      let mut rArgs : Array (Python.arg ResolvedAnn) := #[]
      for arg in args.val do rArgs := rArgs.push (← resolveArg ctx f arg)
      let rVararg ← match vararg.val with
        | some a => pure (some (← resolveArg ctx f a))
        | none => pure none
      let mut rKwonlyargs : Array (Python.arg ResolvedAnn) := #[]
      for arg in kwonlyargs.val do rKwonlyargs := rKwonlyargs.push (← resolveArg ctx f arg)
      let mut rKwDefaults : Array (Python.opt_expr ResolvedAnn) := #[]
      for oe in kwDefaults.val do rKwDefaults := rKwDefaults.push (← resolveOptExpr ctx f oe)
      let rKwarg ← match kwarg.val with
        | some a => pure (some (← resolveArg ctx f a))
        | none => pure none
      let mut rDefaults : Array ResolvedPythonExpr := #[]
      for d in defaults.val do rDefaults := rDefaults.push (← resolveExpr ctx f d)
      return .mk_arguments (f a)
        ⟨f posonlyargs.ann, rPosonlyargs⟩
        ⟨f args.ann, rArgs⟩
        ⟨f vararg.ann, rVararg⟩
        ⟨f kwonlyargs.ann, rKwonlyargs⟩
        ⟨f kwDefaults.ann, rKwDefaults⟩
        ⟨f kwarg.ann, rKwarg⟩
        ⟨f defaults.ann, rDefaults⟩

partial def resolveComprehension (ctx : Ctx) (f : SourceRange → ResolvedAnn) (comp : Python.comprehension SourceRange) : ResolveM (Ctx × Python.comprehension ResolvedAnn) := do
  match comp with
  | .mk_comprehension a target iter ifs isAsync =>
      let targetNames := collectNamesFromTarget target
      let compCtx := targetNames.foldl (fun c n => c.insert n (CtxEntry.variable (annotationToPythonType Option.none))) ctx
      let rTarget ← resolveExpr compCtx f target
      let rIter ← resolveExpr ctx f iter
      let mut rIfs : Array ResolvedPythonExpr := #[]
      for i in ifs.val do rIfs := rIfs.push (← resolveExpr compCtx f i)
      return (compCtx, .mk_comprehension (f a) rTarget rIter ⟨f ifs.ann, rIfs⟩ (resolveInt f isAsync))

partial def resolveComprehensions (ctx : Ctx) (f : SourceRange → ResolvedAnn) (comps : List (Python.comprehension SourceRange)) : ResolveM (Ctx × List (Python.comprehension ResolvedAnn)) := do
  let mut c := ctx
  let mut resolved : List (Python.comprehension ResolvedAnn) := []
  for comp in comps do
    let (c', r) ← resolveComprehension c f comp
    c := c'
    resolved := resolved ++ [r]
  return (c, resolved)

partial def resolveTypeParam (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.type_param SourceRange → ResolveM (Python.type_param ResolvedAnn)
  | .TypeVar a name bound def_ => do
    let rBound ← match bound.val with
      | some e => pure (some (← resolveExpr ctx f e))
      | none => pure none
    let rDef ← match def_.val with
      | some e => pure (some (← resolveExpr ctx f e))
      | none => pure none
    return .TypeVar (f a) (mapAnnVal f name) ⟨f bound.ann, rBound⟩ ⟨f def_.ann, rDef⟩
  | .TypeVarTuple a name def_ => do
    let rDef ← match def_.val with
      | some e => pure (some (← resolveExpr ctx f e))
      | none => pure none
    return .TypeVarTuple (f a) (mapAnnVal f name) ⟨f def_.ann, rDef⟩
  | .ParamSpec a name def_ => do
    let rDef ← match def_.val with
      | some e => pure (some (← resolveExpr ctx f e))
      | none => pure none
    return .ParamSpec (f a) (mapAnnVal f name) ⟨f def_.ann, rDef⟩

/-- The core expression resolver. Annotates each expression node with appropriate `NodeInfo`:
    - `.Name` → look up in ctx, annotate with `.variable`
    - `.Call` → determine callee (function/class/method), annotate with `.funcCall` or `.classNew`
    - `.Attribute` → annotate with `.attribute` (bare field name; Elaboration resolves via receiver type)
    - `.BinOp`/`.UnaryOp`/`.Compare`/`.BoolOp` → create operator FuncSig, annotate with `.funcCall`
    - Comprehensions → extend ctx with iteration variables before resolving element expression -/
partial def resolveExpr (ctx : Ctx) (f : SourceRange → ResolvedAnn) (e : PythonExpr) : ResolveM ResolvedPythonExpr := do
  match e with
  | .Name a n ectx =>
      let nId := PythonIdentifier.fromAst n
      let info := match ctx[nId]? with
        | some (.variable _) => .variable nId
        | some (.function _) => .unresolved
        | some (.overloadedFunction _) => .unresolved
        | some (.class_ _ _ _ _) => .unresolved
        | some (.module_ _) => .irrelevant
        | some .unresolved => .unresolved
        | none => .unresolved
      return .Name { sr := a, info } (mapAnnVal f n) (resolveExprCtx f ectx)
  | .Call a func args kwargs =>
      let callInfo : NodeInfo ← match func with
        | .Name _ n _ =>
          let nId := PythonIdentifier.fromAst n
          match ctx[nId]? with
          | some (.function sig) => pure (.funcCall sig)
          | some (.overloadedFunction overloads) =>
              let matched := overloads.find? fun (_, olSig, _) =>
                matchOverload olSig args.val
              match matched with
              | some (idx, sig, astOpt) => do
                let sig' := { sig with overloadIndex := some idx }
                match astOpt with
                | some fAst => resolveFunctionAstSig ctx f sig' fAst
                | none => pure ()
                pure (.funcCall sig')
              | none => pure .unresolved
          | some (.class_ cId _ methods _) =>
              let initId := PythonIdentifier.builtin "__init__"
              match methods.find? (fun (mName, _) => mName == initId) with
              | some (_, sig) => pure (.classNew cId sig)
              | none =>
                let emptySig : FuncSig := { name := initId, className := some cId, params := .static {required := [], optional := [], kwonly := []}, returnType := anyType, locals := [] }
                pure (.classNew cId emptySig)
          | _ => pure .unresolved
        | .Attribute _ receiver methodName _ =>
            resolveMethodCall ctx receiver methodName args.val
        | _ => pure .unresolved
      let rFunc ← resolveExpr ctx f func
      let mut rArgs : Array ResolvedPythonExpr := #[]
      for arg in args.val do
        rArgs := rArgs.push (← resolveExpr ctx f arg)
      let mut rKwargs : Array (Python.keyword ResolvedAnn) := #[]
      for kw in kwargs.val do
        rKwargs := rKwargs.push (← resolveKeyword ctx f kw)
      return .Call { sr := a, info := callInfo } rFunc ⟨f args.ann, rArgs⟩ ⟨f kwargs.ann, rKwargs⟩
  | .Attribute a obj attr ectx =>
      let rObj ← resolveExpr ctx f obj
      return .Attribute { sr := a, info := .attribute (PythonIdentifier.fromAst attr) } rObj (mapAnnVal f attr) (resolveExprCtx f ectx)
  | .Constant a c tc => return .Constant (f a) (resolveConstant f c) (mapAnnOpt f (mapAnnVal f) tc)
  | .BinOp a left op right =>
      let opSig : FuncSig := { name := .builtin (operatorToLaurel op), className := none, params := .static {required := [(.builtin "left", anyType), (.builtin "right", anyType)], optional := [], kwonly := []}, returnType := anyType, locals := [] }
      let rLeft ← resolveExpr ctx f left
      let rRight ← resolveExpr ctx f right
      return .BinOp { sr := a, info := .funcCall opSig } rLeft (resolveOperator f op) rRight
  | .BoolOp a op operands =>
      let opSig : FuncSig := { name := .builtin (boolopToLaurel op), className := none, params := .static {required := [(.builtin "left", anyType), (.builtin "right", anyType)], optional := [], kwonly := []}, returnType := anyType, locals := [] }
      let mut rOperands : Array ResolvedPythonExpr := #[]
      for operand in operands.val do
        rOperands := rOperands.push (← resolveExpr ctx f operand)
      return .BoolOp { sr := a, info := .funcCall opSig } (resolveBoolop f op) ⟨f operands.ann, rOperands⟩
  | .UnaryOp a op operand =>
      let opSig : FuncSig := { name := .builtin (unaryopToLaurel op), className := none, params := .static {required := [(.builtin "operand", anyType)], optional := [], kwonly := []}, returnType := anyType, locals := [] }
      let rOperand ← resolveExpr ctx f operand
      return .UnaryOp { sr := a, info := .funcCall opSig } (resolveUnaryop f op) rOperand
  | .Compare a left ops comps =>
      let opName := match ops.val[0]? with | some op => cmpopToLaurel op | none => "PEq"
      let opSig : FuncSig := { name := .builtin opName, className := none, params := .static {required := [(.builtin "left", anyType), (.builtin "right", anyType)], optional := [], kwonly := []}, returnType := anyType, locals := [] }
      let rLeft ← resolveExpr ctx f left
      let mut rComps : Array ResolvedPythonExpr := #[]
      for comp in comps.val do
        rComps := rComps.push (← resolveExpr ctx f comp)
      return .Compare { sr := a, info := .funcCall opSig } rLeft (mapAnnArr f (resolveCmpop f) ops) ⟨f comps.ann, rComps⟩
  | .IfExp a test body orelse =>
      let rTest ← resolveExpr ctx f test
      let rBody ← resolveExpr ctx f body
      let rElse ← resolveExpr ctx f orelse
      return .IfExp (f a) rTest rBody rElse
  | .Dict a keys vals =>
      let mut rKeys : Array (Python.opt_expr ResolvedAnn) := #[]
      for k in keys.val do
        rKeys := rKeys.push (← resolveOptExpr ctx f k)
      let mut rVals : Array ResolvedPythonExpr := #[]
      for v in vals.val do
        rVals := rVals.push (← resolveExpr ctx f v)
      return .Dict (f a) ⟨f keys.ann, rKeys⟩ ⟨f vals.ann, rVals⟩
  | .Set a elts =>
      let mut rElts : Array ResolvedPythonExpr := #[]
      for elt in elts.val do
        rElts := rElts.push (← resolveExpr ctx f elt)
      return .Set (f a) ⟨f elts.ann, rElts⟩
  | .ListComp a elt gens =>
      let (compCtx, resolvedGens) ← resolveComprehensions ctx f gens.val.toList
      let rElt ← resolveExpr compCtx f elt
      return .ListComp (f a) rElt ⟨f gens.ann, resolvedGens.toArray⟩
  | .SetComp a elt gens =>
      let (compCtx, resolvedGens) ← resolveComprehensions ctx f gens.val.toList
      let rElt ← resolveExpr compCtx f elt
      return .SetComp (f a) rElt ⟨f gens.ann, resolvedGens.toArray⟩
  | .DictComp a key val gens =>
      let (compCtx, resolvedGens) ← resolveComprehensions ctx f gens.val.toList
      let rKey ← resolveExpr compCtx f key
      let rVal ← resolveExpr compCtx f val
      return .DictComp (f a) rKey rVal ⟨f gens.ann, resolvedGens.toArray⟩
  | .GeneratorExp a elt gens =>
      let (compCtx, resolvedGens) ← resolveComprehensions ctx f gens.val.toList
      let rElt ← resolveExpr compCtx f elt
      return .GeneratorExp (f a) rElt ⟨f gens.ann, resolvedGens.toArray⟩
  | .Await a inner => return .Await (f a) (← resolveExpr ctx f inner)
  | .Yield a valOpt =>
      let rVal ← match valOpt.val with
        | some v => pure (some (← resolveExpr ctx f v))
        | none => pure none
      return .Yield (f a) ⟨f valOpt.ann, rVal⟩
  | .YieldFrom a inner => return .YieldFrom (f a) (← resolveExpr ctx f inner)
  | .FormattedValue a value conv fmt =>
      let rValue ← resolveExpr ctx f value
      let rFmt ← match fmt.val with
        | some fmtExpr => pure (some (← resolveExpr ctx f fmtExpr))
        | none => pure none
      return .FormattedValue (f a) rValue (resolveInt f conv) ⟨f fmt.ann, rFmt⟩
  | .JoinedStr a values =>
      let mut rValues : Array ResolvedPythonExpr := #[]
      for v in values.val do
        rValues := rValues.push (← resolveExpr ctx f v)
      return .JoinedStr (f a) ⟨f values.ann, rValues⟩
  | .Subscript a obj slice ectx =>
      let rObj ← resolveExpr ctx f obj
      let rSlice ← resolveExpr ctx f slice
      return .Subscript (f a) rObj rSlice (resolveExprCtx f ectx)
  | .Starred a inner ectx =>
      return .Starred (f a) (← resolveExpr ctx f inner) (resolveExprCtx f ectx)
  | .Tuple a elts ectx =>
      let mut rElts : Array ResolvedPythonExpr := #[]
      for elt in elts.val do
        rElts := rElts.push (← resolveExpr ctx f elt)
      return .Tuple (f a) ⟨f elts.ann, rElts⟩ (resolveExprCtx f ectx)
  | .List a elts ectx =>
      let mut rElts : Array ResolvedPythonExpr := #[]
      for elt in elts.val do
        rElts := rElts.push (← resolveExpr ctx f elt)
      return .List (f a) ⟨f elts.ann, rElts⟩ (resolveExprCtx f ectx)
  | .NamedExpr a target value =>
      let rTarget ← resolveExpr ctx f target
      let rValue ← resolveExpr ctx f value
      return .NamedExpr (f a) rTarget rValue
  | .Lambda a args body => do
      let pl ← extractParamList ctx f args
      let allParams := pl.required ++ pl.optional.map (fun (n, ty, _) => (n, ty)) ++ pl.kwonly.map (fun (n, ty, _) => (n, ty))
      let lambdaCtx := allParams.foldl (fun c (n, ty) => c.insert n (CtxEntry.variable ty)) ctx
      let rBody ← resolveExpr lambdaCtx f body
      let rArgs ← resolveArguments lambdaCtx f args
      return .Lambda (f a) rArgs rBody
  | .Slice a start stop step =>
      let rStart ← match start.val with
        | some e => pure (some (← resolveExpr ctx f e))
        | none => pure none
      let rStop ← match stop.val with
        | some e => pure (some (← resolveExpr ctx f e))
        | none => pure none
      let rStep ← match step.val with
        | some e => pure (some (← resolveExpr ctx f e))
        | none => pure none
      return .Slice (f a) ⟨f start.ann, rStart⟩ ⟨f stop.ann, rStop⟩ ⟨f step.ann, rStep⟩
  | .TemplateStr a parts =>
      let mut rParts : Array ResolvedPythonExpr := #[]
      for p in parts.val do
        rParts := rParts.push (← resolveExpr ctx f p)
      return .TemplateStr (f a) ⟨f parts.ann, rParts⟩
  | .Interpolation a value conv fmtSpec fmt => do
      let rValue ← resolveExpr ctx f value
      let rFmt ← match fmt.val with
        | some e => pure (some (← resolveExpr ctx f e))
        | none => pure none
      return .Interpolation (f a) rValue (resolveConstant f conv) (resolveInt f fmtSpec) ⟨f fmt.ann, rFmt⟩

partial def resolveAlias (f : SourceRange → ResolvedAnn) : Python.alias SourceRange → Python.alias ResolvedAnn
  | .mk_alias a name asname => .mk_alias (f a) (mapAnnVal f name) (mapAnnOpt f (mapAnnVal f) asname)

/-- Resolves a `with` item: uses `typeOfExpr` on the context expression to find the class,
    then looks up `__enter__` and `__exit__` in its method list. Annotates with `.withCtx`
    carrying both sigs so Translation can emit `StaticCall enter [mgr]` / `StaticCall exit [mgr]`. -/
partial def resolveWithitem (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.withitem SourceRange → ResolveM (Python.withitem ResolvedAnn)
  | .mk_withitem a ctxExpr optVars => do
      let enterId := PythonIdentifier.builtin "__enter__"
      let exitId := PythonIdentifier.builtin "__exit__"
      let info ← match ← typeOfExpr ctx ctxExpr with
        | some (.Name _ className _) =>
          let classId := PythonIdentifier.fromAst className
          match ctx[classId]? with
          | some (.class_ _ _ methods _) =>
            let enterSig := methods.find? (fun (mName, _) => mName == enterId) |>.map (·.2)
            let exitSig := methods.find? (fun (mName, _) => mName == exitId) |>.map (·.2)
            match enterSig, exitSig with
            | some es, some xs => pure (NodeInfo.withCtx es xs)
            | _, _ => pure NodeInfo.unresolved
          | _ => pure NodeInfo.unresolved
        | _ => pure NodeInfo.unresolved
      let rCtxExpr ← resolveExpr ctx f ctxExpr
      let rOptVars ← match optVars.val with
        | some v => pure (some (← resolveExpr ctx f v))
        | none => pure none
      return .mk_withitem { sr := a, info } rCtxExpr ⟨f optVars.ann, rOptVars⟩

partial def resolveExcepthandler (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.excepthandler SourceRange → ResolveM (Python.excepthandler ResolvedAnn)
  | .ExceptHandler a ty name body => do
      let handlerCtx := match name.val with
        | some n => ctx.insert (PythonIdentifier.fromAst n) (CtxEntry.variable (annotationToPythonType Option.none))
        | none => ctx
      let resolvedBody ← resolveBlock handlerCtx f body.val
      let rTy ← match ty.val with
        | some e => pure (some (← resolveExpr ctx f e))
        | none => pure none
      return .ExceptHandler (f a) ⟨f ty.ann, rTy⟩ (mapAnnOpt f (mapAnnVal f) name) ⟨f body.ann, resolvedBody⟩

partial def resolveMatchCase (ctx : Ctx) (f : SourceRange → ResolvedAnn) : Python.match_case SourceRange → ResolveM (Python.match_case ResolvedAnn)
  | .mk_match_case a pat guard body => do
    let resolvedBody ← resolveBlock ctx f body.val
    let rGuard ← match guard.val with
      | some e => pure (some (← resolveExpr ctx f e))
      | none => pure none
    return .mk_match_case (f a) (sorry) ⟨f guard.ann, rGuard⟩ ⟨f body.ann, resolvedBody⟩

/-- Resolves an array of statements sequentially, threading the growing context.
    Each statement may extend the context (e.g., assignments, imports, defs) which
    subsequent statements in the same block can see. -/
partial def resolveBlock (ctx : Ctx) (f : SourceRange → ResolvedAnn) (stmts : Array PythonStmt) : ResolveM (Array ResolvedPythonStmt) := do
  let mut c := ctx
  let mut resolved : Array ResolvedPythonStmt := #[]
  for stmt in stmts do
    let (c', r) ← resolveStmt c f stmt
    c := c'
    resolved := resolved.push r
  return resolved

/-- Resolves a function definition. Takes the pre-computed `FuncSig` (from the ClassDef handler
    or freshly extracted), extends the context with the function name, builds the body context,
    and resolves the body. Returns the updated ctx and all resolved sub-trees for the caller to
    assemble into `FunctionDef` or `AsyncFunctionDef`. -/
partial def resolveFuncDef (ctx : Ctx) (f : SourceRange → ResolvedAnn)
    (sig : FuncSig)
    (a : SourceRange) (name : Ann String SourceRange) (args : Python.arguments SourceRange)
    (body : Ann PythonProgram SourceRange) (decorators : Ann (Array PythonExpr) SourceRange)
    (returns : Ann (Option PythonExpr) SourceRange) (tc : Ann (Option (Ann String SourceRange)) SourceRange)
    (typeParams : Ann (Array (Python.type_param SourceRange)) SourceRange) := do
  let ctx' := ctx.insert (PythonIdentifier.fromAst name) (.function sig)
  let bodyCtx ← resolveFunctionBody ctx' f args body.val
  let ann : ResolvedAnn := { sr := a, info := .funcDecl sig }
  let resolvedBody ← resolveBlock bodyCtx f body.val
  let rBody : Ann (Array ResolvedPythonStmt) ResolvedAnn := ⟨f body.ann, resolvedBody⟩
  let rArgs ← resolveArguments bodyCtx f args
  let mut rDecs : Array ResolvedPythonExpr := #[]
  for d in decorators.val do rDecs := rDecs.push (← resolveExpr ctx' f d)
  let rRets ← match returns.val with
    | some e => pure (some (← resolveExpr ctx' f e))
    | none => pure none
  let mut rTps : Array (Python.type_param ResolvedAnn) := #[]
  for tp in typeParams.val do rTps := rTps.push (← resolveTypeParam ctx' f tp)
  let rDecsAnn : Ann (Array ResolvedPythonExpr) ResolvedAnn := ⟨f decorators.ann, rDecs⟩
  let rRetsAnn : Ann (Option ResolvedPythonExpr) ResolvedAnn := ⟨f returns.ann, rRets⟩
  let rTpsAnn : Ann (Array (Python.type_param ResolvedAnn)) ResolvedAnn := ⟨f typeParams.ann, rTps⟩
  return (ctx', ann, mapAnnVal f name, rArgs, rBody, rDecsAnn, rRetsAnn, mapAnnOpt f (mapAnnVal f) tc, rTpsAnn)

/-- Spine type resolution. Monadic: may trigger demand-driven module loads when
    traversing qualified type annotations (e.g. `boto3.S3`) through module contexts. -/
partial def typeOfExpr (ctx : Ctx) : PythonExpr → ResolveM (Option PythonType)
  | .Name _ n _ => match ctx[PythonIdentifier.fromAst n]? with
    | some (.variable ty) => pure (some ty)
    | _ => pure none
  | .Attribute _ obj fieldName _ => do
    match ← typeOfExpr ctx obj with
    | some (.Name _ className _) =>
      let classId := PythonIdentifier.fromAst className
      match ctx[classId]? with
      | some (.class_ _ fields _ _) =>
        pure (fields.find? (fun (fName, _) => fName == PythonIdentifier.fromAst fieldName) |>.map (·.2))
      | some (.module_ moduleRaw) =>
        let moduleCtx : Ctx := moduleRaw.fold (fun c k v => c.insert k v) {}
        let fieldId := PythonIdentifier.fromAst fieldName
        match moduleCtx[fieldId]? with
        | some (.variable ty) => pure (some ty)
        | some (.class_ _ fields _ _) =>
          pure (fields.find? (fun (fName, _) => fName == fieldId) |>.map (·.2))
        | none =>
          let baseDir ← read
          let components := className.val.splitOn "."
          let moduleDir := components.foldl (· / ·) baseDir
          let f : SourceRange → ResolvedAnn := fun sr => { sr, info := .irrelevant }
          let (subCtx, _) ← resolveModuleComponent fieldName.val moduleDir f
          match subCtx[fieldId]? with
          | some (.variable ty) => pure (some ty)
          | _ => pure none
        | _ => pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- Resolve one imported class method from its raw AST on demand. Extracts the
    FuncSig, resolves the method body, records the resolved FunctionDef into
    `demandedMethods` and the owning class into `demandedClasses` for the
    pipeline to translate. Memoized by qualified name. -/
partial def resolveMethodAstSig (ctx : Ctx) (f : SourceRange → ResolvedAnn)
    (classId : PythonIdentifier) (fields : List (PythonIdentifier × PythonType))
    (mAst : PythonStmt) : ResolveM FuncSig := do
  match mAst with
  | .FunctionDef a mName mArgs body mDecs mReturns mTc mTypeParams =>
    let mId := PythonIdentifier.fromAst mName
    let qualName := s!"{classId.val}@{mName.val}"
    let sig ← extractFuncSig ctx f mId (some classId) mArgs mDecs.val mReturns body.val
    let st ← get
    unless st.demandedMethods.contains qualName do
      let (_, ann, rName, rArgs, rBody, rDecs, rRets, rTc, rTps) ←
        resolveFuncDef ctx f sig a mName mArgs body mDecs mReturns mTc mTypeParams
      let resolvedStmt : ResolvedPythonStmt := .FunctionDef ann rName rArgs rBody rDecs rRets rTc rTps
      modify fun s => { s with
        demandedMethods := s.demandedMethods.insert qualName resolvedStmt
        demandedClasses := s.demandedClasses.insert classId.val (classId, fields) }
    pure sig
  | _ =>
    pure { name := PythonIdentifier.builtin "?", className := some classId, params := .static {required := [], optional := [], kwonly := []}, returnType := anyType, locals := [] }

/-- Resolve one imported top-level function / overload from its raw AST on demand.
    Records the resolved FunctionDef into `demandedFunctions` under its
    disambiguated Laurel name. Memoized. -/
partial def resolveFunctionAstSig (ctx : Ctx) (f : SourceRange → ResolvedAnn)
    (sig : FuncSig) (fAst : PythonStmt) : ResolveM Unit := do
  match fAst with
  | .FunctionDef a fName fArgs body fDecs fReturns fTc fTypeParams =>
    let key := sig.laurelName.text
    let st ← get
    unless st.demandedFunctions.contains key do
      let (_, ann, rName, rArgs, rBody, rDecs, rRets, rTc, rTps) ←
        resolveFuncDef ctx f sig a fName fArgs body fDecs fReturns fTc fTypeParams
      -- Re-annotate the FunctionDef with the disambiguated sig so Translation emits client$N
      let ann' : ResolvedAnn := { ann with info := .funcDecl sig }
      let resolvedStmt : ResolvedPythonStmt := .FunctionDef ann' rName rArgs rBody rDecs rRets rTc rTps
      modify fun s => { s with demandedFunctions := s.demandedFunctions.insert key resolvedStmt }
  | _ => pure ()

/-- Resolves `receiver.method(...)` calls. Monadic: uses `typeOfExpr` which may
    trigger demand-driven module loads. -/
partial def resolveMethodCall (ctx : Ctx) (receiver : PythonExpr) (methodName : Ann String SourceRange) (callArgs : Array PythonExpr := #[]) : ResolveM NodeInfo := do
  let methId := PythonIdentifier.fromAst methodName
  let f : SourceRange → ResolvedAnn := fun sr => { sr, info := .irrelevant }
  match ← typeOfExpr ctx receiver with
  | some (.Name _ className _) =>
    let classId := PythonIdentifier.fromAst className
    match ctx[classId]? with
    | some (.class_ classId fields methods methodAsts) =>
      match methods.find? (fun (mName, _) => mName == methId) with
      | some (_, sig) => pure (.funcCall sig)
      | none => match methodAsts.find? (fun (mName, _) => mName == methId) with
        | some (_, mAst) => do
          let sig ← resolveMethodAstSig ctx f classId fields mAst
          pure (.funcCall sig)
        | none => pure .unresolved
    | _ => pure .unresolved
  | some (.Attribute _ (.Name _ modName _) clsName _) =>
    -- Qualified class type (e.g. boto3.S3): chase module → class, resolve method on demand
    let modId := PythonIdentifier.fromAst modName
    let baseDir ← read
    -- Load the submodule `mod/cls` (e.g. boto3/S3) to find the class.
    let (subCtx, _) ← resolveModuleComponent clsName.val (baseDir / modName.val) f
    match subCtx[PythonIdentifier.fromAst clsName]? with
    | some (.class_ classId fields methods methodAsts) =>
      match methods.find? (fun (mName, _) => mName == methId) with
      | some (_, sig) => pure (.funcCall sig)
      | none => match methodAsts.find? (fun (mName, _) => mName == methId) with
        | some (_, mAst) => do
          let sig ← resolveMethodAstSig subCtx f classId fields mAst
          pure (.funcCall sig)
        | none => pure .unresolved
    | _ =>
      -- Fall back: maybe the name is a class directly in the parent module's ctx
      match ctx[modId]? with
      | some (.module_ moduleRaw) =>
        let moduleCtx : Ctx := moduleRaw.fold (fun c k v => c.insert k v) {}
        match moduleCtx[PythonIdentifier.fromAst clsName]? with
        | some (.class_ classId fields methods methodAsts) =>
          match methods.find? (fun (mName, _) => mName == methId) with
          | some (_, sig) => pure (.funcCall sig)
          | none => match methodAsts.find? (fun (mName, _) => mName == methId) with
            | some (_, mAst) => do
              let sig ← resolveMethodAstSig moduleCtx f classId fields mAst
              pure (.funcCall sig)
            | none => pure .unresolved
        | _ => pure .unresolved
      | _ => pure .unresolved
  | _ => match receiver with
    | .Name _ rName _ =>
      let rId := PythonIdentifier.fromAst rName
      match ctx[rId]? with
      | some (.module_ moduleRaw) =>
        let moduleCtx : Ctx := moduleRaw.fold (fun c k v => c.insert k v) {}
        match moduleCtx[methId]? with
        | some (.function sig) => pure (.funcCall sig)
        | some (.overloadedFunction overloads) =>
          let matched := overloads.find? fun (_, olSig, _) =>
            matchOverload olSig callArgs
          match matched with
          | some (idx, sig, astOpt) => do
            let sig' := { sig with overloadIndex := some idx }
            match astOpt with
            | some fAst => resolveFunctionAstSig moduleCtx f sig' fAst
            | none => pure ()
            pure (.funcCall sig')
          | none => pure .unresolved
        | some (.class_ cId fields methods methodAsts) =>
          let initId := PythonIdentifier.builtin "__init__"
          match methods.find? (fun (mName, _) => mName == initId) with
          | some (_, sig) => pure (.classNew cId sig)
          | none => match methodAsts.find? (fun (mName, _) => mName == initId) with
            | some (_, mAst) => do
              let sig ← resolveMethodAstSig moduleCtx f cId fields mAst
              pure (.classNew cId sig)
            | none =>
              let emptySig : FuncSig := { name := initId, className := some cId, params := .static {required := [], optional := [], kwonly := []}, returnType := anyType, locals := [] }
              pure (.classNew cId emptySig)
        | _ => pure .unresolved
      | _ => pure .unresolved
    | _ => pure .unresolved

/-- Load a module component from disk and resolve it. Tries `dir/name.python.st.ion`
    then `dir/name/__init__.python.st.ion`. Returns the module's resolved program and Ctx. -/
partial def resolveModuleComponent (name : String) (dir : System.FilePath) (f : SourceRange → ResolvedAnn) : ResolveM (Ctx × ResolvedPythonProgram) := do
  let ionPath := dir / (name ++ ".python.st.ion")
  let initPath := dir / name / "__init__.python.st.ion"
  let key := ionPath.toString
  let state ← get
  if let some cachedCtx := state.resolvedPaths[key]? then
    return (cachedCtx, { stmts := #[], moduleLocals := [] })
  let loadResult ← do
    match ← (Python.readPythonStrata ionPath.toString).toBaseIO with
    | .ok stmts => pure (some (ionPath, stmts))
    | .error _ =>
      match ← (Python.readPythonStrata initPath.toString).toBaseIO with
      | .ok stmts => pure (some (initPath, stmts))
      | .error _ => pure none
  match loadResult with
  | some (_, stmts) =>
    -- Index-only scan: top-level functions resolved eagerly (few, needed for overload
    -- matching); class methods stored as raw ASTs for on-demand resolution; TypedDicts
    -- and other assignments skipped. Avoids folding over thousands of irrelevant stmts.
    let mut ctx : Ctx := builtinContext
    for stmt in stmts do
      match stmt with
      | .FunctionDef _ fname fargs fbody fdecs freturns _ _ =>
        let nameId := PythonIdentifier.fromAst fname
        if hasOverloadDecorator fdecs.val then
          let overloads := match ctx[nameId]? with
            | some (.overloadedFunction existing) => existing
            | _ => []
          let idx := overloads.length
          let sig ← extractFuncSig ctx f nameId none fargs fdecs.val freturns fbody.val
          ctx := ctx.insert nameId (.overloadedFunction (overloads ++ [(idx, sig, some stmt)]))
        else
          match ctx[nameId]? with
          | some (.overloadedFunction _) => pure ()  -- impl stub after overloads, keep overloads
          | _ =>
            let sig ← extractFuncSig ctx f nameId none fargs fdecs.val freturns fbody.val
            ctx := ctx.insert nameId (.function sig)
      | .ClassDef _ cname _ _ cbody _ _ =>
        let classId := PythonIdentifier.fromAst cname
        let fields := cbody.val.toList.filterMap fun s => match s with
          | .AnnAssign _ (.Name _ n _) annotation _ _ => some (PythonIdentifier.fromAst n, annotation)
          | _ => none
        let methodAsts := cbody.val.toList.filterMap fun s => match s with
          | .FunctionDef _ mName _ _ _ _ _ _ => some (PythonIdentifier.fromAst mName, s)
          | .AsyncFunctionDef _ mName _ _ _ _ _ _ => some (PythonIdentifier.fromAst mName, s)
          | _ => none
        ctx := ctx.insert classId (.class_ classId fields [] methodAsts)
      | _ => pure ()  -- TypedDicts, assignments, imports — not needed by callers
    modify fun s => { s with resolvedPaths := s.resolvedPaths.insert key ctx }
    pure (ctx, { stmts := #[], moduleLocals := [] })
  | none => pure ({}, { stmts := #[], moduleLocals := [] })

/-- Resolve a dotted module name (e.g. "boto3.AccessAnalyzer") by converting dots to path
    separators and loading the final component. -/
partial def resolveModule (dottedName : String) (dir : System.FilePath) (f : SourceRange → ResolvedAnn) : ResolveM (Ctx × ResolvedPythonProgram) := do
  let components := dottedName.splitOn "."
  let moduleDir := components.dropLast.foldl (· / ·) dir
  match components.getLast? with
  | some name => resolveModuleComponent name moduleDir f
  | none => pure ({}, { stmts := #[], moduleLocals := [] })

/-- The core statement resolver. Threads the context as accumulator:
    - `FunctionDef`/`AsyncFunctionDef` → reuses existing sig from ctx if already registered
      (e.g., by ClassDef's pre-scan), otherwise extracts fresh. Annotates with `.funcDecl`.
    - `ClassDef` → pre-scans body for fields and methods, registers class in ctx with full
      method list, resolves body in classCtx (self typed as class, methods visible).
    - `Import`/`ImportFrom` → extends ctx with module or imported names.
    - `Assign`/`AnnAssign` → extends ctx with assigned names.
    - `AugAssign` → annotates with operator sig (`.funcCall`) for Translation.
    - Control flow → resolves sub-blocks in current ctx (no ctx extension from if/for/while). -/
partial def resolveStmt (ctx : Ctx) (f : SourceRange → ResolvedAnn) (s : PythonStmt) : ResolveM (Ctx × ResolvedPythonStmt) := do
  match s with
  | .FunctionDef a name args body decorators returns tc typeParams =>
      let nameId := PythonIdentifier.fromAst name
      if hasOverloadDecorator decorators.val then
        let sig ← extractFuncSig ctx f nameId none args decorators.val returns body.val
        let overloads := match ctx[nameId]? with
          | some (.overloadedFunction existing) => existing
          | _ => []
        let idx := overloads.length
        let ctx' := ctx.insert nameId (.overloadedFunction (overloads ++ [(idx, sig, none)]))
        let (_, ann, rName, rArgs, rBody, rDecs, rRets, rTc, rTps) ←
          resolveFuncDef ctx f sig a name args body decorators returns tc typeParams
        return (ctx', .FunctionDef ann rName rArgs rBody rDecs rRets rTc rTps)
      else
        match ctx[nameId]? with
        | some (.overloadedFunction _) =>
          -- Non-@overload def after overloads = implementation stub. Keep the overload list.
          let sig ← extractFuncSig ctx f nameId none args decorators.val returns body.val
          let (_, ann, rName, rArgs, rBody, rDecs, rRets, rTc, rTps) ←
            resolveFuncDef ctx f sig a name args body decorators returns tc typeParams
          return (ctx, .FunctionDef ann rName rArgs rBody rDecs rRets rTc rTps)
        | _ =>
          let sig ← match ctx[nameId]? with
            | some (.function existingSig) => pure existingSig
            | _ => extractFuncSig ctx f nameId none args decorators.val returns body.val
          let (ctx', ann, rName, rArgs, rBody, rDecs, rRets, rTc, rTps) ←
            resolveFuncDef ctx f sig a name args body decorators returns tc typeParams
          return (ctx', .FunctionDef ann rName rArgs rBody rDecs rRets rTc rTps)
  | .AsyncFunctionDef a name args body decorators returns tc typeParams =>
      let nameId := PythonIdentifier.fromAst name
      let sig ← match ctx[nameId]? with
        | some (.function existingSig) => pure existingSig
        | _ => extractFuncSig ctx f nameId none args decorators.val returns body.val
      let (ctx', ann, rName, rArgs, rBody, rDecs, rRets, rTc, rTps) ←
        resolveFuncDef ctx f sig a name args body decorators returns tc typeParams
      return (ctx', .AsyncFunctionDef ann rName rArgs rBody rDecs rRets rTc rTps)
  | .ClassDef a name bases keywords body decorators typeParams =>
      let classId := PythonIdentifier.fromAst name
      let classType : PythonType := .Name SourceRange.none ⟨SourceRange.none, name.val⟩ (.Load SourceRange.none)
      let fields := body.val.toList.filterMap fun s => match s with
        | .AnnAssign _ (.Name _ n _) annotation _ _ => some (PythonIdentifier.fromAst n, annotation)
        | _ => Option.none
      let mut methods : List (PythonIdentifier × FuncSig) := []
      for s in body.val.toList do
        match s with
        | .FunctionDef _ mName mArgs ⟨_, mBody⟩ mDecs mReturns _ _ =>
            let mId := PythonIdentifier.fromAst mName
            let sig ← extractFuncSig ctx f mId (some classId) mArgs mDecs.val mReturns mBody
            methods := methods ++ [(mId, sig)]
        | .AsyncFunctionDef _ mName mArgs ⟨_, mBody⟩ mDecs mReturns _ _ =>
            let mId := PythonIdentifier.fromAst mName
            let sig ← extractFuncSig ctx f mId (some classId) mArgs mDecs.val mReturns mBody
            methods := methods ++ [(mId, sig)]
        | _ => pure ()
      let ctx' := ctx.insert classId (CtxEntry.class_ classId fields methods)
      let classCtx := ctx'.insert (PythonIdentifier.fromAst ⟨SourceRange.none, "self"⟩) (CtxEntry.variable classType)
      let classCtx := methods.foldl (fun c (mId, mSig) => c.insert mId (CtxEntry.function mSig)) classCtx
      let methodSigs := methods.map (·.2)
      let resolvedBody ← resolveBlock classCtx f body.val
      let mut rBases : Array ResolvedPythonExpr := #[]
      for b in bases.val do rBases := rBases.push (← resolveExpr ctx' f b)
      let mut rKeywords : Array (Python.keyword ResolvedAnn) := #[]
      for kw in keywords.val do rKeywords := rKeywords.push (← resolveKeyword ctx' f kw)
      let mut rDecorators : Array ResolvedPythonExpr := #[]
      for d in decorators.val do rDecorators := rDecorators.push (← resolveExpr ctx' f d)
      let mut rTypeParams : Array (Python.type_param ResolvedAnn) := #[]
      for tp in typeParams.val do rTypeParams := rTypeParams.push (← resolveTypeParam ctx' f tp)
      return (ctx', .ClassDef { sr := a, info := .classDecl classId fields methodSigs } (mapAnnVal f name)
        ⟨f bases.ann, rBases⟩
        ⟨f keywords.ann, rKeywords⟩
        ⟨f body.ann, resolvedBody⟩
        ⟨f decorators.ann, rDecorators⟩
        ⟨f typeParams.ann, rTypeParams⟩)
  | .Import a aliases => do
      let baseDir ← read
      let mut ctx' := ctx
      for alias in aliases.val do
        match alias with
        | .mk_alias _ modName asName =>
          let registeredId := match asName.val with
            | some aliasName => PythonIdentifier.fromAst aliasName
            | none => PythonIdentifier.fromImport modName
          let (moduleCtx, _) ← resolveModule modName.val baseDir f
          ctx' := ctx'.insert registeredId (CtxEntry.module_ moduleCtx.inner.inner)
      return (ctx', .Import (f a) (mapAnnArr f (resolveAlias f) aliases))
  | .ImportFrom a modName imports level => do
      let baseDir ← read
      let mut ctx' := ctx
      match modName.val with
      | some modAnn =>
        let (moduleCtx, _) ← resolveModule modAnn.val baseDir f
        for imp in imports.val do
          match imp with
          | .mk_alias _ impName asName =>
            let registeredId := match asName.val with
              | some aliasName => PythonIdentifier.fromAst aliasName
              | none => PythonIdentifier.fromAst impName
            match ctx'[registeredId]? with
            | some _ => pure ()
            | none =>
              let impId := PythonIdentifier.fromAst impName
              match moduleCtx[impId]? with
              | some entry => ctx' := ctx'.insert registeredId entry
              | none => ctx' := ctx'.insert registeredId CtxEntry.unresolved
      | none =>
        for imp in imports.val do
          match imp with
          | .mk_alias _ impName asName =>
            let registeredId := match asName.val with
              | some aliasName => PythonIdentifier.fromAst aliasName
              | none => PythonIdentifier.fromAst impName
            match ctx'[registeredId]? with
            | some _ => pure ()
            | none => ctx' := ctx'.insert registeredId CtxEntry.unresolved
      return (ctx', .ImportFrom (f a) (mapAnnOpt f (mapAnnVal f) modName) (mapAnnArr f (resolveAlias f) imports) (mapAnnOpt f (resolveInt f) level))
  | .Assign a targets value tc => do
      let newNames := targets.val.toList.flatMap collectNamesFromTarget
      let ctx' := newNames.foldl (fun c n => c.insert n (CtxEntry.variable (annotationToPythonType Option.none))) ctx
      let mut rTargets : Array ResolvedPythonExpr := #[]
      for t in targets.val do rTargets := rTargets.push (← resolveExpr ctx f t)
      let rValue ← resolveExpr ctx f value
      return (ctx', .Assign (f a) ⟨f targets.ann, rTargets⟩ rValue (mapAnnOpt f (mapAnnVal f) tc))
  | .AnnAssign a target ann value simple => do
      let newNames := collectNamesFromTarget target
      let rTarget ← resolveExpr ctx f target
      let rAnn ← resolveExpr ctx f ann
      let rValue ← match value.val with
        | some v => pure (some (← resolveExpr ctx f v))
        | none => pure none
      -- Prefer the RHS call's resolved return type (e.g. boto3.S3) over the bare
      -- written annotation (e.g. S3), so method calls on the variable resolve
      -- through the module and demand the class.
      let varTy : PythonType := match rValue with
        | some (.Call { info := .funcCall sig, .. } ..) => sig.returnType
        | _ => ann
      let ctx' := newNames.foldl (fun c n => c.insert n (CtxEntry.variable varTy)) ctx
      return (ctx', .AnnAssign (f a) rTarget rAnn ⟨f value.ann, rValue⟩ (resolveInt f simple))
  | .AugAssign a target op value => do
      let opSig : FuncSig := { name := .builtin (operatorToLaurel op), className := none, params := .static {required := [(.builtin "left", anyType), (.builtin "right", anyType)], optional := [], kwonly := []}, returnType := anyType, locals := [] }
      let rTarget ← resolveExpr ctx f target
      let rValue ← resolveExpr ctx f value
      return (ctx, .AugAssign { sr := a, info := .funcCall opSig } rTarget (resolveOperator f op) rValue)
  | .If a test body orelse => do
      let rTest ← resolveExpr ctx f test
      let rBody ← resolveBlock ctx f body.val
      let rElse ← resolveBlock ctx f orelse.val
      return (ctx, .If (f a) rTest ⟨f body.ann, rBody⟩ ⟨f orelse.ann, rElse⟩)
  | .For a target iter body orelse tc => do
      let rTarget ← resolveExpr ctx f target
      let rIter ← resolveExpr ctx f iter
      let rBody ← resolveBlock ctx f body.val
      let rElse ← resolveBlock ctx f orelse.val
      return (ctx, .For (f a) rTarget rIter ⟨f body.ann, rBody⟩ ⟨f orelse.ann, rElse⟩ (mapAnnOpt f (mapAnnVal f) tc))
  | .AsyncFor a target iter body orelse tc => do
      let rTarget ← resolveExpr ctx f target
      let rIter ← resolveExpr ctx f iter
      let rBody ← resolveBlock ctx f body.val
      let rElse ← resolveBlock ctx f orelse.val
      return (ctx, .AsyncFor (f a) rTarget rIter ⟨f body.ann, rBody⟩ ⟨f orelse.ann, rElse⟩ (mapAnnOpt f (mapAnnVal f) tc))
  | .While a test body orelse => do
      let rTest ← resolveExpr ctx f test
      let rBody ← resolveBlock ctx f body.val
      let rElse ← resolveBlock ctx f orelse.val
      return (ctx, .While (f a) rTest ⟨f body.ann, rBody⟩ ⟨f orelse.ann, rElse⟩)
  | .Try a body handlers orelse finalbody => do
      let rBody ← resolveBlock ctx f body.val
      let mut rHandlers : Array (Python.excepthandler ResolvedAnn) := #[]
      for h in handlers.val do
        rHandlers := rHandlers.push (← resolveExcepthandler ctx f h)
      let rElse ← resolveBlock ctx f orelse.val
      let rFinally ← resolveBlock ctx f finalbody.val
      return (ctx, .Try (f a) ⟨f body.ann, rBody⟩ ⟨f handlers.ann, rHandlers⟩ ⟨f orelse.ann, rElse⟩ ⟨f finalbody.ann, rFinally⟩)
  | .TryStar a body handlers orelse finalbody => do
      let rBody ← resolveBlock ctx f body.val
      let mut rHandlers : Array (Python.excepthandler ResolvedAnn) := #[]
      for h in handlers.val do
        rHandlers := rHandlers.push (← resolveExcepthandler ctx f h)
      let rElse ← resolveBlock ctx f orelse.val
      let rFinally ← resolveBlock ctx f finalbody.val
      return (ctx, .TryStar (f a) ⟨f body.ann, rBody⟩ ⟨f handlers.ann, rHandlers⟩ ⟨f orelse.ann, rElse⟩ ⟨f finalbody.ann, rFinally⟩)
  | .With a items body tc => do
      let mut rItems : Array (Python.withitem ResolvedAnn) := #[]
      for item in items.val do rItems := rItems.push (← resolveWithitem ctx f item)
      let rBody ← resolveBlock ctx f body.val
      return (ctx, .With (f a) ⟨f items.ann, rItems⟩ ⟨f body.ann, rBody⟩ (mapAnnOpt f (mapAnnVal f) tc))
  | .AsyncWith a items body tc => do
      let mut rItems : Array (Python.withitem ResolvedAnn) := #[]
      for item in items.val do rItems := rItems.push (← resolveWithitem ctx f item)
      let rBody ← resolveBlock ctx f body.val
      return (ctx, .AsyncWith (f a) ⟨f items.ann, rItems⟩ ⟨f body.ann, rBody⟩ (mapAnnOpt f (mapAnnVal f) tc))
  | .Return a value => do
      let rValue ← match value.val with
        | some v => pure (some (← resolveExpr ctx f v))
        | none => pure none
      return (ctx, .Return (f a) ⟨f value.ann, rValue⟩)
  | .Delete a targets => do
      let mut rTargets : Array ResolvedPythonExpr := #[]
      for t in targets.val do rTargets := rTargets.push (← resolveExpr ctx f t)
      return (ctx, .Delete (f a) ⟨f targets.ann, rTargets⟩)
  | .Raise a exc cause => do
      let rExc ← match exc.val with
        | some e => pure (some (← resolveExpr ctx f e))
        | none => pure none
      let rCause ← match cause.val with
        | some e => pure (some (← resolveExpr ctx f e))
        | none => pure none
      return (ctx, .Raise (f a) ⟨f exc.ann, rExc⟩ ⟨f cause.ann, rCause⟩)
  | .Assert a test msg => do
      let rTest ← resolveExpr ctx f test
      let rMsg ← match msg.val with
        | some m => pure (some (← resolveExpr ctx f m))
        | none => pure none
      return (ctx, .Assert (f a) rTest ⟨f msg.ann, rMsg⟩)
  | .Expr a value => do
      let rValue ← resolveExpr ctx f value
      return (ctx, .Expr (f a) rValue)
  | .Pass a => return (ctx, .Pass (f a))
  | .Break a => return (ctx, .Break (f a))
  | .Continue a => return (ctx, .Continue (f a))
  | .Global a names => return (ctx, .Global (f a) (mapAnnArr f (mapAnnVal f) names))
  | .Nonlocal a names => return (ctx, .Nonlocal (f a) (mapAnnArr f (mapAnnVal f) names))
  | .Match a subject cases => do
      let rSubject ← resolveExpr ctx f subject
      let mut resolvedCases : Array (Python.match_case ResolvedAnn) := #[]
      for c in cases.val do
        resolvedCases := resolvedCases.push (← resolveMatchCase ctx f c)
      return (ctx, .Match (f a) rSubject ⟨f cases.ann, resolvedCases⟩)
  | .TypeAlias a name typeParams value => do
      let rName ← resolveExpr ctx f name
      let mut rTypeParams : Array (Python.type_param ResolvedAnn) := #[]
      for tp in typeParams.val do rTypeParams := rTypeParams.push (← resolveTypeParam ctx f tp)
      let rValue ← resolveExpr ctx f value
      return (ctx, .TypeAlias (f a) rName ⟨f typeParams.ann, rTypeParams⟩ rValue)
end

/-- Result of resolving a program: the resolved AST plus the imported
    declarations the program demanded (methods, functions, classes). -/
structure ResolveResult where
  program : ResolvedPythonProgram
  /-- Resolved FunctionDef stmts for demanded imported methods + top-level functions. -/
  demandedStmts : Array ResolvedPythonStmt
  /-- Demanded imported classes (id × fields) for Composite type emission. -/
  demandedClasses : List (PythonIdentifier × List (PythonIdentifier × PythonType))

/-- Entry point: resolves a full Python module. Folds `resolveStmt` over top-level
    statements, threading the context. Imports are loaded on demand. -/
def resolve (stmts : PythonProgram) (baseDir : System.FilePath := ".") : EIO String ResolveResult := do
  let f : SourceRange → ResolvedAnn := fun sr => { sr, info := .irrelevant }
  let moduleLocals := computeLocals stmts []
  let initCtx := moduleLocals.foldl (fun c (n, ty) => c.insert n (CtxEntry.variable ty)) builtinContext
  let action : ResolveM ResolvedPythonProgram := do
    let mut ctx := initCtx
    let mut resolved : Array ResolvedPythonStmt := #[]
    for stmt in stmts do
      let (ctx', r) ← resolveStmt ctx f stmt
      ctx := ctx'
      resolved := resolved.push r
    return { stmts := resolved, moduleLocals := moduleLocals }
  let (prog, state) ← action.run baseDir |>.run {}
  let demandedStmts := (state.demandedMethods.toList.map (·.2) ++ state.demandedFunctions.toList.map (·.2)).toArray
  let demandedClasses := state.demandedClasses.toList.map (·.2)
  return { program := prog, demandedStmts, demandedClasses }

end -- public section
end Strata.Python.Resolution
