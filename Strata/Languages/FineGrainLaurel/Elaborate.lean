/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.FineGrainLaurel.FineGrainLaurel
public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.HeapParameterizationConstants
public import Strata.Languages.Laurel.CoreDefinitionsForLaurel

/-!
# Pass 3: Elaboration

Elaboration transforms Laurel programs (impure CBV, effects implicit) into
Laurel programs where effects are explicit via calling conventions. The
theoretical foundation is **Fine-Grain Call-By-Value** (FGCBV) with graded
effects and bidirectional typing.

## Why FGCBV?

In plain CBV, every expression can have effects. You cannot tell by looking
at `f(x, g(y))` whether `g(y)` allocates, throws, or is pure. This matters
for verification because the calling convention depends on it: a pure call
returns a value directly; an effectful call returns through output parameters
(heap, error status).

FGCBV separates **values** (pure, duplicable) from **producers** (effectful,
sequenced). A producer must be explicitly sequenced — this makes the
elaborator syntax-directed. At every point, the structure of the term tells
you whether you are looking at a value or a producer.

## Bidirectional Typing

The elaborator has three mutually recursive functions:

- `synthValue`: value synthesis — literals, variables, pure calls, field access
- `checkValue`: value checking — synthesize then coerce (the ONE place subsumption lives)
- `checkProducer`: producer checking — if, while, assign, block, exit, assert, etc.

Values synthesize their types bottom-up. Producers are checked against an
ambient grade and output type top-down. The mode discipline guarantees
deterministic choices at every point.

## Graded Effects

Each producer carries a grade from `{pure, proc, err, heap, heapErr}`. The
grade determines the calling convention (extra heap parameters, error outputs).
Grade inference proceeds by coinduction over the call graph: try each grade
from `pure` upward, the first that succeeds is the procedure's grade.

## Two Passes

1. **Grade inference** (coinductive fixpoint): for each user procedure, find
   the minimal grade at which elaboration succeeds.
2. **Term production**: elaborate each procedure at its inferred grade,
   project the FGCBV term back to Laurel statements.
-/

namespace Strata.FineGrainLaurel
open Strata.Laurel
open StrataDDM  -- for `Decimal` (used by FGLValue.litDecimal), as LaurelAST does
public section

/-! ## Internal Types

Elaboration builds its own environment from `Laurel.Program` declarations.
Ideally call sites would carry callee signatures directly (no lookup needed),
but the Laurel AST uses string-named `StaticCall` nodes. -/

/-- Elaboration's internal function signature (built from Laurel.Procedure declarations). -/
structure FuncSig where
  /-- Procedure name (string, matching StaticCall callee names). -/
  name : String
  /-- Input parameters as (name, type) pairs. -/
  params : List (String × HighType)
  /-- Return type (first non-error output). -/
  returnType : HighType

instance : Inhabited FuncSig where
  default := { name := "", params := [], returnType := .TCore "Any" }

/-- What a name resolves to in Elaboration's type environment. -/
inductive NameInfo where
  /-- A callable procedure with its signature. -/
  | function (sig : FuncSig)
  /-- A variable binding with its type. -/
  | variable (ty : HighType)

instance : Inhabited NameInfo where
  default := .variable (.TCore "Any")

/-- The typing environment: maps names to their info and class names to field lists. -/
structure ElabTypeEnv where
  /-- All known names (procedures, variables, datatype constructors). -/
  names : Std.HashMap String NameInfo := {}
  /-- Class fields: class name -> list of (field name, field type). -/
  classFields : Std.HashMap String (List (String × HighType)) := {}
  deriving Inhabited

/-- Builds the type environment from a Laurel program's declarations. Scans all
    procedures (user + runtime) for signatures, all types for class fields. -/
def buildElabEnvFromProgram (program : Laurel.Program) (runtime : Laurel.Program := default) : ElabTypeEnv := Id.run do
  let mut names : Std.HashMap String NameInfo := {}
  let mut classFields : Std.HashMap String (List (String × HighType)) := {}
  for proc in program.staticProcedures ++ runtime.staticProcedures do
    let params := proc.inputs.map fun p => (p.name.text, p.type.val)
    let retTy := match proc.outputs.head? with
      | some o => o.type.val | none => HighType.TVoid
    names := names.insert proc.name.text (.function { name := proc.name.text, params, returnType := retTy })
  for td in program.types ++ runtime.types do
    match td with
    | .Composite ct =>
      let fields := ct.fields.map fun f => (f.name.text, f.type.val)
      classFields := classFields.insert ct.name.text fields
      -- Register the class as a callable constructor: CircularBuffer(args) → CircularBuffer
      let retTy := HighType.UserDefined { text := ct.name.text, uniqueId := none }
      names := names.insert ct.name.text (.function { name := ct.name.text, params := [], returnType := retTy })
    | .Datatype dt =>
      for ctor in dt.constructors do
        let ctorParams := ctor.args.map fun p => (p.name.text, p.type.val)
        let retTy := HighType.UserDefined { text := dt.name.text, uniqueId := none }
        names := names.insert ctor.name.text (.function { name := ctor.name.text, params := ctorParams, returnType := retTy })
    | .Constrained _ => pure ()
    | .Alias _ => pure ()
  { names, classFields }

def mkLaurel (md : Option FileRange) (e : StmtExpr) : StmtExprMd :=
  { val := e, source := md }
def mkHighTypeMd (md : Option FileRange) (ty : HighType) : HighTypeMd :=
  { val := ty, source := md }

/-! ## The Grade Monoid

Grades classify which effects a producer performs. The monoid structure
ensures compositionality: sequencing two producers joins their grades.
The left residual `d \ e` ("what grade remains for the continuation after
a call at grade `d` within ambient grade `e`") drives grade inference —
if `d \ e` is undefined (d > e), elaboration fails and the grade is
pushed upward. -/

/-- The effect grade lattice: pure < proc < {err, heap} < heapErr. -/
inductive Grade where
  /-- No effects. Value-level `staticCall`, no extra params. -/
  | pure
  /-- Effectful but no error or heap. Outputs: `[result]`. -/
  | proc
  /-- May throw. Outputs: `[result, maybe_except]`. -/
  | err
  /-- Reads/writes heap. Inputs: `[$heap]`. Outputs: `[$heap, result]`. -/
  | heap
  /-- Heap + error. Inputs: `[$heap]`. Outputs: `[$heap, result, maybe_except]`. -/
  | heapErr
  deriving Inhabited, BEq, Repr

/-- Join (least upper bound) of two grades. Sequencing two producers joins their grades. -/
def Grade.join : Grade → Grade → Grade
  | .pure, e => e | e, .pure => e
  | .proc, .proc => .proc
  | .proc, .err => .err | .err, .proc => .err
  | .proc, .heap => .heap | .heap, .proc => .heap
  | .proc, .heapErr => .heapErr | .heapErr, .proc => .heapErr
  | .err, .err => .err
  | .err, .heap => .heapErr | .heap, .err => .heapErr
  | .err, .heapErr => .heapErr | .heapErr, .err => .heapErr
  | .heap, .heap => .heap
  | .heap, .heapErr => .heapErr | .heapErr, .heap => .heapErr
  | .heapErr, .heapErr => .heapErr

/-- Left residual: `d\e` = grade for the continuation after a call at grade `d`
    within ambient grade `e`. Returns `none` if `d > e` (elaboration fails).

    Satisfies the residuation law for an idempotent semilattice:
    `d ⊔ x ≤ e` iff `x ≤ d\e`. Since `⊔` is idempotent (join),
    the largest `x` with `d ⊔ x ≤ e` is `e` itself (when `d ≤ e`).
    So `d\e = e` whenever `d ≤ e`, and undefined otherwise.
```
d\e = e    if d ≤ e
d\e = ⊥    otherwise
```
-/
def Grade.leftResidual : Grade → Grade → Option Grade
  | .pure, e => some e
  | .proc, e => if e == .pure then none else some e
  | .err, e => match e with | .err | .heapErr => some e | _ => none
  | .heap, e => match e with | .heap | .heapErr => some e | _ => none
  | .heapErr, .heapErr => some .heapErr
  | _, _ => none

/-! ## Type Erasure

Elaboration operates on `LowType` — the erased version of `HighType`.
User-defined types erase to `Composite` (they live on the heap). The
subtyping/coercion system operates on `LowType` values. -/

/-- The erased type system. User-defined types become `Composite` (heap-allocated).
    Subsumption and coercion operate on `LowType` values. -/
inductive LowType where
  /-- Machine integer. -/
  | TInt
  /-- Boolean. -/
  | TBool
  /-- String. -/
  | TString
  /-- 64-bit float. -/
  | TFloat64
  /-- Unit/void. -/
  | TVoid
  /-- Named core type (Any, Error, Heap, Composite, ListAny, DictStrAny, etc.). -/
  | TCore (name : String)
  /-- A user-defined class, name preserved. Erases to `Composite` for boxing/subtyping
      purposes (see `eraseForSubtype`), but kept distinct here so a `var self : Account`
      declaration round-trips back to `.UserDefined "Account"` — the kbd Laurel resolver
      resolves `self.field` via the receiver's static `.UserDefined` type, so collapsing
      every class to `Composite` would lose field resolution. -/
  | TUser (name : String)
  deriving Inhabited, Repr, BEq

/-- Type erasure: HighType -> LowType. Primitives map directly, user-defined classes
    keep their name (`.TUser`), unknown/complex types become Any. -/
def eraseType : HighType → LowType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n
  | .UserDefined id => match id.text with
    | "Any" => .TCore "Any" | "Error" => .TCore "Error"
    | "ListAny" => .TCore "ListAny" | "DictStrAny" => .TCore "DictStrAny"
    | "OptionInt" => .TCore "OptionInt"
    | "Box" => .TCore "Box" | "Field" => .TCore "Field" | "TypeTag" => .TCore "TypeTag"
    | _ => .TUser id.text
  | .TReal => .TCore "real"
  | .TSet _ | .TMap _ _ | .Applied _ _ | .Intersection _ | .Unknown
  | .TBv _ | .MultiValuedExpr _ => .TCore "Any"
  | .Pure _ => .TCore "Composite"

/-- Collapse a LowType to its subtyping/boxing representative: every user-defined class
    is `Composite` for the purposes of the `subtype` coercion table. -/
def eraseForSubtype : LowType → LowType
  | .TUser _ => .TCore "Composite"
  | other => other

/-- Inverse of erasure (partial): lifts a LowType back to HighType for env extension. -/
def liftType : LowType → HighType
  | .TUser name => .UserDefined { text := name, uniqueId := none }
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n

/-! ## FGL Terms

The intermediate representation between Laurel input and Laurel output.
Values are pure (can appear in any context). Producers are effectful
(must be sequenced). Every constructor carries source metadata so
provenance is preserved through elaboration. -/

abbrev Md := Option FileRange

/-- A pure value in the FGCBV intermediate term. Can appear in any context.
    Every constructor carries source metadata for provenance. -/
inductive FGLValue where
  /-- Integer literal. -/
  | litInt (md : Md) (n : Int)
  /-- Boolean literal. -/
  | litBool (md : Md) (b : Bool)
  /-- String literal. -/
  | litString (md : Md) (s : String)
  /-- Decimal/real literal (Python float). -/
  | litDecimal (md : Md) (d : Decimal)
  /-- Variable reference. -/
  | var (md : Md) (name : String)
  /-- Coercion: int → Any. -/
  | fromInt (md : Md) (inner : FGLValue)
  /-- Coercion: string → Any. -/
  | fromStr (md : Md) (inner : FGLValue)
  /-- Coercion: bool → Any. -/
  | fromBool (md : Md) (inner : FGLValue)
  /-- Coercion: float → Any. -/
  | fromFloat (md : Md) (inner : FGLValue)
  /-- Coercion: Composite → Any. -/
  | fromComposite (md : Md) (inner : FGLValue)
  /-- Coercion: ListAny → Any. -/
  | fromListAny (md : Md) (inner : FGLValue)
  /-- Coercion: DictStrAny → Any. -/
  | fromDictStrAny (md : Md) (inner : FGLValue)
  /-- Coercion: None → Any. -/
  | fromNone (md : Md)
  /-- Field access (pre-heap-resolution). -/
  | fieldAccess (md : Md) (obj : FGLValue) (field : String)
  /-- Pure function call. -/
  | staticCall (md : Md) (name : String) (args : List FGLValue)
  /-- Object creation (pre-heap-resolution). heapParameterizationPass allocates. -/
  | new (md : Md) (className : String)
  deriving Inhabited

def FGLValue.getMd : FGLValue → Md
  | .litInt md _ | .litBool md _ | .litString md _ | .litDecimal md _ | .var md _
  | .fromInt md _ | .fromStr md _ | .fromBool md _ | .fromFloat md _
  | .fromComposite md _ | .fromListAny md _ | .fromDictStrAny md _ | .fromNone md
  | .fieldAccess md _ _ | .staticCall md _ _ | .new md _ => md

/-- An effectful producer in the FGCBV intermediate term. Must be sequenced.
    Each form carries a continuation (`body`/`after`) — the CPS structure
    makes projection to Laurel statements trivial. -/
inductive FGLProducer where
  /-- Return a value (terminal — no continuation). -/
  | produce (md : Md) (v : FGLValue)
  /-- Assign to an existing variable, then continue. RHS is a producer whose
      resolved value is assigned to target. -/
  | assign (md : Md) (target : FGLValue) (val : FGLProducer) (body : FGLProducer)
  /-- Declare a local variable, then continue in extended scope. Init is a
      producer whose resolved value initializes the variable. -/
  | varDecl (md : Md) (name : String) (ty : LowType) (init : FGLProducer) (body : FGLProducer)
  /-- Conditional: check condition, branch, then continue after. -/
  | ifThenElse (md : Md) (cond : FGLValue) (thn : FGLProducer) (els : FGLProducer) (after : FGLProducer)
  /-- Loop: check condition, iterate body, then continue after. -/
  | whileLoop (md : Md) (cond : FGLValue) (body : FGLProducer) (after : FGLProducer)
  /-- Assert condition holds, then continue. -/
  | assert (md : Md) (cond : FGLValue) (body : FGLProducer)
  /-- Assume condition holds, then continue. -/
  | assume (md : Md) (cond : FGLValue) (body : FGLProducer)
  /-- Effectful call: bind outputs, then continue in extended scope. -/
  | procedureCall (md : Md) (callee : String) (args : List FGLValue)
      (outputs : List (String × LowType)) (body : FGLProducer)
  /-- Exit to enclosing labeled block (non-returning). -/
  | exit (md : Md) (label : String)
  /-- Labeled block: body may exit to label, then continue after. -/
  | labeledBlock (md : Md) (label : String) (body : FGLProducer) (after : FGLProducer)
  /-- Empty continuation (end of block). -/
  | skip
  deriving Inhabited

-- ═══════════════════════════════════════════════════════════════════════════════
-- Monad
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Reader environment for elaboration. Carries the type environment, program,
    runtime, inferred grades, and current procedure's input list (for hole args). -/
structure ElabEnv where
  /-- The typing context (names + class fields). -/
  typeEnv : ElabTypeEnv
  /-- The user program being elaborated. -/
  program : Laurel.Program
  /-- The runtime prelude (builtins, data structure operations). -/
  runtime : Laurel.Program := default
  /-- Inferred grades for all procedures. -/
  procGrades : Std.HashMap String Grade := {}
  /-- Current procedure's input params (used as hole arguments). -/
  procInputs : List (String × HighType) := []

/-- Mutable state for elaboration: fresh name counter and hole collector. -/
structure ElabState where
  /-- Counter for generating fresh variable names. -/
  freshCounter : Nat := 0
  /-- Hole functions used (emitted as opaque procedure declarations in output). -/
  usedHoles : List (String × Bool × HighType) := []

abbrev ElabM := ReaderT ElabEnv (StateT ElabState Option)

private def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }; pure s!"{pfx}${s.freshCounter}"


/-- Reads a runtime procedure's grade structurally from its signature: does it
    have a Heap input? An Error output? The combination determines the grade.
    User procedure grades are inferred by coinduction, not read from signature. -/
def gradeFromSignature (proc : Laurel.Procedure) : Grade :=
  -- Exceptions-only principle: heap is owned by heapParameterizationPass, so
  -- a runtime proc that takes a Heap input is just `.proc` (or `.err` if it can also throw).
  let hasError := proc.outputs.any fun o => eraseType o.type.val == .TCore "Error"
  match hasError with
  | true => .err
  | false => if proc.isFunctional then .pure else .proc

-- ═══════════════════════════════════════════════════════════════════════════════
-- Env helpers
-- ═══════════════════════════════════════════════════════════════════════════════

def lookupEnv (name : String) : ElabM NameInfo := do
  match (← read).typeEnv.names[name]? with | some info => pure info | none => failure
def extendEnv (name : String) (ty : HighType) (action : ElabM α) : ElabM α :=
  withReader (fun env => { env with typeEnv := { env.typeEnv with names := env.typeEnv.names.insert name (.variable ty) } }) action
def lookupFuncSig (name : String) : ElabM FuncSig := do
  match (← read).typeEnv.names[name]? with | some (.function sig) => pure sig | _ => failure
def lookupFieldType (className fieldName : String) : ElabM HighType := do
  match (← read).typeEnv.classFields[className]? with
  | some fields => match fields.find? (fun (n, _) => n == fieldName) with
    | some (_, ty) => pure ty
    | none => failure
  | none => failure

/-! ## HOAS Smart Constructors

These construct effectful call nodes using higher-order abstract syntax:
the continuation is a Lean function from fresh output variables to the
body producer. This ensures output variables are always correctly scoped
(extended in the environment before the body is elaborated). -/

def mkEffectfulCall (md : Md) (callee : String) (args : List FGLValue)
    (outputSpecs : List (String × HighType))
    (body : List FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let mut names : List String := []
  let mut lowOutputs : List (String × LowType) := []
  for (pfx, ty) in outputSpecs do
    let n ← freshVar pfx
    names := names ++ [n]
    lowOutputs := lowOutputs ++ [(n, eraseType ty)]
  let vars := names.map (FGLValue.var md)
  let cont ← names.zip (outputSpecs.map (·.2)) |>.foldr
    (fun (n, ty) acc => extendEnv n ty acc) (body vars)
  pure (.procedureCall md callee args lowOutputs cont)

def mkVarDecl (md : Md) (name : String) (ty : LowType) (init : FGLProducer)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let cont ← extendEnv name (liftType ty) (body (.var md name))
  pure (.varDecl md name ty init cont)

/-- Subgrading witness: `d ≤ e ↦ (pre, outs)`. Constructs a `procedureCall`
    with the correct calling convention based on grade.
```
d ≤ e ↦ (args_prepended, outputs_declared, resultIdx)

pure:     ([], [], —)                                  — value-level, no procedureCall
proc:     ([], [result:B], 0)
err:      ([], [result:B, except:Error], 0)
heap:     ([heap_var], [heap:Heap, result:B], 1)
heapErr:  ([heap_var], [heap:Heap, result:B, except:Error], 1)
```
-/
def mkGradedCall (md : Md) (callee : String) (args : List FGLValue)
    (declaredOutputs : List (String × HighType))
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  mkEffectfulCall md callee args declaredOutputs fun outs => do
    let resultVar := outs[0]?
    match resultVar with
    | some rv => body rv
    | none => body (.fromNone md)

/-! ## Subsumption

A subtyping judgment `A <= B` has a witness: a coercion function. Upward
coercions (T <= Any) are value constructors (boxing). Downward coercions
(Any <= T) are pure function calls (unboxing). `applySubtype` is called
ONLY from `checkValue` — this is the bidirectional discipline. -/

/-- The result of a subsumption check: identity (types equal), a coercion witness
    (function to apply), or unrelated (no subtyping relationship). -/
inductive CoercionResult where
  /-- Types are equal — no coercion needed. -/
  | refl
  /-- Subtyping holds — apply this coercion function. -/
  | coerce (w : Md → FGLValue → FGLValue)
  /-- No subtyping relationship. -/
  | unrelated
  deriving Inhabited

/-- Subtyping judgment `A ≤ B ↦ c` as a total case analysis: every `(A, B)` pair
is decided. `.refl` when `A = B`; `.coerce w` when Python implicitly converts
`A → B`, witnessed by one direct runtime function; `.unrelated` otherwise — a
deliberate verdict, never a forgotten case. `TCore` names outside the finite set
`eraseType` produces are `.unrelated` (sound default for an unknown type).
```
A ≤ A ↦ id  (reflexivity)

box   T ≤ Any:    TInt↦fromInt  TBool↦fromBool  TString↦fromStr  TFloat64↦fromFloat
                  Composite↦fromComposite  ListAny↦fromListAny
                  DictStrAny↦fromDictStrAny  TVoid↦fromNone
unbox Any ≤ T:    bool↦Any_to_bool  int↦as_int!  str↦as_string!  float↦as_float!
                  Composite↦as_Composite!  DictStrAny↦as_Dict!  ListAny↦as_ListAny!
truth T ≤ bool:   TInt↦int_to_bool  TString↦str_to_bool  TFloat64↦float_to_bool
                  ListAny↦list_to_bool  DictStrAny↦dict_to_bool
                  TVoid↦false  Composite↦true
num   bool≤int≤float: TBool↦int bool_to_int  TInt↦float int_to_real
                  TBool↦float bool_to_real
```
-/
def subtype (actual0 expected0 : LowType) : CoercionResult :=
  if actual0 == expected0 then .refl else
  -- Collapse user-defined classes to `Composite` for the coercion table: a class value
  -- boxes to Any exactly as a Composite does, and unboxes the same way. The distinct
  -- `.TUser` name only matters for var-decl projection / field resolution, not coercion.
  let actual := eraseForSubtype actual0
  let expected := eraseForSubtype expected0
  if actual == expected then .refl else match expected, actual with
  -- box: T ≤ Any
  | .TCore "Any", .TInt => .coerce (fun md => .fromInt md)
  | .TCore "Any", .TBool => .coerce (fun md => .fromBool md)
  | .TCore "Any", .TString => .coerce (fun md => .fromStr md)
  | .TCore "Any", .TFloat64 => .coerce (fun md => .fromFloat md)
  -- `eraseType .TReal = .TCore "real"` (Python floats are reals). Box real→Any via the
  -- same `from_float` (which takes a `real`), matching the .TFloat64 arm.
  | .TCore "Any", .TCore "real" => .coerce (fun md => .fromFloat md)
  | .TCore "Any", .TCore "Composite" => .coerce (fun md => .fromComposite md)
  | .TCore "Any", .TCore "ListAny" => .coerce (fun md => .fromListAny md)
  | .TCore "Any", .TCore "DictStrAny" => .coerce (fun md => .fromDictStrAny md)
  | .TCore "Any", .TVoid => .coerce (fun md _ => .fromNone md)
  | .TCore "Any", _ => .unrelated
  -- to bool: unbox from Any, else per-type truthiness
  | .TBool, .TCore "Any" => .coerce (fun md v => .staticCall md "Any_to_bool" [v])
  | .TBool, .TInt => .coerce (fun md v => .staticCall md "int_to_bool" [v])
  | .TBool, .TString => .coerce (fun md v => .staticCall md "str_to_bool" [v])
  | .TBool, .TFloat64 => .coerce (fun md v => .staticCall md "float_to_bool" [v])
  | .TBool, .TCore "ListAny" => .coerce (fun md v => .staticCall md "list_to_bool" [v])
  | .TBool, .TCore "DictStrAny" => .coerce (fun md v => .staticCall md "dict_to_bool" [v])
  | .TBool, .TVoid => .coerce (fun md _ => .litBool md false)
  | .TBool, .TCore "Composite" => .coerce (fun md _ => .litBool md true)
  | .TBool, _ => .unrelated
  -- to int: unbox from Any, else bool widening
  | .TInt, .TCore "Any" => .coerce (fun md v => .staticCall md "Any..as_int!" [v])
  | .TInt, .TBool => .coerce (fun md v => .staticCall md "bool_to_int" [v])
  | .TInt, _ => .unrelated
  -- to float: unbox from Any, else int/bool widening
  | .TFloat64, .TCore "Any" => .coerce (fun md v => .staticCall md "Any..as_float!" [v])
  | .TCore "real", .TCore "Any" => .coerce (fun md v => .staticCall md "Any..as_float!" [v])
  | .TFloat64, .TInt => .coerce (fun md v => .staticCall md "int_to_real" [v])
  | .TFloat64, .TBool => .coerce (fun md v => .staticCall md "bool_to_real" [v])
  | .TFloat64, _ => .unrelated
  -- to string: unbox from Any
  | .TString, .TCore "Any" => .coerce (fun md v => .staticCall md "Any..as_string!" [v])
  | .TString, _ => .unrelated
  -- to container/Composite: unbox from Any
  | .TCore "Composite", .TCore "Any" => .coerce (fun md v => .staticCall md "Any..as_Composite!" [v])
  | .TCore "DictStrAny", .TCore "Any" => .coerce (fun md v => .staticCall md "Any..as_Dict!" [v])
  | .TCore "ListAny", .TCore "Any" => .coerce (fun md v => .staticCall md "Any..as_ListAny!" [v])
  | _, _ => .unrelated

/-- Effects-only subsumption: the elaborator goes *untyped Laurel → effect-typed
    (FGCBV) Laurel*, threading EFFECTS (grades, via `leftResidual`), NOT value
    (box/unbox) coercions. The pure-type coercions are now inserted by the Laurel
    resolver's proof-relevant subtyping judgment (`coerce` + the frontend's
    `realizeCoercion`), which runs after elaboration. So `applySubtype` is the
    identity on values — it must NOT box/unbox, or the resolver would double-coerce
    (the elaborator and resolver are mutually exclusive coercers). `subtype` /
    `CoercionResult` remain as the reference the Python realizer is transcribed from. -/
def applySubtype (val : FGLValue) (_actual _expected : LowType) : FGLValue :=
  val

/-! ## The Translation ⟦·⟧ : Laurel → GFGL

Three functions: synthValue (⟦·⟧⇒ᵥ), checkValue (⟦·⟧⇐ᵥ), checkProducer (⟦·⟧⇐ₚ).
Entry point is checkProducer — every Laurel derivation maps to a GFGL producer.
synthValue/checkValue are internal helpers for building value sub-terms.
Producer synthesis (⟦·⟧⇒ₚ) is applied by inversion inside the call clause. -/

/-- Fetch the declared outputs of a proc from the runtime or user program. -/
private def lookupProcDeclaredOutputs (callee : String) : ElabM (List (String × HighType)) := do
  let env ← read
  let findProc (procs : List Laurel.Procedure) : Option Laurel.Procedure :=
    procs.find? (fun p => p.name.text == callee)
  match findProc env.runtime.staticProcedures with
  | some proc => pure (proc.outputs.map fun o => (o.name.text, o.type.val))
  | none => match findProc env.program.staticProcedures with
    | some proc => pure (proc.outputs.map fun o => (o.name.text, o.type.val))
    | none => failure

/-- Rewrite declared outputs for a given inferred grade: strip any existing Error
    output and re-add it for err/heapErr grades. Heap is owned by the downstream
    `heapParameterizationPass` — no `$heap` output is emitted here. -/
private def rewriteOutputsForGrade (declaredOutputs : List (String × HighType)) (g : Grade) : List (String × HighType) :=
  let resultOutputs := declaredOutputs.filter fun (_, ty) => eraseType ty != .TCore "Error"
  match g with
  | .err | .heapErr => resultOutputs ++ [("maybe_except", .TCore "Error")]
  | _ => resultOutputs

/-- Look up a proc's outputs rewritten for its inferred grade. -/
partial def lookupProcOutputs (callee : String) : ElabM (List (String × HighType)) := do
  let g := (← read).procGrades[callee]?.getD .pure
  let declared ← lookupProcDeclaredOutputs callee
  pure (rewriteOutputsForGrade declared g)

-- ═══════════════════════════════════════════════════════════════════════════════
-- The Translation ⟦·⟧ : Laurel → GFGL
--
-- Three functions: synthValue (⟦·⟧⇒ᵥ), checkValue (⟦·⟧⇐ᵥ), checkProducer (⟦·⟧⇐ₚ)
-- Entry point is checkProducer. synthValue/checkValue are internal helpers.
-- Producer synthesis (⟦·⟧⇒ₚ) is applied by inversion inside the call clause.
-- ═══════════════════════════════════════════════════════════════════════════════

mutual

/-- ⟦·⟧⇒ᵥ (literal):
```
D :: Γ ⊢ n : int   [lit]

    ↦

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ litInt n ⇒ TInt   [litInt]
```
(analogous for bool, string)
-/
partial def synthValueLiteral (md : Md) (expr : StmtExpr) : Option (FGLValue × HighType) :=
  match expr with
  | .LiteralInt n => some (.litInt md n, .TInt)
  | .LiteralBool b => some (.litBool md b, .TBool)
  | .LiteralString s => some (.litString md s, .TString)
  | .LiteralDecimal d => some (.litDecimal md d, .TReal)
  | _ => none

/-- ⟦·⟧⇒ᵥ (variable):
```
D :: Γ ⊢ x : A   [var, (x:A) ∈ Γ]

    ↦

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ var x ⇒ ⟦A⟧   [var, (x:⟦A⟧) ∈ ⟦Γ⟧]
```
-/
partial def synthValueVar (md : Md) (id : Identifier) : ElabM (FGLValue × HighType) := do
  match (← lookupEnv id.text) with
  | .variable ty => pure (.var md id.text, ty)
  | _ => failure

/-- ⟦·⟧⇒ᵥ (field access):
```
D :: Γ ⊢ obj.f : T   [fieldSelect]
└─ D_obj :: Γ ⊢ obj : C

    ↦    precondition: ($heap : Heap) ∈ ⟦Γ⟧

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ functionCall unbox_T [functionCall readField [$heap, V_obj, $field.C.f]] ⇒ ⟦T⟧   [functionCall]
└─ ⟦Γ⟧ ⊢ functionCall readField [$heap, V_obj, $field.C.f] ⇐ Box   [subsumption]
   ├─ ⟦Γ⟧ ⊢ functionCall readField [$heap, V_obj, $field.C.f] ⇒ Box   [functionCall]
   │  ├─ ⟦Γ⟧ ⊢ $heap ⇐ Heap   [subsumption]
   │  │  ├─ ⟦Γ⟧ ⊢ $heap ⇒ Heap   [var]
   │  │  └─ Heap ≤ Heap ↦ id
   │  ├─ ⟦D_obj⟧⇐ᵥ :: ⟦Γ⟧ ⊢ V_obj ⇐ Composite   [subsumption]
   │  │  ├─ ⟦D_obj⟧⇒ᵥ :: ⟦Γ⟧ ⊢ V_obj ⇒ Composite   (since ⟦C⟧ = Composite for user-defined C)
   │  │  └─ Composite ≤ Composite ↦ id
   │  └─ ⟦Γ⟧ ⊢ functionCall $field.C.f [] ⇐ Field   [subsumption]
   │     ├─ ⟦Γ⟧ ⊢ functionCall $field.C.f [] ⇒ Field   [functionCall]
   │     └─ Field ≤ Field ↦ id
   └─ Box ≤ Box ↦ id
```
-/
partial def synthValueFieldSelect (md : Md) (obj : StmtExprMd) (field : Identifier) : ElabM (FGLValue × HighType) := do
  let (ov, objTy) ← synthValue obj
  -- Synth rule for field access:  e ⇒ &{… l : A_l …}  ⊢  e.l ⇒ A_l ;  e ⇒ Any ⊢ e.l ⇒ Any.
  -- We trust the user's field annotations (the frontend's contract) and let the coercion
  -- mechanism reconcile A_l with whatever the use-site demands. The bare `.fieldAccess` is
  -- lowered by heapParameterizationPass to `Box..<A_l>Val!(readField …)`, which unboxes to
  -- exactly A_l — so synthesizing A_l here is faithful, not optimistic. `Any` is the genuine
  -- FALLTHROUGH: only when the receiver's type isn't a known composite (e.g. `self`/`Any`).
  let fieldTy ←
    match objTy with
    | .UserDefined cls =>
      match ← (do match (← read).typeEnv.classFields[cls.text]? with
                  | some fields => pure (fields.find? (fun (n, _) => n == field.text))
                  | none => pure none) with
      | some (_, ty) => pure ty
      | none => pure (.TCore "Any")
    | _ => pure (.TCore "Any")
  pure (.fieldAccess md ov field.text, fieldTy)

/-- ⟦·⟧⇒ᵥ (pure call):
```
D :: Γ ⊢ f(e₁,…,eₙ) : B   [call, f : (Aᵢ) → B & pure]
└─ D_i :: Γ ⊢ eᵢ : Aᵢ  (for each i)

    ↦

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ functionCall f [V₁,…,Vₙ] ⇒ ⟦B⟧   [functionCall]
└─ ⟦D_i⟧⇐ᵥ :: ⟦Γ⟧ ⊢ Vᵢ ⇐ ⟦Aᵢ⟧  (for each i)   [subsumption]
   ├─ ⟦D_i⟧⇒ᵥ :: ⟦Γ⟧ ⊢ Vᵢ ⇒ Bᵢ   (Bᵢ discovered by recursive synthValue)
   └─ Bᵢ ≤ ⟦Aᵢ⟧ ↦ cᵢ
```
-/
partial def synthValueStaticCall (md : Md) (callee : Identifier) (args : List StmtExprMd) : ElabM (FGLValue × HighType) := do
  -- A name carrying a function signature but no explicit procedure grade is pure:
  -- datatype constructors (from_None, from_int, ...) and pure runtime functions
  -- live in typeEnv.names but not in procGrades. Default to pure, as elaborateCall
  -- and lookupProcOutputs do; only a name graded above pure is rejected here.
  let g := (← read).procGrades[callee.text]?.getD .pure
  guard (g == .pure)
  let sig : FuncSig := match (← read).typeEnv.names[callee.text]? with
    | some (.function s) => s
    | _ => { name := callee.text, params := [], returnType := HighType.Unknown }
  let checkedArgs ← checkArgValues args sig.params
  pure (.staticCall md callee.text checkedArgs, sig.returnType)

/-- ⟦·⟧⇒ᵥ: Value synthesis. Dispatches to clause helpers. -/
partial def synthValue (expr : StmtExprMd) : ElabM (FGLValue × HighType) := do
  let md := expr.source
  match expr.val with
  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ =>
    match synthValueLiteral md expr.val with
    | some r => pure r
    | none => failure
  | .Var (.Local id) => synthValueVar md id
  | .Var (.Field obj field) => synthValueFieldSelect md obj field
  | .StaticCall callee args => synthValueStaticCall md callee args
  | _ => failure

/-- Helper: check a list of arguments as values against parameter types. -/
partial def checkArgValues (args : List StmtExprMd) (params : List (String × HighType)) : ElabM (List FGLValue) := do
  match args, params with
  | [], _ => pure []
  | arg :: rest, (_, pty) :: prest => do
    let v ← checkValue arg pty
    let vs ← checkArgValues rest prest
    pure (v :: vs)
  | _ :: _, [] => failure

/-- ⟦·⟧⇐ᵥ: Value checking. Synthesizes then applies subtyping coercion.
```
⟦D⟧⇐ᵥ (deterministic hole) :: ⟦Γ⟧ ⊢ functionCall hole_N [input₁,...,inputₖ] ⇐ ⟦A⟧   [functionCall]
└─ (hole_N : (⟦T₁⟧,...,⟦Tₖ⟧) → ⟦A⟧ & pure) ∈ ⟦Γ⟧
```
-/
partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let md := expr.source
  match expr.val with
  | .Hole _ _ =>
    -- A hole in pure value position (a contract, or an argument of a pure call)
    -- denotes a deterministic uninterpreted function of the procedure's inputs:
    -- nondeterminism is meaningless in a pure value, so even a hole Translation
    -- marked nondeterministic (e.g. an unresolved `re.search(...)` inside a
    -- `requires`) is elaborated here as the deterministic `hole_N(inputs)`. This
    -- keeps the contract well-typed; the caller obligation is sound but
    -- uninterpretable (verification stays inconclusive, never unsound).
    let hv ← freshVar "hole"
    let args := (← read).procInputs.map fun (name, _) => FGLValue.var md name
    modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, true, expected)] }
    pure (.staticCall md hv args)
  | _ =>
    let (val, actual) ← synthValue expr
    pure (applySubtype val (eraseType actual) (eraseType expected))

/-- ⟦·⟧⇐ₚ*: Check a list of statements as a producer (list extension). -/
partial def checkProducers (stmts : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  match stmts with
  | [] => pure .skip
  | stmt :: rest => checkProducer stmt rest retTy grade

/-- ⟦·⟧⇐ₚ (if):
```
D :: Γ ⊢ (if c then t else f); k : A   [if]
├─ D_c :: Γ ⊢ c : bool
├─ D_t :: Γ ⊢ t : A
├─ D_f :: Γ ⊢ f : A
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (ifThenElse x_c M_t M_f M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d
└─ ⟦Γ⟧, x_c:bool ⊢ ifThenElse x_c M_t M_f M_k ⇐ ⟦A⟧ & d   [ifThenElse]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   ├─ ⟦D_t⟧⇐ₚ :: ⟦Γ⟧, x_c:bool ⊢ M_t ⇐ ⟦A⟧ & d
   ├─ ⟦D_f⟧⇐ₚ :: ⟦Γ⟧, x_c:bool ⊢ M_f ⇐ ⟦A⟧ & d
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerIf (md : Md) (cond thn : StmtExprMd) (els : Option StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let M_c ← checkProducer cond [] .TBool grade
  let x_c ← freshVar "cond"
  let body ← extendEnv x_c .TBool do
    let M_t ← checkProducer thn [] retTy grade
    let M_f ← match els with
      | some e => checkProducer e [] retTy grade
      | none => pure .skip
    let M_k ← checkProducers rest retTy grade
    pure (.ifThenElse md (.var md x_c) M_t M_f M_k)
  pure (.varDecl md x_c .TBool M_c body)

/-- ⟦·⟧⇐ₚ (while):
```
D :: Γ ⊢ (while c do body); k : A   [while]
├─ D_c :: Γ ⊢ c : bool
├─ D_b :: Γ ⊢ body : A
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (whileLoop x_c M_b' M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d          (initial guard evaluation)
└─ ⟦Γ⟧, x_c:bool ⊢ whileLoop x_c M_b' M_k ⇐ ⟦A⟧ & d   [whileLoop]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   ├─ ⟦D_b ; (x_c := c)⟧⇐ₚ :: ⟦Γ⟧, x_c:bool ⊢ M_b' ⇐ ⟦A⟧ & d
   │     where M_b' = ⟦body ; (x_c := c)⟧  — the guard is RE-EVALUATED at the end of
   │     each iteration, so the loop tests a fresh value, not a frozen one. The
   │     re-evaluation is threaded by appending the source-level assignment `x_c := c`
   │     to `body`'s statement block before elaboration (so M_b' is a single derivation
   │     over the extended body, sharing the body's sequencing). This is REQUIRED for
   │     soundness: with a frozen `x_c`, downstream loop-elimination (which havocs
   │     loop-modified vars) lets the verifier prove post-loop facts the loop should
   │     not establish.
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerWhile (md : Md) (cond loopBody : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  -- The condition must be RE-EVALUATED every iteration. We bind it to `x_c` before the
  -- loop AND re-assign `x_c := cond` at the END of the loop body, so the next guard test
  -- sees the updated value. Hoisting it once (looping on a frozen `x_c`) was a real bug:
  -- the guard never changed, and after LoopElim havoc the loop was mis-modeled (it let the
  -- verifier "prove" post-loop facts the loop should havoc — see test_while_loop). The
  -- proven PythonToLaurel inlines the condition expression into the While for the same
  -- reason. We keep the value-bound form (the elaborator needs a value guard) but refresh
  -- it inside the body.
  let M_c ← checkProducer cond [] .TBool grade
  let x_c ← freshVar "cond"
  -- Append `x_c := cond` to the END of the loop body (at the Laurel level) so it elaborates
  -- with the body's natural sequencing and refreshes the guard each iteration. `loopBody`
  -- is a Block; we extend its statement list with the reassignment.
  let reassign : StmtExprMd := mkLaurel md (.Assign [⟨.Local { text := x_c }, md⟩] cond)
  let loopBody' : StmtExprMd := match loopBody.val with
    | .Block stmts lbl => mkLaurel md (.Block (stmts ++ [reassign]) lbl)
    | _ => mkLaurel md (.Block [loopBody, reassign] none)
  let body ← extendEnv x_c .TBool do
    let M_b ← checkProducer loopBody' [] retTy grade
    let M_k ← checkProducers rest retTy grade
    pure (.whileLoop md (.var md x_c) M_b M_k)
  pure (.varDecl md x_c .TBool M_c body)

/-- ⟦·⟧⇐ₚ (varDecl):
```
D :: Γ ⊢ (var x:T := e); k : A   [varDecl]
├─ D_e :: Γ ⊢ e : T
└─ D_k :: Γ, x:T ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x ⟦T⟧ M_e M_k ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_e⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_e ⇐ ⟦T⟧ & d
└─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x:⟦T⟧ ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerVarDecl (md : Md) (nameId : Identifier) (typeMd : HighTypeMd)
    (initOpt : Option StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let M_e ← match initOpt with
    | some init => checkProducer init [] typeMd.val grade
    | none => do
      let v ← checkValue (mkLaurel md (.Hole true none)) typeMd.val
      pure (.produce md v)
  let body ← extendEnv nameId.text typeMd.val do
    checkProducers rest retTy grade
  pure (.varDecl md nameId.text (eraseType typeMd.val) M_e body)

/-- ⟦·⟧⇐ₚ (assert):
```
D :: Γ ⊢ (assert c); k : A   [assert]
├─ D_c :: Γ ⊢ c : bool
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (assert x_c M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d
└─ ⟦Γ⟧, x_c:bool ⊢ assert x_c M_k ⇐ ⟦A⟧ & d   [assert]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerAssert (md : Md) (cond : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let M_c ← checkProducer cond [] .TBool grade
  let x_c ← freshVar "cond"
  let body ← extendEnv x_c .TBool do
    let M_k ← checkProducers rest retTy grade
    pure (.assert md (.var md x_c) M_k)
  pure (.varDecl md x_c .TBool M_c body)

/-- ⟦·⟧⇐ₚ (assume):
```
D :: Γ ⊢ (assume c); k : A   [assume]
├─ D_c :: Γ ⊢ c : bool
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (assume x_c M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d
└─ ⟦Γ⟧, x_c:bool ⊢ assume x_c M_k ⇐ ⟦A⟧ & d   [assume]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerAssume (md : Md) (cond : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let M_c ← checkProducer cond [] .TBool grade
  let x_c ← freshVar "cond"
  let body ← extendEnv x_c .TBool do
    let M_k ← checkProducers rest retTy grade
    pure (.assume md (.var md x_c) M_k)
  pure (.varDecl md x_c .TBool M_c body)

partial def elaborateCall (md : Md) (callee : Identifier) (args : List StmtExprMd)
    (grade : Grade) (body : FGLValue → Grade → ElabM FGLProducer) : ElabM FGLProducer := do
  let callGrade := (← read).procGrades[callee.text]?.getD .pure
  let some residual := Grade.leftResidual callGrade grade | failure
  let sig ← lookupFuncSig callee.text
  -- Runtime `function` procs (isFunctional=true) are called as StaticCalls regardless of
  -- their grade. Their exceptions are encoded as values (returning `exception(...)` inside
  -- `Any`), not as a Laurel `Error` output. Only user procs and runtime `procedure`s get the
  -- full procedureCall calling convention.
  let env ← read
  let isFunctionalRuntime : Bool :=
    match env.runtime.staticProcedures.find? (fun p => p.name.text == callee.text) with
    | some rp => rp.isFunctional
    | none => false
  bindArgs md args sig.params grade fun boundVars => do
    if isFunctionalRuntime || callGrade == .pure then
      let rv := FGLValue.staticCall md callee.text boundVars
      body rv residual
    else
      let declaredOutputs ← lookupProcOutputs callee.text
      mkGradedCall md callee.text boundVars declaredOutputs fun rv =>
        body rv residual

/-- ⟦·⟧⇐ₚ (bare call, discards return value):
```
D :: Γ ⊢ g(e₁,…,eₙ); k : A   [call]
├─ (g : (A₁,...,Aₙ) → B) ∈ Γ
├─ Dᵢ :: Γ ⊢ eᵢ : Aᵢ  (for each i)
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x₁ ⟦A₁⟧ M₁ (...(varDecl xₙ ⟦Aₙ⟧ Mₙ (procedureCall g (pre ++ [x₁,...,xₙ]) outs M_k))) ⇐ ⟦A⟧ & d
├─ ⟦D₁⟧⇐ₚ :: ⟦Γ⟧ ⊢ M₁ ⇐ ⟦A₁⟧ & d
├─ ...   [varDecl]
├─ ⟦Dₙ⟧⇐ₚ :: ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ₋₁:⟦Aₙ₋₁⟧ ⊢ Mₙ ⇐ ⟦Aₙ⟧ & d
└─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ procedureCall g (pre ++ [x₁,...,xₙ]) outs M_k ⇐ ⟦A⟧ & d   [producerSubsumption]
   ├─ (g : (⟦A₁⟧,...,⟦Aₙ⟧) → ⟦B⟧ & d') ∈ ⟦Γ⟧
   ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ xᵢ ⇐ ⟦Aᵢ⟧   [subsumption]
   │  ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ xᵢ ⇒ ⟦Aᵢ⟧   [var]
   │  └─ ⟦Aᵢ⟧ ≤ ⟦Aᵢ⟧ ↦ id
   ├─ d' ≤ d ↦ (pre, outs)
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ M_k ⇐ ⟦A⟧ & (d'\d)
```
-/
partial def checkProducerStaticCall (md : Md) (callee : Identifier) (args : List StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  elaborateCall md callee args grade fun rv residual => do
    match rest with
    | [] =>
      let sig ← lookupFuncSig callee.text
      pure (.produce md (applySubtype rv (eraseType sig.returnType) (eraseType retTy)))
    | _ => checkProducers rest retTy residual

/-- ⟦·⟧⇐ₚ (block):
```
D :: Γ ⊢ {body}_l; k : A   [block]
├─ D_b :: Γ, l ⊢ body : A
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ labeledBlock l M_b M_k ⇐ ⟦A⟧ & d   [labeledBlock]
├─ ⟦D_b⟧⇐ₚ :: ⟦Γ⟧, l ⊢ M_b ⇐ ⟦A⟧ & d
└─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧ ⊢ M_k ⇐ ⟦A⟧ & d
```
Unlabeled blocks are flattened into the enclosing scope.
-/
partial def checkProducerBlock (md : Md) (stmts : List StmtExprMd) (label : Option String)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  match label with
  | some l =>
    let M_b ← checkProducers stmts retTy grade
    let M_k ← checkProducers rest retTy grade
    pure (.labeledBlock md l M_b M_k)
  | none => checkProducers (stmts ++ rest) retTy grade

/-- ⟦·⟧⇐ₚ: Producer checking. Entry point of the translation.
    Dispatches on statement form to clause helpers. -/
partial def checkProducer (stmt : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let md := stmt.source
  match stmt.val with
  | .IfThenElse cond thn els => checkProducerIf md cond thn els rest retTy grade
  | .While cond _invs _dec loopBody => checkProducerWhile md cond loopBody rest retTy grade
  | .Exit target => pure (.exit md target)
  | .Var (.Declare ⟨nameId, typeMd⟩) => checkProducerVarDecl md nameId typeMd none rest retTy grade
  | .Assert cond => checkProducerAssert md cond.condition rest retTy grade
  | .Assume cond => checkProducerAssume md cond rest retTy grade
  | .Assign targets value => match targets with
    | [target] => checkAssign target value rest retTy grade
    | _ => failure
  | .StaticCall callee args => checkProducerStaticCall md callee args rest retTy grade
  | .Block stmts label => checkProducerBlock md stmts label rest retTy grade
  | .New _ => failure
  | .Hole deterministic _ => do
    let hv ← freshVar "havoc"
    modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, deterministic, retTy)] }
    -- A deterministic hole is a pure function of the procedure's inputs, so it is
    -- declared with those inputs (see emission below) and must be applied to them
    -- here — same as the value-judgment `.Hole` case. A nondeterministic hole
    -- (havoc) is declared with no inputs and called with none.
    let env ← read
    let args := if deterministic then env.procInputs.map (fun (name, _) => FGLValue.var md name) else []
    let declaredOutputs := [("result", retTy)]
    mkGradedCall md hv args declaredOutputs fun rv => do
      let M_k ← checkProducers rest retTy grade
      match rest with
      | [] => pure (.produce md rv)
      | _ => pure M_k
  | _ => do
    let v ← checkValue stmt retTy
    match rest with
    | [] => pure (.produce md v)
    | _ => failure

/-- Bind a list of arguments as producers via nested varDecls.
    Each arg is checked as a producer, bound to a fresh var, and the
    continuation receives the list of bound values. -/
partial def bindArgs (md : Md) (args : List StmtExprMd) (params : List (String × HighType))
    (grade : Grade) (cont : List FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  match args, params with
  | [], _ => cont []
  | arg :: restArgs, (_, pty) :: restParams => do
    let M_arg ← checkProducer arg [] pty grade
    let x_arg ← freshVar "arg"
    let body ← extendEnv x_arg pty do
      bindArgs md restArgs restParams grade fun restVars =>
        cont (.var md x_arg :: restVars)
    pure (.varDecl md x_arg (eraseType pty) M_arg body)
  | _ :: _, [] => failure

/-- ⟦·⟧⇐ₚ (field write):
```
D :: Γ ⊢ (obj.f := v); k : A   [fieldWrite]
├─ D_obj :: Γ ⊢ obj : C   (C discovered by synthesis on obj)
├─ fieldType(C, f) = T
├─ D_v :: Γ ⊢ v : T
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_obj ⟦C⟧ M_obj (varDecl x_v ⟦T⟧ M_v (varDecl h' Heap M_update M_k)) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_obj⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_obj ⇐ ⟦C⟧ & d
└─ ⟦Γ⟧, x_obj:⟦C⟧ ⊢ varDecl x_v ⟦T⟧ M_v (varDecl h' Heap M_update M_k) ⇐ ⟦A⟧ & d   [varDecl]
   ├─ ⟦D_v⟧⇐ₚ :: ⟦Γ⟧, x_obj ⊢ M_v ⇐ ⟦T⟧ & d
   └─ ⟦Γ⟧, x_obj, x_v ⊢ varDecl h' Heap M_update M_k ⇐ ⟦A⟧ & d   [varDecl]
      ├─ ⟦Γ⟧, x_obj, x_v ⊢ produce (functionCall updateField [$heap, x_obj, $field.C.f, functionCall box_T [x_v]]) ⇐ Heap & d   [produce]
      │  └─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall updateField [$heap, x_obj, $field.C.f, functionCall box_T [x_v]] ⇐ Heap   [subsumption]
      │     ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall updateField [$heap, x_obj, $field.C.f, functionCall box_T [x_v]] ⇒ Heap   [functionCall]
      │     │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ $heap ⇐ Heap   [subsumption]
      │     │  │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ $heap ⇒ Heap   [var]
      │     │  │  └─ Heap ≤ Heap ↦ id
      │     │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ x_obj ⇐ Composite   [subsumption]
      │     │  │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ x_obj ⇒ Composite   [var]
      │     │  │  └─ Composite ≤ Composite ↦ id
      │     │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall $field.C.f [] ⇐ Field   [subsumption]
      │     │  │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall $field.C.f [] ⇒ Field   [functionCall]
      │     │  │  └─ Field ≤ Field ↦ id
      │     │  └─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall box_T [x_v] ⇐ Box   [subsumption]
      │     │     ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall box_T [x_v] ⇒ Box   [functionCall]
      │     │     │  └─ ⟦Γ⟧, x_obj, x_v ⊢ x_v ⇐ ⟦T⟧   [subsumption]
      │     │     │     ├─ ⟦Γ⟧, x_obj, x_v ⊢ x_v ⇒ ⟦T⟧   [var]
      │     │     │     └─ ⟦T⟧ ≤ ⟦T⟧ ↦ id
      │     │     └─ Box ≤ Box ↦ id
      │     └─ Heap ≤ Heap ↦ id
      └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_obj, x_v, h':Heap ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkAssignFieldWrite (md : Md) (obj : StmtExprMd) (field : Identifier)
    (value : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  -- Write rule for field access:  Γ ⊢ e.l := v ; k  with  v ⇐ A_l  (the DECLARED field
  -- type). We check the RHS against `A_l` so the coercion mechanism inserts the right
  -- boxing — we trust the user's annotation and let coercion handle impedance. `A_l` is
  -- looked up from the receiver's composite type; `Any` is the genuine fallthrough when
  -- the receiver isn't a known composite (e.g. `self`/dynamic).
  -- The heap is threaded by heapParameterizationPass, which consumes a BARE field-write
  -- `.Assign [.Field obj f] rhs` and rewrites it into `updateField($heap, obj, $field.C.f,
  -- box_<A_l>(rhs))`. We emit it DIRECTLY as `.assign (.fieldAccess obj f) rhs` — no
  -- intermediate fresh temp (a `val$N` temp collides with a same-named field/param, e.g.
  -- `self.val = val`). This matches the proven pipeline's single `self#val := val`.
  let (ov, objTy) ← synthValue obj
  let fieldTy ←
    match objTy with
    | .UserDefined cls =>
      match ← (do match (← read).typeEnv.classFields[cls.text]? with
                  | some fields => pure (fields.find? (fun (n, _) => n == field.text))
                  | none => pure none) with
      | some (_, ty) => pure ty
      | none => pure (.TCore "Any")
    | _ => pure (.TCore "Any")
  let M_v ← checkProducer value [] fieldTy grade
  let M_k ← checkProducers rest retTy grade
  pure (.assign md (.fieldAccess md ov field.text) M_v M_k)

/-- Dispatches on LHS to get assignee, then on RHS form. -/
partial def checkAssign (target : VariableMd) (value : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let md := target.source
  match target.val with
  | .Field obj field => checkAssignFieldWrite md obj field value rest retTy grade
  -- A `.Declare` target is a local-variable declaration with an initializer
  -- (`var x : T := value`); route it to `checkProducerVarDecl` with the initializer.
  | .Declare ⟨nameId, typeMd⟩ => checkProducerVarDecl md nameId typeMd (some value) rest retTy grade
  | .Local id =>
    let .variable targetTy := (← lookupEnv id.text) | failure
    match value.val with
    | .StaticCall callee args => checkAssignStaticCall md id.text targetTy callee args rest retTy grade
    | .New classId => checkAssignNew md id.text targetTy classId rest retTy grade
    | _ => checkAssignVar md id.text targetTy value rest retTy grade

/-- ⟦·⟧⇐ₚ (assign, generic RHS):
```
D :: Γ ⊢ (x := e); k : A   [assign]
├─ D_e :: Γ ⊢ e : Γ(x)
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ assign x M M_k ⇐ ⟦A⟧ & d   [assign]
├─ ⟦D_e⟧⇐ₚ :: ⟦Γ⟧ ⊢ M ⇐ ⟦Γ(x)⟧ & d
└─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧ ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkAssignVar (md : Md) (targetName : String) (targetTy : HighType)
    (value : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let M ← checkProducer value [] targetTy grade
  let M_k ← checkProducers rest retTy grade
  pure (.assign md (.var md targetName) M M_k)

/-- ⟦·⟧⇐ₚ (assign + call):
```
D :: Γ ⊢ (x := f(e₁,...,eₙ)); k : A   [assign]
├─ D_e :: Γ ⊢ f(e₁,...,eₙ) : Γ(x)   [call]
│  ├─ (f : (A₁,...,Aₙ) → B) ∈ Γ
│  └─ Dᵢ :: Γ ⊢ eᵢ : Aᵢ   (for i = 1,...,n)
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x₁ ⟦A₁⟧ M₁ (...(varDecl xₙ ⟦Aₙ⟧ Mₙ (procedureCall f (pre ++ [x₁,...,xₙ]) outs (assign x (produce c(rv)) M_k)))) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D₁⟧⇐ₚ :: ⟦Γ⟧ ⊢ M₁ ⇐ ⟦A₁⟧ & d
├─ ...   [varDecl]
├─ ⟦Dₙ⟧⇐ₚ :: ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ₋₁:⟦Aₙ₋₁⟧ ⊢ Mₙ ⇐ ⟦Aₙ⟧ & d
└─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ procedureCall f (pre ++ [x₁,...,xₙ]) outs (assign x (produce c(rv)) M_k) ⇐ ⟦A⟧ & d   [producerSubsumption]
   ├─ (f : (⟦A₁⟧,...,⟦Aₙ⟧) → ⟦B⟧ & d') ∈ ⟦Γ⟧
   ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ xᵢ ⇐ ⟦Aᵢ⟧   [subsumption]
   │  ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ xᵢ ⇒ ⟦Aᵢ⟧   [var]
   │  └─ ⟦Aᵢ⟧ ≤ ⟦Aᵢ⟧ ↦ id
   ├─ d' ≤ d ↦ (pre, outs)   where (rv : ⟦B⟧) ∈ outs
   └─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ assign x (produce c(rv)) M_k ⇐ ⟦A⟧ & (d'\d)   [assign]
      ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ produce c(rv) ⇐ ⟦Γ(x)⟧ & (d'\d)   [produce]
      │  └─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ c(rv) ⇐ ⟦Γ(x)⟧   [subsumption]
      │     ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ rv ⇒ ⟦B⟧   [var]
      │     └─ ⟦B⟧ ≤ ⟦Γ(x)⟧ ↦ c
      └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ M_k ⇐ ⟦A⟧ & (d'\d)
```
-/
partial def checkAssignStaticCall (md : Md) (targetName : String) (targetTy : HighType)
    (callee : Identifier) (args : List StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let sig ← lookupFuncSig callee.text
  elaborateCall md callee args grade fun rv residual => do
    let coerced := applySubtype rv (eraseType sig.returnType) (eraseType targetTy)
    let M_k ← checkProducers rest retTy residual
    pure (.assign md (.var md targetName) (.produce md coerced) M_k)

/-- ⟦·⟧⇐ₚ (assign + new):
```
D :: Γ ⊢ (x := new C); k : A   [assign]
├─ D_e :: Γ ⊢ new C : Γ(x)   [new]
│  └─ C is a class ∈ Γ
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl h' Heap (produce (functionCall increment [$heap])) (assign x (produce c(functionCall MkComposite [functionCall Heap..nextReference! [$heap], functionCall C_TypeTag []])) M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦Γ⟧ ⊢ produce (functionCall increment [$heap]) ⇐ Heap & d   [produce]
│  └─ ⟦Γ⟧ ⊢ functionCall increment [$heap] ⇐ Heap   [subsumption]
│     ├─ ⟦Γ⟧ ⊢ functionCall increment [$heap] ⇒ Heap   [functionCall]
│     │  └─ ⟦Γ⟧ ⊢ $heap ⇐ Heap   [subsumption]
│     │     ├─ ⟦Γ⟧ ⊢ $heap ⇒ Heap   [var]
│     │     └─ Heap ≤ Heap ↦ id
│     └─ Heap ≤ Heap ↦ id
└─ ⟦Γ⟧, h':Heap ⊢ assign x (produce c(functionCall MkComposite [functionCall Heap..nextReference! [$heap], functionCall C_TypeTag []])) M_k ⇐ ⟦A⟧ & d   [assign]
   ├─ ⟦Γ⟧, h':Heap ⊢ produce c(functionCall MkComposite [...]) ⇐ ⟦Γ(x)⟧ & d   [produce]
   │  └─ ⟦Γ⟧, h':Heap ⊢ c(functionCall MkComposite [...]) ⇐ ⟦Γ(x)⟧   [subsumption]
   │     ├─ ⟦Γ⟧, h':Heap ⊢ functionCall MkComposite [functionCall Heap..nextReference! [$heap], functionCall C_TypeTag []] ⇒ Composite   [functionCall]
   │     │  ├─ ⟦Γ⟧, h':Heap ⊢ functionCall Heap..nextReference! [$heap] ⇐ int   [subsumption]
   │     │  │  ├─ ⟦Γ⟧, h':Heap ⊢ functionCall Heap..nextReference! [$heap] ⇒ int   [functionCall]
   │     │  │  │  └─ ⟦Γ⟧, h':Heap ⊢ $heap ⇐ Heap   [subsumption]
   │     │  │  │     ├─ ⟦Γ⟧, h':Heap ⊢ $heap ⇒ Heap   [var]
   │     │  │  │     └─ Heap ≤ Heap ↦ id
   │     │  │  └─ int ≤ int ↦ id
   │     │  └─ ⟦Γ⟧, h':Heap ⊢ functionCall C_TypeTag [] ⇐ TypeTag   [subsumption]
   │     │     ├─ ⟦Γ⟧, h':Heap ⊢ functionCall C_TypeTag [] ⇒ TypeTag   [functionCall]
   │     │     └─ TypeTag ≤ TypeTag ↦ id
   │     └─ Composite ≤ ⟦Γ(x)⟧ ↦ c
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, h':Heap ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkAssignNew (md : Md) (targetName : String) (targetTy : HighType)
    (classId : Identifier) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  -- Exceptions-only: allocation is heapParameterizationPass's job. It consumes a BARE
  -- `.New classId` node and rewrites it into a heap-allocated `MkComposite` with a fresh
  -- reference + threads `$heap`. So here we emit the bare `.new` value and assign it.
  let _ := targetTy
  let M_k ← checkProducers rest retTy grade
  pure (.assign md (.var md targetName) (.produce md (.new md classId.text)) M_k)

end

/-! ## Grade Inference

Grade inference is coinductive over the call graph. For each procedure,
try elaboration at successively higher grades until one succeeds. When a
callee's grade exceeds the trial grade, the left residual is undefined,
elaboration fails (returns `none`), and the next grade is tried. The
finite lattice guarantees convergence. -/

/-- Try elaborating a procedure body at each grade in order. Returns the
    first grade that succeeds, or `heapErr` as fallback. -/
partial def tryGrades (callee : String) (env : ElabEnv) (body : StmtExprMd)
    (retTy : HighType) (grades : List Grade) : Option Grade :=
  match grades with
  | [] => some .err  -- Exceptions-only: top of the lattice we use is .err
  | g :: rest =>
    let st : ElabState := { freshCounter := 0 }
    let trialEnv := { env with procGrades := env.procGrades.insert callee g }
    match (checkProducer body [] retTy g).run trialEnv |>.run st with
    | some _ => some g
    | none => tryGrades callee env body retTy rest

/-! ## Projection (Destination Passing Style)

Projection reverses elaboration: GFGL derivations → Laurel derivations.
Uses a writer monad that accumulates declarations (hoisted to procedure top).

```
⟦D⟧ₓ⁻¹ : (⟦Γ⟧ ⊢ M ⇐ ⟦A⟧ & d) → ∃e⃗. (Γ, x : A ⊢ e⃗ : TVoid)
```
-/

structure ProjM (α : Type) where
  run : α × List StmtExprMd

instance : Monad ProjM where
  pure a := ⟨(a, [])⟩
  bind ma f := let (a, d1) := ma.run; let (b, d2) := (f a).run; ⟨(b, d1 ++ d2)⟩

def projDecl (decl : StmtExprMd) : ProjM Unit := ⟨((), [decl])⟩

def projectValue : FGLValue → StmtExprMd
  | .litInt md n => mkLaurel md (.LiteralInt n)
  | .litBool md b => mkLaurel md (.LiteralBool b)
  | .litString md s => mkLaurel md (.LiteralString s)
  | .litDecimal md d => mkLaurel md (.LiteralDecimal d)
  | .var md name => mkLaurel md (.Var (.Local { text := name }))
  | .fromInt md v => mkLaurel md (.StaticCall { text := "from_int" } [projectValue v])
  | .fromStr md v => mkLaurel md (.StaticCall { text := "from_str" } [projectValue v])
  | .fromBool md v => mkLaurel md (.StaticCall { text := "from_bool" } [projectValue v])
  | .fromFloat md v => mkLaurel md (.StaticCall { text := "from_float" } [projectValue v])
  | .fromComposite md v =>
    -- kbd has no structural `Composite → Any` constructor (from_ClassInstance takes
    -- (classname, attr-dict), a different representation). Use the value-PRESERVING
    -- uninterpreted stub `Any..from_Composite(v)` so the term type-checks (Composite⇒Any)
    -- and stays sound-but-uninterpreted, rather than discarding `v` into an empty
    -- from_ClassInstance("", {}) (which both loses the value and mis-types).
    mkLaurel md (.StaticCall { text := "Any..from_Composite" } [projectValue v])
  | .fromListAny md v => mkLaurel md (.StaticCall { text := "from_ListAny" } [projectValue v])
  | .fromDictStrAny md v => mkLaurel md (.StaticCall { text := "from_DictStrAny" } [projectValue v])
  | .fromNone md => mkLaurel md (.StaticCall { text := "from_None" } [])
  | .fieldAccess md obj f => mkLaurel md (.Var (.Field (projectValue obj) { text := f }))
  | .staticCall md name args => mkLaurel md (.StaticCall { text := name } (args.map projectValue))
  | .new md className => mkLaurel md (.New { text := className })

/-- Project an FGL value used as an assignment destination into a `VariableMd`.
    Assignment/declaration destinations are always variables (`.var`) or, for
    field writes, field selections (`.fieldAccess`). -/
def projectVarTarget : FGLValue → VariableMd
  | .var md name => ⟨.Local { text := name }, md⟩
  | .fieldAccess md obj f => ⟨.Field (projectValue obj) { text := f }, md⟩
  | v => ⟨.Local default, v.getMd⟩

mutual

/-- Destination-passing projection.
```
⟦·⟧ₓ⁻¹ : (⟦Γ⟧ ⊢ M ⇔ ⟦A⟧ & d) → ∃e⃗. (Γ, x : A ⊢ e⃗ : TVoid)
⟦·⟧⁻¹  : (⟦Γ⟧ ⊢ V ⇔ ⟦A⟧)     → ∃e. (Γ ⊢ e : A)
```
Dispatches to per-constructor helpers. -/
partial def proj (dest : Option VariableMd) : FGLProducer → ProjM (List StmtExprMd)
  | .produce md v => projProduce dest md v
  | .varDecl md name ty init body => projVarDecl dest md name ty init body
  | .assign md target val body => projAssign dest md target val body
  | .ifThenElse md cond thn els after => projIfThenElse dest md cond thn els after
  | .whileLoop md cond body after => projWhileLoop dest md cond body after
  | .procedureCall md callee args outputs body => projProcedureCall dest md callee args outputs body
  | .assert md cond body => projAssert dest md cond body
  | .assume md cond body => projAssume dest md cond body
  | .labeledBlock md label body after => projLabeledBlock dest md label body after
  | .exit md label => projExit md label
  | .skip => projSkip

/-- projProduce:
```
D :: ⟦Γ⟧ ⊢ produce V ⇐ ⟦A⟧ & d   [produce]
└─ D_V :: ⟦Γ⟧ ⊢ V ⇐ ⟦A⟧

    ↦   (destination x : A present)

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (x := e_V); skip : TVoid   [assign]
├─ ⟦D_V⟧⁻¹ :: Γ ⊢ e_V : A
└─ Γ ⊢ skip : TVoid   [skip]
```
With no destination (a `TVoid` command — the body, or a control-flow path with
no `x : A` in context), the produced value has nowhere to go and projects to the
empty statement list. -/
partial def projProduce (dest : Option VariableMd) (md : Md) (v : FGLValue) : ProjM (List StmtExprMd) :=
  match dest with
  | some d => pure [mkLaurel md (.Assign [d] (projectValue v))]
  | none => pure []

/-- projVarDecl:
```
D :: ⟦Γ⟧ ⊢ varDecl y T M N ⇐ ⟦A⟧ & d
├─ D_M :: ⟦Γ⟧ ⊢ M ⇐ T & d
└─ D_N :: ⟦Γ⟧, y:T ⊢ N ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (var y : T; e⃗_M; e⃗_N) : TVoid   [varDecl]
├─ ⟦D_M⟧ᵧ⁻¹ :: Γ, y : T ⊢ e⃗_M : TVoid
└─ ⟦D_N⟧ₓ⁻¹ :: Γ, x : A, y : T ⊢ e⃗_N : TVoid
```
-/
partial def projVarDecl (dest : Option VariableMd) (md : Md) (name : String) (ty : LowType)
    (init : FGLProducer) (body : FGLProducer) : ProjM (List StmtExprMd) := do
  let nameVar : VariableMd := ⟨.Local { text := name }, md⟩
  let decl := mkLaurel md (.Var (.Declare { name := { text := name }, type := mkHighTypeMd md (liftType ty) }))
  projDecl decl
  let initStmts ← proj (some nameVar) init
  let bodyStmts ← proj dest body
  pure (initStmts ++ bodyStmts)

/-- projAssign:
```
D :: ⟦Γ⟧ ⊢ assign y M K ⇐ ⟦A⟧ & d
├─ D_M :: ⟦Γ⟧ ⊢ M ⇐ ⟦Γ(y)⟧ & d
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (e⃗_M; e⃗_K) : TVoid   [assign]
├─ ⟦D_M⟧ᵧ⁻¹ :: Γ, y : Γ(y) ⊢ e⃗_M : TVoid
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projAssign (dest : Option VariableMd) (_md : Md) (target : FGLValue)
    (val : FGLProducer) (body : FGLProducer) : ProjM (List StmtExprMd) := do
  let valStmts ← proj (some (projectVarTarget target)) val
  let bodyStmts ← proj dest body
  pure (valStmts ++ bodyStmts)

/-- projIfThenElse:
```
D :: ⟦Γ⟧ ⊢ ifThenElse V M N K ⇐ ⟦A⟧ & d
├─ D_V :: ⟦Γ⟧ ⊢ V ⇐ bool
├─ D_M :: ⟦Γ⟧ ⊢ M ⇐ ⟦A⟧ & d
├─ D_N :: ⟦Γ⟧ ⊢ N ⇐ ⟦A⟧ & d
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (if e_V then {e⃗_M} else {e⃗_N}); e⃗_K : TVoid   [if]
├─ ⟦D_V⟧⁻¹ :: Γ ⊢ e_V : bool
├─ ⟦D_M⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_M : TVoid
├─ ⟦D_N⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_N : TVoid
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projIfThenElse (dest : Option VariableMd) (md : Md) (cond : FGLValue)
    (thn els after : FGLProducer) : ProjM (List StmtExprMd) := do
  let thnStmts ← proj dest thn
  let elsStmts ← proj dest els
  -- kbd-forced: the Laurel resolver types BOTH `if` branches and rejects a value
  -- branch paired with an empty (void) branch ('if' branches have incompatible
  -- types 'int' and 'void'). When one branch is empty, emit a one-armed `if`
  -- (kbd `IfThenElse` takes `elseBranch : Option`). For an empty THEN, flip the
  -- condition with `Any_to_bool(PNot ·)` — conditions are Any-typed here, exactly
  -- as the proven PythonToLaurel pipeline wraps them.
  let ite : StmtExprMd :=
    match thnStmts.isEmpty, elsStmts.isEmpty with
    | true, true => mkLaurel md (.Block [] none)
    | false, true => mkLaurel md (.IfThenElse (projectValue cond) (mkLaurel md (.Block thnStmts none)) none)
    | true, false =>
      -- Empty THEN: emit only the else under the negated condition. `cond` was checked
      -- at `.TBool`, so it projects to a bool — negate with the boolean `PrimitiveOp .Not`
      -- (NOT `Any_to_bool(PNot ·)`, which assumes an Any-typed cond and yields an
      -- arrow-type mismatch when cond is already bool, e.g. `if x > 10: pass`).
      let negCond := mkLaurel md (.PrimitiveOp .Not [projectValue cond])
      mkLaurel md (.IfThenElse negCond (mkLaurel md (.Block elsStmts none)) none)
    | false, false =>
      mkLaurel md (.IfThenElse (projectValue cond) (mkLaurel md (.Block thnStmts none))
        (some (mkLaurel md (.Block elsStmts none))))
  let afterStmts ← proj dest after
  pure ([ite] ++ afterStmts)

/-- projWhileLoop:
```
D :: ⟦Γ⟧ ⊢ whileLoop V M K ⇐ ⟦A⟧ & d
├─ D_V :: ⟦Γ⟧ ⊢ V ⇐ bool
├─ D_M :: ⟦Γ⟧ ⊢ M ⇐ ⟦A⟧ & d
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (while e_V {e⃗_M}); e⃗_K : TVoid   [while]
├─ ⟦D_V⟧⁻¹ :: Γ ⊢ e_V : bool
├─ ⟦D_M⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_M : TVoid
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projWhileLoop (dest : Option VariableMd) (md : Md) (cond : FGLValue)
    (body after : FGLProducer) : ProjM (List StmtExprMd) := do
  let bodyStmts ← proj dest body
  let bodyBlock := mkLaurel md (.Block bodyStmts none)
  let loop := mkLaurel md (.While (projectValue cond) [] none bodyBlock)
  let afterStmts ← proj dest after
  pure ([loop] ++ afterStmts)

/-- projProcedureCall:
```
D :: ⟦Γ⟧ ⊢ procedureCall f [Vᵢ] [outⱼ : Tⱼ] K ⇐ ⟦A⟧ & d
├─ D_Vᵢ :: ⟦Γ⟧ ⊢ Vᵢ ⇐ ⟦Aᵢ⟧
└─ D_K :: ⟦Γ⟧, outⱼ:Tⱼ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (var out₁:T₁; ...; var outₙ:Tₙ; (out₁,...,outₙ) := f(e_Vᵢ); e⃗_K) : TVoid   [call]
├─ ⟦D_Vᵢ⟧⁻¹ :: Γ ⊢ e_Vᵢ : Aᵢ
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A, out₁:T₁, ..., outₙ:Tₙ ⊢ e⃗_K : TVoid
```
-/
partial def projProcedureCall (dest : Option VariableMd) (md : Md) (callee : String)
    (args : List FGLValue) (outputs : List (String × LowType)) (body : FGLProducer) : ProjM (List StmtExprMd) := do
  for (n, ty) in outputs do
    projDecl (mkLaurel md (.Var (.Declare { name := { text := n }, type := mkHighTypeMd md (liftType ty) })))
  let targets : List VariableMd := outputs.map fun (n, _) => ⟨.Local { text := n }, md⟩
  let call := mkLaurel md (.Assign targets (mkLaurel md (.StaticCall { text := callee } (args.map projectValue))))
  let bodyStmts ← proj dest body
  pure ([call] ++ bodyStmts)

/-- projAssert:
```
D :: ⟦Γ⟧ ⊢ assert V K ⇐ ⟦A⟧ & d
├─ D_V :: ⟦Γ⟧ ⊢ V ⇐ bool
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (assert e_V); e⃗_K : TVoid   [assert]
├─ ⟦D_V⟧⁻¹ :: Γ ⊢ e_V : bool
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projAssert (dest : Option VariableMd) (md : Md) (cond : FGLValue)
    (body : FGLProducer) : ProjM (List StmtExprMd) := do
  let bodyStmts ← proj dest body
  pure ([mkLaurel md (.Assert { condition := projectValue cond })] ++ bodyStmts)

/-- projAssume:
```
D :: ⟦Γ⟧ ⊢ assume V K ⇐ ⟦A⟧ & d
├─ D_V :: ⟦Γ⟧ ⊢ V ⇐ bool
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (assume e_V); e⃗_K : TVoid   [assume]
├─ ⟦D_V⟧⁻¹ :: Γ ⊢ e_V : bool
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projAssume (dest : Option VariableMd) (md : Md) (cond : FGLValue)
    (body : FGLProducer) : ProjM (List StmtExprMd) := do
  let bodyStmts ← proj dest body
  pure ([mkLaurel md (.Assume (projectValue cond))] ++ bodyStmts)

/-- projLabeledBlock:
```
D :: ⟦Γ⟧ ⊢ labeledBlock l M K ⇐ ⟦A⟧ & d
├─ D_M :: ⟦Γ⟧, l ⊢ M ⇐ ⟦A⟧ & d
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ {e⃗_M}_l; e⃗_K : TVoid   [labeledBlock]
├─ ⟦D_M⟧ₓ⁻¹ :: Γ, x : A, l ⊢ e⃗_M : TVoid
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projLabeledBlock (dest : Option VariableMd) (md : Md) (label : String)
    (body after : FGLProducer) : ProjM (List StmtExprMd) := do
  let bodyStmts ← proj dest body
  let bodyBlock := mkLaurel md (.Block bodyStmts (some label))
  let afterStmts ← proj dest after
  pure ([bodyBlock] ++ afterStmts)

/-- projExit:
```
D :: ⟦Γ⟧ ⊢ exit l ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ exit l : TVoid   [exit]
└─ l ∈ Γ
```
-/
partial def projExit (md : Md) (label : String) : ProjM (List StmtExprMd) :=
  pure [mkLaurel md (.Exit label)]

/-- projSkip:
```
⟦skip⟧ₓ⁻¹ :: Γ, x : A ⊢ skip : TVoid   [skip]
```
-/
partial def projSkip : ProjM (List StmtExprMd) := pure []

end

/-- Run projection of a procedure body. The body is a command (`TVoid`), so it
    has no destination: its return value reaches `LaurelResult` only through the
    explicit `LaurelResult := e` assignments Translation emits for `return e`, not
    through a tail value. Declarations hoisted to top. -/
def projectProducer (prod : FGLProducer) : List StmtExprMd :=
  let (stmts, decls) := (proj none prod).run
  decls ++ stmts

/-- Run projection, return as a block. -/
def projectBody (md : Md) (prod : FGLProducer) : StmtExprMd :=
  mkLaurel md (.Block (projectProducer prod) none)

/-! ## Entry Point

`fullElaborate` orchestrates both passes. Pass 1 iterates to a fixpoint on
grades. Pass 2 elaborates each procedure at its final grade and projects
back to Laurel. Also emits auxiliary datatypes (TypeTag, Composite, Field,
Box) and hole procedure declarations needed by the output program. -/

/-- Entry point: elaborates a Laurel program. Returns the elaborated program
    and a list of procedure names that failed to elaborate (emitted unchanged). -/
def fullElaborate (program : Laurel.Program) (runtime : Laurel.Program := default) (initialGrades : Std.HashMap String Grade := {}) : Except String (Laurel.Program × List String) := do
  let typeEnv := buildElabEnvFromProgram program runtime
  let baseEnv : ElabEnv := { typeEnv := typeEnv, program := program, runtime := runtime }

  -- PASS 1: Coinductive fixpoint iteration
  let mut knownGrades : Std.HashMap String Grade := initialGrades
  let mut changed := true
  while changed do
    changed := false
    for proc in program.staticProcedures do
      let bodyOpt := match proc.body with
        | .Transparent b => some b
        | .Opaque _ (some impl) _ => some impl
        | _ => none
      match bodyOpt with
      | some bodyExpr =>
        let extEnv := (proc.inputs ++ proc.outputs).foldl
          (fun (e : ElabTypeEnv) p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
        let inputList := proc.inputs.map fun p => (p.name.text, p.type.val)
        let procEnv : ElabEnv := { baseEnv with typeEnv := extEnv, procGrades := knownGrades, procInputs := inputList }
        -- The body is a command (DPS): checked at TVoid, not the return type. The
        -- return value flows only through explicit `LaurelResult := e` assigns.
        match tryGrades proc.name.text procEnv bodyExpr .TVoid [.pure, .proc, .err] with
        | some g =>
          -- A proc with >1 output carries a trailing `maybe_except` (it can throw),
          -- so its grade is at least `.err`. Without this join a caller elaborated at
          -- `.pure`/`.proc` cannot call it (leftResidual .err _ = none) and the call is
          -- silently dropped. (v2 verbatim; independent of heap removal.)
          let g := if proc.outputs.length > 1 then Grade.join g .err else g
          if knownGrades[proc.name.text]? != some g then
            knownGrades := knownGrades.insert proc.name.text g
            changed := true
        | none => pure ()
      | none => pure ()

  -- PASS 2: Elaborate each proc with final grades
  let mut procs : List Laurel.Procedure := []
  let mut allHoles : List (String × Bool × List (String × HighType) × HighType) := []
  let mut elabFailures : List String := []
  let mut globalCounter : Nat := 0
  for proc in program.staticProcedures do
    let bodyOpt2 : Option (StmtExprMd × Bool) := match proc.body with
      | .Transparent b => some (b, false)
      | .Opaque _ (some impl) _ => some (impl, true)
      | _ => none
    match bodyOpt2 with
    | some (bodyExpr, isOpaque) =>
      let extEnv := (proc.inputs ++ proc.outputs).foldl
        (fun (e : ElabTypeEnv) p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
      let inputList := proc.inputs.map fun p => (p.name.text, p.type.val)
      let procEnv : ElabEnv := { baseEnv with typeEnv := extEnv, procGrades := knownGrades, procInputs := inputList }
      let g := knownGrades[proc.name.text]?.getD .pure
      let st : ElabState := { freshCounter := globalCounter }
      -- Elaborate preconditions: a `requires` is a pure value of type bool, not an
      -- effect-sequenced statement, so it elaborates with the value judgment
      -- (checkValue) rather than the producer judgment. checkValue synthesizes the
      -- term and applies subtyping coercions — from_int/from_str on argument
      -- literals (the runtime operators take Any parameters) and Any_to_bool on the
      -- Any-typed result — then projectValue yields the single Core expression.
      -- Holes are collected as for bodies.
      let mut elabPreconditions : List Condition := []
      for pre in proc.preconditions do
        let preSt : ElabState := { freshCounter := globalCounter }
        match (checkValue pre.condition .TBool).run procEnv |>.run preSt with
        | some (preVal, preSt') =>
          globalCounter := preSt'.freshCounter
          let newHoles := (preSt'.usedHoles.map fun (name, det, outTy) => (name, det, inputList, outTy)).filter
            (fun (n, _, _, _) => !allHoles.any (fun (n2, _, _, _) => n == n2))
          allHoles := allHoles ++ newHoles
          elabPreconditions := elabPreconditions ++ [{ condition := ⟨(projectValue preVal).val, pre.condition.source⟩ }]
        | none => elabPreconditions := elabPreconditions ++ [pre]
      let proc := { proc with preconditions := elabPreconditions }
      match (checkProducer bodyExpr [] .TVoid g).run procEnv |>.run st with
      | some (fgl, st') =>
        globalCounter := st'.freshCounter
        let newHoles := (st'.usedHoles.map fun (name, det, outTy) => (name, det, inputList, outTy)).filter
          (fun (n, _, _, _) => !allHoles.any (fun (n2, _, _, _) => n == n2))
        allHoles := allHoles ++ newHoles
        let projected := projectBody bodyExpr.source fgl
        let md := bodyExpr.source
        let errOutParam : Laurel.Parameter := { name := { text := "maybe_except" }, type := mkHighTypeMd md (.TCore "Error") }
        let resultOutputs := proc.outputs.filter fun o => eraseType o.type.val != .TCore "Error"
        let mkBody (b : StmtExprMd) : Laurel.Body :=
          if isOpaque then .Opaque [] (some b) [] else .Transparent b
        match g with
        | .err =>
          procs := procs ++ [{ proc with
            outputs := resultOutputs ++ [errOutParam]
            body := mkBody projected }]
        | _ =>
          procs := procs ++ [{ proc with body := mkBody projected }]
      | none =>
        elabFailures := elabFailures ++ [proc.name.text]
        procs := procs ++ [proc]
    | none => procs := procs ++ [proc]
  -- Hole procs are emitted because grade inference may introduce them.
  -- Everything else (heap, box types, auxiliary datatypes) is owned by downstream passes.
  let holeProcs := allHoles.map fun (name, deterministic, inputs, outTy) =>
    let params := inputs.map fun (pName, pType) =>
      ({ name := { text := pName }, type := ⟨pType, none⟩ } : Laurel.Parameter)
    let outputParam : Laurel.Parameter := { name := { text := "result" }, type := ⟨outTy, none⟩ }
    { name := { text := name }
      inputs := if deterministic then params else []
      outputs := [outputParam]
      preconditions := []
      decreases := none
      isFunctional := true
      body := .Opaque [] none [] : Laurel.Procedure }
  let result : Laurel.Program :=
    { program with
      staticProcedures := holeProcs ++ procs }
  pure (result, elabFailures)

end
end Strata.FineGrainLaurel

