/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.FineGrainLaurel.FineGrainLaurel
public import Strata.Languages.Laurel.Laurel
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
    | .Datatype dt =>
      for ctor in dt.constructors do
        let ctorParams := ctor.args.map fun p => (p.name.text, p.type.val)
        let retTy := HighType.UserDefined { text := dt.name.text, uniqueId := none }
        names := names.insert ctor.name.text (.function { name := ctor.name.text, params := ctorParams, returnType := retTy })
    | .Constrained _ => pure ()
  { names, classFields }

def mkLaurel (md : Imperative.MetaData Core.Expression) (e : StmtExpr) : StmtExprMd :=
  { val := e, md := md }
def mkHighTypeMd (md : Imperative.MetaData Core.Expression) (ty : HighType) : HighTypeMd :=
  { val := ty, md := md }

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
  deriving Inhabited, Repr, BEq

/-- Type erasure: HighType -> LowType. Primitives map directly, user-defined types
    become Composite, unknown/complex types become Any. -/
def eraseType : HighType → LowType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n
  | .UserDefined id => match id.text with
    | "Any" => .TCore "Any" | "Error" => .TCore "Error"
    | "ListAny" => .TCore "ListAny" | "DictStrAny" => .TCore "DictStrAny"
    | "OptionInt" => .TCore "OptionInt"
    | "Box" => .TCore "Box" | "Field" => .TCore "Field" | "TypeTag" => .TCore "TypeTag"
    | _ => .TCore "Composite"
  | .THeap => .TCore "Heap"
  | .TReal => .TCore "real" | .TTypedField _ => .TCore "Field"
  | .TSet _ | .TMap _ _ | .Applied _ _ | .Intersection _ | .Unknown => .TCore "Any"
  | .Pure _ => .TCore "Composite"

/-- Inverse of erasure (partial): lifts a LowType back to HighType for env extension. -/
def liftType : LowType → HighType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .TCore n

/-! ## FGL Terms

The intermediate representation between Laurel input and Laurel output.
Values are pure (can appear in any context). Producers are effectful
(must be sequenced). Every constructor carries source metadata so
provenance is preserved through elaboration. -/

abbrev Md := Imperative.MetaData Core.Expression

/-- A pure value in the FGCBV intermediate term. Can appear in any context.
    Every constructor carries source metadata for provenance. -/
inductive FGLValue where
  /-- Integer literal. -/
  | litInt (md : Md) (n : Int)
  /-- Boolean literal. -/
  | litBool (md : Md) (b : Bool)
  /-- String literal. -/
  | litString (md : Md) (s : String)
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
  deriving Inhabited

def FGLValue.getMd : FGLValue → Md
  | .litInt md _ | .litBool md _ | .litString md _ | .var md _
  | .fromInt md _ | .fromStr md _ | .fromBool md _ | .fromFloat md _
  | .fromComposite md _ | .fromListAny md _ | .fromDictStrAny md _ | .fromNone md
  | .fieldAccess md _ _ | .staticCall md _ _ => md

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

/-- Mutable state for elaboration: fresh name counter, current heap variable name,
    and collectors for box constructors and holes used (emitted as declarations). -/
structure ElabState where
  /-- Counter for generating fresh variable names. -/
  freshCounter : Nat := 0
  /-- Current heap variable name (updated after each heap-writing call). -/
  heapVar : Option String := none
  /-- Box constructors used (emitted as datatype constructors in output). -/
  usedBoxConstructors : List (String × String × HighType) := []
  /-- Hole functions used (emitted as opaque procedure declarations in output). -/
  usedHoles : List (String × Bool × HighType) := []

abbrev ElabM := ReaderT ElabEnv (StateT ElabState Option)

private def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }; pure s!"{pfx}${s.freshCounter}"

-- ═══════════════════════════════════════════════════════════════════════════════
-- Box protocol (type-directed)
-- Architecture §"Heap Field Access"
-- ═══════════════════════════════════════════════════════════════════════════════

def boxConstructorName (ty : HighType) : String :=
  match ty with
  | .TInt => "BoxInt" | .TBool => "BoxBool" | .TFloat64 => "BoxFloat64"
  | .TReal => "BoxReal" | .TString => "BoxString"
  | .UserDefined _ => "BoxComposite"
  | .TCore "Any" => "BoxAny"
  | .TCore name => s!"Box..{name}"
  | _ => "BoxComposite"

def boxDestructorName (ty : HighType) : String :=
  match ty with
  | .TInt => "Box..intVal!" | .TBool => "Box..boolVal!" | .TFloat64 => "Box..float64Val!"
  | .TReal => "Box..realVal!" | .TString => "Box..stringVal!"
  | .UserDefined _ => "Box..compositeVal!"
  | .TCore "Any" => "Box..AnyVal!"
  | .TCore name => s!"Box..{name}Val!"
  | _ => "Box..compositeVal!"

def boxFieldName (ty : HighType) : String :=
  match ty with
  | .TInt => "intVal" | .TBool => "boolVal" | .TFloat64 => "float64Val"
  | .TReal => "realVal" | .TString => "stringVal"
  | .UserDefined _ => "compositeVal"
  | .TCore "Any" => "AnyVal"
  | .TCore name => s!"{name}Val"
  | _ => "compositeVal"

def boxFieldType (ty : HighType) : HighType :=
  match ty with
  | .UserDefined _ => .UserDefined (Identifier.mk "Composite" none)
  | other => other

def recordBoxUse (ty : HighType) : ElabM Unit := do
  let ctor := boxConstructorName ty
  let existing := (← get).usedBoxConstructors
  unless existing.any (fun (c, _, _) => c == ctor) do
    modify fun s => { s with usedBoxConstructors := s.usedBoxConstructors ++ [(ctor, boxDestructorName ty, ty)] }

/-- Reads a runtime procedure's grade structurally from its signature: does it
    have a Heap input? An Error output? The combination determines the grade.
    User procedure grades are inferred by coinduction, not read from signature. -/
def gradeFromSignature (proc : Laurel.Procedure) : Grade :=
  let hasError := proc.outputs.any fun o => eraseType o.type.val == .TCore "Error"
  let hasHeap := proc.inputs.any fun i => eraseType i.type.val == .TCore "Heap"
  match hasHeap, hasError with
  | true, true => .heapErr
  | true, false => .heap
  | false, true => .err
  | false, false => if proc.isFunctional then .pure else .proc

-- ═══════════════════════════════════════════════════════════════════════════════
-- Env helpers
-- ═══════════════════════════════════════════════════════════════════════════════

def lookupEnv (name : String) : ElabM NameInfo := do
  match (← read).typeEnv.names[name]? with | some info => pure info | none => dbg_trace s!"lookupEnv: {name} not found"; failure
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
    (declaredOutputs : List (String × HighType)) (callGrade : Grade)
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let actualArgs ← if callGrade == .heap || callGrade == .heapErr then do
    let hv := (← get).heapVar
    let heapArg := match hv with | some h => FGLValue.var md h | none => FGLValue.var md "$heap"
    pure (heapArg :: args)
  else pure args
  mkEffectfulCall md callee actualArgs declaredOutputs fun outs => do
    if callGrade == .heap || callGrade == .heapErr then
      match outs[0]? with
      | some v => match v with | .var _ n => modify fun s => { s with heapVar := some n } | _ => pure ()
      | none => pure ()
    let resultVar := match callGrade with
      | .heap | .heapErr => outs[1]?
      | _ => outs[0]?
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

/-- Subtyping judgment: `A ≤ B ↦ c`. Returns the coercion witness.
```
A ≤ A ↦ id  (reflexivity)

TInt ≤ Any ↦ fromInt          TBool ≤ Any ↦ fromBool
TString ≤ Any ↦ fromStr       TFloat64 ≤ Any ↦ fromFloat
Composite ≤ Any ↦ fromComposite
ListAny ≤ Any ↦ fromListAny   DictStrAny ≤ Any ↦ fromDictStrAny
TVoid ≤ Any ↦ fromNone

Any ≤ TBool ↦ Any_to_bool     Any ≤ TInt ↦ Any..as_int!
Any ≤ TString ↦ Any..as_string!
Any ≤ TFloat64 ↦ Any..as_float!
Any ≤ Composite ↦ Any..as_Composite!
```
-/
def subtype (actual expected : LowType) : CoercionResult :=
  if actual == expected then .refl else match actual, expected with
  | .TInt, .TCore "Any" => .coerce (fun md => .fromInt md)
  | .TBool, .TCore "Any" => .coerce (fun md => .fromBool md)
  | .TString, .TCore "Any" => .coerce (fun md => .fromStr md)
  | .TFloat64, .TCore "Any" => .coerce (fun md => .fromFloat md)
  | .TCore "Composite", .TCore "Any" => .coerce (fun md => .fromComposite md)
  | .TCore "ListAny", .TCore "Any" => .coerce (fun md => .fromListAny md)
  | .TCore "DictStrAny", .TCore "Any" => .coerce (fun md => .fromDictStrAny md)
  | .TVoid, .TCore "Any" => .coerce (fun md _ => .fromNone md)
  | .TCore "Any", .TBool => .coerce (fun md v => .staticCall md "Any_to_bool" [v])
  | .TCore "Any", .TInt => .coerce (fun md v => .staticCall md "Any..as_int!" [v])
  | .TCore "Any", .TString => .coerce (fun md v => .staticCall md "Any..as_string!" [v])
  | .TCore "Any", .TFloat64 => .coerce (fun md v => .staticCall md "Any..as_float!" [v])
  | .TCore "Any", .TCore "Composite" => .coerce (fun md v => .staticCall md "Any..as_Composite!" [v])
  | .TCore "Any", .TCore "DictStrAny" => .coerce (fun md v => .staticCall md "Any..as_Dict!" [v])
  | .TCore "Any", .TCore "ListAny" => .coerce (fun md v => .staticCall md "Any..as_ListAny!" [v])
  | _, _ => .unrelated

/-- Apply the coercion witness for `actual <= expected` to a value. Identity if equal. -/
def applySubtype (val : FGLValue) (actual expected : LowType) : FGLValue :=
  match subtype actual expected with | .refl => val | .coerce c => c val.getMd val | .unrelated => val

/-! ## The Translation ⟦·⟧ : Laurel → GFGL

Three functions: synthValue (⟦·⟧⇒ᵥ), checkValue (⟦·⟧⇐ᵥ), checkProducer (⟦·⟧⇐ₚ).
Entry point is checkProducer — every Laurel derivation maps to a GFGL producer.
synthValue/checkValue are internal helpers for building value sub-terms.
Producer synthesis (⟦·⟧⇒ₚ) is applied by inversion inside the call clause. -/

-- Look up a proc's declared outputs, accounting for signature rewriting.
partial def lookupProcOutputs (callee : String) : ElabM (List (String × HighType)) := do
  let env ← read
  let g := env.procGrades[callee]?.getD .pure
  let findProc (procs : List Laurel.Procedure) : Option Laurel.Procedure :=
    procs.find? (fun p => p.name.text == callee)
  match findProc env.runtime.staticProcedures with
  | some proc => pure (proc.outputs.map fun o => (o.name.text, o.type.val))
  | none => match findProc env.program.staticProcedures with
    | some proc =>
      let resultOutputs := proc.outputs.filter fun o => eraseType o.type.val != .TCore "Error"
      let resultList := resultOutputs.map fun o => (o.name.text, o.type.val)
      match g with
      | .heap => pure ([("$heap", .THeap)] ++ resultList)
      | .heapErr => pure ([("$heap", .THeap)] ++ resultList ++ [("maybe_except", .TCore "Error")])
      | .err => pure (resultList ++ [("maybe_except", .TCore "Error")])
      | _ => pure (proc.outputs.map fun o => (o.name.text, o.type.val))
    | none => failure

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
  | _ => dbg_trace s!"synthValueVar: {id.text} not a variable"; failure

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
  match (← get).heapVar with
  | some hv =>
    let owner := match objTy with | .UserDefined id => some id.text | _ => none
    match owner with
    | some cn =>
      match (← read).typeEnv.classFields[cn]? with
      | some _ =>
        let fieldTy ← lookupFieldType cn field.text
        recordBoxUse fieldTy
        let qualifiedName := "$field." ++ cn ++ "." ++ field.text
        let compositeObj := applySubtype ov (eraseType objTy) (.TCore "Composite")
        let read := FGLValue.staticCall md "readField" [.var md hv, compositeObj, .staticCall md qualifiedName []]
        pure (.staticCall md (boxDestructorName fieldTy) [read], fieldTy)
      | none =>
        let hv ← freshVar "havoc"
        modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, false, .TCore "Any")] }
        pure (.staticCall md hv [], .TCore "Any")
    | none =>
      let hv ← freshVar "havoc"
      modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, false, .TCore "Any")] }
      pure (.staticCall md hv [], .TCore "Any")
  | none => failure

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
  let some g := (← read).procGrades[callee.text]? | failure
  guard (g == .pure)
  let sig ← lookupFuncSig callee.text
  let checkedArgs ← checkArgValues args sig.params
  pure (.staticCall md callee.text checkedArgs, sig.returnType)

/-- ⟦·⟧⇒ᵥ: Value synthesis. Dispatches to clause helpers. -/
partial def synthValue (expr : StmtExprMd) : ElabM (FGLValue × HighType) := do
  let md := expr.md
  match expr.val with
  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ =>
    match synthValueLiteral md expr.val with
    | some r => pure r
    | none => failure
  | .Identifier id => synthValueVar md id
  | .FieldSelect obj field => synthValueFieldSelect md obj field
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
  let md := expr.md
  match expr.val with
  | .Hole deterministic _ =>
    guard deterministic
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

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (whileLoop x_c M_b M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d
└─ ⟦Γ⟧, x_c:bool ⊢ whileLoop x_c M_b M_k ⇐ ⟦A⟧ & d   [whileLoop]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   ├─ ⟦D_b⟧⇐ₚ :: ⟦Γ⟧, x_c:bool ⊢ M_b ⇐ ⟦A⟧ & d
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerWhile (md : Md) (cond loopBody : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let M_c ← checkProducer cond [] .TBool grade
  let x_c ← freshVar "cond"
  let body ← extendEnv x_c .TBool do
    let M_b ← checkProducer loopBody [] retTy grade
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
  let some residual := Grade.leftResidual callGrade grade |
    dbg_trace s!"elaborateCall: leftResidual {repr callGrade} {repr grade} = none for {callee.text}"; failure
  let sig ← lookupFuncSig callee.text
  bindArgs md args sig.params grade fun boundVars => do
    match callGrade with
    | .pure =>
      let rv := FGLValue.staticCall md callee.text boundVars
      body rv residual
    | _ =>
      let declaredOutputs ← lookupProcOutputs callee.text
      mkGradedCall md callee.text boundVars declaredOutputs callGrade fun rv =>
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
  let md := stmt.md
  match stmt.val with
  | .IfThenElse cond thn els => checkProducerIf md cond thn els rest retTy grade
  | .While cond _invs _dec loopBody => checkProducerWhile md cond loopBody rest retTy grade
  | .Exit target => pure (.exit md target)
  | .LocalVariable nameId typeMd initOpt => checkProducerVarDecl md nameId typeMd initOpt rest retTy grade
  | .Assert cond => checkProducerAssert md cond rest retTy grade
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
    mkGradedCall md hv args declaredOutputs .proc fun rv => do
      let M_k ← checkProducers rest retTy grade
      match rest with
      | [] => pure (.produce md rv)
      | _ => pure M_k
  | _ => do
    dbg_trace s!"checkProducer catch-all at grade={repr grade}"
    let v ← checkValue stmt retTy
    match rest with
    | [] => pure (.produce md v)
    | _ => dbg_trace s!"checkProducer catch-all: non-empty rest"; failure

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
  guard (Grade.leftResidual .heap grade |>.isSome)
  let (_, objHighTy) ← synthValue obj
  match objHighTy with
  | .UserDefined id =>
    let owner := id.text
    let fieldTy ← lookupFieldType owner field.text
    let M_obj ← checkProducer obj [] objHighTy grade
    let x_obj ← freshVar "obj"
    let qualifiedName := "$field." ++ owner ++ "." ++ field.text
    recordBoxUse fieldTy
    let body_obj ← extendEnv x_obj objHighTy do
      let M_v ← checkProducer value [] fieldTy grade
      let x_v ← freshVar "val"
      let body_v ← extendEnv x_v fieldTy do
        match (← get).heapVar with
        | some hv =>
          let boxed := FGLValue.staticCall md (boxConstructorName fieldTy) [.var md x_v]
          let newHeap := FGLValue.staticCall md "updateField" [.var md hv, .var md x_obj, .staticCall md qualifiedName [], boxed]
          let freshH ← freshVar "heap"
          modify fun s => { s with heapVar := some freshH }
          let body_h ← extendEnv freshH .THeap do
            checkProducers rest retTy grade
          pure (.varDecl md freshH (.TCore "Heap") (.produce md newHeap) body_h)
        | none => failure
      pure (.varDecl md x_v (eraseType fieldTy) M_v body_v)
    pure (.varDecl md x_obj (.TCore "Composite") M_obj body_obj)
  | _ => checkProducers rest retTy grade

/-- Dispatches on LHS to get assignee, then on RHS form. -/
partial def checkAssign (target value : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let md := target.md
  match target.val with
  | .FieldSelect obj field => checkAssignFieldWrite md obj field value rest retTy grade
  | .Identifier id =>
    let .variable targetTy := (← lookupEnv id.text) | failure
    match value.val with
    | .StaticCall callee args => checkAssignStaticCall md id.text targetTy callee args rest retTy grade
    | .New classId => checkAssignNew md id.text targetTy classId rest retTy grade
    | _ => checkAssignVar md id.text targetTy value rest retTy grade
  | _ => failure

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
  dbg_trace s!"checkAssignStaticCall: {targetName} := {callee.text}(...) at grade={repr grade}"
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
  match (← get).heapVar with
  | some hv =>
    let newHeap := FGLValue.staticCall md "increment" [.var md hv]
    let ref := FGLValue.staticCall md "Heap..nextReference!" [.var md hv]
    let obj := FGLValue.staticCall md "MkComposite" [ref, .staticCall md (classId.text ++ "_TypeTag") []]
    let coerced := applySubtype obj (.TCore "Composite") (eraseType targetTy)
    let freshH ← freshVar "heap"
    modify fun s => { s with heapVar := some freshH }
    let M_k ← extendEnv freshH .THeap do checkProducers rest retTy grade
    pure (.varDecl md freshH (.TCore "Heap") (.produce md newHeap)
      (.assign md (.var md targetName) (.produce md coerced) M_k))
  | none => failure

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
  | [] => some .heapErr
  | g :: rest =>
    let st : ElabState := {
      freshCounter := 0
      heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
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
  | .var md name => mkLaurel md (.Identifier (Identifier.mk name none))
  | .fromInt md v => mkLaurel md (.StaticCall (Identifier.mk "from_int" none) [projectValue v])
  | .fromStr md v => mkLaurel md (.StaticCall (Identifier.mk "from_str" none) [projectValue v])
  | .fromBool md v => mkLaurel md (.StaticCall (Identifier.mk "from_bool" none) [projectValue v])
  | .fromFloat md v => mkLaurel md (.StaticCall (Identifier.mk "from_float" none) [projectValue v])
  | .fromComposite md v => mkLaurel md (.StaticCall (Identifier.mk "from_Composite" none) [projectValue v])
  | .fromListAny md v => mkLaurel md (.StaticCall (Identifier.mk "from_ListAny" none) [projectValue v])
  | .fromDictStrAny md v => mkLaurel md (.StaticCall (Identifier.mk "from_DictStrAny" none) [projectValue v])
  | .fromNone md => mkLaurel md (.StaticCall (Identifier.mk "from_None" none) [])
  | .fieldAccess md obj f => mkLaurel md (.FieldSelect (projectValue obj) (Identifier.mk f none))
  | .staticCall md name args => mkLaurel md (.StaticCall (Identifier.mk name none) (args.map projectValue))

mutual

/-- Destination-passing projection.
```
⟦·⟧ₓ⁻¹ : (⟦Γ⟧ ⊢ M ⇔ ⟦A⟧ & d) → ∃e⃗. (Γ, x : A ⊢ e⃗ : TVoid)
⟦·⟧⁻¹  : (⟦Γ⟧ ⊢ V ⇔ ⟦A⟧)     → ∃e. (Γ ⊢ e : A)
```
Dispatches to per-constructor helpers. -/
partial def proj (dest : StmtExprMd) : FGLProducer → ProjM (List StmtExprMd)
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

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (x := e_V); skip : TVoid   [assign]
├─ ⟦D_V⟧⁻¹ :: Γ ⊢ e_V : A
└─ Γ ⊢ skip : TVoid   [skip]
```
-/
partial def projProduce (dest : StmtExprMd) (md : Md) (v : FGLValue) : ProjM (List StmtExprMd) :=
  pure [mkLaurel md (.Assign [dest] (projectValue v))]

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
partial def projVarDecl (dest : StmtExprMd) (md : Md) (name : String) (ty : LowType)
    (init : FGLProducer) (body : FGLProducer) : ProjM (List StmtExprMd) := do
  let nameExpr := mkLaurel md (.Identifier (Identifier.mk name none))
  let decl := mkLaurel md (.LocalVariable (Identifier.mk name none) (mkHighTypeMd md (liftType ty)) none)
  projDecl decl
  let initStmts ← proj nameExpr init
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
partial def projAssign (dest : StmtExprMd) (_md : Md) (target : FGLValue)
    (val : FGLProducer) (body : FGLProducer) : ProjM (List StmtExprMd) := do
  let valStmts ← proj (projectValue target) val
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
partial def projIfThenElse (dest : StmtExprMd) (md : Md) (cond : FGLValue)
    (thn els after : FGLProducer) : ProjM (List StmtExprMd) := do
  let thnStmts ← proj dest thn
  let elsStmts ← proj dest els
  let thnBlock := mkLaurel md (.Block thnStmts none)
  let elsBlock := mkLaurel md (.Block elsStmts none)
  let ite := mkLaurel md (.IfThenElse (projectValue cond) thnBlock (some elsBlock))
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
partial def projWhileLoop (dest : StmtExprMd) (md : Md) (cond : FGLValue)
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
partial def projProcedureCall (dest : StmtExprMd) (md : Md) (callee : String)
    (args : List FGLValue) (outputs : List (String × LowType)) (body : FGLProducer) : ProjM (List StmtExprMd) := do
  for (n, ty) in outputs do
    projDecl (mkLaurel md (.LocalVariable (Identifier.mk n none) (mkHighTypeMd md (liftType ty)) none))
  let targets := outputs.map fun (n, _) => mkLaurel md (.Identifier (Identifier.mk n none))
  let call := mkLaurel md (.Assign targets (mkLaurel md (.StaticCall (Identifier.mk callee none) (args.map projectValue))))
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
partial def projAssert (dest : StmtExprMd) (md : Md) (cond : FGLValue)
    (body : FGLProducer) : ProjM (List StmtExprMd) := do
  let bodyStmts ← proj dest body
  pure ([mkLaurel md (.Assert (projectValue cond))] ++ bodyStmts)

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
partial def projAssume (dest : StmtExprMd) (md : Md) (cond : FGLValue)
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
partial def projLabeledBlock (dest : StmtExprMd) (md : Md) (label : String)
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

/-- Run projection with `LaurelResult` as destination. Declarations hoisted to top. -/
def projectProducer (prod : FGLProducer) : List StmtExprMd :=
  let (stmts, decls) := (proj (mkLaurel #[] (.Identifier (Identifier.mk "LaurelResult" none))) prod).run
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
        let retTy := match (proc.outputs.filter fun o => eraseType o.type.val != .TCore "Error").head? with
          | some o => o.type.val | none => .TVoid
        match tryGrades proc.name.text procEnv bodyExpr retTy [.pure, .proc, .err, .heap, .heapErr] with
        | some g =>
          let g := if proc.outputs.length > 1 then Grade.join g .err else g
          if knownGrades[proc.name.text]? != some g then
            knownGrades := knownGrades.insert proc.name.text g
            changed := true
        | none => pure ()
      | none => pure ()

  -- PASS 2: Elaborate each proc with final grades
  let mut procs : List Laurel.Procedure := []
  let mut allBoxConstructors : List (String × String × HighType) := []
  let mut allHoles : List (String × Bool × List (String × HighType) × HighType) := []
  let mut elabFailures : List String := []
  let mut globalCounter : Nat := 0
  for proc in program.staticProcedures do
    match proc.body with
    | .Transparent bodyExpr =>
      let extEnv := (proc.inputs ++ proc.outputs).foldl
        (fun (e : ElabTypeEnv) p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
      let inputList := proc.inputs.map fun p => (p.name.text, p.type.val)
      let procEnv : ElabEnv := { baseEnv with typeEnv := extEnv, procGrades := knownGrades, procInputs := inputList }
      let g := knownGrades[proc.name.text]?.getD .pure
      let retTy := match (proc.outputs.filter fun o => eraseType o.type.val != .TCore "Error").head? with
        | some o => o.type.val | none => .TVoid
      let st : ElabState := {
        freshCounter := globalCounter
        heapVar := if g == .heap || g == .heapErr then some "$heap" else none }
      -- Elaborate preconditions: a `requires` is a pure value of type bool, not an
      -- effect-sequenced statement, so it elaborates with the value judgment
      -- (checkValue) rather than the producer judgment. checkValue synthesizes the
      -- term and applies subtyping coercions — from_int/from_str on argument
      -- literals (the runtime operators take Any parameters) and Any_to_bool on the
      -- Any-typed result — then projectValue yields the single Core expression.
      -- Holes are collected as for bodies.
      let mut elabPreconditions : List (WithMetadata StmtExpr) := []
      for pre in proc.preconditions do
        let preSt : ElabState := { freshCounter := globalCounter }
        match (checkValue pre .TBool).run procEnv |>.run preSt with
        | some (preVal, preSt') =>
          globalCounter := preSt'.freshCounter
          let newHoles := (preSt'.usedHoles.map fun (name, det, outTy) => (name, det, inputList, outTy)).filter
            (fun (n, _, _, _) => !allHoles.any (fun (n2, _, _, _) => n == n2))
          allHoles := allHoles ++ newHoles
          elabPreconditions := elabPreconditions ++ [⟨(projectValue preVal).val, pre.md⟩]
        | none => elabPreconditions := elabPreconditions ++ [pre]
      let proc := { proc with preconditions := elabPreconditions }
      match (checkProducer bodyExpr [] retTy g).run procEnv |>.run st with
      | some (fgl, st') =>
        globalCounter := st'.freshCounter
        allBoxConstructors := allBoxConstructors ++ st'.usedBoxConstructors.filter
          (fun (c, _, _) => !allBoxConstructors.any (fun (c2, _, _) => c == c2))
        let newHoles := (st'.usedHoles.map fun (name, det, outTy) => (name, det, inputList, outTy)).filter
          (fun (n, _, _, _) => !allHoles.any (fun (n2, _, _, _) => n == n2))
        allHoles := allHoles ++ newHoles
        let projected := projectBody bodyExpr.md fgl
        let md := bodyExpr.md
        let heapInParam : Laurel.Parameter := { name := Identifier.mk "$heap_in" none, type := mkHighTypeMd md .THeap }
        let heapOutParam : Laurel.Parameter := { name := Identifier.mk "$heap" none, type := mkHighTypeMd md .THeap }
        let errOutParam : Laurel.Parameter := { name := Identifier.mk "maybe_except" none, type := mkHighTypeMd md (.TCore "Error") }
        let resultOutputs := proc.outputs.filter fun o => eraseType o.type.val != .TCore "Error"
        match g with
        | .heap =>
          let heapInit := mkLaurel md (.Assign [mkLaurel md (.Identifier (Identifier.mk "$heap" none))] (mkLaurel md (.Identifier (Identifier.mk "$heap_in" none))))
          let newBody := mkLaurel md (.Block ([heapInit] ++ (projectProducer fgl)) none)
          procs := procs ++ [{ proc with
            inputs := [heapInParam] ++ proc.inputs
            outputs := [heapOutParam] ++ resultOutputs
            body := .Transparent newBody }]
        | .heapErr =>
          let heapInit := mkLaurel md (.Assign [mkLaurel md (.Identifier (Identifier.mk "$heap" none))] (mkLaurel md (.Identifier (Identifier.mk "$heap_in" none))))
          let newBody := mkLaurel md (.Block ([heapInit] ++ (projectProducer fgl)) none)
          procs := procs ++ [{ proc with
            inputs := [heapInParam] ++ proc.inputs
            outputs := [heapOutParam] ++ resultOutputs ++ [errOutParam]
            body := .Transparent newBody }]
        | .err =>
          procs := procs ++ [{ proc with
            outputs := resultOutputs ++ [errOutParam]
            body := .Transparent projected }]
        | .proc | .pure =>
          procs := procs ++ [{ proc with body := .Transparent projected }]
      | none =>
        elabFailures := elabFailures ++ [proc.name.text]
        procs := procs ++ [proc]
    | _ => procs := procs ++ [proc]
  let hasHeap := knownGrades.toList.any fun (_, g) => g == .heap || g == .heapErr
  let compositeNames := typeEnv.classFields.toList.map (·.1)
  let typeTagDatatype : TypeDefinition := .Datatype {
    name := "TypeTag", typeArgs := [],
    constructors := compositeNames.map fun n => { name := Identifier.mk (n ++ "_TypeTag") none, args := [] } }
  let compositeType : TypeDefinition := .Datatype {
    name := "Composite", typeArgs := [],
    constructors := [{ name := Identifier.mk "MkComposite" none, args := [
      { name := Identifier.mk "ref" none, type := ⟨.TInt, #[]⟩ },
      { name := Identifier.mk "typeTag" none, type := ⟨.UserDefined "TypeTag", #[]⟩ }] }] }
  let fieldConstructors := typeEnv.classFields.toList.foldl (fun acc (className, fields) =>
    acc ++ fields.map fun (fieldName, _) =>
      { name := Identifier.mk ("$field." ++ className ++ "." ++ fieldName) none, args := [] : DatatypeConstructor }) []
  let fieldDatatype : TypeDefinition := .Datatype {
    name := "Field", typeArgs := [], constructors := fieldConstructors }
  let boxConstructors := allBoxConstructors.map fun (ctorName, _, ty) =>
    { name := Identifier.mk ctorName none, args := [
      { name := Identifier.mk (boxFieldName ty) none, type := ⟨boxFieldType ty, #[]⟩ }] : DatatypeConstructor }
  let boxDatatype : TypeDefinition := .Datatype {
    name := "Box", typeArgs := [], constructors := boxConstructors }
  let holeProcs := allHoles.map fun (name, deterministic, inputs, outTy) =>
    let params := inputs.map fun (pName, pType) =>
      ({ name := Identifier.mk pName none, type := ⟨pType, #[]⟩ } : Laurel.Parameter)
    let outputParam : Laurel.Parameter := { name := Identifier.mk "result" none, type := ⟨outTy, #[]⟩ }
    { name := Identifier.mk name none
      inputs := if deterministic then params else []
      outputs := [outputParam]
      preconditions := []
      determinism := if deterministic then .deterministic none else .nondeterministic
      decreases := none
      isFunctional := true
      body := .Opaque [] none []
      md := #[] : Laurel.Procedure }
  let result := if hasHeap then
    let heapTypesFiltered := heapConstants.types.filter fun td => match td with
      | .Datatype dt => dt.name.text != "Composite" && dt.name.text != "NotSupportedYet"
      | _ => true
    { program with
      staticProcedures := holeProcs ++ coreDefinitionsForLaurel.staticProcedures ++ heapConstants.staticProcedures ++ procs
      types := [fieldDatatype, boxDatatype, typeTagDatatype, compositeType] ++ heapTypesFiltered ++ coreDefinitionsForLaurel.types ++ program.types }
  else
    { program with
      staticProcedures := holeProcs ++ coreDefinitionsForLaurel.staticProcedures ++ procs
      types := [typeTagDatatype, compositeType] ++ coreDefinitionsForLaurel.types ++ program.types }
  pure (result, elabFailures)

end
end Strata.FineGrainLaurel

