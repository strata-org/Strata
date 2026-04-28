/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.SourceRange

/-!
# PythonSSA: Static Single Assignment IR for Python

Block-argument style SSA (Crucible/SWIFT) with instruction-level exception
precision. See `docs/PythonSSA.md` for the full reference manual.
-/

public section
namespace Strata.Python.SSA

/-! ## Module Name -/

/-- A Python module name split into dot-separated components.
    Parallel to `Specs.ModuleName` but kept separate to avoid coupling. -/
structure SSAModuleName where
  parts : Array String
  partsSizePos : parts.size > 0
deriving Repr

instance : BEq SSAModuleName where
  beq a b := a.parts == b.parts

instance : Hashable SSAModuleName where
  hash m := hash m.parts

instance : ToString SSAModuleName where
  toString m :=
    let p : m.parts.size > 0 := m.partsSizePos
    m.parts.foldl (init := m.parts[0]) (start := 1) (s!"{·}.{·}")

instance : Inhabited SSAModuleName where
  default := ⟨#["_"], by simp⟩

/-- Construct a single-component module name. -/
def SSAModuleName.ofString (s : String) : SSAModuleName :=
  ⟨#[s], by simp⟩

/-! ## Qualified Name -/

/-- A reference to a named object in a specific module.
    Pretty-prints with dot notation: `builtins.len`, `os.path.join`. -/
structure QualifiedName where
  module : SSAModuleName
  name   : String
deriving Inhabited, Repr, BEq

instance : Hashable QualifiedName where
  hash qn := mixHash (hash qn.module) (hash qn.name)

instance : ToString QualifiedName where
  toString qn := s!"{qn.module}.{qn.name}"

/-- Construct a qualified name from a single module component and name. -/
def QualifiedName.mk' (mod : String) (name : String) : QualifiedName :=
  ⟨SSAModuleName.ofString mod, name⟩

/-! ## Literal Values -/

inductive LiteralValue where
  | intVal  (v : Int)
  | strVal  (v : String)
  | boolVal (v : Bool)
deriving Inhabited, Repr, BEq

/-! ## OrderedMap -/

/-- An ordered map backed by `Array B` and `HashMap A Nat` for
    O(1) positional access and O(1) keyed lookup.
    Used for TypedDict fields. -/
structure OrderedMap (A : Type) (B : Type) [BEq A] [Hashable A] where
  values : Array B
  index  : Std.HashMap A Nat
  -- invariant: index maps keys to valid indices into values
deriving Inhabited

/-! ## Type System -/

inductive PyType where
  -- Primitives (corpus annotations + PySpec builtins)
  | any | str | int | bool | float | none | bytes | object
  -- Containers
  | list     (elem : PyType)
  | dict     (key val : PyType)
  | set      (elem : PyType)
  | tuple    (elems : Array PyType)
  -- Combinators
  | optional (inner : PyType)
  | union    (alts : Array PyType)
  -- Structural (from PySpec TypedDict)
  | typedDict (fields : OrderedMap String PyType) (total : Bool)
  -- Literal types (from PySpec)
  | literal  (alts : Array LiteralValue)
  -- Nominal (classes, services)
  | named    (name : String)
deriving Inhabited

/-! ## SSA Core Types -/

/-- An SSA value reference. IDs are unique within a function. -/
structure SSAVal where
  id : Nat
deriving Inhabited, Repr, BEq, Hashable

/-- A block label. IDs are unique within a function. -/
structure BlockId where
  id : Nat
deriving Inhabited, Repr, BEq, Hashable

/-- Human-readable name for an SSA value.
    `base` is the source-level variable name, `suffix` distinguishes versions. -/
structure SSAName where
  base   : String
  suffix : Nat
deriving Inhabited, Repr, BEq

instance : ToString SSAName where
  toString n := s!"{n.base}.{n.suffix}"

/-! ## Call Arguments -/

inductive CallArg where
  | positional (val : SSAVal)
  | keyword    (name : String) (val : SSAVal)
  | starArgs   (val : SSAVal)
  | starKwargs (val : SSAVal)
deriving Inhabited, Repr

/-! ## Operator Enums -/

inductive BinOpKind where
  | add | sub | mult | div | floorDiv | mod | pow
deriving Inhabited, Repr, BEq

inductive UnaryOpKind where
  | not_ | uSub
deriving Inhabited, Repr, BEq

inductive CmpOpKind where
  | eq | notEq | lt | ltE | gt | gtE | is_ | isNot | in_ | notIn
deriving Inhabited, Repr, BEq

/-! ## Instructions -/

/-- Non-terminal instructions. Each defines exactly one SSA value. -/
inductive Instruction where
  -- Control flow helpers (never raise)
  | undef       (name : String)
  | isDefined   (val : SSAVal)
  -- Constants (never raise)
  | intLit      (val : Int)
  | floatLit    (val : String)
  | strLit      (val : String)
  | boolLit     (val : Bool)
  | noneLit
  | bytesLit    (val : String)
  -- Calls and references (potentially raising)
  | call        (func : SSAVal) (args : Array CallArg)
  | qualifiedRef (qn : QualifiedName)
  | attr        (obj : SSAVal) (name : String)
  | setAttr     (obj : SSAVal) (name : String) (val : SSAVal)
  -- Operators (potentially raising)
  | binOp       (op : BinOpKind) (lhs rhs : SSAVal)
  | unaryOp     (op : UnaryOpKind) (operand : SSAVal)
  | compareOp   (op : CmpOpKind) (lhs rhs : SSAVal)
  -- Data structures
  | mkDict      (keys vals : Array SSAVal)
  | mkList      (elems : Array SSAVal)
  | mkTuple     (elems : Array SSAVal)
  | getItem     (obj key : SSAVal)
  | setItem     (obj key val : SSAVal)
  | getSlice    (obj : SSAVal) (lo hi step : Option SSAVal)
  -- Strings
  | fmtValue    (val : SSAVal)
  | strConcat   (parts : Array SSAVal)
  -- Assertions (potentially raising AssertionError)
  | assert_     (cond : SSAVal) (msg : Option SSAVal)
  -- Graceful degradation (never raises)
  | unsupported (name : String)
deriving Inhabited, Repr

/-! ## Terminators -/

inductive Terminator where
  | branch     (target : BlockId) (args : Array SSAVal)
  | condBranch (cond : SSAVal)
               (thenB : BlockId) (thenArgs : Array SSAVal)
               (elseB : BlockId) (elseArgs : Array SSAVal)
  | ret        (val : Option SSAVal)
  | raise      (exc : SSAVal)
  | unreachable
deriving Inhabited, Repr

/-! ## Exception Handling -/

/-- A value in an `exceptArgs` array: either a regular SSA value or the
    `exc` placeholder representing the exception object. -/
inductive ExceptArgVal where
  | val  (v : SSAVal)
  | exc
deriving Inhabited, Repr, BEq

/-- Exception handler target for a block. -/
structure ExceptTarget where
  target : BlockId
deriving Inhabited

/-! ## Blocks -/

/-- Block parameter (entry argument). -/
structure BlockParam where
  val  : SSAVal
  type : Option PyType
  sr   : SourceRange
deriving Inhabited

/-- A named instruction defining an SSA value. -/
structure NamedInstr where
  result     : Option SSAVal
  type       : Option PyType
  instr      : Instruction
  sr         : SourceRange
  exceptArgs : Option (Array ExceptArgVal)
deriving Inhabited

/-- A basic block with one entry and multiple exits. -/
structure Block where
  id     : BlockId
  params : Array BlockParam
  instrs : Array NamedInstr
  term   : Terminator
  termSr : SourceRange
  except : Option ExceptTarget
deriving Inhabited

/-! ## Functions -/

inductive ParamKind where
  | positional | posOnly | kwOnly | varPositional | varKeyword
deriving Inhabited, Repr, BEq

structure FuncParam where
  val     : SSAVal
  name    : String
  type    : Option PyType
  default : Option SSAVal
  kind    : ParamKind
deriving Inhabited

/-- A function in the SSA IR. -/
structure Func where
  name       : String
  params     : Array FuncParam
  retType    : Option PyType
  blocks     : Array Block
  names      : Array SSAName
  decorators : Array String
  sr         : SourceRange
deriving Inhabited

/-! ## Module -/

/-- A complete SSA module. -/
structure Module where
  name  : String
  funcs : Array Func
deriving Inhabited

/-! ## Prelude -/

/-- The Python builtin prelude: source-level names → qualified identities. -/
def pythonPrelude : Std.HashMap String QualifiedName :=
  let builtins := SSAModuleName.ofString "builtins"
  let mk name := (name, QualifiedName.mk builtins name)
  .ofList [
    -- Functions
    mk "print", mk "len", mk "str", mk "open", mk "input",
    mk "enumerate", mk "int", mk "list", mk "range", mk "set",
    mk "sum", mk "isinstance", mk "abs", mk "float", mk "iter",
    mk "next",
    -- Exceptions/Types
    mk "Exception", mk "ValueError", mk "KeyboardInterrupt",
    mk "TypeError", mk "KeyError", mk "RuntimeError",
    mk "StopIteration", mk "AssertionError"
  ]
