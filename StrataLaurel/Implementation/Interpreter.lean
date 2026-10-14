/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Std.Data.HashMap
public import StrataLaurel.Implementation

namespace Strata.Laurel.Interpreter

public section

open Strata.Laurel

structure Options where
  dumpState : Bool := true
  entryProcedure : String := "main"
  /-- Print a line per passing `assert`. On by default because the existing
      Laurel examples read as a transcript; a runtime with hundreds of thousands
      of asserts needs it off. -/
  printAsserts : Bool := true
  /-- Maximum evaluation steps before giving up, so a divergent program under
      test fails instead of hanging. -/
  fuel : Nat := 100000000
  deriving Inhabited

/-- A value that lives in the host (backend) language rather than in Lean —
    the result of an external procedure call. The interpreter never inspects
    the host value directly; it only holds a *handle* to it:
    - `path`: the on-disk location where the backend serialized the host value.
      Externals are exchanged with the host through files rather than in-process,
      so the interpreter refers to a host value by the path to its blob and hands
      that path back to the backend to reload, down-convert, or compare it (see
      `ExternalBackend`).
    - `display`: a human-readable rendering of the host value, captured at
      creation time for state dumps / debugging (`Value.display`). -/
structure ExternalValue where
  path    : System.FilePath
  display : String
  deriving Inhabited

structure IntPrimitive where
  n : Int
  deriving Inhabited, DecidableEq

structure BoolPrimitive where
  b : Bool
  deriving Inhabited, DecidableEq

structure StringPrimitive where
  s : String
  deriving Inhabited, DecidableEq

/-- A runtime value in the interpreter. This is deliberately *not* the full
    Laurel type system — it is only what the interpreter needs to hold in the
    stack and pass across the external boundary:
    - the three Laurel *primitives* (`int`, `bool`, `string`), which the
      interpreter owns and manipulates directly; and
    - `external`, an opaque handle to a value living in the host/backend
      language (see `ExternalValue`).

    It does *not* yet have a case for aggregates / objects (C `struct`, Java
    `class`, arrays, tuples, etc.).  For now such values only reach the
    interpreter as `external` handles produced and consumed by the backend. -/
inductive Value where
  | external (v : ExternalValue)
  | int      (v : IntPrimitive)
  | bool     (v : BoolPrimitive)
  | string   (v : StringPrimitive)
  /-- A `real`. Laurel's `real` is the mathematical reals, so `Rat` models it
      exactly rather than approximating it as a float. -/
  | real     (v : Rat)
  /-- A reference to a composite instance: an index into `EvalState.heap`.
      Composites are reference types, so this is what `==` compares (identity)
      and what a field write mutates through. -/
  | ref      (addr : Nat)
  /-- A datatype value: the constructor's name and its arguments. Compared
      structurally, which is what makes two equal `PyKey`s the same dict key. -/
  | data     (ctor : String) (args : Array Value)
  /-- A `Sequence<T>`, as its elements. A value, not a buffer: `seqUpdate`
      returns a new one. -/
  | seq      (items : Array Value)
  /-- A `Map<K, V>`, as an association list of
      `(Value.keyRepr key, key, value)`.

      An association list and not a `Std.HashMap`: a hash map nested inside this
      inductive is not a legal nested occurrence (the kernel rejects it), and
      `List` is. Lookup is therefore linear, which is affordable because the maps
      a Laurel program builds are small — PyDyn's largest are a module's globals
      and a type's method table, tens of entries each. `mapSet` REPLACES an
      existing entry rather than shadowing it, so repeated writes to one key keep
      the list at its number of live keys instead of growing without bound.

      `absent` is what a read of a key the map does not hold answers: the value
      type's default, fixed when the map is created, since a read site does not
      carry the value type. -/
  | map      (entries : List (String × Value × Value)) (absent : Value)
  /-- A `bv width` value, as its unsigned magnitude `n < 2 ^ width`. -/
  | bv       (width : Nat) (n : Nat)
  /-- A variable, field or output of a type with no default value (a composite, a
      datatype, a type variable) that has been declared but never assigned. Laurel
      gives it an arbitrary value, so reading one is not an error; consuming it is
      (an operator, a branch condition, a comparison), because the interpreter has
      no value of that type to choose. A type that has a default starts at it
      instead, see `defaultValue`. -/
  | unset
  deriving Inhabited

partial def Value.display : Value → String
  | .external e => e.display
  | .int p      => toString p.n
  | .bool p     => toString p.b
  | .string p   => p.s
  | .real r     => toString r
  | .ref a      => s!"#{a}"
  | .data c as_ =>
    if as_.isEmpty then s!"{c}()"
    else s!"{c}({String.intercalate ", " (as_.toList.map Value.display)})"
  | .seq items  => s!"[{String.intercalate ", " (items.toList.map Value.display)}]"
  | .map m _    => s!"map(size {m.length})"
  | .bv w n     => s!"{n}bv{w}"
  | .unset      => "<unset>"

/-- A collision-free string rendering used as a `Map` key.

    A Laurel `Map` key is an arbitrary value, and `Std.HashMap` needs `Hashable`,
    which `Value` cannot derive while it carries an `ExternalValue`. Rendering the
    key structurally sidesteps that. It must be injective, so constructor
    arguments are length-prefixed rather than separated — otherwise `K("a,b")` and
    `K("a", "b")` would collide, and two distinct dict keys would become one. -/
partial def Value.keyRepr : Value → String
  | .int p      => s!"i{p.n}"
  | .bool p     => s!"b{p.b}"
  | .string p   => s!"s{p.s.length}:{p.s}"
  | .real r     => s!"r{r}"
  | .ref a      => s!"@{a}"
  | .data c as_ =>
    let parts := as_.toList.map (fun a => let r := Value.keyRepr a; s!"{r.length}:{r}")
    s!"d{c.length}:{c}({String.intercalate "" parts})"
  | .seq items =>
    let parts := items.toList.map (fun a => let r := Value.keyRepr a; s!"{r.length}:{r}")
    s!"q[{String.intercalate "" parts}]"
  | .map m d =>
    let dr := Value.keyRepr d
    let m := m.filter fun (_, _, v) => Value.keyRepr v != dr
    -- Sorted by the entry key's repr: `mapSet` conses fresh entries to the
    -- front, so two equal maps built in different orders hold their entries in
    -- different orders, and injectivity is over the map VALUE, not the list.
    let parts := (m.map (fun (kr, _, v) =>
      let vr := Value.keyRepr v
      s!"{kr.length}:{kr}{vr.length}:{vr}")).mergeSort (· ≤ ·)
    s!"m{m.length}[{String.intercalate "" parts}]{dr.length}:{dr}"
  | .bv w n     => s!"v{w}:{n}"
  | .unset      => "u"
  | .external e => s!"x{e.path}"

/-- Structural equality, with reference identity for composites.

    `.ref` compares addresses because a Laurel composite is a reference type, so
    `==` on two composites is identity — the distinction PyDyn relies on for
    `x is None`. Everything else compares by value. -/
partial def Value.eq : Value → Value → Bool
  | .int a,    .int b    => a == b
  | .bool a,   .bool b   => a == b
  | .string a, .string b => a == b
  | .real a,   .real b   => a == b
  | .ref a,    .ref b    => a == b
  | .bv w1 a,  .bv w2 b  => w1 == w2 && a == b
  | .unset,    .unset    => true
  | .data c1 a1, .data c2 a2 =>
    c1 == c2 && a1.size == a2.size &&
      (a1.zip a2).all (fun (x, y) => Value.eq x y)
  | .seq a,    .seq b    =>
    a.size == b.size && (a.zip b).all (fun (x, y) => Value.eq x y)
  | .map a da, .map b db =>
    -- Extensional: equal defaults, and the same value at every key once an
    -- entry holding the default is read as absent.
    let live (m : List (String × Value × Value)) (d : Value) :=
      m.filter fun (_, _, v) => !Value.eq v d
    let a := live a da
    let b := live b db
    Value.eq da db &&
    -- Order-insensitive: `mapSet` conses to the front, so equal maps can hold
    -- their entries in different orders. Key reprs are unique within a map,
    -- so equal sizes plus every left entry matched on the right is equality.
    a.length == b.length &&
      a.all (fun (kr, _, v) =>
        match b.find? (fun (r, _, _) => r == kr) with
        | some (_, _, w) => Value.eq v w
        | none => false)
  | _,         _         => false

/-- One composite instance on the heap: its runtime type name (what `is`/`as`
    test against) and its fields. -/
structure HeapObject where
  typeName : String
  fields   : Std.HashMap String Value
  deriving Inhabited

/-- One call frame: local variables (keyed by name) to their evaluated values.
    The stack of frames is implicit in Lean's own call stack — `invokeProc`
    saves the caller's frame, runs the callee with a fresh one, then restores. -/
abbrev StackFrame := Std.HashMap String Value

/-- One live coroutine instance: everything about a suspended `coroutine` body
    that has to survive between two `resume`s.

    The instance itself is an ordinary `HeapObject`, so a plain `Value.ref`
    denotes it and `is` / `as` / state dumps need no coroutine-specific cases;
    this record is the side state that a heap object cannot hold, keyed by the
    same address (`EvalState.coros`).

    State is threaded functionally through `EvalM` — there is no shared mutable
    heap — so a suspended coroutine cannot be a paused Lean computation (a thread
    or a continuation). Instead a suspension is *reified*: `resumePt` is the path
    of child indices from the body's root to the `yield` that stopped it, and a
    resume replays the body, fast-forwarding to that path. -/
structure CoroState where
  /-- The `coroutine` procedure this is an instance of. -/
  proc      : String
  /-- Its locals: the captured inputs, the `yields` / `resumes` bindings, and
      whatever the body declared before it suspended. -/
  frame     : StackFrame
  /-- The suspension point, as a path of child indices from the body's root.
      `none` before the first resume — the body has not started. -/
  resumePt  : Option (List Nat)
  /-- Set once the body returns or falls off its end. A finished coroutine
      cannot be resumed again. -/
  finished  : Bool := false
  /-- Set while the body is executing, so a resume from inside it is refused
      instead of replaying the body into itself. -/
  running   : Bool := false
  /-- The value the pending `resume` sent in: what the expression form of
      `yield` (`z := yield`) evaluates to when the body wakes up. -/
  sent      : Value := .unset
  /-- The value the body finished *with* — the payload of the `return` that ended
      it, `.unset` if it fell off its end. This is what lets a client tell
      "finished, and the result was v" from plain "finished"; read it with
      `coroCompletion(co)`. -/
  completed : Value := .unset
  deriving Inhabited

/-- Everything about a program that does not change while it runs, computed once
    at startup. Procedures are looked up through hash maps, because a runtime
    written in Laurel makes millions of calls. -/
structure ProgramIndex where
  procs : Std.HashMap String Procedure := {}
  /-- Static procedures by the `uniqueId` resolution stamped on their name. A
      resolved call carries its overload's id, which is what tells two overloads
      sharing a name apart; an unresolved call falls back to `procs`. -/
  procsById : Std.HashMap Nat Procedure := {}
  /-- Composite name → its own instance procedures, by name. An instance call
      walks the receiver's `ancestors` and takes the first hit, which is dynamic
      dispatch: an override in a subtype is found before the method it overrides. -/
  methods : Std.HashMap String (Std.HashMap String Procedure) := {}
  /-- Names declared by more than one static procedure. A call to one carries no
      overload unless it was resolved. -/
  overloaded : Std.HashSet String := {}
  /-- Every static procedure declaring a name, overloads included. -/
  procsNamed : Std.HashMap String (List Procedure) := {}
  /-- Composite name → its fields, including inherited ones, with initializers. -/
  compositeFields : Std.HashMap String (List (String × HighType × Option StmtExprMd)) := {}
  /-- Type alias and constrained type name → the type it stands for, so a value of
      one starts at that type's default. -/
  typeAliases : Std.HashMap String HighType := {}
  /-- Constrained type name → its witness's value. A value of the type starts at its
      witness, which satisfies the constraint where the base type's default might not.
      A literal witness is read when the index is built; any other is evaluated before
      the entry runs. -/
  witnesses : Std.HashMap String Value := {}
  /-- Constrained types whose witness could not be evaluated, so they have no value to
      start at. -/
  noWitness : Std.HashSet String := {}
  /-- Composite name → its ancestors, including itself. `x is T` is a membership
      test in this list, so it is precomputed rather than walked per test. -/
  ancestors : Std.HashMap String (List String) := {}
  /-- Datatype constructor name → its field names, in order. -/
  ctors : Std.HashMap String (List String) := {}
  /-- Tester name (`PyKey..isKInt`) → the constructor it tests. -/
  testers : Std.HashMap String String := {}
  /-- Destructor name (`PyKey..ki`, and the `!` variant) → (constructor, index). -/
  destructors : Std.HashMap String (String × Nat × HighType) := {}
  deriving Inhabited

structure EvalState where
  stack    : StackFrame
  program  : Program
  index    : ProgramIndex := {}
  /-- Composite instances, indexed by the address a `Value.ref` carries.
      A single growable array rather than a map per object, so allocation is a
      push and a field write is an in-place `Array.set`. -/
  heap     : Array HeapObject := #[]
  /-- Steps remaining. The Laurel interpreter has no fuel of its own, but a
      program under test can diverge, and a test harness needs that to come back
      as an error rather than a hang. -/
  fuel     : Nat := 0
  /-- Runtime assertion failures accumulated during a run, in evaluation order.
      A failing `assert` records a source-mapped `Message` here and execution
      continues, mirroring the Core interpreter's `collectAllAssertFailures`
      behavior so the same examples can be checked against both interpreters. -/
  assertFailures : Array Strata.Message := #[]
  /-- Set when `printAsserts` is off; see `Options`. -/
  quiet : Bool := false
  /-- Names of the procedures currently on the call stack, innermost first.
      Only used to locate a runtime error: a message like "read of unassigned
      field" is nearly useless without knowing which procedure did the reading,
      and a Laurel-level runtime has no source positions to fall back on. -/
  callStack : List String := []
  /-- File-scope globals (`Program.staticFields`), by name.
      Kept apart from `stack` because a frame comes and goes with every call while
      these outlive all of them. A reference to one is syntactically just
      `Variable.Local` -- resolution records the distinction in its model, not in the
      tree -- so a read falls back here when the name is not a local of the current
      frame, and a write goes here only when the name is not a local either. A
      declared local therefore always shadows a global of the same name, which is
      what Laurel's scoping says. -/
  globals  : Std.HashMap String Value := {}
  /-- Live coroutine instances, keyed by the heap address their `Value.ref`
      carries. See `CoroState`. -/
  coros    : Std.HashMap Nat CoroState := {}
  /-- The instance whose coroutine body is currently running, `none` outside any
      coroutine body. A `yield` suspends *this* instance, and a procedure called
      from a coroutine body is not part of it, so the callee runs with `none`.

      It doubles as the switch for the two position fields below: they only mean
      anything inside a coroutine body, so every statement list checks this once
      and otherwise walks with no bookkeeping at all. -/
  coroSelf : Option Nat := none
  /-- The position currently being executed, as the path of child indices from
      the running coroutine body's root, outermost first. A `yield` reifies its
      suspension point by copying this. Only maintained while `coroSelf` is set.

      Every construct sets its children's position *absolutely*, from the value
      it read on entry, rather than by pushing and popping: an `exit`, a `throw`
      or a suspension leaves through the exception channel and would skip a pop
      exactly when the position matters. -/
  cursor   : List Nat := []
  /-- Set for the duration of a resume's fast-forward: the remaining path to the
      suspension point. While it is `some (i :: _)` the statements before child
      `i` are skipped — they already ran in an earlier step. `some []` is the
      arrival marker: the next `yield` reached is the one that suspended, so it
      delivers the resumed value instead of suspending again. -/
  seek     : Option (List Nat) := none
  /-- The source range of the call expression most recently entered, read by the
      call itself before its arguments overwrite it. A violated precondition is
      reported there, as the verifier reports it. -/
  callSite : FileRange := .unknown
  /-- The source range of the statement being run, where a check Core places on a
      whole statement (a safe destructor's constructor test) is reported. -/
  stmtSite : FileRange := .unknown
  /-- The heap, file-scope globals and in-out parameters a procedure was entered
      with, while its postconditions are being checked. `old(e)` evaluates `e`
      against these: it is Core's two-state `old`, so every other local and
      parameter reads its current value. -/
  entryState : Option (Array HeapObject × Std.HashMap String Value × StackFrame) := none
  /-- Set while an `old(e)` is being evaluated, so a read of an object the
      procedure allocated can say so. -/
  inOld : Bool := false
  deriving Inhabited

abbrev DisplayStackFrame := Std.HashMap String String

structure DisplayEvalState where
  stack : DisplayStackFrame
  deriving Inhabited

def DisplayEvalState.format (s : DisplayEvalState) : String :=
  let entries := s.stack.toList.mergeSort (fun a b => a.1 < b.1)
  let lines := entries.map (fun (k, v) => s!"  {k} = {v}")
  String.intercalate "\n" ("stack:" :: lines)

/-- Non-local control-flow signals that unwind the interpreter monad.
    `return_` is thrown at a `return` statement and caught at the procedure-call
    boundary; the others are described on their constructors. -/
inductive Control where
  /-- A `return`. Carries the values of the procedure's outputs, which for a
      multi-output procedure are read out of the frame rather than supplied by the
      `return` itself. Caught at the call boundary. -/
  | return_ (value : Option Value)
  /-- `exit L` — leave the enclosing block labelled `L`. Caught by that block,
      which is how Laurel spells `break` and `continue`. -/
  | exit_ (label : String)
  /-- `throw v` — the exceptional channel. Caught by an enclosing `catch` whose
      predicate holds, and otherwise propagates through the call boundary, unlike
      `return_`. -/
  | throw_ (value : Value)
  /-- Step budget exhausted. Distinct from an `IO` error so a harness can tell a
      divergent program from a malformed one. -/
  | outOfFuel
  /-- `yield` — the running coroutine body suspends. Carries nothing: the
      suspension point and the frame are written into the instance
      (`EvalState.coros`) at the `yield` itself, because `EvalState.cursor` names
      the yield's own position only there. Caught by the `resume` that started
      this step, and by nothing in between — in particular a `finally` must not
      run at a suspension, since the body has not left its `try`. -/
  | suspended

abbrev EvalM := ExceptT Control (StateT EvalState IO)

/-- Abstraction for backends that support external (host-language) values.
    Every field except `cleanup` defaults to throwing `IO.userError`, so a
    backend with no external support (e.g. pure Lean) is just `{}`. Backends
    that *do* support externals override the relevant fields. -/
structure ExternalBackend where
  cleanup      : IO Unit := pure ()
  /-- Runs the named external procedure with `args`. Always produces a host
      value; callers wrap with `.external` at the use site. -/
  callExternal : (name : String) → (args : List Value) → IO ExternalValue :=
    fun name _ => throw (IO.userError s!"No ExternalBackend support for calling external procedure '{name}'")
  /-- Explicit down-conversion from an `ExternalValue` to a Laurel primitive.
      The type system is expected to guarantee the underlying host value has
      the requested Laurel type; a wrong-shape `display` throws. -/
  valueInt     : ExternalValue → IO IntPrimitive :=
    fun _ => throw (IO.userError "No ExternalBackend support for valueInt")
  valueBool    : ExternalValue → IO BoolPrimitive :=
    fun _ => throw (IO.userError "No ExternalBackend support for valueBool")
  valueString  : ExternalValue → IO StringPrimitive :=
    fun _ => throw (IO.userError "No ExternalBackend support for valueString")
  /-- Direct truthiness read of a host value using the host language's own
      coercion rules. Not a type-checked Bool conversion — assertions may
      consume any host value, so backends decide truthiness (e.g. JS
      `Boolean(v)`, Python `bool(v)`). -/
  externalTruthy : ExternalValue → IO Bool :=
    fun _ => throw (IO.userError "No ExternalBackend support for externalTruthy")

/-- Laurel-owned truthiness. `.external` defers to the backend's
    `externalTruthy` since only the host knows its own coercion rules;
    `.int`/`.string` error rather than being coerced. -/
private def isTrue (cfg : ExternalBackend) : Value → IO Bool
  | .bool p     => pure p.b
  | .external e => cfg.externalTruthy e
  | v           => throw (IO.userError s!"expected Bool for truthiness, got: {v.display}")

/-- Structural equality on primitives. External-vs-external comparison
    is unsupported: `display` is a rendering, not identity, and only the
    host language defines equality on its own values. Mixed
    `.external`/primitive shapes down-convert via the backend and compare
    as Laurel primitives (needed so `len("s") == 5` works: an external
    call's return value is `.external`, but the assertion phrases it as
    a primitive). Mixed primitive shapes are unequal. -/
private def primEq (cfg : ExternalBackend) : Value → Value → IO Bool
  -- The aggregate and reference cases are Laurel-owned and never involve the
  -- host, so they answer from `Value.eq` (identity for `.ref`, structural
  -- otherwise) without consulting the backend.
  -- An unassigned value of a type with no default is one fixed arbitrary value:
  -- equal to itself, and to no assigned value.
  | .unset,       .unset       => pure true
  | .unset,       _            => pure false
  | _,            .unset       => pure false
  | .ref a,       .ref b       => pure (a == b)
  | .real a,      .real b      => pure (a == b)
  | .bv w1 a,     .bv w2 b     => pure (w1 == w2 && a == b)
  | a@(.data ..), b            => pure (Value.eq a b)
  | a,            b@(.data ..) => pure (Value.eq a b)
  | a@(.seq _),   b            => pure (Value.eq a b)
  | a,            b@(.seq _)   => pure (Value.eq a b)
  | a@(.map ..),  b            => pure (Value.eq a b)
  | a,            b@(.map ..)  => pure (Value.eq a b)
  | .int a,       .int b       => pure (a == b)
  | .bool a,      .bool b      => pure (a == b)
  | .string a,    .string b    => pure (a == b)
  | .external _,  .external _  =>
      throw (IO.userError "unsupported equality on two .external values: host-value equality is a host concern; cast one side via valueInt/valueBool/valueString first")
  | .external a,  .int b       => do let p ← cfg.valueInt a;    pure (p == b)
  | .int a,       .external b  => do let p ← cfg.valueInt b;    pure (a == p)
  | .external a,  .bool b      => do let p ← cfg.valueBool a;   pure (p == b)
  | .bool a,      .external b  => do let p ← cfg.valueBool b;   pure (a == p)
  | .external a,  .string b    => do let p ← cfg.valueString a; pure (p == b)
  | .string a,    .external b  => do let p ← cfg.valueString b; pure (a == p)
  | _,            _            => pure false

/-- Compact per-variant label for error messages, so mismatched-shape
    op-dispatch errors read as `[.int, .string]` rather than dumping the
    entire value. -/
private def reprVariant : Value → String
  | .external _ => ".external"
  | .int _      => ".int"
  | .bool _     => ".bool"
  | .string _   => ".string"
  | .real _     => ".real"
  | .ref _      => ".ref"
  | .data c _   => s!".data({c})"
  | .seq _      => ".seq"
  | .map ..     => ".map"
  | .bv w _     => s!".bv{w}"
  | .unset      => ".unset"

/-- Laurel-owned primitive-op dispatch. `.external` values are rejected:
    callers must explicitly cast via `valueInt`/`valueBool`/`valueString`
    before feeding a host value to a primitive op. `.Eq`/`.Neq` are the sole
    exception, since equality legitimately spans shapes via `primEq`. -/
private def evalOp (cfg : ExternalBackend) : Operation → List Value → IO Value
  -- Bool
  | .Not, [.bool ⟨x⟩]              => pure (.bool ⟨!x⟩)
  | .Not, args                     =>
      throw (IO.userError s!"unsupported types for op .Not: {args.map reprVariant}")
  | .And, [.bool ⟨x⟩, .bool ⟨y⟩]   => pure (.bool ⟨x && y⟩)
  | .And, args                     =>
      throw (IO.userError s!"unsupported types for op .And: {args.map reprVariant}")
  | .Or, [.bool ⟨x⟩, .bool ⟨y⟩]    => pure (.bool ⟨x || y⟩)
  | .Or, args                      =>
      throw (IO.userError s!"unsupported types for op .Or: {args.map reprVariant}")
  -- Int arithmetic
  | .Add, [.int ⟨x⟩, .int ⟨y⟩]     => pure (.int ⟨x + y⟩)
  | .Add, [.real x, .real y]       => pure (.real (x + y))
  | .Add, args                     =>
      throw (IO.userError s!"unsupported types for op .Add: {args.map reprVariant}")
  | .Sub, [.int ⟨x⟩, .int ⟨y⟩]     => pure (.int ⟨x - y⟩)
  | .Sub, [.real x, .real y]       => pure (.real (x - y))
  | .Sub, args                     =>
      throw (IO.userError s!"unsupported types for op .Sub: {args.map reprVariant}")
  | .Mul, [.int ⟨x⟩, .int ⟨y⟩]     => pure (.int ⟨x * y⟩)
  | .Mul, [.real x, .real y]       => pure (.real (x * y))
  | .Mul, args                     =>
      throw (IO.userError s!"unsupported types for op .Mul: {args.map reprVariant}")
  -- A zero divisor violates the operator's `requires`, which the call reports
  -- (see `checkOpPreconditions`); the quotient itself is then unconstrained, and
  -- answers the type's default.
  | .Div, [.int ⟨x⟩, .int ⟨y⟩]     =>
      if y == 0 then pure (.int ⟨0⟩) else pure (.int ⟨Int.ediv x y⟩)
  | .Div, [.real x, .real y]       =>
      if y == 0 then pure (.real 0) else pure (.real (x / y))
  | .Div, args                     =>
      throw (IO.userError s!"unsupported types for op .Div: {args.map reprVariant}")
  | .Mod, [.int ⟨x⟩, .int ⟨y⟩]     =>
      if y == 0 then pure (.int ⟨0⟩) else pure (.int ⟨Int.emod x y⟩)
  | .Mod, args                     =>
      throw (IO.userError s!"unsupported types for op .Mod: {args.map reprVariant}")
  | .Neg, [.int ⟨x⟩]               => pure (.int ⟨-x⟩)
  | .Neg, [.real x]                => pure (.real (-x))
  | .Neg, args                     =>
      throw (IO.userError s!"unsupported types for op .Neg: {args.map reprVariant}")
  -- String
  | .StrConcat, [.string ⟨x⟩, .string ⟨y⟩] => pure (.string ⟨x ++ y⟩)
  | .StrConcat, args                       =>
      throw (IO.userError s!"unsupported types for op .StrConcat: {args.map reprVariant}")
  -- Int, real and string comparisons. `real` is Laurel's mathematical reals, so
  -- these are exact `Rat` comparisons rather than float ones; strings compare
  -- lexicographically by code point, as the prelude's `$strLt` does.
  | .Lt, [.int ⟨x⟩, .int ⟨y⟩]      => pure (.bool ⟨x < y⟩)
  | .Lt, [.real x, .real y]        => pure (.bool ⟨x < y⟩)
  | .Lt, [.string ⟨x⟩, .string ⟨y⟩] => pure (.bool ⟨decide (x < y)⟩)
  | .Lt, args                      =>
      throw (IO.userError s!"unsupported types for op .Lt: {args.map reprVariant}")
  | .Leq, [.int ⟨x⟩, .int ⟨y⟩]     => pure (.bool ⟨x <= y⟩)
  | .Leq, [.real x, .real y]       => pure (.bool ⟨x <= y⟩)
  | .Leq, [.string ⟨x⟩, .string ⟨y⟩] => pure (.bool ⟨decide (x ≤ y)⟩)
  | .Leq, args                     =>
      throw (IO.userError s!"unsupported types for op .Leq: {args.map reprVariant}")
  | .Gt, [.int ⟨x⟩, .int ⟨y⟩]      => pure (.bool ⟨x > y⟩)
  | .Gt, [.real x, .real y]        => pure (.bool ⟨x > y⟩)
  | .Gt, [.string ⟨x⟩, .string ⟨y⟩] => pure (.bool ⟨decide (y < x)⟩)
  | .Gt, args                      =>
      throw (IO.userError s!"unsupported types for op .Gt: {args.map reprVariant}")
  | .Geq, [.int ⟨x⟩, .int ⟨y⟩]     => pure (.bool ⟨x >= y⟩)
  | .Geq, [.real x, .real y]       => pure (.bool ⟨x >= y⟩)
  | .Geq, [.string ⟨x⟩, .string ⟨y⟩] => pure (.bool ⟨decide (y ≤ x)⟩)
  | .Geq, args                     =>
      throw (IO.userError s!"unsupported types for op .Geq: {args.map reprVariant}")
  | .Implies, [.bool ⟨x⟩, .bool ⟨y⟩] => pure (.bool ⟨!x || y⟩)
  | .Implies, args                 =>
      throw (IO.userError s!"unsupported types for op .Implies: {args.map reprVariant}")
  -- Real arithmetic shares these `Operation` constructors with the integer forms
  -- and is dispatched on the argument shape, so each `.real` alternative sits
  -- beside its `.int` one -- above the shared catch-all, or it would be dead.
  -- Truncating division and modulus, i.e. rounding toward zero. Distinct from
  -- `.Div`/`.Mod`, which are Euclidean, and the two disagree on negatives.
  | .DivT, [.int ⟨x⟩, .int ⟨y⟩]    =>
      if y == 0 then pure (.int ⟨0⟩) else pure (.int ⟨x.tdiv y⟩)
  | .DivT, args                    =>
      throw (IO.userError s!"unsupported types for op .DivT: {args.map reprVariant}")
  | .ModT, [.int ⟨x⟩, .int ⟨y⟩]    =>
      if y == 0 then pure (.int ⟨0⟩) else pure (.int ⟨x.tmod y⟩)
  | .ModT, args                    =>
      throw (IO.userError s!"unsupported types for op .ModT: {args.map reprVariant}")
  -- Equality (spans shapes via primEq)
  | .Eq,  [a, b] => do
      let eq ← primEq cfg a b
      pure (.bool ⟨eq⟩)
  | .Neq, [a, b] => do
      let eq ← primEq cfg a b
      pure (.bool ⟨!eq⟩)
  | op, args =>
      throw (IO.userError s!"unsupported op {repr op} on args: {args.map reprVariant}")

/-! ## Prelude collections, as interpreter builtins

`Sequence` and `Map` reach Laurel as `external` prelude
procedures whose meaning lives in Core's factory (`mapGet` even has a Laurel body
spelled with Core's `select`). None of that is available here, so the interpreter
owns them directly, dispatched by procedure name before any body is consulted.

Implementing them natively rather than interpreting a Laurel encoding is also what
keeps them cheap: a dict lookup is a hash lookup, not a walk down a chain of
`update` frames. -/

/-- The prelude's per-width signed bitvector comparisons, `$bv<w>SLt` and friends.
    They are `external` in the prelude because Core implements them, so the
    interpreter supplies them here. -/
private def bvBuiltin? (name : String) (args : List Value) : Option (IO Value) := do
  let cs := name.toList
  guard (cs.take 3 == "$bv".toList)
  let rest := cs.drop 3
  let digits := rest.takeWhile Char.isDigit
  let width ← (String.ofList digits).toNat?
  let cmp : Int → Int → Bool ← match String.ofList (rest.drop digits.length) with
    | "SLt" => some (fun a b => decide (a < b))
    | "SLe" => some (fun a b => decide (a ≤ b))
    | "SGt" => some (fun a b => decide (a > b))
    | "SGe" => some (fun a b => decide (a ≥ b))
    | _ => none
  let signed (n : Nat) : Int :=
    if width > 0 && n ≥ 2 ^ (width - 1) then Int.ofNat n - Int.ofNat (2 ^ width) else Int.ofNat n
  match args with
  | [.bv w1 a, .bv w2 b] =>
    if w1 == width && w2 == width then some (pure (.bool ⟨cmp (signed a) (signed b)⟩))
    else some (throw (IO.userError s!"'{name}' applied to bv{w1} and bv{w2}"))
  | _ => some (throw (IO.userError s!"'{name}' applied to {args.map reprVariant}"))

/-- Whether a partial operation's arguments violate its prelude `requires`: a zero
    integer divisor (real division has no `requires`), or an index or count outside
    the sequence. -/
private def partialOpFails (name : String) (args : List Value) : Bool :=
  match name, args with
  | "seqSelect", [.seq q, .int ⟨i⟩] | "seqUpdate", [.seq q, .int ⟨i⟩, _] =>
    i < 0 || i >= Int.ofNat q.size
  | "seqTake", [.seq q, .int ⟨n⟩] | "seqDrop", [.seq q, .int ⟨n⟩] =>
    n < 0 || n > Int.ofNat q.size
  | _, [_, .int ⟨0⟩] => true
  | _, _ => false

/-- Run the prelude operation named `name`, or `none` if it is not one.

    `none` means "not a builtin", so the caller falls through to an ordinary
    procedure lookup. A builtin that is applied to the wrong shapes throws
    instead, since that is a real error rather than a miss. -/
private def callBuiltin (name : String) (args : List Value) (absent : Value := .unset)
    : Option (IO Value) :=
  let bad : IO Value := throw (IO.userError
    s!"builtin '{name}' applied to {args.map reprVariant}")
  match name, args with
  -- Sequences. An index out of range violates the operation's `requires`, which the
  -- call reports; the result is then unconstrained, and answers a fixed value.
  | "seqEmpty",    []                          => some (pure (.seq #[]))
  | "seqLength",   [.seq q]                    => some (pure (.int ⟨Int.ofNat q.size⟩))
  | "seqBuild",    [.seq q, v]                 => some (pure (.seq (q.push v)))
  | "seqSelect",   [.seq q, .int ⟨i⟩]          => some (
      if i < 0 || i >= Int.ofNat q.size then pure .unset else pure q[i.toNat]!)
  | "seqUpdate",   [.seq q, .int ⟨i⟩, v]       => some (
      if i < 0 || i >= Int.ofNat q.size then pure (.seq q) else pure (.seq (q.set! i.toNat v)))
  | "seqAppend",   [.seq a, .seq b]            => some (pure (.seq (a ++ b)))
  | "seqContains", [.seq q, v]                 =>
      some (pure (.bool ⟨q.any (fun x => Value.eq x v)⟩))
  | "seqTake",     [.seq q, .int ⟨n⟩]          => some (
      if n < 0 || n > Int.ofNat q.size then pure (.seq q) else pure (.seq (q.extract 0 n.toNat)))
  | "seqDrop",     [.seq q, .int ⟨n⟩]          => some (
      if n < 0 || n > Int.ofNat q.size then pure (.seq #[]) else pure (.seq (q.extract n.toNat q.size)))
  | "seqEmpty", _ | "seqLength", _ | "seqBuild", _ | "seqSelect", _
  | "seqUpdate", _ | "seqAppend", _ | "seqContains", _ | "seqTake", _
  | "seqDrop", _ => some bad
  -- Maps. Reading an absent key is unconstrained in the prelude, so it answers the
  -- map's `absent` value, the value type's default. `mapEmpty<K, V>` is where that
  -- is fixed, from the call's recorded type arguments (`absent` here).
  | "mapEmpty",    []                          => some (pure (.map [] absent))
  | "mapContains", [.map m _, k]               =>
      let kr := k.keyRepr
      some (pure (.bool ⟨m.any (fun (r, _, _) => r == kr)⟩))
  | "mapGet",      [.map m d, k]               => some (
      let kr := k.keyRepr
      match m.find? (fun (r, _, _) => r == kr) with
      | some (_, _, v) => pure v
      | none => pure d)
  | "mapSet",      [.map m d, k, v]            =>
      let kr := k.keyRepr
      some (pure (.map ((m.filter (fun (r, _, _) => r != kr)).cons (kr, k, v)) d))
  | "mapRemove",   [.map m d, k]               =>
      let kr := k.keyRepr
      some (pure (.map (m.filter (fun (r, _, _) => r != kr)) d))
  | "mapEmpty", _ | "mapContains", _ | "mapGet", _ | "mapSet", _
  | "mapRemove", _ => some bad
  -- Core's total maps: `mapConst v` holds `v` at every key, which is exactly a map
  -- whose absent value is `v`.
  | "mapConst",    [v]                         => some (pure (.map [] v))
  | "select",      [.map m d, k]               => some (
      let kr := k.keyRepr
      match m.find? (fun (r, _, _) => r == kr) with
      | some (_, _, v) => pure v
      | none => pure d)
  | "update",      [.map m d, k, v]            =>
      let kr := k.keyRepr
      some (pure (.map ((m.filter (fun (r, _, _) => r != kr)).cons (kr, k, v)) d))
  | "mapConst", _ | "select", _ | "update", _ => some bad
  | _, _ => bvBuiltin? name args


/-! ## Static program information -/

/-- The name of a `HighType`, for `is`/`as` and for `new`. -/
private def highTypeName? (t : HighType) : Option String :=
  match t with
  | .UserDefined n => some n.text
  | .Applied base _ => match base.val with
    | .UserDefined n => some n.text
    | _ => none
  | _ => none

/-- Collect a composite's fields, its parents' first so a subtype's `new`
    allocates the inherited `ob_type` as well as its own payload. -/
private partial def collectFields (defs : Std.HashMap String CompositeType) (name : String)
    : List (String × HighType × Option StmtExprMd) :=
  match defs[name]? with
  | none => []
  | some ct =>
    let inherited := ct.extending.flatMap fun parent =>
      match highTypeName? parent.val with
      | some p => collectFields defs p
      | none => []
    inherited ++ ct.fields.map (fun f => (f.name.text, f.type.val, f.initializer))

private partial def collectAncestors (defs : Std.HashMap String CompositeType) (name : String)
    : List String :=
  match defs[name]? with
  | none => [name]
  | some ct =>
    name :: ct.extending.flatMap fun parent =>
      match highTypeName? parent.val with
      | some p => collectAncestors defs p
      | none => []

/-! ## Lifting `yield` out of expressions

A suspended coroutine resumes at the statement that suspended (see `CoroState`),
so a `yield` that sits inside a larger expression would re-run whatever that
expression evaluated before it. Before a coroutine body runs, every such `yield`
is lifted into a statement of its own, `var $yN := yield`, and every operand the
expression evaluates before it is lifted into a temporary in the same left-to-right
order. The rest of the expression then reads the temporaries, so a resume replays
nothing. `&&`, `||`, `==>`, an `if` in expression position and a `while` condition
only evaluate part of themselves, so they are lifted into the equivalent statements.
The temporaries' leading `$` keeps them apart from every user name. -/

private abbrev LiftM := StateM Nat

private def liftFresh : LiftM String := modifyGet fun n => (s!"$y{n}", n + 1)

private def hasYield (e : StmtExprMd) : Bool :=
  anyStmtExpr (fun n => match n.val with | .Yield => true | _ => false) e

private def liftVar (name : String) (src : FileRange) : StmtExprMd :=
  ⟨.Var (.Local { text := name }), src⟩

private def liftDecl (name : String) (value : StmtExprMd) : StmtExprMd :=
  ⟨.Assign [⟨.Declare { name := { text := name }, type := none }, value.source⟩] value, value.source⟩

private def liftSet (name : String) (value : StmtExprMd) : StmtExprMd :=
  ⟨.Assign [⟨.Local { text := name }, value.source⟩] value, value.source⟩

private def liftBlock (stmts : List StmtExprMd) (src : FileRange) : StmtExprMd :=
  match stmts with
  | [s] => s
  | _ => ⟨.Block stmts none, src⟩

mutual

/-- The statements to run first and the expression to evaluate after them. -/
private partial def liftExpr (e : StmtExprMd) : LiftM (List StmtExprMd × StmtExprMd) := do
  if !hasYield e then return ([], e)
  let src := e.source
  match e.val with
  | .Yield => do
      let t ← liftFresh
      pure ([liftDecl t e], liftVar t src)
  | .StaticCall callee [a, b] tys =>
    match Operation.ofProcName? callee.text with
    | some .AndThen | some .OrElse | some .Implies =>
      if !hasYield b then do
        let (pa, a') ← liftExpr a
        pure (pa, ⟨.StaticCall callee [a', b] tys, src⟩)
      else do
        let (pa, a') ← liftExpr a
        let t ← liftFresh
        let (pb, b') ← liftExpr b
        let setB := liftBlock (pb ++ [liftSet t b']) src
        let tv := liftVar t src
        let skip : StmtExprMd := ⟨.Block [] none, src⟩
        let branch : StmtExprMd := match Operation.ofProcName? callee.text with
          | some .OrElse => ⟨.IfThenElse tv skip (some setB), src⟩
          | some .Implies =>
            ⟨.IfThenElse tv setB (some (liftSet t ⟨.LiteralBool true, src⟩)), src⟩
          | _ => ⟨.IfThenElse tv setB none, src⟩
        pure (pa ++ [liftDecl t a', branch], tv)
    | _ => do
      let (pre, args') ← liftArgs [a, b]
      pure (pre, ⟨.StaticCall callee args' tys, src⟩)
  | .StaticCall callee args tys => do
      let (pre, args') ← liftArgs args
      pure (pre, ⟨.StaticCall callee args' tys, src⟩)
  | .InstanceCall target callee args => do
      let (pre, all') ← liftArgs (target :: args)
      match all' with
      | t' :: args' => pure (pre, ⟨.InstanceCall t' callee args', src⟩)
      | [] => pure (pre, e)
  | .Var (.Field target field) => do
      let (pre, t') ← liftExpr target
      pure (pre, ⟨.Var (.Field t' field), src⟩)
  | .Assign targets value => do
      let (pre, v') ← liftExpr value
      pure (pre, ⟨.Assign targets v', src⟩)
  | .CompoundAssign op (⟨.Local x, tsrc⟩) rhs => do
      let old ← liftFresh
      let (pre, rhs') ← liftExpr rhs
      let next : StmtExprMd :=
        ⟨.StaticCall { text := op.procName } [liftVar old src, rhs'] [], src⟩
      pure ([liftDecl old ⟨.Var (.Local x), tsrc⟩] ++ pre,
        ⟨.Assign [⟨.Local x, tsrc⟩] next, src⟩)
  | .CompoundAssign op (⟨.Field target field, tsrc⟩) rhs => do
      let (pt, t') ← liftExpr target
      let recv ← liftFresh
      let old ← liftFresh
      let (pre, rhs') ← liftExpr rhs
      let slot : Variable := .Field (liftVar recv src) field
      let next : StmtExprMd :=
        ⟨.StaticCall { text := op.procName } [liftVar old src, rhs'] [], src⟩
      pure (pt ++ [liftDecl recv t', liftDecl old ⟨.Var slot, tsrc⟩] ++ pre,
        ⟨.Assign [⟨slot, tsrc⟩] next, src⟩)
  | .IfThenElse c thn els => do
      let (pc, c') ← liftExpr c
      if !hasYield thn && !(els.any hasYield) then
        return (pc, ⟨.IfThenElse c' thn els, src⟩)
      let t ← liftFresh
      let (pt, t') ← liftExpr thn
      let thenB := liftBlock (pt ++ [liftSet t t']) src
      let elseB ← match els with
        | some el => do
            let (pe, e') ← liftExpr el
            pure (some (liftBlock (pe ++ [liftSet t e']) src))
        | none => pure none
      let decl : StmtExprMd := ⟨.Var (.Declare { name := { text := t }, type := none }), src⟩
      pure (pc ++ [decl, ⟨.IfThenElse c' thenB elseB, src⟩], liftVar t src)
  | .Block stmts none =>
    match stmts.reverse with
    | [] => pure ([], e)
    | last :: earlier => do
        let pre ← earlier.reverse.flatMapM liftStmt
        let (pl, l') ← liftExpr last
        pure (pre ++ pl, l')
  | .Resume target value? => do
      let (pre, all') ← liftArgs (target :: value?.toList)
      match all' with
      | [t'] => pure (pre, ⟨.Resume t' none, src⟩)
      | [t', v'] => pure (pre, ⟨.Resume t' (some v'), src⟩)
      | _ => pure (pre, e)
  | .HasNext target => do
      let (pre, t') ← liftExpr target
      pure (pre, ⟨.HasNext t', src⟩)
  | .AsType target ty => do
      let (pre, t') ← liftExpr target
      pure (pre, ⟨.AsType t' ty, src⟩)
  | .IsType target ty => do
      let (pre, t') ← liftExpr target
      pure (pre, ⟨.IsType t' ty, src⟩)
  | .ReferenceEquals a b => do
      let (pre, args') ← liftArgs [a, b]
      match args' with
      | [a', b'] => pure (pre, ⟨.ReferenceEquals a' b', src⟩)
      | _ => pure (pre, e)
  | _ => pure ([], e)

/-- Operands evaluated left to right: every one up to the last that contains a
    `yield` is evaluated before the expression resumes, so it moves into a
    temporary; the ones after it stay where they are. -/
private partial def liftArgs (args : List StmtExprMd) : LiftM (List StmtExprMd × List StmtExprMd) := do
  let lastYield := (args.zipIdx.filter (fun (a, _) => hasYield a)).getLast?.map (·.2)
  match lastYield with
  | none => pure ([], args)
  | some k => do
    let mut pre : List StmtExprMd := []
    let mut out : List StmtExprMd := []
    for (a, i) in args.zipIdx do
      if i < k then
        let (pa, a') ← liftExpr a
        let t ← liftFresh
        pre := pre ++ pa ++ [liftDecl t a']
        out := out ++ [liftVar t a.source]
      else if i == k then
        let (pa, a') ← liftExpr a
        pre := pre ++ pa
        out := out ++ [a']
      else
        out := out ++ [a]
    pure (pre, out)

/-- A statement, as the statements that replace it. -/
private partial def liftStmt (s : StmtExprMd) : LiftM (List StmtExprMd) := do
  let src := s.source
  match s.val with
  | .Block stmts label => do
      let stmts' ← stmts.flatMapM liftStmt
      pure [⟨.Block stmts' label, src⟩]
  | .Assign _ ⟨.Yield, _⟩ | .Yield | .Var (.Declare _) => pure [s]
  | .IfThenElse c thn els => do
      let (pc, c') ← liftExpr c
      let thn' ← liftStmtBlock thn
      let els' ← els.mapM liftStmtBlock
      pure (pc ++ [⟨.IfThenElse c' thn' els', src⟩])
  | .While c invs dec body postTest => do
      let body' ← liftStmtBlock body
      if !hasYield c then
        return [⟨.While c invs dec body' postTest, src⟩]
      -- The condition suspends, so it becomes the head of an unconditional loop
      -- that leaves through a labelled block when the condition is false.
      let label ← liftFresh
      let (pc, c') ← liftExpr c
      let notC : StmtExprMd := ⟨.StaticCall { text := Operation.Not.procName } [c'] [], c.source⟩
      -- The invariants are checked where the `while` case checks them: after the
      -- condition for a `while`, before each run of the body for a `do`/`while`.
      let invChecks := invs.map fun inv => (⟨.Assert inv none, inv.source⟩ : StmtExprMd)
      let test := pc ++ [⟨.IfThenElse notC ⟨.Exit label, src⟩ none, src⟩]
      let loopBody := if postTest then invChecks ++ body' :: test
        else pc ++ invChecks ++ [⟨.IfThenElse notC ⟨.Exit label, src⟩ none, src⟩, body']
      let loop : StmtExprMd :=
        ⟨.While ⟨.LiteralBool true, c.source⟩ [] none ⟨.Block loopBody none, body.source⟩ false, src⟩
      pure [⟨.Block [loop] (some label), src⟩]
  | .Try body catches fin => do
      let body' ← liftStmtBlock body
      let catches' ← catches.mapM fun c => do
        let cb ← liftStmtBlock c.body
        pure { c with body := cb }
      let fin' ← fin.mapM liftStmtBlock
      pure [⟨.Try body' catches' fin', src⟩]
  | .Return (some v) => do
      let (pre, v') ← liftExpr v
      pure (pre ++ [⟨.Return (some v'), src⟩])
  | .Throw v => do
      let (pre, v') ← liftExpr v
      pure (pre ++ [⟨.Throw v', src⟩])
  | .Assert c summary => do
      let (pre, c') ← liftExpr c
      pure (pre ++ [⟨.Assert c' summary, src⟩])
  | _ => do
      let (pre, e') ← liftExpr s
      pure (pre ++ [e'])

private partial def liftStmtBlock (s : StmtExprMd) : LiftM StmtExprMd := do
  let stmts ← liftStmt s
  pure (liftBlock stmts s.source)

end

/-- `proc` with every `yield` in its body lifted to statement level. -/
def liftCoroutineYields (proc : Procedure) : Procedure :=
  let lift (b : StmtExprMd) : StmtExprMd := ((liftStmtBlock b).run' 0)
  match proc.body with
  | .Transparent b => { proc with body := .Transparent (lift b) }
  | .Opaque posts (some impl) mods => { proc with body := .Opaque posts (some (lift impl)) mods }
  | _ => proc

/-- The value of a literal, or of a negated integer or decimal literal. -/
private def literalValue? : StmtExpr → Option Value
  | .LiteralInt n => some (.int ⟨n⟩)
  | .LiteralBool b => some (.bool ⟨b⟩)
  | .LiteralString str => some (.string ⟨str⟩)
  | .LiteralDecimal d => some (.real (StrataDDM.Decimal.toRat d))
  | .LiteralBv v w => some (.bv w (v % 2 ^ w))
  | .StaticCall callee [⟨.LiteralInt n, _⟩] _ =>
    match Operation.ofProcName? callee.text with
    | some .Neg => some (.int ⟨-n⟩)
    | _ => none
  | .StaticCall callee [⟨.LiteralDecimal d, _⟩] _ =>
    match Operation.ofProcName? callee.text with
    | some .Neg => some (.real (-(StrataDDM.Decimal.toRat d)))
    | _ => none
  | _ => none

def buildIndex (p : Program) : ProgramIndex :=
  let composites : Std.HashMap String CompositeType :=
    p.types.foldl (init := {}) fun acc t =>
      match t with
      | .Composite ct => acc.insert ct.name.text ct
      | _ => acc
  let staticProcs := p.staticProcedures.map fun pr =>
    if pr.is_coroutine then liftCoroutineYields pr else pr
  let procs := staticProcs.foldl (init := {}) fun acc pr =>
    acc.insert pr.name.text pr
  let procsById := staticProcs.foldl (init := {}) fun acc pr =>
    match pr.name.uniqueId with
    | some id => acc.insert id pr
    | none => acc
  let overloaded := (p.staticProcedures.foldl (init := ({} : Std.HashMap String Nat)) fun acc pr =>
      acc.insert pr.name.text (acc.getD pr.name.text 0 + 1)).fold (init := {}) fun acc n k =>
    if k > 1 then acc.insert n else acc
  let procsNamed := staticProcs.foldl (init := {}) fun acc pr =>
    acc.insert pr.name.text ((acc.getD pr.name.text []) ++ [pr])
  let methods := composites.fold (init := {}) fun acc n ct =>
    acc.insert n (ct.instanceProcedures.foldl (init := {}) fun m pr => m.insert pr.name.text pr)
  let compositeFields := composites.fold (init := {}) fun acc n _ =>
    acc.insert n (collectFields composites n)
  let typeAliases := p.types.foldl (init := {}) fun acc t =>
    match t with
    | .Alias a => acc.insert a.name.text a.target.val
    | _ => acc
  let witnesses := p.types.foldl (init := {}) fun acc t =>
    match t with
    | .Constrained c =>
      match literalValue? c.witness.val with
      | some v => acc.insert c.name.text v
      | none => acc
    | _ => acc
  let ancestors := composites.fold (init := {}) fun acc n _ =>
    acc.insert n (collectAncestors composites n)
  let (ctors, testers, destructors) :=
    p.types.foldl (init := ({}, {}, {})) fun (cs, ts, ds) t =>
      match t with
      | .Datatype dt =>
        dt.constructors.foldl (init := (cs, ts, ds)) fun (cs, ts, ds) ctor =>
          let fieldNames := ctor.args.map (·.name.text)
          let ds := ctor.args.zipIdx.foldl (init := ds) fun ds (arg, i) =>
            let base := dt.destructorName arg
            (ds.insert base (ctor.name.text, i, arg.type.val)).insert (base ++ "!")
              (ctor.name.text, i, arg.type.val)
          (cs.insert ctor.name.text fieldNames,
           ts.insert (dt.testerName ctor) ctor.name.text,
           ds)
      | _ => (cs, ts, ds)
  { procs, procsById, methods, overloaded, procsNamed, compositeFields, typeAliases, witnesses,
    ancestors, ctors, testers, destructors }

/-- The value a variable of type `t` holds before it is first assigned. Laurel gives
    it an arbitrary value, and the interpreter runs one execution, so it picks a
    fixed one: zero, false, empty. A constrained type starts at its witness when
    that is a literal, and is otherwise `unset`; an alias starts at its target's
    default. A type with no such value (a composite, a datatype, a type
    variable) starts `unset`. -/
partial def defaultValue (index : ProgramIndex) (t : HighType) (depth : Nat := 16) : Value :=
  match depth, t with
  | 0, _ => .unset
  | _, .TBool => .bool ⟨false⟩
  | _, .TInt => .int ⟨0⟩
  | _, .TReal | _, .TFloat64 => .real 0
  | _, .TString => .string ⟨""⟩
  | _, .TBv n => .bv n 0
  | d + 1, .TMap _ v => .map [] (defaultValue index v.val d)
  | d + 1, .UserDefined n =>
    match n.text with
    | "Sequence" => .seq #[]
    | "Map" => .map [] .unset
    | other => match index.witnesses[other]? with
      | some w => w
      | none => match index.typeAliases[other]? with
        | some target => defaultValue index target d
        | none => .unset
  | d + 1, .Applied base args =>
    match base.val with
    | .UserDefined n =>
      match n.text, args with
      | "Sequence", _ => .seq #[]
      | "Map", [_, v] => .map [] (defaultValue index v.val d)
      | "Map", _ => .map [] .unset
      | other, _ => match index.typeAliases[other]? with
        | some target => defaultValue index target d
        | none => .unset
    | _ => .unset
  | _, _ => .unset

private def EvalState.toDisplay (s : EvalState) : DisplayEvalState :=
  { stack := (s.stack.filter fun k _ =>
      !(k.startsWith "$shadowed$" || k.startsWith "$scopeDepth$")).map (fun _ v => v.display) }

/-! ## Coroutine positions

A suspended coroutine is a *position* in its body, not a paused computation (see
`CoroState`), so every construct with more than one child numbers its children
and a `yield` records the path of indices that reaches it. The two helpers below
are the whole protocol: `seekEntry` reads a pending path as "the suspension point
is at or below child `i`", and `enterChild` moves into a child.

A construct with exactly one child (`while`'s body) numbers nothing and hands its
own path straight down, so re-entering it costs no index. A `try` numbers its arms
so that a `yield` in a `catch` is distinguishable from one in the body — only the
body can be resumed into.
-/

/-- The index to start at and the path remainder to hand that child, for a
    construct whose children are being walked under the pending `seek`.
    A remainder of `some []` is the arrival marker (see `EvalState.seek`); no
    pending seek means start at child 0 with nothing to fast-forward. -/
private def seekEntry : Option (List Nat) → Nat × Option (List Nat)
  | some (i :: rest) => (i, some rest)
  | _ => (0, none)

/-- Move into child `k` of the construct whose own path is `base`, handing it
    `childSeek` (the remainder from `seekEntry` for the child being
    fast-forwarded into, `none` for every other child — a sibling after the
    suspension point runs normally). -/
private def enterChild (base : List Nat) (k : Nat) (childSeek : Option (List Nat))
    : EvalM Unit :=
  modify fun s => { s with cursor := base ++ [k], seek := childSeek }

/-- The reserved procedure name that reads a coroutine's completion value:
    `coroCompletion(co)`. Recognized by the interpreter before any procedure
    lookup, exactly as the prelude collection and string operations are
    (`callBuiltin`), so it needs no new `StmtExpr` case and no grammar support.
    A program may additionally *declare* it (bodiless and `opaque`) to satisfy
    resolution and the verifier; the declaration is never run. -/
def coroCompletionName : String := "coroCompletion"

/-- Where a `catch` binding or a block-local declaration keeps the value it
    shadows, inside the frame itself so that a coroutine suspended in its scope
    carries it across the suspension. A stack, because scopes nest. A leading `$`
    cannot clash with a user name. -/
private def shadowKey (name : String) : String := "$shadowed$" ++ name

private def absentMarker : Value := .data "$absent" #[]

/-- Bind a `catch` clause's name to `v`, saving whatever it shadowed. -/
def bindCatch (frame : StackFrame) (name : String) (v : Value) : StackFrame :=
  let saved := match frame[shadowKey name]? with
    | some (.seq q) => q
    | _ => #[]
  let prior := frame[name]?.getD absentMarker
  (frame.insert (shadowKey name) (.seq (saved.push prior))).insert name v

/-- How many shadowed values `name` currently has saved. -/
def shadowDepth (frame : StackFrame) (name : String) : Nat :=
  match frame[shadowKey name]? with
  | some (.seq q) => q.size
  | _ => 0

/-- Declare `name` as `v`, saving what it shadows so the enclosing block can put
    it back. A name not yet bound saves its absence, so leaving the block unbinds
    it again rather than letting it hide a global of the same name. -/
def declareLocal (frame : StackFrame) (name : String) (v : Value) : StackFrame :=
  bindCatch frame name v

/-- Undo the innermost `bindCatch` of `name`. -/
def unbindCatch (frame : StackFrame) (name : String) : StackFrame :=
  match frame[shadowKey name]? with
  | some (.seq q) =>
    match q.back? with
    | none => frame
    | some prior =>
      let frame := if q.size == 1 then frame.erase (shadowKey name)
        else frame.insert (shadowKey name) (.seq q.pop)
      match prior with
      | .data c _ => if c == "$absent" then frame.erase name else frame.insert name prior
      | _ => frame.insert name prior
  | _ => frame

/-- Undo saves of `name` until only `depth` remain, restoring as it goes. -/
def popShadowsTo (frame : StackFrame) (name : String) (depth : Nat) : StackFrame :=
  let rec go : Nat → StackFrame → StackFrame
    | 0, f => f
    | k + 1, f => if shadowDepth f name > depth then go k (unbindCatch f name) else f
  go (shadowDepth frame name) frame

/-- The names a block's own statements declare (not those of nested blocks). -/
private def blockDeclarations (stmts : List StmtExprMd) : List String :=
  stmts.flatMap fun s => match s.val with
    | .Var (.Declare p) => [p.name.text]
    | .Assign targets _ => targets.filterMap fun t => match t.val with
      | .Declare p => some p.name.text
      | _ => none
    | _ => []

/-- The static procedure a call names: by its resolved `uniqueId` when it has
    one, which is what selects among overloads, and otherwise by name. -/
def lookupCallee (index : ProgramIndex) (callee : Identifier) : Option Procedure :=
  (callee.uniqueId.bind index.procsById.get?) <|> index.procs[callee.text]?

mutual

/-- Run `act` as the body of a block whose statements are `stmts`: a name the block
    declares is visible inside it only. Each declaration saves the local it shadows
    (`declareLocal`), and on the way out the block pops those saves back to the depth
    it was entered with, so the local means what it last meant outside, writes made
    inside the block before the declaration included. Inside a coroutine body the
    entry depth lives in the frame, keyed by the block's position, so a resume back
    into the block finds the depth of the original entry. A suspension leaves
    everything in place, since the block is paused rather than left. -/
partial def withBlockScope (stmts : List StmtExprMd) (act : EvalM α) : EvalM α := do
  let names := blockDeclarations stmts
  if names.isEmpty then act else
  let st ← get
  let inCoro := st.coroSelf.isSome
  let depthKey (n : String) := s!"$scopeDepth${st.cursor}${n}"
  let depths : List (String × Nat) := names.map fun n =>
    match (if inCoro then st.stack[depthKey n]? else none) with
    | some (.int ⟨d⟩) => (n, d.toNat)
    | _ => (n, shadowDepth st.stack n)
  let record (frame : StackFrame) : StackFrame :=
    depths.foldl (init := frame) fun acc nd => acc.insert (depthKey nd.1) (.int ⟨Int.ofNat nd.2⟩)
  let unwind (frame : StackFrame) : StackFrame :=
    depths.foldl (init := frame) fun acc nd =>
      let acc := popShadowsTo acc nd.1 nd.2
      if inCoro then acc.erase (depthKey nd.1) else acc
  if inCoro then
    modify fun s => { s with stack := record s.stack }
  let restore : EvalM Unit := modify fun s => { s with stack := unwind s.stack }
  let r ← tryCatch act fun sig => do
    match sig with
    | .suspended => pure ()
    | _ => restore
    throw sig
  restore
  pure r

/-- Run a statement that is the body of an `if` arm or a loop. One that is not a
    block is still a scope of its own, so a declaration it makes is undone when it
    finishes, as it would be inside braces. -/
partial def evalScopedStmt (cfg : ExternalBackend) (s : StmtExprMd) : EvalM Unit :=
  match s.val with
  | .Block _ _ => evalStmt cfg s
  | _ => withBlockScope [s] (evalStmt cfg s)

/-- `evalExpr` on a node, recording a call's own source range in
    `EvalState.callSite` first so the call can report a violated precondition
    there. Only calls pay for the write. -/
partial def evalExprMd (cfg : ExternalBackend) (e : StmtExprMd) : EvalM Value := do
  match e.val with
  | .StaticCall .. | .InstanceCall .. =>
      modify fun s => { s with callSite := e.source }
      evalExpr cfg e.val
  -- An `assert` in expression position is checked as the statement it is, at its
  -- own range, and its value is unused.
  | .Assert .. => do
      evalStmt cfg e
      pure default
  | _ => evalExpr cfg e.val

/-- Evaluate a Laurel expression to a `Value`. Mutually recursive with
    `evalStmt` (procedure bodies contain statements) and `invokeProc`
    (`StaticCall` invokes another procedure). -/
partial def evalExpr (cfg : ExternalBackend) : StmtExpr → EvalM Value
  | .LiteralBool b   => pure (.bool ⟨b⟩)
  | .LiteralInt n    => pure (.int ⟨n⟩)
  | .LiteralString s => pure (.string ⟨s⟩)
  | .Var (Variable.Local name) => do
      let s ← get
      match s.stack[name.text]? with
      | some v => pure v
      | none =>
          -- Not a local of this frame, so it may be a file-scope global: resolution
          -- leaves both as `Variable.Local` and records the difference in its model.
          match s.globals[name.text]? with
          | some v => pure v
          | none =>
            liftM (m := IO) (throw (IO.userError s!"undefined identifier '{name.text}'"))
  | .LiteralDecimal d => pure (.real (StrataDDM.Decimal.toRat d))
  -- A hole stands for an unconstrained value. Concretely there is nothing to choose,
  -- so it evaluates to `unset`, and USING one is an error -- which is the useful
  -- reading: Laurel makes a composite-typed file-scope global use a hole (`new` is not
  -- effect-free, and omitting the initializer is rejected), so the hole means
  -- "assigned before anything uses it" and an early use should say so.
  | .Hole _ ty => do
      match ty with
      | some t => pure (defaultValue (← get).index t.val)
      | none => pure .unset
  -- A conditional in EXPRESSION position (`var x := if c then a else b`). Laurel
  -- has one statement-expression type, so the same node appears in both
  -- positions; only the branch taken is evaluated.
  | .IfThenElse cond thenB elseB => do
      -- An arm is a scope of its own, as it is in statement position.
      let arm (b : StmtExprMd) : EvalM Value := match b.val with
        | .Block _ _ => evalExprMd cfg b
        | _ => withBlockScope [b] (evalExprMd cfg b)
      let c ← evalExprMd cfg cond
      if ← liftM (isTrue cfg c) then arm thenB
      else match elseB with
        | some e => arm e
        | none => pure default
  -- A block in expression position evaluates to its last statement's value, so a
  -- `{ lemma(x); e }` yields `e`.
  | .Block stmts none => withBlockScope stmts (evalStmtList cfg stmts (asExpr := true))
  | .Var (Variable.Field target field) => do
      let tv ← evalExprMd cfg target
      readField tv field.text
  | .New ref _ => do
      let st ← get
      let fields := st.index.compositeFields[ref.text]?.getD []
      -- A field with no initializer starts at its type's default.
      let addr := st.heap.size
      let obj : HeapObject := { typeName := ref.text, fields := {} }
      modify fun s => { s with heap := s.heap.push obj }
      for (fname, fty, init?) in fields do
        let v ← match init? with
          | some e => evalExprMd cfg e
          | none => pure (defaultValue st.index fty)
        writeField (.ref addr) fname v
      pure (.ref addr)
  | .IsType target ty => do
      let tv ← evalExprMd cfg target
      let st ← get
      match tv, highTypeName? ty.val with
      | .ref a, some tn =>
        let some obj := st.heap[a]?
          | liftM (m := IO) (throw (IO.userError s!"dangling reference #{a}"))
        pure (.bool ⟨(st.index.ancestors[obj.typeName]?.getD [obj.typeName]).contains tn⟩)
      -- A non-reference is not an instance of any composite; this is how PyDyn's
      -- `x is PyAbsent` answers `false` for a primitive.
      | _, _ => pure (.bool ⟨false⟩)
  -- A cast is a checked no-op: the value already carries its runtime type, and
  -- `is` is what a program uses to guard the cast.
  | .AsType target _ => evalExprMd cfg target
  | .ReferenceEquals lhs rhs => do
      let a ← evalExprMd cfg lhs
      let b ← evalExprMd cfg rhs
      pure (.bool ⟨Value.eq a b⟩)
  -- `yield`, `resume(co[, v])` and `has_next(co)` are all dual-position, and this
  -- is the position that keeps their value: `z := yield` reads what the resume
  -- sent in, `v := resume(co)` reads the next yielded payload. The statement
  -- forms in `evalStmt` run these and drop the value.
  | .Yield => evalError
      "`yield` inside this expression is not supported: the construct around it has no lifting into statements (see `liftCoroutineYields`)"
  | .Resume target value? => do
      let tv ← evalExprMd cfg target
      let sent ← match value? with
        | some e => evalExprMd cfg e
        | none => pure .unset
      resumeCoroutine cfg tv sent
  | .HasNext target => do
      let tv ← evalExprMd cfg target
      let (_, co) ← coroInstance tv "has_next"
      pure (.bool ⟨!co.finished⟩)
  | .StaticCall callee args typeArgs => do
      let site := (← get).callSite
      -- `coroCompletion(co)`: the reserved reader for a coroutine's completion
      -- value, recognized before operators, builtins and procedures alike (see
      -- `coroCompletionName`).
      if callee.text == coroCompletionName then
        match args with
        | [t] =>
            let tv ← evalExprMd cfg t
            let (_, co) ← coroInstance tv coroCompletionName
            if !co.finished then
              evalError s!"'{coroCompletionName}' on coroutine '{co.proc}', which has not finished"
            return co.completed
        | _ => evalError s!"'{coroCompletionName}' expects 1 argument, got {args.length}"
      match Operation.ofProcName? callee.text with
      | some .AndThen =>
          match args with
          | [a, b] => do
            let va ← evalExprMd cfg a
            if ← liftM (isTrue cfg va) then
              let vb ← evalExprMd cfg b
              pure (.bool ⟨← liftM (isTrue cfg vb)⟩)
            else
              pure (.bool ⟨false⟩)
          | _ => liftM (m := IO) (throw (IO.userError "andThen expects exactly 2 arguments"))
      | some .OrElse =>
          match args with
          | [a, b] => do
            let va ← evalExprMd cfg a
            if ← liftM (isTrue cfg va) then
              pure (.bool ⟨true⟩)
            else
              let vb ← evalExprMd cfg b
              pure (.bool ⟨← liftM (isTrue cfg vb)⟩)
          | _ => liftM (m := IO) (throw (IO.userError "orElse expects exactly 2 arguments"))
      | some .Implies =>
          match args with
          | [a, b] => do
            let va ← evalExprMd cfg a
            if ← liftM (isTrue cfg va) then
              let vb ← evalExprMd cfg b
              pure (.bool ⟨← liftM (isTrue cfg vb)⟩)
            else
              pure (.bool ⟨true⟩)
          | _ => liftM (m := IO) (throw (IO.userError "implies expects exactly 2 arguments"))
      | some op => do
          let argVals ← args.mapM (evalExprMd cfg)
          -- Only the partial operators have a `requires` on their prelude wrapper,
          -- so only they pay for looking it up.
          match op with
          | .Div | .Mod | .DivT | .ModT =>
            -- Reported on the enclosing statement, as Core places the check.
            match lookupCallee (← get).index callee with
            | some proc => checkPreconditions cfg (← get).stmtSite proc argVals
            | none => missingPrelude callee.text argVals
          | _ => pure ()
          -- A bitvector comparison is signed, as the lowering to Core makes it.
          let bvCmp : Option String := match op, argVals with
            | .Lt, [.bv w _, .bv _ _] => some s!"$bv{w}SLt"
            | .Leq, [.bv w _, .bv _ _] => some s!"$bv{w}SLe"
            | .Gt, [.bv w _, .bv _ _] => some s!"$bv{w}SGt"
            | .Geq, [.bv w _, .bv _ _] => some s!"$bv{w}SGe"
            | _, _ => none
          match bvCmp >>= (bvBuiltin? · argVals) with
          | some act => liftM act
          | none => liftM (evalOp cfg op argVals)
      | none => do
          let argVals ← args.mapM (evalExprMd cfg)
          let st ← get
          let name := callee.text
          -- Order matters only in that all four are disjoint name spaces; a
          -- builtin is checked first because it is the hottest path.
          -- `mapEmpty<K, V>`'s second type argument is the value type whose default
          -- the new map answers for an absent key; resolution records it on the
          -- call, since no argument determines it.
          let absent := match typeArgs with
            | [_, v] => defaultValue st.index v.val
            | _ => .unset
          -- The partial sequence operations carry a `requires` on their prelude
          -- declaration, checked on the enclosing statement, as Core places it.
          if name == "seqSelect" || name == "seqUpdate" || name == "seqTake" || name == "seqDrop" then
            match lookupCallee st.index callee with
            | some proc => checkPreconditions cfg st.stmtSite proc argVals
            | none => missingPrelude name argVals
          match callBuiltin name argVals absent with
          | some act => liftM act
          | none =>
            if let some fieldNames := st.index.ctors[name]? then
              if fieldNames.length != argVals.length then
                liftM (m := IO) (throw (IO.userError
                  s!"constructor '{name}' expects {fieldNames.length} args, got {argVals.length}"))
              else pure (.data name argVals.toArray)
            else if let some ctor := st.index.testers[name]? then
              match argVals with
              | [.data c _] => pure (.bool ⟨c == ctor⟩)
              | _ => liftM (m := IO) (throw (IO.userError
                  s!"tester '{name}' applied to {argVals.map reprVariant}"))
            else if let some (ctor, i, fty) := st.index.destructors[name]? then
              match argVals with
              | [.data c as_] =>
                if c != ctor then do
                  -- The safe destructor's precondition is that the value was built by
                  -- its constructor; Core checks it as an assertion on the statement.
                  -- Either way the field read is unconstrained, so it answers the
                  -- field type's default.
                  unless name.endsWith "!" do
                    let failure := Strata.Message.withRange st.stmtSite "assertion does not hold"
                    modify fun s => { s with assertFailures := s.assertFailures.push failure }
                  pure (defaultValue st.index fty)
                else match as_[i]? with
                  | some v => pure v
                  | none => liftM (m := IO) (throw (IO.userError
                      s!"destructor '{name}': no argument {i}"))
              | _ => liftM (m := IO) (throw (IO.userError
                  s!"destructor '{name}' applied to {argVals.map reprVariant}"))
            else do
              let outs ← invokeCallee cfg site callee argVals
              pure (outs[0]?.getD default)
  | .Assert cond summary => do
      -- An `assert` in expression position: same check, and its value is unused.
      evalStmt cfg ⟨.Assert cond summary, .unknown⟩
      pure default
  | .Assume _ => pure default
  | .LiteralBv value width => pure (.bv width (value % 2 ^ width))
  | .Old value none => do
      let st ← get
      let some (heap, globals, inouts) := st.entryState
        | evalError "`old` outside a postcondition"
      let restore : EvalM Unit := modify fun s =>
        { s with heap := st.heap, globals := st.globals, stack := st.stack, inOld := st.inOld }
      let stack := inouts.fold (init := st.stack) fun acc k v => acc.insert k v
      modify fun s => { s with heap, globals, stack, inOld := true }
      let v ← tryCatch (evalExprMd cfg value) fun sig => do restore; throw sig
      -- The entry heap is discarded afterwards, so an object allocated in here
      -- would leave a reference into a heap that no longer exists.
      if (← get).heap.size != heap.size then
        restore
        evalError "`old(...)` allocates an object, which does not outlive it"
      restore
      pure v
  -- An assignment in expression position yields the value it assigned, so
  -- `var z: int := y := y + 1` binds `z` to the new `y`.
  | .Assign targets value => do
      match targets with
      | [t] => do
          let v ← evalExprMd cfg value
          assignTo cfg t.val v
          pure v
      | _ => do
          evalStmt cfg ⟨.Assign targets value, value.source⟩
          pure default
  -- The target is evaluated once: `a#f++` reads and writes the field of the one
  -- object `a` denotes.
  | .IncrDecr mode op target => do
      let (old, write) ← readForUpdate cfg target.val
      let new ← liftM (evalOp cfg (if op == .Incr then .Add else .Sub) [old, .int ⟨1⟩])
      write new
      pure (if mode == .Pre then new else old)
  | .CompoundAssign op target rhs => do
      let (old, write) ← readForUpdate cfg target.val
      let r ← evalExprMd cfg rhs
      -- `x /= d` is `x := x / d`, so it carries the operator's precondition.
      match op with
      | .Div | .Mod | .DivT | .ModT =>
        let st ← get
        -- `$div` is overloaded on `int` and `real`; the operands' shape picks one.
        let fits (pr : Procedure) : Bool := pr.inputs.all fun i => match i.type.val, old with
          | .TInt, .int _ | .TReal, .real _ => true
          | _, _ => false
        match (st.index.procsNamed[op.procName]?.getD []).find? fits with
        | some proc => checkPreconditions cfg st.stmtSite proc [old, r]
        | none => missingPrelude op.procName [old, r]
      | _ => pure ()
      let new ← liftM (evalOp cfg op [old, r])
      write new
      pure new
  | .InstanceCall target callee args => do
      let site := (← get).callSite
      let tv ← evalExprMd cfg target
      let argVals ← args.mapM (evalExprMd cfg)
      let proc ← resolveMethod tv callee.text
      let outs ← invokeProc cfg site proc (tv :: argVals)
      pure (outs[0]?.getD default)
  | e => evalError s!"unsupported expression: {e.constrName}"

/-- Fail with `msg`, naming the procedures that led here. -/
partial def evalError (msg : String) : EvalM α := do
  let st ← get
  let where_ :=
    if st.callStack.isEmpty then ""
    else s!" [in {String.intercalate " <- " (st.callStack.take 8)}]"
  liftM (m := IO) (throw (IO.userError (msg ++ where_)))

/-- A partial operation whose prelude declaration is not in the program, so its
    `requires` cannot be reported: a violation is an error rather than a silent
    continuation. -/
partial def missingPrelude (name : String) (args : List Value) : EvalM Unit := do
  if partialOpFails name args then
    evalError s!"'{name}' applied outside its precondition, and the program has no prelude declaration to report it"

/-- Read field `name` off a composite reference. -/
partial def readField (target : Value) (name : String) : EvalM Value := do
  match target with
  | .ref a => do
    let st ← get
    let some obj := st.heap[a]?
      | if st.inOld then evalError "`old(...)` reads an object allocated after the procedure was entered"
        else liftM (m := IO) (throw (IO.userError s!"dangling reference #{a}"))
    match obj.fields[name]? with
    | some v => pure v
    | none => evalError s!"no field '{name}' on {obj.typeName}"
  | v => evalError s!"field read '{name}' on a non-composite {reprVariant v}"

/-- Write field `name` on a composite reference, in place. Every alias of the
    object observes it, which is what makes a Laurel composite a reference type. -/
partial def writeField (target : Value) (name : String) (v : Value) : EvalM Unit := do
  match target with
  | .ref a => do
    let st ← get
    let some obj := st.heap[a]?
      | liftM (m := IO) (throw (IO.userError s!"dangling reference #{a}"))
    modify fun s => { s with heap := s.heap.set! a { obj with fields := obj.fields.insert name v } }
  | v' => liftM (m := IO) (throw (IO.userError
      s!"field write '{name}' on a non-composite {reprVariant v'}"))

/-- Assign to one target, whichever kind it is. -/
partial def assignTo (cfg : ExternalBackend) (target : Variable) (v : Value) : EvalM Unit := do
  match target with
  | .Declare param => modify fun s => { s with stack := declareLocal s.stack param.name.text v }
  | .Local name => modify fun s =>
      -- A local always wins; otherwise a known global is updated in place. An
      -- unknown name goes to `stack`, which is what the assign-before-declare
      -- shapes the front ends emit rely on.
      if s.stack.contains name.text then { s with stack := s.stack.insert name.text v }
      else if s.globals.contains name.text then
        { s with globals := s.globals.insert name.text v }
      else { s with stack := s.stack.insert name.text v }
  | .Field tgt field => do
      let tv ← evalExprMd cfg tgt
      writeField tv field.text v

/-- The current value of an update target, and how to write it back, with any
    receiver evaluated exactly once. -/
partial def readForUpdate (cfg : ExternalBackend) (target : Variable)
    : EvalM (Value × (Value → EvalM Unit)) := do
  match target with
  | .Local name => do
      let v ← evalExpr cfg (.Var (.Local name))
      pure (v, fun nv => assignTo cfg (.Local name) nv)
  | .Field tgt field => do
      let tv ← evalExprMd cfg tgt
      let v ← readField tv field.text
      pure (v, fun nv => writeField tv field.text nv)
  | .Declare param => evalError s!"cannot update the declaration of '{param.name.text}'"

/-- The instance procedure `name` that a receiver dispatches to: its runtime
    type's own, else the nearest ancestor's. -/
partial def resolveMethod (target : Value) (name : String) : EvalM Procedure := do
  match target with
  | .ref a => do
    let st ← get
    let some obj := st.heap[a]?
      | evalError s!"dangling reference #{a}"
    let chain := st.index.ancestors[obj.typeName]?.getD [obj.typeName]
    -- The declarers of `name` among the receiver's ancestors; the one that
    -- dispatches is the most derived, i.e. the declarer no other declarer
    -- extends. Taking the first one in ancestor order would let an earlier
    -- parent's inherited copy win over a later parent's own override.
    let declarers := chain.filter fun t => (st.index.methods[t]? >>= (·[name]?)).isSome
    let mostDerived := declarers.find? fun t =>
      declarers.all fun d => d == t || !((st.index.ancestors[d]?.getD [d]).contains t)
    match mostDerived >>= (fun t => st.index.methods[t]? >>= (·[name]?)) with
    | some proc => pure proc
    | none => evalError s!"no instance procedure '{name}' on {obj.typeName}"
  | v => evalError s!"instance call '{name}' on a non-composite {reprVariant v}"

/-- Evaluate a Laurel statement for its side effects on the eval state. May
    throw `Control.return_` to unwind to the nearest `invokeProc`. -/
partial def evalStmt (cfg : ExternalBackend) : Strata.Laurel.StmtExprMd → EvalM Unit
  | ⟨.Block stmts none, _⟩ => do
      -- The step budget is charged per statement, which is enough to stop a
      -- divergent loop without paying for a counter on every expression node.
      -- It is also what makes a non-terminating generator come back as
      -- `outOfFuel`: every resume of its body re-enters this block.
      let st ← get
      if st.fuel == 0 then throw .outOfFuel
      modify fun s => { s with fuel := s.fuel - 1 }
      let _ ← withBlockScope stmts (evalStmtList cfg stmts (asExpr := false))
  | ⟨.Block stmts (some label), _⟩ => do
      -- A labelled block is `exit label`'s target: that signal unwinds to here
      -- and no further, which is how Laurel spells `break`/`continue`.
      let base := (← get).cursor
      tryCatch (do let _ ← withBlockScope stmts (evalStmtList cfg stmts (asExpr := false))) fun
        | .exit_ l =>
            if l == label then
              -- The exit skipped the walk's own position bookkeeping, so restore
              -- this block's position before execution continues after it.
              modify fun s => { s with cursor := base, seek := none }
            else throw (.exit_ l)
        | other => throw other
  | ⟨.Exit target, _⟩ => throw (.exit_ target)
  | ⟨.Assign targets value, _⟩ => do
      match targets with
      | [t] => do
          let v ← match value.val with
            | .Yield => evalYield
            | _ => evalExprMd cfg value
          assignTo cfg t.val v
      | _ => do
          -- Multiple targets only arise from a call with multiple outputs, so the
          -- right-hand side is evaluated once and its outputs distributed.
          modify fun s => { s with callSite := value.source }
          let outs ← evalCallOutputs cfg value.val
          if outs.size != targets.length then
            liftM (m := IO) (throw (IO.userError
              s!"assignment expects {targets.length} values, call produced {outs.size}"))
          for (t, v) in targets.zip outs.toList do
            assignTo cfg t.val v
  -- A bare declaration with no initializer.
  | ⟨.Var (Variable.Declare param), _⟩ => do
      if let some ⟨.UserDefined n, _⟩ := param.type then
        if (← get).index.noWitness.contains n.text then
          evalError s!"'{param.name.text}' has no starting value: the witness of '{n.text}' could not be evaluated"
      modify fun s =>
        let v := match param.type with
          | some t => defaultValue s.index t.val
          | none => .unset
        { s with stack := declareLocal s.stack param.name.text v }
  | ⟨.IfThenElse cond thenB elseB, _⟩ => do
      let st ← get
      if st.coroSelf.isNone then
        let c ← evalExprMd cfg cond
        if ← liftM (isTrue cfg c) then evalScopedStmt cfg thenB
        else match elseB with
          | some e => evalScopedStmt cfg e
          | none => pure ()
      else
        -- Inside a coroutine the branch taken is part of the suspension path
        -- (child 0 is `then`, child 1 is `else`), so a resume re-enters the arm
        -- the body actually suspended in. Re-deciding it by re-testing the
        -- condition would be wrong: the caller may have changed the state the
        -- condition reads while the coroutine was suspended.
        let base := st.cursor
        match st.seek with
        | some (branch :: rest) => do
            enterChild base branch (some rest)
            match branch, elseB with
            | 0, _ => evalScopedStmt cfg thenB
            | 1, some e => evalScopedStmt cfg e
            | _, _ => evalError s!"resumed into `if` branch {branch}, which is not there"
        | _ => do
            let c ← evalExprMd cfg cond
            if ← liftM (isTrue cfg c) then do
              enterChild base 0 none
              evalScopedStmt cfg thenB
            else match elseB with
              | some e => do
                  enterChild base 1 none
                  evalScopedStmt cfg e
              | none => pure ()
        modify fun s => { s with cursor := base, seek := none }
  | ⟨.While cond invariants _ body postTest, _⟩ => do
      -- Each invariant is checked at the loop head and a false one is reported at
      -- the invariant as a failing assertion, as the verifier reports one that
      -- fails on entry. For a `while` the head follows the condition, which may
      -- have effects, and is reached on the way out too; for a `do`/`while` it
      -- precedes every run of the body. The
      -- termination measure is a proof obligation only and is not run.
      let checkInvariants : EvalM Unit :=
        for inv in invariants do
          evalStmt cfg ⟨.Assert inv none, inv.source⟩
      let st ← get
      -- The body is the loop's only child, so it shares the loop's own position
      -- and needs no index. It IS re-entered per iteration though, so its
      -- position is re-established absolutely each time rather than inherited
      -- from wherever the previous iteration left off.
      let base := st.cursor
      let enterBody : EvalM Unit :=
        if st.coroSelf.isSome then modify fun s => { s with cursor := base } else pure ()
      -- A pending seek means the coroutine suspended *inside* the body, so the
      -- resumed iteration runs without testing the condition: the body was
      -- already entered, in a step that has gone.
      if postTest && st.seek.isNone then do
        checkInvariants
        evalScopedStmt cfg body
      else if st.seek.isSome then do
        evalScopedStmt cfg body
      let rec loop : Nat → EvalM Unit
        | 0 => throw .outOfFuel
        | n + 1 => do
          enterBody
          let c ← evalExprMd cfg cond
          unless postTest do checkInvariants
          if ← liftM (isTrue cfg c) then do
            if postTest then checkInvariants
            evalScopedStmt cfg body
            loop n
          else pure ()
      loop st.fuel
  | ⟨.Throw value, _⟩ => do
      let v ← evalExprMd cfg value
      throw (.throw_ v)
  | ⟨.Try body catches finally?, _⟩ => do
      let st ← get
      let inCoro := st.coroSelf.isSome
      -- Each arm of a `try` is a child of its own (0 is the body, `k + 1` is
      -- catch clause `k`, last is `finally`), so a `yield` inside one reifies a
      -- path that says which arm it was in.
      --
      -- The body's arm and any `catch` arm can both be resumed into. A `catch` needs
      -- neither the exception that selected it nor its predicate re-evaluated: the
      -- binding was inserted into the frame's locals on the way in and the frame is
      -- restored wholesale on resume, and the predicate already made its choice --
      -- re-running it could even observe a different answer, since a Python `except`
      -- target is an arbitrary expression. So the resume re-enters that clause's body
      -- directly. This is what lets `yield` sit inside an `except` clause, which
      -- Python allows and a generator holding state across a handler needs.
      let base := st.cursor
      let enterArm (k : Nat) (childSeek : Option (List Nat)) : EvalM Unit :=
        if inCoro then enterChild base k childSeek else pure ()
      let armSeek := if inCoro then st.seek else none
      -- Arm 0 is the body; arms 1..n are the catch clauses; `n + 1` is the `finally`,
      -- which is not resumable (a `finally` reached by a resume would have to decide
      -- what it was unwinding, and that signal is not reified).
      if let some (k :: _) := armSeek then
        if k > catches.length then
          evalError s!"resumed into `try` arm {k}: a `finally` arm cannot be resumed into"
      let bodySeek : Option (List Nat) := match armSeek with
        | some (0 :: rest) => some rest
        | _ => none
      -- Set when the suspension being resumed was inside catch clause `k - 1`.
      let resumeClause? : Option (Nat × CatchClause × List Nat) :=
        match armSeek with
        | some (k :: rest) =>
          if h : k > 0 ∧ k - 1 < catches.length
            then some (k, catches[k - 1]'(h.2), rest)
            else none
        | _ => none
      -- `finally` runs on every exit path, including an unwinding one, so the
      -- signal is re-thrown only after it has run.
      let runFinally : EvalM Unit := match finally? with
        | some f => do
            enterArm (catches.length + 1) none
            evalScopedStmt cfg f
        | none => pure ()
      -- Run a handler, then unbind its clause and run the `finally` exactly once,
      -- whether the handler finished or left by a signal. A signal raised by the
      -- `finally` itself therefore leaves without running it again.
      let finishClause (c : CatchClause) : EvalM Unit := do
        let handled ← tryCatch (do evalScopedStmt cfg c.body; pure (none : Option Control)) fun sig =>
          match sig with
          -- As in the body arm: a suspension pauses the handler, it does not leave
          -- the `try`, so `finally` must not run.
          | .suspended => throw .suspended
          | _ => pure (some sig)
        modify fun s => { s with stack := unbindCatch s.stack c.binding.text }
        runFinally
        if let some sig := handled then throw sig
      if let some (k, c, rest) := resumeClause? then
        -- Straight back into the handler that was running. The `try` body is NOT
        -- re-executed: it already ran, and re-running it would repeat its effects.
        enterArm k (some rest)
        finishClause c
      else do
      enterArm 0 bodySeek
      let outcome ← tryCatch (do evalScopedStmt cfg body; pure (none : Option Control)) fun
        | .throw_ v => pure (some (.throw_ v))
        | other => pure (some other)
      match outcome with
      | none => runFinally
      | some .suspended =>
          -- A suspension is not an exit from the `try`: the body is paused
          -- inside it and will come back, so `finally` must not run.
          throw .suspended
      | some (.throw_ v) => do
          -- Clauses are tried in order, first match wins; an unmatched value
          -- keeps unwinding so an outer handler still sees it.
          -- `k` is the clause's own index, so `enterArm (k + 1)` names this arm in the
          -- path a `yield` inside the handler reifies -- which is what makes the
          -- resume above able to come back to it.
          let rec tryClauses : Nat → List CatchClause → EvalM Unit
            | _, [] => do runFinally; throw (.throw_ v)
            | k, c :: rest => do
              -- The binding is scoped to its clause, so a same-named local of the
              -- enclosing procedure is put back once the clause is done with it.
              let name := c.binding.text
              let unbind : EvalM Unit := modify fun s =>
                { s with stack := unbindCatch s.stack name }
              modify fun s => { s with stack := bindCatch s.stack name v }
              let clauseMatches ← match c.predicate with
                | none => pure true
                | some pred => do
                    let pv ← tryCatch (evalExprMd cfg pred) fun sig => do
                      unbind; runFinally; throw sig
                    liftM (isTrue cfg pv)
              if clauseMatches then do
                enterArm (k + 1) none
                -- A `yield` inside the handler pauses it, so `finishClause` does not
                -- run the `finally` then. Otherwise it would fire once per
                -- suspension: a handler that yields twice would run it twice, and
                -- anything the `finally` was balancing -- a pushed exception, an
                -- acquired resource -- would be released while the handler is live.
                finishClause c
              else do
                unbind
                tryClauses (k + 1) rest
          tryClauses 0 catches
      | some other => do runFinally; throw other
  | ⟨.Assume _, _⟩ =>
      -- An `assume` constrains the verifier's state space and has no runtime
      -- effect, so the interpreter ignores it -- matching the Core interpreter's
      -- `ignoreAssumes`.
      pure ()
  | ⟨.Assert cond summary, stmtSource⟩ => do
      let v ← evalExprMd cfg cond
      if (← liftM (isTrue cfg v)) then
        unless (← get).quiet do
          let exprText := toString (Strata.Laurel.formatStmtExpr cond)
          liftM (m := IO) (IO.println s!"· PASS assert {exprText}")
      else
        -- Use `stmtSource` (the whole `assert` statement's range, not just the
        -- condition's) so the inline `// ^^^` annotations match both interpreters.
        let summaryText := summary.getD "assertion"
        let failure := Strata.Message.withRange stmtSource s!"{summaryText} does not hold"
        modify fun s => { s with assertFailures := s.assertFailures.push failure }
  | ⟨.Return value?, _⟩ => do
      let v? ← match value? with
               | some e => some <$> evalExprMd cfg e
               | none   => pure none
      throw (.return_ v?)
  | stmt@⟨.StaticCall .., _⟩ => do
      -- Bare `foo(args)` as a statement — discard the return value.
      let _ ← evalExprMd cfg stmt
      pure ()
  | ⟨.Yield, _⟩ => do
      let _ ← evalYield
      pure ()
  | ⟨s@(.Resume ..), _⟩ | ⟨s@(.HasNext ..), _⟩ => do
      -- Statement position drops the value: a bare `yield` ignores what the next
      -- resume sends in, and a bare `resume(co)` ignores the yielded payload.
      let _ ← evalExpr cfg s
      pure ()
  -- Any other expression in statement position (`x++`, `x += e`, `o#m()`, a bare
  -- trailing `x`) runs for its effects and its value is dropped.
  | stmt => do
      let _ ← evalExprMd cfg stmt
      pure ()

/-- Run a statement list, maintaining the coroutine position and honouring a
    pending fast-forward.

    Statement lists are the only place a coroutine's suspension path branches, so
    this is where child indices are assigned and where `seek` is consumed: while
    it says `some (i :: rest)` the statements before index `i` are skipped —
    they ran in an earlier step — statement `i` is entered with `rest`, and
    everything after it runs normally. Outside a coroutine body neither the
    position nor the seek means anything, and the walk is a plain `forM`.

    `asExpr` selects the value: with `asExpr := true` the trailing statement is
    evaluated as an expression and its value returned, which is what a
    `{ lemma(x); e }` block in expression position evaluates to. -/
partial def evalStmtList (cfg : ExternalBackend) (stmts : List Strata.Laurel.StmtExprMd)
    (asExpr : Bool) : EvalM Value := do
  let runStmt (s : Strata.Laurel.StmtExprMd) : EvalM Unit := do
    modify fun st => { st with stmtSite := s.source }
    evalStmt cfg s
  let st ← get
  if st.coroSelf.isNone then
    if asExpr then
      match stmts.reverse with
      | [] => pure default
      | last :: earlier => do
          earlier.reverse.forM (fun s => runStmt s)
          modify fun s => { s with stmtSite := last.source }
          evalExprMd cfg last
    else do
      stmts.forM (fun s => runStmt s)
      pure default
  else
    let base := st.cursor
    let (start, inner) := seekEntry st.seek
    let rec go : Nat → List Strata.Laurel.StmtExprMd → EvalM Value
      | _, [] => pure default
      | k, s :: rest => do
        enterChild base k (if k == start then inner else none)
        if rest.isEmpty then do
          let v ← if asExpr then evalExprMd cfg s else do runStmt s; pure default
          modify fun s' => { s' with cursor := base, seek := none }
          pure v
        else do
          runStmt s
          go (k + 1) rest
    go start (stmts.drop start)

/-- The coroutine instance a value denotes, with the address it is keyed by (the
    same address the `Value.ref` carries). `what` names the operation for the
    error message, since every way of failing here is a client mistake: a
    `resume` / `has_next` / `coroCompletion` applied to something that is not a
    coroutine. -/
partial def coroInstance (v : Value) (what : String) : EvalM (Nat × CoroState) := do
  match v with
  | .ref addr => do
      let st ← get
      match st.coros[addr]? with
      | some co => pure (addr, co)
      | none => evalError s!"'{what}' on #{addr}, which is not a coroutine instance"
  | _ => evalError s!"'{what}' on a non-coroutine {reprVariant v}"

/-- `yield`: suspend the coroutine body that is running, or — when this is the
    suspension point the current resume is fast-forwarding to — deliver the value
    that resume sent in and carry on.

    The suspension path and the frame are written into the instance here, rather
    than where `Control.suspended` is caught, because `EvalState.cursor` names the
    yield's own position only at the yield itself. -/
partial def evalYield : EvalM Value := do
  let st ← get
  let some addr := st.coroSelf
    | evalError "`yield` outside a coroutine body"
  let some co := st.coros[addr]?
    | evalError s!"`yield` in a coroutine whose instance #{addr} is gone"
  match st.seek with
  | some [] => do
      -- The arrival marker: this `yield` already suspended, in the step that led
      -- here. It does not suspend again; it hands the body the resumed value and
      -- the fast-forward is over.
      modify fun s => { s with seek := none }
      pure co.sent
  | _ => do
      modify fun s =>
        let suspended := { co with resumePt := some s.cursor, frame := s.stack }
        { s with coros := s.coros.insert addr suspended }
      throw .suspended

/-- `resume(co, v)`: run the coroutine instance `target` denotes until it next
    suspends or finishes, and evaluate to the value it yields.

    The instance's frame becomes the running stack and its suspension path becomes
    the pending `seek`, so the body replays from its root but executes nothing
    before the `yield` it stopped at. Everything the caller had — its stack, its
    own position and seek, which coroutine (if any) it was itself running — is
    saved and restored by absolute value: a suspension leaves through the
    exception channel, so a restore expressed as an undo would be skipped exactly
    when it is needed. -/
partial def resumeCoroutine (cfg : ExternalBackend) (target : Value) (sent : Value)
    : EvalM Value := do
  let (addr, co) ← coroInstance target "resume"
  if co.finished then
    evalError s!"'resume' of coroutine '{co.proc}' after it ran to completion"
  if co.running then
    evalError s!"'resume' of coroutine '{co.proc}' from inside its own body"
  let st ← get
  let some proc := st.index.procs[co.proc]?
    | evalError s!"unknown coroutine '{co.proc}'"
  let some body := proc.body.implementation
    | evalError s!"coroutine '{co.proc}' has no body to run"
  let restoreCaller : EvalM Unit := modify fun s =>
    { s with stack := st.stack, callStack := st.callStack, cursor := st.cursor,
             seek := st.seek, coroSelf := st.coroSelf, stmtSite := st.stmtSite,
             callSite := st.callSite }
  modify fun s =>
    { s with stack := co.frame, callStack := co.proc :: s.callStack, cursor := [],
             seek := co.resumePt, coroSelf := some addr,
             coros := s.coros.insert addr { co with sent, running := true } }
  let stopped : EvalM Unit := modify fun s =>
    match s.coros[addr]? with
    | some c => { s with coros := s.coros.insert addr { c with running := false } }
    | none => s
  let signal ← tryCatch (do evalStmt cfg body; pure (none : Option Control)) fun
    | .suspended     => pure (some .suspended)
    | .return_ value => pure (some (.return_ value))
    | other => do
        -- A signal escaping the body ends the coroutine: resuming it again would
        -- re-run the statements after its last suspension.
        modify fun s =>
          let done := { (s.coros[addr]?.getD co) with resumePt := none, finished := true }
          { s with coros := s.coros.insert addr done }
        stopped
        restoreCaller
        throw other
  let yielded ←
    match signal with
    | some .suspended =>
        -- `yield` saved the frame and the path; the resume's value is the
        -- coroutine's `yields` binding as of that frame.
        let s ← get
        match proc.yields.head? with
        | none => pure .unset
        | some p => pure ((s.coros[addr]?.bind (·.frame[p.name.text]?)).getD .unset)
    | _ => do
        -- The body returned or fell off its end. Its completion value is the
        -- `return`'s payload, and there is no yielded value for this step: a
        -- client is expected to have checked `has_next(co)`.
        let finalFrame := (← get).stack
        let completed := match signal with
          | some (.return_ (some v)) => v
          | _ => .unset
        modify fun s =>
          let done := { (s.coros[addr]?.getD co) with
            frame := finalFrame, resumePt := none, finished := true, completed }
          { s with coros := s.coros.insert addr done }
        pure .unset
  stopped
  restoreCaller
  pure yielded

/-- Evaluate a call in a position that wants ALL of its outputs. Only a
    `StaticCall` can produce more than one, so anything else yields a singleton. -/
partial def evalCallOutputs (cfg : ExternalBackend) (e : StmtExpr) : EvalM (Array Value) := do
  match e with
  | .StaticCall callee args typeArgs =>
    match Operation.ofProcName? callee.text with
    | some _ => do let v ← evalExpr cfg e; pure #[v]
    | none => do
      let site := (← get).callSite
      let st ← get
      if (lookupCallee st.index callee).isNone then
        let v ← evalExpr cfg e
        return #[v]
      let argVals ← args.mapM (evalExprMd cfg)
      let absent := match typeArgs with
        | [_, v] => defaultValue st.index v.val
        | _ => .unset
      match callBuiltin callee.text argVals absent with
      | some act => do let v ← liftM act; pure #[v]
      | none => invokeCallee cfg site callee argVals
  | .InstanceCall target callee args => do
    let site := (← get).callSite
    let tv ← evalExprMd cfg target
    let argVals ← args.mapM (evalExprMd cfg)
    let proc ← resolveMethod tv callee.text
    invokeProc cfg site proc (tv :: argVals)
  | _ => do let v ← evalExpr cfg e; pure #[v]

/-- Invoke a static (top-level) procedure by name with already-evaluated
    arguments, returning its outputs in declaration order.

    Frame discipline: the heap and `program` are shared across the call, but
    locals are isolated — we save the caller's `StackFrame`, swap in a fresh
    callee frame containing the parameters, run the body, then restore. Outputs
    are pre-declared `.unset` in that frame, because a multi-output procedure
    assigns them by name and then `return`s nothing.

    `return_` is caught here; `throw_` and `exit_` are not. A thrown value has to
    cross the call boundary to reach an enclosing `catch`, and that asymmetry is
    the whole difference between Laurel's two non-local exits. -/
partial def invokeCallee (cfg : ExternalBackend) (site : FileRange) (callee : Identifier)
    (argVals : List Value) : EvalM (Array Value) := do
  let index := (← get).index
  if callee.uniqueId.isNone && index.overloaded.contains callee.text then
    evalError s!"call to overloaded '{callee.text}' was not resolved, so its overload is unknown"
  match lookupCallee index callee with
  | some proc => invokeProc cfg site proc argVals
  | none => evalError s!"unknown procedure '{callee.text}'"

/-- Check `proc`'s call-site preconditions against `argVals`, recording each one
    that is false at `site` and carrying on, as a failing `assert` does. A free
    precondition is assumed by the callee and not checked. -/
partial def checkPreconditions (cfg : ExternalBackend) (site : FileRange) (proc : Procedure)
    (argVals : List Value) : EvalM Unit := do
  let checked := proc.preconditions.filter (·.mode.doesAssert)
  if checked.isEmpty then return
  let caller ← get
  let restore : EvalM Unit := modify fun st =>
    { st with stack := caller.stack, cursor := caller.cursor, seek := caller.seek,
              coroSelf := caller.coroSelf }
  let frame : StackFrame :=
    (proc.inputs.zip argVals).foldl (fun acc (param, v) => acc.insert param.name.text v) {}
  modify fun st => { st with stack := frame, cursor := [], seek := none, coroSelf := none }
  tryCatch
    (for c in checked do
      let v ← evalExprMd cfg c.condition
      unless ← liftM (isTrue cfg v) do
        let failure := Strata.Message.withRange site
          s!"{c.summary.getD "precondition"} does not hold"
        modify fun st => { st with assertFailures := st.assertFailures.push failure })
    fun sig => do restore; throw sig
  restore

/-- Check `posts` on exit from `proc`: inputs at their entry values, outputs at
    their final ones (a `return e` supplies the single output), and `old(e)`
    against the entry heap, globals and in-out parameters. A false one is recorded at its own source, as the
    verifier and the Core interpreter report it. Runs in the callee's context, so
    the caller restores its own frame afterwards. -/
partial def checkPostconditions (cfg : ExternalBackend) (proc : Procedure)
    (posts : List Condition) (entryFrame : StackFrame)
    (entry : Array HeapObject × Std.HashMap String Value)
    (exitFrame : StackFrame) (returned : Option Value) : EvalM Unit := do
  let outputs : StackFrame := match returned, proc.outputs with
    | some v, [o] => ({} : StackFrame).insert o.name.text v
    | _, _ => proc.outputs.foldl (init := {}) fun acc o =>
        acc.insert o.name.text (exitFrame[o.name.text]?.getD .unset)
  let frame := outputs.fold (init := entryFrame) fun acc k v => acc.insert k v
  let inouts : StackFrame := proc.outputs.foldl (init := {}) fun acc o =>
    if proc.inputs.any (·.name.text == o.name.text) then
      match entryFrame[o.name.text]? with
      | some v => acc.insert o.name.text v
      | none => acc
    else acc
  let enclosing := (← get).entryState
  modify fun st => { st with stack := frame, entryState := some (entry.1, entry.2, inouts) }
  tryCatch
    (for c in posts do
      let v ← evalExprMd cfg c.condition
      unless ← liftM (isTrue cfg v) do
        let failure := Strata.Message.withRange c.condition.source
          s!"{c.summary.getD "postcondition"} does not hold"
        modify fun st => { st with assertFailures := st.assertFailures.push failure })
    fun sig => do
      modify fun st => { st with entryState := enclosing }
      throw sig
  modify fun st => { st with entryState := enclosing }

partial def invokeProc (cfg : ExternalBackend) (site : FileRange) (proc : Procedure)
    (argVals : List Value) : EvalM (Array Value) := do
  let name := proc.name.text
  if argVals.length != proc.inputs.length then
    liftM (m := IO) (throw (IO.userError
      s!"arity mismatch calling '{proc.name.text}': expected {proc.inputs.length} args, got {argVals.length}"))
  checkPreconditions cfg site proc argVals
  -- Calling a `coroutine` SPAWNS an instance instead of running it — the body
  -- only ever runs under `resume`. The instance is a heap object so that an
  -- ordinary `Value.ref` denotes it, with the coroutine's own frame and
  -- suspension point held alongside in `EvalState.coros` (see `CoroState`). The
  -- frame captures the arguments now, so later mutation of the caller's variables
  -- is not visible to the coroutine.
  if proc.is_coroutine then
    let withInputs : StackFrame :=
      (proc.inputs.zip argVals).foldl
        (fun acc (param, v) => acc.insert param.name.text v) {}
    -- The `yields` / `resumes` bindings are the coroutine's own locals; they start
    -- at their type's default, as any declared local does.
    let index := (← get).index
    let frame : StackFrame :=
      (proc.yields ++ proc.resumes).foldl
        (fun acc p => acc.insert p.name.text (defaultValue index p.type.val)) withInputs
    let addr := (← get).heap.size
    let spawned : CoroState := { proc := name, frame, resumePt := none }
    let obj : HeapObject := { typeName := name, fields := {} }
    modify fun st =>
      { st with heap := st.heap.push obj, coros := st.coros.insert addr spawned }
    return #[.ref addr]
  -- `.External` short-circuits to the host language: no Laurel body, so no frame
  -- swap and no return-control to catch.
  let body ← match proc.body with
    | .External         => do
        let ext ← liftM (cfg.callExternal proc.name.text argVals)
        return #[.external ext]
    | b => match b.implementation with
      | some body => pure body
      | none => do
          -- No body: every output is unconstrained, so it answers its type's
          -- default, except an in-out parameter, which keeps its argument.
          let index := (← get).index
          return proc.outputs.toArray.map fun o =>
            match (proc.inputs.zip argVals).find? (·.1.name.text == o.name.text) with
            | some (_, v) => v
            | none => defaultValue index o.type.val
  let withParams : StackFrame :=
    (proc.inputs.zip argVals).foldl
      (fun acc (param, v) => acc.insert param.name.text v) {}
  -- An output that is also an input is an in-out parameter and keeps its argument.
  let index := (← get).index
  let calleeStack : StackFrame :=
    proc.outputs.foldl (init := withParams) fun acc o =>
      if acc.contains o.name.text then acc
      else acc.insert o.name.text (defaultValue index o.type.val)
  let caller ← get
  let saved := caller.stack
  let savedCalls := caller.callStack
  let restoreCaller : EvalM Unit := modify fun st =>
    { st with stack := saved, callStack := savedCalls, cursor := caller.cursor,
              seek := caller.seek, coroSelf := caller.coroSelf, stmtSite := caller.stmtSite,
              callSite := caller.callSite }
  -- A `yield` suspends the coroutine whose body lexically contains it, so a
  -- procedure called *from* a coroutine body is not part of that coroutine:
  -- clearing `coroSelf` turns a `yield` in the callee into a reported error
  -- instead of a suspension recorded against a position in the wrong body. It
  -- also switches the callee's position bookkeeping off, which is what keeps the
  -- ordinary (coroutine-free) call path free of it.
  modify fun st => { st with stack := calleeStack, callStack := name :: st.callStack,
                             cursor := [], seek := none, coroSelf := none }
  let posts := proc.body.postconditions.filter (·.mode.doesAssert)
  -- Holding the entry heap keeps it shared, so the callee's first write copies
  -- it; only a procedure with postconditions pays for that.
  let cur ← get
  let entry := if posts.isEmpty then (#[], {}) else (cur.heap, cur.globals)
  let returned : Option Value ←
    tryCatch (do evalStmt cfg body; pure none) fun
      | .return_ v? => pure v?
      | other => do
          -- Restore the caller's frame before the signal leaves, or an enclosing
          -- `catch` would run against the callee's locals.
          restoreCaller
          throw other
  let calleeFrame := (← get).stack
  unless posts.isEmpty do
    tryCatch (checkPostconditions cfg proc posts calleeStack entry calleeFrame returned)
      fun sig => do restoreCaller; throw sig
  restoreCaller
  match returned with
  | some v =>
      -- `return e` in a single-output procedure supplies the value directly.
      pure #[v]
  | none =>
      -- Otherwise the outputs were assigned by name. A void procedure has none,
      -- and an output the body never assigned is arbitrary, so it comes back
      -- `unset` and only a use of it is an error.
      pure (proc.outputs.toArray.map fun o => calleeFrame[o.name.text]?.getD .unset)

end

/-- What an entry-point run produced beyond its assertion failures. -/
inductive Outcome where
  /-- Ran to completion (or returned) without an escaping signal. -/
  | completed
  /-- A `throw` reached the top of the entry procedure. -/
  | escaped (value : Value)
  /-- The step budget ran out; the program under test may not terminate. -/
  | outOfFuel
  deriving Inhabited

/-- Entry point: locate and run the single procedure named by
    `opts.entryProcedure`, then return the final stack as a displayable snapshot
    paired with any runtime assertion failures collected during the run. A
    top-level `return` is treated as a clean exit just like falling off the end;
    accumulated failures survive it. Runs exactly one entry — the test harness
    iterates over `entry`-marked procedures and calls this once per entry. -/
def evalProgramWithOutcome (cfg : ExternalBackend) (opts : Options) (p : Program)
    : IO (DisplayEvalState × Array Strata.Message × Outcome) := do
  try
    let initState : EvalState :=
      { stack := {}, program := p, index := buildIndex p
        fuel := opts.fuel, quiet := !opts.printAsserts }
    let (outcome, finalState) ←
      match p.staticProcedures.find? (·.name.text == opts.entryProcedure) with
      | none => throw (IO.userError s!"no `{opts.entryProcedure}` procedure")
      | some mainProc =>
        -- Run the body's implementation for both `transparent` and `opaque`
        -- procedures (an `opaque` body carries its statements under
        -- `implementation`); a bodiless `opaque`/`abstract`/`external` entry has
        -- nothing to run.
        match mainProc.body.implementation with
        | some body =>
            -- Outputs are pre-declared so an entry that assigns them by name can
            -- run, exactly as at a call boundary.
            let withOutputs := mainProc.outputs.foldl
              (fun (acc : StackFrame) o => acc.insert o.name.text (defaultValue initState.index o.type.val)) {}
            -- File-scope globals are initialised BEFORE the entry runs, in
            -- declaration order so a later initialiser can read an earlier global.
            -- An initialiser is an ordinary expression and may call a procedure, so
            -- this runs through the evaluator rather than a constant folder -- which
            -- is what lets a language runtime build its own interpreter state in one.
            -- A global with no initialiser starts at its type's default, as a
            -- composite field does.
            -- Each constrained type's witness is evaluated once, before anything
            -- starts at the type's default (the outputs above are re-defaulted for
            -- that reason), and checked against the type's constraint and those of
            -- the constrained types it refines, as the verifier checks the
            -- definition. Failures are reported at the witness. A witness that
            -- cannot be evaluated leaves its type without a default rather than
            -- stopping a run that may never use the type.
            let constrained : Std.HashMap String ConstrainedType :=
              p.types.foldl (init := {}) fun acc t => match t with
                | .Constrained c => acc.insert c.name.text c
                | _ => acc
            let attempt (act : EvalM Value) : EvalM (Option Value) := do
              let before ← get
              let restore : EvalM Unit := modify fun st =>
                { st with stack := before.stack, callStack := before.callStack,
                          fuel := before.fuel, cursor := before.cursor, seek := before.seek }
              tryCatchThe IO.Error
                (tryCatch (some <$> act) (fun _ => do restore; pure none))
                (fun _ => do restore; pure none)
            let report (c : ConstrainedType) (msg : String) : EvalM Unit := do
              let failure := Strata.Message.withRange c.witness.source msg
              modify fun st => { st with assertFailures := st.assertFailures.push failure }
            let rec constraintChain (fuel : Nat) (c : ConstrainedType) : List ConstrainedType :=
              match fuel, c.base.val with
              | k + 1, .UserDefined n => match constrained[n.text]? with
                | some b => c :: constraintChain k b
                | none => [c]
              | _, _ => [c]
            let initGlobals : EvalM Unit := do
              for t in p.types do
                if let .Constrained c := t then
                  modify fun st => { st with stmtSite := c.witness.source }
                  let v? ← match (← get).index.witnesses[c.name.text]? with
                    | some v => pure (some v)
                    | none => attempt (evalExprMd cfg c.witness)
                  match v? with
                  | none => do
                    report c s!"witness of '{c.name.text}' could not be evaluated"
                    modify fun st => { st with index := { st.index with
                      noWitness := st.index.noWitness.insert c.name.text } }
                  | some v =>
                    modify fun st =>
                      { st with index := { st.index with
                          witnesses := st.index.witnesses.insert c.name.text v } }
                    for k in constraintChain constrained.size c do
                      let saved := (← get).stack
                      modify fun st => { st with stack := st.stack.insert k.valueName.text v }
                      let r? ← attempt (evalExprMd cfg k.constraint)
                      modify fun st => { st with stack := saved }
                      match r? with
                      | some r => unless ← liftM (isTrue cfg r) do report c "assertion does not hold"
                      | none => report c s!"constraint of '{k.name.text}' could not be evaluated on the witness"
              modify fun st => { st with stmtSite := .unknown }
              for o in mainProc.outputs do
                modify fun st =>
                  { st with stack := st.stack.insert o.name.text (defaultValue st.index o.type.val) }
              for f in p.staticFields do
                match f.initializer with
                | some e => do
                    modify fun st => { st with stmtSite := e.source }
                    let v ← evalExprMd cfg e
                    modify fun st => { st with globals := st.globals.insert f.name.text v }
                | none =>
                    modify fun st =>
                      { st with globals := st.globals.insert f.name.text (defaultValue st.index f.type.val) }
            let start := { initState with stack := withOutputs }
            let start ← match ← (initGlobals.run.run start) with
              | (.ok (), s') => pure s'
              | (.error .outOfFuel, _) => throw (IO.userError "out of fuel initialising file-scope globals")
              | (.error (.throw_ v), _) =>
                  throw (IO.userError s!"uncaught throw of {v.display} initialising file-scope globals")
              | (.error _, _) => throw (IO.userError "unexpected control flow initialising file-scope globals")
            let res ← (evalStmt cfg body).run.run start
            match res with
            | (.ok (),                s') => pure (Outcome.completed, s')
            | (.error (.return_ _),    s') => pure (Outcome.completed, s')
            | (.error (.throw_ v),     s') => pure (Outcome.escaped v, s')
            | (.error .outOfFuel,      s') => pure (Outcome.outOfFuel, s')
            | (.error (.exit_ l),      _)  =>
                throw (IO.userError s!"`exit {l}` with no enclosing block labelled '{l}'")
            | (.error .suspended,      _)  =>
                throw (IO.userError "`yield` with no coroutine to suspend")
        | none => pure (Outcome.completed, initState)
    let display := finalState.toDisplay
    if opts.dumpState then
      IO.println display.format
    pure (display, finalState.assertFailures, outcome)
  finally
    cfg.cleanup

/-- `evalProgramWithOutcome`, dropping the outcome: an escaping `throw` or
    exhausted fuel becomes an `IO` error, and only the display state and
    assertion failures are returned. -/
def evalProgram (cfg : ExternalBackend) (opts : Options) (p : Program)
    : IO (DisplayEvalState × Array Strata.Message) := do
  let (display, failures, outcome) ← evalProgramWithOutcome cfg opts p
  match outcome with
  | .completed => pure (display, failures)
  | .escaped v => throw (IO.userError s!"uncaught throw of {v.display}")
  | .outOfFuel => throw (IO.userError "out of fuel")

def runInternalLaurel (opts : Options) (filePath : String) : IO Unit := do
  let path : System.FilePath := filePath
  let prog ← Strata.readLaurelTextFile path
  let _ ← evalProgram ({} : ExternalBackend) opts prog

end -- public section

end Strata.Laurel.Interpreter
