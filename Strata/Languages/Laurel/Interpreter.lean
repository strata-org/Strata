/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Std.Data.HashMap
public import Strata.Languages.Laurel

namespace Strata.Laurel.Interpreter

public section

open Strata.Laurel

structure Options where
  dumpState : Bool := true
  entryProcedure : String := "main"
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
  deriving Inhabited

def Value.display : Value → String
  | .external e => e.display
  | .int p      => toString p.n
  | .bool p     => toString p.b
  | .string p   => p.s

/-- One call frame: local variables (keyed by name) to their evaluated values.
    The stack of frames is implicit in Lean's own call stack — `invokeProcedure`
    saves the caller's frame, runs the callee with a fresh one, then restores. -/
abbrev StackFrame := Std.HashMap String Value

structure EvalState where
  stack    : StackFrame
  program  : Program
  /-- Runtime assertion failures accumulated during a run, in evaluation order.
      A failing `assert` records a source-mapped `Message` here and execution
      continues, mirroring the Core interpreter's `collectAllAssertFailures`
      behavior so the same examples can be checked against both interpreters. -/
  assertFailures : Array Strata.Message := #[]
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
    Currently only `return_`, which is thrown at a `return` statement and
    caught at the procedure-call boundary. -/
inductive Control where
  | return_ (value : Option Value)

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
  | .Add, args                     =>
      throw (IO.userError s!"unsupported types for op .Add: {args.map reprVariant}")
  | .Sub, [.int ⟨x⟩, .int ⟨y⟩]     => pure (.int ⟨x - y⟩)
  | .Sub, args                     =>
      throw (IO.userError s!"unsupported types for op .Sub: {args.map reprVariant}")
  | .Mul, [.int ⟨x⟩, .int ⟨y⟩]     => pure (.int ⟨x * y⟩)
  | .Mul, args                     =>
      throw (IO.userError s!"unsupported types for op .Mul: {args.map reprVariant}")
  | .Div, [.int ⟨x⟩, .int ⟨y⟩]     =>
      if y == 0 then throw (IO.userError "division by zero in op .Div")
      else pure (.int ⟨Int.ediv x y⟩)
  | .Div, args                     =>
      throw (IO.userError s!"unsupported types for op .Div: {args.map reprVariant}")
  | .Mod, [.int ⟨x⟩, .int ⟨y⟩]     =>
      if y == 0 then throw (IO.userError "modulo by zero in op .Mod")
      else pure (.int ⟨Int.emod x y⟩)
  | .Mod, args                     =>
      throw (IO.userError s!"unsupported types for op .Mod: {args.map reprVariant}")
  | .Neg, [.int ⟨x⟩]               => pure (.int ⟨-x⟩)
  | .Neg, args                     =>
      throw (IO.userError s!"unsupported types for op .Neg: {args.map reprVariant}")
  -- String
  | .StrConcat, [.string ⟨x⟩, .string ⟨y⟩] => pure (.string ⟨x ++ y⟩)
  | .StrConcat, args                       =>
      throw (IO.userError s!"unsupported types for op .StrConcat: {args.map reprVariant}")
  -- Equality (spans shapes via primEq)
  | .Eq,  [a, b] => do
      let eq ← primEq cfg a b
      pure (.bool ⟨eq⟩)
  | .Neq, [a, b] => do
      let eq ← primEq cfg a b
      pure (.bool ⟨!eq⟩)
  | op, args =>
      throw (IO.userError s!"unsupported op {repr op} on args: {args.map reprVariant}")

private def EvalState.toDisplay (s : EvalState) : DisplayEvalState :=
  { stack := s.stack.map (fun _ v => v.display) }


mutual

/-- Evaluate a Laurel expression to a `Value`. Mutually recursive with
    `evalStmt` (procedure bodies contain statements) and `invokeProcedure`
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
          liftM (m := IO) (throw (IO.userError s!"undefined identifier '{name.text}'"))
  | .StaticCall callee args => do
      match Operation.ofProcName? callee.text with
      | some .AndThen =>
          match args with
          | [a, b] => do
            let va ← evalExpr cfg a.val
            if ← liftM (isTrue cfg va) then
              let vb ← evalExpr cfg b.val
              pure (.bool ⟨← liftM (isTrue cfg vb)⟩)
            else
              pure (.bool ⟨false⟩)
          | _ => liftM (m := IO) (throw (IO.userError "andThen expects exactly 2 arguments"))
      | some .OrElse =>
          match args with
          | [a, b] => do
            let va ← evalExpr cfg a.val
            if ← liftM (isTrue cfg va) then
              pure (.bool ⟨true⟩)
            else
              let vb ← evalExpr cfg b.val
              pure (.bool ⟨← liftM (isTrue cfg vb)⟩)
          | _ => liftM (m := IO) (throw (IO.userError "orElse expects exactly 2 arguments"))
      | some op => do
          let argVals ← args.mapM (fun a => evalExpr cfg a.val)
          liftM (evalOp cfg op argVals)
      | none => do
          let argVals ← args.mapM (fun a => evalExpr cfg a.val)
          invokeProcedure cfg callee.text argVals
  | _ => liftM (m := IO) (throw (IO.userError "unsupported expression"))

/-- Evaluate a Laurel statement for its side effects on the eval state. May
    throw `Control.return_` to unwind to the nearest `invokeProcedure`. -/
partial def evalStmt (cfg : ExternalBackend) : Strata.Laurel.StmtExprMd → EvalM Unit
  | ⟨.Block stmts none, _⟩ =>
      stmts.forM (fun s => evalStmt cfg s)
  | ⟨.Assign [⟨Variable.Declare param, _⟩] value, _⟩ => do
      let v ← evalExpr cfg value.val
      modify fun s => { s with stack := s.stack.insert param.name.text v }
  | ⟨.Assert cond summary, stmtSource⟩ => do
      let v ← evalExpr cfg cond.val
      let exprText := toString (Strata.Laurel.formatStmtExpr cond)
      if (← liftM (isTrue cfg v)) then
        liftM (m := IO) (IO.println s!"· PASS assert {exprText}")
      else
        -- Use `stmtSource` (the whole `assert` statement's range, not just the
        -- condition's) so the inline `// ^^^` annotations match both interpreters.
        let summaryText := summary.getD "assertion"
        let failure := Strata.Message.withRange stmtSource s!"{summaryText} does not hold"
        modify fun s => { s with assertFailures := s.assertFailures.push failure }
  | ⟨.Return value?, _⟩ => do
      let v? ← match value? with
               | some e => some <$> evalExpr cfg e.val
               | none   => pure none
      throw (.return_ v?)
  | ⟨s@(.StaticCall ..), _⟩ => do
      -- Bare `foo(args)` as a statement — discard the return value.
      let _ ← evalExpr cfg s
      pure ()
  | ⟨stmt, _⟩ => do
      liftM (m := IO) (throw (IO.userError
        s!"unsupported statement: {stmt.constrName}"))

/-- Invoke a static (top-level) procedure by name with already-evaluated
    arguments. The procedure is resolved from the program carried in `EvalM`'s
    state, so callers only supply the name and the argument values.

    Frame discipline: the heap (not yet supported) and `program` are shared
    across the call, but locals are isolated — we save the caller's `StackFrame`,
    swap in a fresh callee `StackFrame` containing only the parameters, run the
    body, then restore. The body's `return` is delivered via a `Control`
    exception caught here. -/
partial def invokeProcedure (cfg : ExternalBackend) (name : String) (argVals : List Value)
    : EvalM Value := do
  let s ← get
  let some proc := s.program.staticProcedures.find? (·.name.text == name)
    | liftM (m := IO) (throw (IO.userError s!"unknown procedure '{name}'"))
  -- Arity check only (no type check — we trust the source).
  if argVals.length != proc.inputs.length then
    liftM (m := IO) (throw (IO.userError
      s!"arity mismatch calling '{proc.name.text}': expected {proc.inputs.length} args, got {argVals.length}"))
  -- Pick the body. `.External` short-circuits to the host language: there
  -- is no Laurel-level body, so no frame swap and no return-control to
  -- catch — the backend hands back a `Value` and we're done.
  let body ← match proc.body with
    | .External         => do
        let ext ← liftM (cfg.callExternal proc.name.text argVals)
        return .external ext
    -- `transparent` and `opaque` (with an implementation) both carry runnable
    -- statements under `Body.implementation`; run those.
    | b => match b.implementation with
      | some body => pure body
      | none => liftM (m := IO) (throw (IO.userError
          s!"procedure '{proc.name.text}' has unsupported body kind"))
  let calleeStack : StackFrame :=
    (proc.inputs.zip argVals).foldl
      (fun acc (param, v) => acc.insert param.name.text v) {}
  let cur ← get
  let saved := cur.stack
  modify fun s => { s with stack := calleeStack }
  let result : Option Value ←
    tryCatch (do evalStmt cfg body; pure none) fun
      | .return_ v? => pure v?
  modify fun s => { s with stack := saved }
  -- Return the value. Void procedures (no declared outputs) may fall off the
  --    end without a `return`; their result is discarded by the bare-statement
  --    caller anyway. A non-void procedure that returns no value is an error —
  --    we must not fabricate one, since any fabricated value would ignore the
  --    declared output type.
  match result with
  | some v => return v
  | none   =>
      if proc.outputs.isEmpty then
        return default
      else
        liftM (m := IO) (throw (IO.userError
          s!"procedure '{proc.name.text}' declares outputs but returned no value"))

end

/-- Entry point: locate and run the single procedure named by
    `opts.entryProcedure`, then return the final stack as a displayable snapshot
    paired with any runtime assertion failures collected during the run. A
    top-level `return` is treated as a clean exit just like falling off the end;
    accumulated failures survive it. Runs exactly one entry — the test harness
    iterates over `entry`-marked procedures and calls this once per entry. -/
def evalProgram (cfg : ExternalBackend) (opts : Options) (p : Program)
    : IO (DisplayEvalState × Array Strata.Message) := do
  try
    let initState : EvalState := { stack := {}, program := p }
    let finalState ←
      match p.staticProcedures.find? (·.name.text == opts.entryProcedure) with
      | none => throw (IO.userError s!"no `{opts.entryProcedure}` procedure")
      | some mainProc =>
        -- Run the body's implementation for both `transparent` and `opaque`
        -- procedures (an `opaque` body carries its statements under
        -- `implementation`); a bodiless `opaque`/`abstract`/`external` entry has
        -- nothing to run.
        match mainProc.body.implementation with
        | some body =>
            let outcome ← (evalStmt cfg body).run.run initState
            match outcome with
            | (.ok (),              s') => pure s'
            | (.error (.return_ _), s') => pure s'
        | none => pure initState
    let display := finalState.toDisplay
    if opts.dumpState then
      IO.println display.format
    pure (display, finalState.assertFailures)
  finally
    cfg.cleanup

def runInternalLaurel (opts : Options) (filePath : String) : IO Unit := do
  let path : System.FilePath := filePath
  let prog ← Strata.readLaurelTextFile path
  let _ ← evalProgram ({} : ExternalBackend) opts prog

end -- public section

end Strata.Laurel.Interpreter
