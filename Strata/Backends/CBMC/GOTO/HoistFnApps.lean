/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.GOTO.CoreToCProverGOTO
public import Strata.Backends.CBMC.GOTO.InstToJson

/-! ## Hoisting function applications to GOTO function calls

The GOTO translation renders applications of program-defined Core functions
as `function_application` expression nodes backed by nil-valued
`mathematical_function` symbols — *uninterpreted* functions. CBMC never
consults a function definition through that route, so any assertion whose
truth depends on a function's body is unprovable.

GOTO's native mechanism for giving calls meaning is the statement-level
`FUNCTION_CALL` instruction targeting a GOTO function with a real body,
which symex executes. This module rewrites a GOTO program accordingly: each
`function_application f(args)` whose callee has an emitted GOTO body (the
`defined` set) is *hoisted* out of its expression:

    DECL          <fn>::1::$fcall<n> : <ret-ty>
    FUNCTION_CALL <fn>::1::$fcall<n> := f(args)

is inserted before the host instruction, and the application node is
replaced by the temporary. Nested applications hoist bottom-up, so
`f(g(x))` produces the call to `g` before the call to `f`. Sibling
applications are hoisted left to right, so `f(g1(x), g2(x))` calls `g1`
before `g2`. This fixes an evaluation order the source does not have, but
nothing can observe it: Core functions are pure (a body is a single
`SET_RETURN_VALUE` over an expression — no state reads, writes, or
nondeterminism), so the calls commute and any order yields the same values.

### Conditional expressions

Hoisting a call out of an `ite` branch would evaluate it unconditionally,
which is wrong: `if c then 1 else f(x)` must not call `f` when `c` holds.
When an `ite` branch contains hoistable calls, the `ite` itself is lowered
to instruction-level branching:

    <hoisted calls of cond>
    DECL  tmp
    GOTO  ELSE if !cond
    <hoisted calls of then-branch>
    ASSIGN tmp := then-value
    GOTO  END
    ELSE: <hoisted calls of else-branch>
    ASSIGN tmp := else-value
    END:  ...

and the `ite` node is replaced by `tmp`. Branches without hoistable calls
keep the plain `ite` expression form.

The same guarding applies to the short-circuit boolean operators: when a
non-first operand of `&&`/`||`/`=>` contains a hoistable call, the operator
is desugared to its `ite` form (`a && b ≡ ite a b false`, `a || b ≡ ite a
true b`, `a => b ≡ ite a b true`) and hoisted through the `ite` lowering, so
e.g. the recursive call in `even(n) = n == 0 || odd(n-1)` executes only when
`n == 0` fails. Operators whose non-first operands are call-free keep their
plain expression form.

Instruction `Code` is traversed structurally (`hoistCode`): nested
`statements` are straight-line in translator output — the Core→GOTO
translation expresses all control flow at the instruction level and never
nests `Code.controlFlow` inside an instruction — so hoisting a nested
statement's calls before the host instruction preserves conditionality.

Notes:
- Applications of names outside `defined` (built-in string/regex operators
  the CBMC patches interpret at the solver level, or bodiless functions)
  are left as uninterpreted `function_application` nodes.
- `hoistProgram` hoists every application of a name in `defined`, recursive
  or not; which recursive functions are in `defined` is decided by
  `emitProc` (`hoistRecursive`).
- `Expr.namedFields` carry specification annotations (`#spec_requires`,
  `#spec_loop_invariant`, ...). Those are assertion-time expressions, not
  program-order code, so applications inside them are *not* hoisted.
- Quantifier (`forall`/`exists`) bodies are not hoisted either: a hoisted
  call would be evaluated before the quantifier binds its variable, turning
  the bound variable into a free one.
- Applications left in place for either reason (`residualFnApps`), and those
  in procedure contracts, still need their callee to be a
  `mathematical_function` symbol, which a function with a GOTO body cannot
  also be. `emitProc` therefore keeps any function with such an application
  out of `defined`, so all of its applications stay uninterpreted.
- Instruction location numbers are reassigned after insertion, and GOTO
  targets are patched: targets of *original* instructions (which reference
  original location numbers) are mapped to the first instruction hoisted
  for their target, so a jump executes the calls its target depends on;
  targets of *inserted* instructions (the `ite` lowering) are buffer-local
  indices resolved against the insertion position.
-/

namespace CProverGOTO

open Std (ToFormat Format format)

public section

/-- State threaded through hoisting: a fresh-temporary counter, the
    instructions pending insertion before the current host instruction, and
    the accumulated temporaries (base name and type).

    `pending` instructions are freshly synthesized; a `GOTO` among them
    carries a *pending-local* target — an index into the buffer it was
    created in (an index equal to the buffer's final size denotes the first
    instruction after the buffer). `hoistProgram` resolves these against the
    buffer's insertion position. -/
structure HoistState where
  counter : Nat := 0
  pending : Array Instruction := #[]
  newLocals : List (String × Ty) := []
  /-- Applications already hoisted in the current straight-line region, mapped
      to their temporaries, so a structurally identical application (after its
      operands have been rewritten) reuses the temporary instead of issuing a
      second call. Sound because Core functions are pure, so equal applications
      denote equal values. Scoped exactly like `pending`: reset per host
      instruction and per `ite` branch, since a temporary bound inside one
      branch is not available in the other or after the join. -/
  memo : List (Expr × Expr) := []

/-- Shift the pending-local GOTO targets of a hoisted-instruction buffer by
    `k`, for splicing it into an enclosing buffer at offset `k`. -/
private def shiftTargets (buf : Array Instruction) (k : Nat) : Array Instruction :=
  buf.map fun inst =>
    match inst.target with
    | some t => { inst with target := some (t + k) }
    | none => inst

/-- Allocate a fresh temporary of type `ty`, registering it as a local. -/
private def freshTemp (pname : String) (ty : Ty) (st : HoistState) :
    Expr × HoistState :=
  let baseName := s!"$fcall{st.counter}"
  let fullName := mkLocalSymbol pname baseName
  (Expr.symbol fullName ty,
   { st with counter := st.counter + 1,
             newLocals := st.newLocals ++ [(baseName, ty)] })

/-- Is `e` a quantifier (`forall`/`exists`) node? Its body may mention the
    bound variable, so no application inside it can be hoisted. -/
def isQuantifier (e : Expr) : Bool :=
  match e.id with
  | .binary .Forall | .binary .Exists => true
  | _ => false

/-- Does the expression contain a hoistable application of a defined function
    in its operand tree? Quantifier bodies and `namedFields` (spec annotations)
    are not traversed, matching `hoistExpr`. Decides whether a conditional
    context must be lowered to guarded instructions before hoisting. -/
partial def exprHasHoistableCall (defined : Std.HashSet String) (e : Expr) : Bool :=
  if isQuantifier e then false else
  (match e.id with
   | .functionApplication name => defined.contains name
   | _ => false)
  || e.operands.any (exprHasHoistableCall defined)

/-- Names of the function applications in `e` that `hoistExpr` leaves in
    place whatever `defined` is: those under a quantifier and those inside
    `namedFields` (spec annotations). `inResidual` is set once the traversal is
    inside such a context. -/
partial def residualFnAppsExpr (e : Expr) (inResidual : Bool := false) : List String :=
  let here := match e.id with
    | .functionApplication n => if inResidual then [n] else []
    | _ => []
  let inner := inResidual || isQuantifier e
  here ++ e.operands.flatMap (residualFnAppsExpr · inner)
    ++ e.namedFields.flatMap fun (_, v) => residualFnAppsExpr v true

/-- `residualFnAppsExpr` lifted to code statements. -/
partial def residualFnAppsCode (c : Code) : List String :=
  c.operands.flatMap (residualFnAppsExpr ·) ++ c.statements.flatMap residualFnAppsCode

/-- Names of the function applications of a program that hoisting leaves in
    place (see `residualFnAppsExpr`). -/
def residualFnApps (program : Program) : List String :=
  program.instructions.toList.flatMap fun inst =>
    residualFnAppsExpr inst.guard ++ residualFnAppsCode inst.code

/-- Callee names of the `function_application` nodes in serialized GOTO JSON
    (as produced by `exprToJson`): each callee is a `symbol` whose type is a
    `mathematical_function`. Used for procedure contracts, which a context
    stores only in serialized form. -/
partial def jsonFnAppNames (j : Lean.Json) : List String :=
  let here := match j.getObjValD "id", (j.getObjValD "namedSub").getObjValD "type" with
    | .str "symbol", ty =>
      match ty.getObjValD "id", (j.getObjValD "namedSub").getObjValD "identifier" with
      | .str "mathematical_function", ident =>
        match ident.getObjValD "id" with
        | .str n => [n]
        | _ => []
      | _, _ => []
    | _, _ => []
  let children := match j with
    | .obj kvs => kvs.toList.flatMap fun (_, v) => jsonFnAppNames v
    | .arr xs => xs.toList.flatMap jsonFnAppNames
    | _ => []
  here ++ children

private def falseExpr : Expr :=
  { id := .nullary (.constant "false"), type := Ty.Boolean }

/-- Build an `ite` expression node (used to desugar short-circuit operators so
    their guarded evaluation goes through the `ite` lowering). `orig` is the
    operator node being desugared; its `sourceLoc` and `namedFields` carry over
    so counterexamples on the desugared subexpression keep their location. -/
private def mkIte (c t e : Expr) (ty : Ty) (orig : Expr) : Expr :=
  { id := .ternary .ite, type := ty, operands := [c, t, e],
    sourceLoc := orig.sourceLoc, namedFields := orig.namedFields }

/-- Hoist defined-function applications out of an expression, bottom-up.
    Returns the rewritten expression; hoisted instructions accumulate in the
    state's `pending` buffer. `namedFields` (spec annotations) are
    deliberately not traversed. -/
partial def hoistExpr (defined : Std.HashSet String) (pname : String)
    (srcLoc : SourceLocation) (e : Expr) (st : HoistState) :
    Expr × HoistState :=
  match e.id, e.operands with
  | .ternary .ite, [c, t, els] =>
    let (c', st) := hoistExpr defined pname srcLoc c st
    -- Hoist each branch into its own buffer so branch calls can be guarded.
    let saved := st.pending
    let savedMemo := st.memo
    let (t', st) := hoistExpr defined pname srcLoc t { st with pending := #[] }
    let tPend := st.pending
    let (els', st) := hoistExpr defined pname srcLoc els { st with pending := #[], memo := savedMemo }
    let elsPend := st.pending
    let st := { st with pending := saved, memo := savedMemo }
    if tPend.isEmpty && elsPend.isEmpty then
      ({ e with operands := [c', t', els'] }, st)
    else Id.run do
      -- Lower the ite to guarded branches assigning a temporary.
      let (tmp, st) := freshTemp pname e.type st
      let mut pending := st.pending
      pending := pending.push
        { type := .DECL, code := .decl tmp, sourceLoc := srcLoc }
      let gotoElseIdx := pending.size
      pending := pending.push
        { type := .GOTO, guard := Expr.not c', sourceLoc := srcLoc }
      pending := pending ++ shiftTargets tPend pending.size
      pending := pending.push
        { type := .ASSIGN, code := .assign tmp t', sourceLoc := srcLoc }
      let gotoEndIdx := pending.size
      pending := pending.push
        { type := .GOTO, sourceLoc := srcLoc }
      let elseStart := pending.size
      pending := pending ++ shiftTargets elsPend pending.size
      pending := pending.push
        { type := .ASSIGN, code := .assign tmp els', sourceLoc := srcLoc }
      let endIdx := pending.size
      pending := pending.set! gotoElseIdx
        { pending[gotoElseIdx]! with target := some elseStart }
      pending := pending.set! gotoEndIdx
        { pending[gotoEndIdx]! with target := some endIdx }
      return (tmp, { st with pending := pending })
  -- Short-circuit operators: desugared to `ite` (see the module doc).
  | .multiary .And, ops =>
    if ops.length ≥ 2 && (ops.drop 1).any (exprHasHoistableCall defined) then
      let desugared := match ops with
        | [] => Expr.true
        | [x] => x
        | x :: rest => rest.foldr (init := none) (fun op acc =>
            match acc with
            | none => some op
            | some a => some (mkIte op a falseExpr Ty.Boolean e))
          |>.map (fun rest' => mkIte x rest' falseExpr Ty.Boolean e) |>.getD x
      hoistExpr defined pname srcLoc desugared st
    else
      hoistDefault e st
  | .multiary .Or, ops =>
    if ops.length ≥ 2 && (ops.drop 1).any (exprHasHoistableCall defined) then
      let desugared := match ops with
        | [] => falseExpr
        | [x] => x
        | x :: rest => rest.foldr (init := none) (fun op acc =>
            match acc with
            | none => some op
            | some a => some (mkIte op Expr.true a Ty.Boolean e))
          |>.map (fun rest' => mkIte x Expr.true rest' Ty.Boolean e) |>.getD x
      hoistExpr defined pname srcLoc desugared st
    else
      hoistDefault e st
  | .binary .Implies, [a, b] =>
    if exprHasHoistableCall defined b then
      hoistExpr defined pname srcLoc (mkIte a b Expr.true Ty.Boolean e) st
    else
      hoistDefault e st
  -- Quantifiers: left untouched (see the module doc).
  | .binary .Forall, _ | .binary .Exists, _ => (e, st)
  | _, _ => hoistDefault e st
where
  hoistDefault (e : Expr) (st : HoistState) : Expr × HoistState :=
    let (ops, st) := e.operands.foldl (init := ([], st)) fun (acc, st) op =>
      let (op', st) := hoistExpr defined pname srcLoc op st
      (acc ++ [op'], st)
    let e := { e with operands := ops }
    match e.id with
    | .functionApplication name =>
      if defined.contains name then
        match st.memo.find? (fun (app, _) => app == e) with
        | some (_, tmp) => (tmp, st)
        | none =>
          let (tmp, st) := freshTemp pname e.type st
          let calleeSym := Expr.symbol name (Ty.mkCode (ops.map (·.type)) e.type)
          let declInst : Instruction :=
            { type := .DECL, code := .decl tmp, sourceLoc := srcLoc }
          let callInst : Instruction :=
            { type := .FUNCTION_CALL, code := .functionCall tmp calleeSym ops,
              sourceLoc := srcLoc }
          (tmp, { st with pending := (st.pending.push declInst).push callInst,
                          memo := (e, tmp) :: st.memo })
      else (e, st)
    | _ => (e, st)

/-- Hoist defined-function applications out of a code statement (operands and
    nested statements). -/
partial def hoistCode (defined : Std.HashSet String) (pname : String)
    (srcLoc : SourceLocation) (c : Code) (st : HoistState) :
    Code × HoistState :=
  let (ops, st) := c.operands.foldl (init := ([], st)) fun (acc, st) op =>
    let (op', st) := hoistExpr defined pname srcLoc op st
    (acc ++ [op'], st)
  let (stmts, st) := c.statements.foldl (init := ([], st)) fun (acc, st) s =>
    let (s', st) := hoistCode defined pname srcLoc s st
    (acc ++ [s'], st)
  ({ c with operands := ops, statements := stmts }, st)

/-- Hoist defined-function applications out of every instruction of a GOTO
    program: rewrite each instruction's guard and code, insert the pending
    instructions before it, renumber locations, and patch GOTO targets —
    original instructions through the old→new location map, inserted
    instructions by resolving their pending-local targets against the
    insertion position. Returns the new program and the introduced
    temporaries (base name and type). -/
def hoistProgram (defined : Std.HashSet String) (pname : String)
    (program : Program) : Program × List (String × Ty) := Id.run do
  -- Pass 1: rewrite instructions, collecting per-host pending buffers.
  let mut st : HoistState := {}
  let mut rewritten : Array (Array Instruction × Instruction) := #[]
  for inst in program.instructions do
    st := { st with pending := #[], memo := [] }
    let (guard', st') := hoistExpr defined pname inst.sourceLoc inst.guard st
    let (code', st'') := hoistCode defined pname inst.sourceLoc inst.code st'
    st := st''
    rewritten := rewritten.push (st.pending, { inst with guard := guard', code := code' })
  -- Pass 2: renumber locations and resolve pending-local GOTO targets.
  let mut locMap : Std.HashMap Nat Nat := {}
  let mut newInsts : Array Instruction := #[]
  let mut hostIdxs : Array Nat := #[]
  for (pending, host) in rewritten do
    let base := newInsts.size
    locMap := locMap.insert host.locationNum base
    for p in pending do
      let p := match p.target with
        | some t => { p with target := some (base + t) }
        | none => p
      newInsts := newInsts.push { p with locationNum := newInsts.size }
    hostIdxs := hostIdxs.push newInsts.size
    newInsts := newInsts.push { host with locationNum := newInsts.size }
  -- Pass 3: patch original instructions' targets through the location map.
  for i in hostIdxs do
    let inst := newInsts[i]!
    match inst.target with
    | some t => newInsts := newInsts.set! i { inst with target := some (locMap.getD t t) }
    | none => pure ()
  return ({ program with instructions := newInsts }, st.newLocals)

end -- public section

end CProverGOTO

namespace CoreToGOTO

public section

/-- Hoist defined-function applications in a GOTO context (see
    `CProverGOTO.hoistProgram`), registering the introduced temporaries as
    locals so they receive symbol-table entries. `pname` must be the program
    name later passed to `Context.toJson`, so the temporaries' full names
    (`pname::1::$fcall<n>`) match their symbol-table entries. -/
def CProverGOTO.Context.hoistFnApps (defined : Std.HashSet String)
    (pname : String) (ctx : CProverGOTO.Context) : CProverGOTO.Context :=
  let (pgm, temps) := _root_.CProverGOTO.hoistProgram defined pname ctx.program
  { ctx with
    program := pgm
    locals := ctx.locals ++ temps.map (·.1)
    localTypes := temps.foldl (init := ctx.localTypes) fun m (k, v) => m.insert k v }

end -- public section

end CoreToGOTO
