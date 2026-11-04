/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelPass
public import StrataLaurel.Implementation.CoreWithLaurelTypes
import StrataLaurel.Implementation.TransparencyPass
import StrataLaurel.Implementation.LaurelTypes
import StrataLaurel.Implementation.EliminateReturnStatements
import Strata.Util.Tactics

/-!
# Functional Rewrite Pass

Rewrites a function body from imperative form into a single pure expression.

A function body reaching this pass has already had its returns lowered by
`EliminateReturnStatements`, so it is a `$return`-labelled block in which every
`return e` has become `output := e; exit $return`. This pass eliminates the
label mechanism by continuation passing: each statement is translated into an
expression that *contains* the translation of the statements following it.

Writing `F(stmts, k)` for the translation of `stmts` whose value is `k` when
control falls off the end:

    F([], k)                          = k
    F(exit $return :: rest, k)        = <output variable>
    F(exit L :: rest, k)              = <continuation bound to L>
    F((x := e) :: rest, k)            = { var x : T := e; F(rest, k) }
    F((var x : T;) :: rest, k)        = { var x : T := <hoisted hole>; F(rest, k) }
    F(if c then A else B :: rest, k)  = if c then F(A, kr) else F(B, kr)
                                        where kr = F(rest, k)
    F({ A } L :: rest, k)             = F(A, kr) with L bound to kr
                                        where kr = F(rest, k)
    F([e], k)                         = k     for a pure expression e

## Uninitialized variables become holes

Every variable a body does not initialize — a local declared without an initializer,
*and the output parameter* — starts out holding an arbitrary value. A function cannot
yield an *arbitrary* value, but it can yield an arbitrary-but-*fixed* one, so each such
variable is bound at the top of the body to a deterministic hole: a call to an
uninterpreted function generated for it (`declHoleProcs`, bound by `holePrelude`). So

    var x : int; if b then { x := 1 }; return x

evaluates to 1 when `b` holds and to the hole otherwise, and

    procedure f(c : bool) returns (r : int) { if c then { return 1 } }

becomes `if c then 1 else <hole>` once the bindings are inlined. Both are the
imperative reading of reading a variable that was never assigned, and both agree with
the procedure twin, which havocs an unassigned output.

Binding the output outermost is what makes an *assignment* to it still win: `r := e`
becomes a declaration shadowing the hole, so only a path that never assigns reads it.
The fall-through value cannot instead be made the hole directly, because falling off
the end *after* an assignment must still yield the assigned value — `r := 7` with no
explicit return evaluates to 7.

Binding *every* bare declaration, rather than eliding it and analysing whether some
later assignment supplies the binding, is what makes this sound. An elided declaration
leaves a free reference to the local on any path that never assigns it, and when the
name shadows an input parameter of the same name that reference resolves to the
**input**: the body would verify while silently returning the parameter. Binding the
declaration removes that possibility instead of analysing for it, which is why there
is no "does every path assign this" check here at all.

The hole takes the enclosing function's inputs as arguments rather than being a
nullary constant. A constant would additionally assert that the uninitialized local
holds the same value for every input, which lets a caller prove more than
"arbitrary" — that `f(1) == f(2)`, for instance.

For the same reason the call is *hoisted* to the outermost scope of the body and bound
to `$declHoleVal_<uniqueId>`, which the declaration refers to (`holePrelude`). Left
where the declaration sits, a body that shadows an input with a local of the same name
would capture the hole's argument, defeating the parameterization exactly as a nullary
constant would.

In a polymorphic body the holes carry the function's type parameters (`declHoleProcs`),
so a local or output of type `T` left uninitialized is holed like any other.

Because the hole is emitted as a call to an uninterpreted function rather than as a
`.Hole` node, it needs no later elimination: this pass runs long after
`eliminateDeterministicHolesPass`, so a `.Hole` introduced here would survive to the
Core translation. This is that pass's output form, produced directly.

An `exit $return` discards `rest`: the statements after it are unreachable, and
the value of the function is the output variable, whose innermost binding holds
what the preceding assignment just stored. This is what makes an early exit
expressible: it becomes the branch of an if-expression.

An `exit L` to a user label works the same way, with a per-label continuation
instead of the output. A labelled block `{ A } L` binds `L` to `F(rest, k)` — the
translation of whatever follows the block — while translating `A`, so an exit
inside `A` evaluates to what comes after the block, which is exactly what the
imperative exit does. Falling off the end of `A` reaches the same expression,
because leaving the block normally and exiting it are the same control flow.
Labels nest, so an inner block's exit can name an outer label. Note that
`bodyStatements` must not peel a user-labelled block off the body: doing so would
discard the label before it can be bound (only `$return`-labelled and unlabelled
wrappers are peeled).

An assignment becomes a *declaration*, which is why the statements that follow
it move into a nested block: a destructive update re-declares a name that is
already bound, and shadowing is only legal in a nested scope. Whether a target is
an input parameter is decided by `uniqueId`, not by name, so a local that shadows
an input is updated as an ordinary local rather than rejected. So

    var x : int := a; x := x + 1; return x

becomes

    { var x : int := a; { var x : int := x + 1; { var r : int := x; r } } }

`InlineLocalVariables` then inlines every declaration away, leaving `a + 1`, so
no local variable reaches the Core schema translation. Nothing else needs to
change for the destructive case: because the inner declaration's initializer is
resolved in the enclosing scope, `x + 1` still reads the *previous* binding.

The continuation rule handles if-lifting: for
`if c then { x := e1 } else { x := e2 }; rest`, both branches translate to
`{ var x := e_i; F(rest, k) }`, and inlining collapses them. No dedicated
if-lifting step is needed, and no restriction to one assigned variable per
branch.

## Known cost: the continuation is duplicated

`F` substitutes `kr` into *both* branches of an if, so the continuation is copied
once per path that reaches it. The growth depends on how many branches actually
fall through:

- A **guard** (`if c then { return e }; rest`) exits in its `then` branch, so only
  the `else` branch carries `kr` and there is exactly one copy per guard. Chained
  guards are therefore **linear**, not exponential — measured at 201, 375, and 843
  characters of rewritten body for 2, 4, and 8 chained guards, and 16 chained
  guards compile end-to-end in about a second.
- An if where **both** branches fall through duplicates `kr`, giving 2^n. This is
  the shape that hurts: measured at 681, 4033, and 21745 characters for n = 2, 4,
  and 6, and end-to-end compile time of roughly 6s at n = 10 versus 147s at
  n = 13.
- An if inside an assigned **block value** counts as one at statement level, since the
  block is flattened into the enclosing statements.

So the exponential case needs about a dozen consecutive both-branch-falling-through
ifs in a single transparent body before it becomes noticeable. That is accepted for
now rather than capped: Core's `Term` has no `let`, and its partial evaluator
beta-reduces an applied lambda before SMT encoding, so there is currently no way to
bind `kr` once. Binding it once is the fix, and is separate work — a size cap would
only convert a slow compile into a rejected program, without making any additional
body expressible.

## Only assignments in statement position become bindings

The rule `F((x := e) :: rest, k) = { var x : T := e; F(rest, k) }` needs a
`rest` for the new binding to scope over, so it applies exactly to an assignment
in *statement* position. An assignment nested inside an expression — the `x := 2`
of `requires (x := 2) == 2`, or of `return (x := x + 1) + 0` — has no such
continuation: it is a side effect in the middle of a value, and there is nothing
to bind it around. Those are left untouched and stay rejected.

## Blocks that write are hoisted out of expressions first

A call to a procedure that writes a global or the heap reaches this pass as a block
value, because that is how `GlobalParameterization` lowers such a call in a value
position:

    r := { var $out := setG(g, v); g := $outputs_setG..g($out); …; <result> } + 1

The assignment to `g` inside it was not written by the user, and it is in statement
position *within the block*. Before translating, `hoistStmts` moves the statements of
every block that writes a local out of the expression and ahead of the statement that
evaluates it, replacing the block by its last element:

    var $out := setG(g, v); g := $outputs_setG..g($out); …; r := <result> + 1

so the write becomes an ordinary statement whose binding scopes over the rest of the
body. This applies wherever an expression is evaluated: an assigned value, a returned
value, an if-condition, an expression statement, and a block that is itself the whole
value.

Operands are evaluated left to right, so an operand to the left of such a block must
read what it read before the block's statements ran. Each variable an earlier operand
reads that a later operand's hoisted statements assign is bound to a snapshot first:
`g + setG(5)` reads `g` into `$snapshot$0` before the call, while `setG(5) + g` reads
the written `g`.

A block in a branch of an if-expression is evaluated only on that branch, so it is not
hoisted unconditionally: the enclosing statement becomes a statement-level `if` with a
copy of the statement in each branch, and each copy hoists its own branch's block. The
short-circuit operators are treated as the if-expressions they mean, the right operand
being the conditional one. A block under a quantifier, an `old`, or an assignment
nested in an expression is left in place and stays rejected.

This is also why a contract is unaffected. Preconditions and postconditions are
`Condition` expressions, not body statements, so they are outside this pass
entirely (`rewriteFunctionBody` matches only on `proc.body`) and a destructive
assignment in one is reported by the Core schema translation.

## Rejecting what has no functional form

A body containing a construct with no functional form — a loop, an assignment to
an inout parameter, an assignment to several targets —
cannot become an expression, and this pass reports it as a `userError`. Since the
translation is a single recursive function, a construct cannot be admitted by a
guard that the rewrite then silently mishandles: acceptance *is* transformability.

Reporting here rather than leaving the body for the Core schema translation to
reject also keeps the diagnostic precise. The untransformed body is still in
`exit $return` form, which the schema pass would report a second time (as a
"destructive assignment", pointing at the lowered `return`) after the real
message.

A construct that an *earlier pass* is responsible for eliminating is a different
matter, and is reported as a `strataBug` rather than a user error: an assert or
assume (stripped from the function copy by the transparency pass), a call
(rewritten to functional form by the same pass), or a field assignment
(eliminated by heap parameterization). Reaching one of these means the pipeline
is misordered, not that the user wrote something unsupported, so the message
names the pass responsible. Because any non-warning diagnostic from an
unordered-core pass discards the Core program, these abort the pipeline.
-/

namespace Strata.Laurel

public section

/-- The statements of a function body, with the wrapper blocks
    `EliminateReturnStatements` and the transparency pass put around it removed.

    A single-statement block is a wrapper: unwrapping it reaches the
    `$return`-labelled block whose statements are the body proper. Peeling stops
    at the first block with more than one statement.

    A block labelled with anything *other* than `$return` is not a wrapper — it is
    a user's labelled block, and an `exit` inside it needs that label to still be
    in scope. Peeling it would discard the label, so such a block is returned
    intact and translated by the `.Block` rule like any other statement.

    Matching on `body` rather than on `body.val` is deliberate: it makes `single` a
    structural subterm of the argument, so Lean proves termination on its own and
    this needs no `partial` or `termination_by`. -/
private def bodyStatements (body : StmtExprMd) : List StmtExprMd :=
  match body with
  | ⟨.Block [single] label _ _, _⟩ =>
    if label.all (· == returnLabel) then bodyStatements single else [body]
  | ⟨.Block stmts label _ _, _⟩ =>
    if label.all (· == returnLabel) then stmts else [body]
  | _ => [body]

/-- `bodyStatements` never returns something larger than its input: each arm either
    returns a list from inside `body`, or `[body]` itself.

    Needed to prove termination of `functionalizeStmts`, which recurses into
    `bodyStatements` of an if's branches. -/
private theorem bodyStatements_sizeOf_le (body : StmtExprMd) :
    sizeOf (bodyStatements body) ≤ sizeOf body + 2 := by
  fun_induction bodyStatements body <;> simp +arith <;> omega

/-- `sizeOf` of an append is the sum, less the one `nil` counted twice.

    Stated for any element type: the proof uses nothing about `StmtExprMd`. -/
private theorem sizeOf_append {α : Type} [SizeOf α] (xs ys : List α) :
    sizeOf (xs ++ ys) + 1 = sizeOf xs + sizeOf ys := by
  induction xs with
  | nil => simp; omega
  | cons a as ih => simp only [List.cons_append, List.cons.sizeOf_spec]; omega

/-- The name of the uninterpreted function standing for the initial value of the
    bare declaration whose `uniqueId` is `uid`, and the name of the local the rewrite
    binds its result to.

    Deriving both from `uniqueId` is what lets this pass mint hole names without
    threading a counter through `functionalizeStmts`, keeping that function pure and its
    termination proof unchanged.

    The hole *procedure* name is additionally qualified by the owning procedure, because
    it is GLOBAL and a `uniqueId` is not in fact unique program-wide: a pass that copies
    a procedure with `{ proc with … }` carries its parameter ids into the copy.
    `LiftInstanceProcedures` does exactly that, emitting a virtual method as both
    `T$m$impl` and a `T$m` dispatcher, so the two share their output parameter's id — and
    the output gets a hole just as a bare local does. Named by `uniqueId` alone, two
    transparent copies mint the same name and resolution reports a duplicate definition.
    The procedure name separates them, and is itself unique here because
    `UniqueOverloadNames` runs earlier. `declHoleValName` needs no such qualification:
    it names a local, bound inside one body.

    The prefixes are deliberately *not* `EliminateDeterministicHoles`' `$hole_`: that
    pass numbers its holes from a counter, so sharing a prefix could produce the same
    name twice and resolution would report a duplicate definition. Both start with `$`,
    which a user cannot write, so neither can be shadowed by a program's own name. -/
private def declHoleName (procName : Identifier) (uid : Nat) : Identifier :=
  s!"$declHole_{procName.text}_{uid}"

private def declHoleValName (uid : Nat) : Identifier := s!"$declHoleVal_{uid}"

/-- A value the rewrite must start out holding an arbitrary-but-fixed value: the
    `uniqueId` the hole is named after, the local name the prelude binds its result to,
    and the declared type.

    Bare local declarations bind `$declHoleVal_<uid>`, which the rewritten declaration
    then refers to. The *output* parameter instead binds its own name, so that an
    assignment to it — which the rewrite turns into a shadowing declaration — shadows
    the hole and the fall-through read sees the assigned value. -/
private abbrev HoleBinding := Nat × Identifier × HighTypeMd

/-- Whether `e` contains an `exit` or a `return` anywhere inside it.

    Used to reject a block *value* that contains control flow, as in
    `r := { if c then { exit L }; 5 }`, rather than translate it. `hoistExpr` moves a
    block value's statements ahead of the statement that evaluates it and drops the
    block's own label, so an `exit` naming that label would lose its target. -/
private def containsExitOrReturn (e : StmtExprMd) : Bool :=
  let check (n : StmtExprMd) : StateM Bool StmtExprMd := do
    match n.val with
    | .Goto _ _ | .Return _ => set true; pure n
    | _ => pure n
  ((mapStmtExprM check e).run false).2

/-- The message for a block value the rewrite will not translate. -/
private def blockValueExitMsg : String :=
  "an `exit` or `return` inside an assigned block value is not YET supported in transparent bodies or contracts"

private def declaredLocalUids (body : StmtExprMd) : List Nat :=
  let collect (e : StmtExprMd) : StateM (List Nat) StmtExprMd := do
    match e.val with
    | .Var (.Declare p) | .Assign [⟨.Declare p, _⟩] _ =>
      match p.name.uniqueId with
      | none => pure e
      | some uid => modify (uid :: ·); pure e
    | _ => pure e
  ((mapStmtExprM collect body).run []).2

private def renamedLocal (declared : List Nat) (id : Identifier) : Identifier :=
  match id.uniqueId with
  | some uid => if declared.contains uid then { id with text := s!"$v_{uid}" } else id
  | none => id

/-- Alpha-convert every local *declared in* `body` to a name unique to that declaration.

    This is what makes the rewrite capture-safe. Translating a statement list extends each
    declaration's scope over the translation of the statements that follow, and an if's
    continuation is substituted into both branches — so a declaration inside a branch or
    block ends up enclosing a continuation written against an *outer* variable of the same
    name. Left alone, `var x := 0; if c then { var x := 1 }; return x` returns the
    branch-local 1 instead of 0.

    Renaming, rather than binding the continuation outside the branch, is what keeps state
    flow intact. Substitution is how this rewrite propagates values: `x := e` becomes a
    shadowing declaration of the *same* name precisely so the continuation underneath it
    reads the new value. Binding the continuation once outside would evaluate it before the
    branch ran, and an assignment inside a branch would stop being visible after it.

    Declarations and updates can be told apart because resolution already did it: two
    source declarations of `x` have different `uniqueId`s, while an update carries the
    `uniqueId` of the declaration it targets. Renaming *by* `uniqueId` therefore makes
    distinct declarations textually distinct — so neither can shadow the other — while an
    update still names its own declaration and continues to flow.

    Input and output parameters are not declared in the body, so their ids are not in this
    set and they keep their names: hole arguments naming inputs, and the output the
    fall-through reads, are unaffected.

    This is also what makes `stripLocalUids` sound. It erases ids and lets the re-resolve
    bind by name, which is only correct when names are unambiguous — which is exactly what
    this establishes. -/
private def alphaConvertLocals (body : StmtExprMd) : StmtExprMd :=
  let declared := declaredLocalUids body
  let renamed := renamedLocal declared
  mapStmtExpr (fun n =>
    match n.val with
    | .Var (.Local id) => ⟨.Var (.Local (renamed id)), n.source⟩
    | .Var (.Declare p) =>
      ⟨.Var (.Declare { p with name := renamed p.name }), n.source⟩
    | .Assign [⟨.Declare p, ts⟩] v =>
      ⟨.Assign [⟨.Declare { p with name := renamed p.name }, ts⟩] v, n.source⟩
    | .Assign [⟨.Local id, ts⟩] v =>
      ⟨.Assign [⟨.Local (renamed id), ts⟩] v, n.source⟩
    | _ => n) body

/-- The bare declarations of `body`: each initializer-less `var`, as a `HoleBinding`.

    A declaration with no `uniqueId` is skipped, matching `functionalizeStmts`: it has
    no stable name to generate, and resolution reports the missing id as the real
    problem. -/
private def bareDecls (body : StmtExprMd) : List HoleBinding :=
  let collect (e : StmtExprMd) : StateM (List HoleBinding) StmtExprMd := do
    match e.val with
    | .Var (.Declare param) =>
      match param.name.uniqueId with
      | none => pure e
      | some uid =>
        modify (· ++ [(uid, declHoleValName uid, param.type.getD ⟨.Unknown, e.source⟩)])
        pure e
    | _ => pure e
  ((mapStmtExprM collect body).run []).2

/-- One uninterpreted `Procedure` per bare declaration, standing for the
    arbitrary-but-fixed value that declaration starts out holding.

    `inputs` mirrors the enclosing function's inputs, so a hole's value may depend on
    them. A nullary constant would instead assert that the uninitialized local takes
    the *same* value for every input, which lets a caller prove more than "arbitrary" —
    see the module docstring.

    `typeArgs` carries the enclosing function's type parameters. A hole binds only the
    ones mentioned by its mirrored inputs or its declared type. In a polymorphic function
    (`f<T>(x : T)`) the inputs mention `T`, so the hole must bind `T`, or `T` is a free
    type variable at Core and the program fails to type-check. A parameter neither
    mentions, like `Q` in a contract helper for `requires forall(x: Q) => x == x`, could
    not be inferred at the hole's call, so it is not bound.

    The body is `.Opaque [] none []`, which the Core schema translation turns into a
    function with no body, i.e. an uninterpreted one. That is the already-eliminated
    form of a deterministic hole: this pass runs long after
    `eliminateDeterministicHolesPass`, so emitting a `.Hole` here would never be
    eliminated. -/
private def declHoleProcs (procName : Identifier) (typeArgs : List Identifier)
    (inputs : List Parameter) (decls : List HoleBinding) : List Procedure :=
  let inputTVars := inputs.flatMap (tvarNames ·.type.val)
  decls.map fun (uid, _, ty) =>
    let mentioned := inputTVars ++ tvarNames ty.val
    { name := declHoleName procName uid
      typeArgs := typeArgs.filter (mentioned.contains ·.text)
      inputs := inputs
      outputs := [{ name := "$result", type := ty }]
      preconditions := []
      decreases := none
      body := .Opaque [] none [] }

/-- Wrap `body` in one `var <name> : T := $declHole_<uid>(inputs…)` binding per
    `HoleBinding`.

    The calls are hoisted to the *outermost* scope of the body rather than left where
    the declarations sit, because the arguments name the enclosing function's input
    parameters and a body may shadow an input with a local of the same name. Left in
    place, `$declHole_5(a)` inside the scope of a `var a : int := 100` re-resolves `a`
    to that local — the hole stops varying with the input, and a caller can prove
    `f(1) == f(2)`, which is exactly what parameterizing the hole is meant to prevent.
    Preserving the argument's `uniqueId` does not help: `stripLocalUids` clears it and
    the re-resolve binds by name. At the top of the body no local is in scope yet, so
    the names can only mean the parameters.

    Hoisting is also what makes the *output* binding work: it is outermost, so every
    assignment to the output — a shadowing declaration after the rewrite — shadows it,
    and only a path that never assigns reads the hole.

    Hoisting evaluates every hole even on paths that never read it, which is harmless:
    an uninterpreted function is pure and total. -/
private def holePrelude (procName : Identifier) (inputs : List Parameter)
    (decls : List HoleBinding) (body : StmtExprMd) : StmtExprMd :=
  let src := body.source
  let args : List StmtExprMd := inputs.map fun p => ⟨.Var (.Local p.name), src⟩
  decls.foldr (init := body) fun (uid, name, ty) acc =>
    let call : StmtExprMd := ⟨.StaticCall (declHoleName procName uid) args [], src⟩
    let decl : StmtExprMd :=
      ⟨.Assign [⟨.Declare ⟨name, some ty⟩, src⟩] call, src⟩
    ⟨.Block [decl, acc] none [] none, src⟩

/-- An expression whose evaluation has no effect. Laurel discards a body's trailing
    expression instead of assigning it to an output, so one of these in tail position is
    dropped. A call is included because by this point the transparency pass has rewritten
    every call in a function copy into a function application. Every other construct in
    tail position is reported exactly as it would be anywhere else, so a trailing loop or
    an effect is never silently removed. -/
private def isPureValue (s : StmtExprMd) : Bool :=
  match s.val with
  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ | .LiteralBv _ _
  | .Var (.Local _) | .Var (.Field ..) | .StaticCall .. | .ReferenceEquals .. | .AsType ..
  | .IsType .. | .Quantifier .. | .PureFieldUpdate .. | .Old .. => true
  | _ => false

/-- The reason a statement has no functional form, and how to report it.

    A construct the user can legitimately write in a transparent body is a
    `userError`: the body is not expressible as a function, and saying so is the
    point. A construct an earlier pass is supposed to have eliminated is a
    `strataBug` — reaching one here means the pipeline is misordered, not that the
    user wrote something wrong. The wording of the user-facing messages matches
    the equivalent messages in the Core schema translation, which reports the same
    constructs when they appear in a contract. -/
private def unsupportedStmt (s : StmtExprMd) : String × MessageKind :=
  match s.val with
  | .While .. =>
    ("loops are not YET supported in transparent bodies or contracts", .userError)
  | .Var (.Declare _) =>
    -- Handled in `functionalizeStmts`; a bare declaration binds nothing, so it is
    -- skipped rather than reported.
    ("local variables must have initializers in transparent bodies or contracts", .userError)
  -- Unreachable: `PackageFunctionOutputs` rewrites a multi-output call into one call
  -- plus a projection per target before this pass runs. Kept for totality.
  | .Assign targets _ =>
    if targets.any (fun t => match t.val with | .Field .. => true | _ => false) then
      ("field assignment should have been eliminated by heap parameterization", .strataBug)
    else
      ("assignments to multiple targets are not YET supported in transparent bodies or contracts",
       .userError)
  -- The transparency pass strips asserts and assumes from a function copy
  -- and rewrites calls into functional form (`functionalize`), so none of these
  -- can be reached from a
  -- well-ordered pipeline.
  | .Assert .. =>
    ("assert should have been stripped from the function copy by the transparency pass",
     .strataBug)
  | .Assume _ =>
    ("assume should have been stripped from the function copy by the transparency pass",
     .strataBug)
  | .StaticCall .. | .InstanceCall .. =>
    ("call should have been rewritten to functional form by the transparency pass", .strataBug)
  | _ =>
    (s!"{s.val.constructorName} should have been eliminated before the functional rewrite",
     .strataBug)

/-- Strip the `uniqueId` from every local declaration and local reference in `e`.

    An assignment becomes a shadowing declaration, which would otherwise reuse the
    assignment target's id and give two declarations the same id. Only `Resolution`
    mints ids, so instead of trying to invent them here, drop them and let the
    re-resolve (`needsResolves := true`) re-derive them from the scope nesting this
    rewrite just built. Resolution binds a declaration's initializer in the
    *enclosing* scope, so `x := x + 1` still reads the previous binding. -/
private def stripLocalUids (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun n =>
    match n.val with
    | .Var (.Local id) => ⟨.Var (.Local { id with uniqueId := none }), n.source⟩
    | .Var (.Declare p) =>
      ⟨.Var (.Declare { p with name := { p.name with uniqueId := none } }), n.source⟩
    | .Assign [⟨.Declare p, ts⟩] v =>
      ⟨.Assign [⟨.Declare { p with name := { p.name with uniqueId := none } }, ts⟩] v, n.source⟩
    | _ => n) e

/-- The locals `s` assigns anywhere inside it, as the identifiers of the assignment
    targets. A declaration is not an assignment: it introduces a name nothing outside can
    have read yet. -/
private def assignedLocals (s : StmtExprMd) : List Identifier :=
  let collect (n : StmtExprMd) : StateM (List Identifier) StmtExprMd := do
    match n.val with
    | .Assign targets _ =>
      for t in targets do
        match t.val with
        | .Local id => modify (id :: ·)
        | _ => pure ()
      pure n
    | _ => pure n
  ((mapStmtExprM collect s).run []).2

/-- Whether two references name the same variable: by `uniqueId` when both carry one,
    so that a quantifier-bound name never matches an outer variable of the same text. -/
private def sameVar (a b : Identifier) : Bool :=
  match a.uniqueId, b.uniqueId with
  | some x, some y => x == y
  | _, _ => a.text == b.text

/-- Whether `e` contains a block that assigns a local. This is the shape
    `GlobalParameterization` gives a call to a global or heap writer in a value position,
    `{ …; g := <new value>; …; <result> }`, and the shape `hoistExpr` moves out of an
    expression. A block that only declares is left where it is. -/
private def containsBlockWrite (e : StmtExprMd) : Bool :=
  let check (n : StmtExprMd) : StateM Bool StmtExprMd := do
    match n.val with
    | .Block .. => if !(assignedLocals n).isEmpty then set true
    | _ => pure ()
    pure n
  ((mapStmtExprM check e).run false).2

/-- An expression with the statements hoisted out of it: `pre` runs first, then the
    expression evaluates to `value`. A `branch` is an if-expression whose branches had
    statements hoisted out of them, so it cannot become a single prefix: the enclosing
    statement is emitted in each branch of a statement-level `if` (`toStmts`). -/
private inductive Hoisted (α : Type) where
  | done (pre : List StmtExprMd) (value : α)
  | branch (pre : List StmtExprMd) (cond : StmtExprMd) (source : FileRange)
      (thenH elseH : Hoisted α)

private def Hoisted.prepend {α : Type} (stmts : List StmtExprMd) : Hoisted α → Hoisted α
  | .done pre v => .done (stmts ++ pre) v
  | .branch pre c src t e => .branch (stmts ++ pre) c src t e

private def Hoisted.map {α β : Type} (f : α → β) : Hoisted α → Hoisted β
  | .done pre v => .done pre (f v)
  | .branch pre c src t e => .branch pre c src (t.map f) (e.map f)

private def Hoisted.bindM {m : Type → Type} [Monad m] {α β : Type}
    (h : Hoisted α) (f : α → m (Hoisted β)) : m (Hoisted β) :=
  match h with
  | .done pre v => return (← f v).prepend pre
  | .branch pre c src t e => return .branch pre c src (← t.bindM f) (← e.bindM f)

/-- The locals any statement of `h` assigns, on any path. -/
private def Hoisted.writes {α : Type} : Hoisted α → List Identifier
  | .done pre _ => pre.flatMap assignedLocals
  | .branch pre _ _ t e => pre.flatMap assignedLocals ++ t.writes ++ e.writes

/-- The statements that run `h` and then the statement `mk` builds from its value. -/
private def Hoisted.toStmts {α : Type} (mk : α → StmtExprMd) : Hoisted α → List StmtExprMd
  | .done pre v => pre ++ [mk v]
  | .branch pre c src t e =>
    pre ++ [⟨.IfThenElse c ⟨.Block (t.toStmts mk) none [] none, src⟩
      (some ⟨.Block (e.toStmts mk) none [] none, src⟩), src⟩]

private abbrev HoistM := StateT Nat (Except Message)

/-- Bind every variable `v` reads that one of `later` assigns to a fresh snapshot, and
    read the snapshot instead. The snapshot declarations run where `v` is evaluated, so
    the statements hoisted out of a later operand cannot change what `v` reads. -/
private def snapshotReads (model : SemanticModel) (later : List Identifier)
    (v : StmtExprMd) : HoistM (List StmtExprMd × StmtExprMd) := do
  if later.isEmpty then return ([], v)
  let collect (n : StmtExprMd) : StateM (List Identifier) StmtExprMd := do
    match n.val with
    | .Var (.Local id) =>
      if later.any (sameVar id) && !(← get).any (sameVar id) then modify (· ++ [id])
      pure n
    | _ => pure n
  let reads := ((mapStmtExprM collect v).run []).2
  let mut decls : List StmtExprMd := []
  let mut renames : List (Identifier × Identifier) := []
  for id in reads do
    let n ← getModify (· + 1)
    let snap := mkId s!"$snapshot${n}"
    let src := v.source
    let ty := computeExprType model ⟨.Var (.Local id), src⟩
    decls := decls ++
      [⟨.Assign [⟨.Declare ⟨snap, some ty⟩, src⟩] ⟨.Var (.Local id), src⟩, src⟩]
    renames := renames ++ [(id, snap)]
  let v' := mapStmtExpr (fun n =>
    match n.val with
    | .Var (.Local id) =>
      match renames.find? (sameVar id ·.1) with
      | some (_, snap) => ⟨.Var (.Local snap), n.source⟩
      | none => n
    | _ => n) v
  return (decls, v')

/-- Combine hoisted operands, evaluated left to right, into one hoisted operand list.
    An operand's value is evaluated before the statements hoisted out of the operands
    after it, so each variable it reads that those statements assign is snapshotted. -/
private def hoistSequence (model : SemanticModel) :
    List (Hoisted StmtExprMd) → HoistM (Hoisted (List StmtExprMd))
  | [] => return .done [] []
  | h :: hs => do
    let rest ← hoistSequence model hs
    let later := rest.writes
    h.bindM fun v => do
      let (snaps, v') ← snapshotReads model later v
      return (rest.map (v' :: ·)).prepend snaps

private def hoistPair (model : SemanticModel) (a b : Hoisted StmtExprMd)
    (mk : StmtExprMd → StmtExprMd → StmtExprMd) (orig : StmtExprMd)
    : HoistM (Hoisted StmtExprMd) := do
  let h ← hoistSequence model [a, b]
  return h.map fun | [a', b'] => mk a' b' | _ => orig

/-- Wrap the statements hoisting produced for one branch of an if back into one node. -/
private def asBranch (orig : StmtExprMd) : List StmtExprMd → StmtExprMd
  | [single] => single
  | stmts => ⟨.Block stmts none [] none, orig.source⟩

mutual
/-- Move every block that assigns a local out of `e`.

    A block value `{ S; t }` is replaced by `t`, with `S` run first. Operands are
    evaluated left to right (`hoistSequence`). An if-expression with such a block in a
    branch becomes a `branch`, and so does a short-circuit operator whose right operand
    has one, spelled as the if-expression it means. Positions that are not evaluated at
    all where they appear — a quantifier body, an `old`, an assignment nested in an
    expression — are left in place. -/
private def hoistExpr (model : SemanticModel) (e : StmtExprMd)
    : HoistM (Hoisted StmtExprMd) := do
  let isBlock := match e.val with | .Block .. => true | _ => false
  if !isBlock && !containsBlockWrite e then return .done [] e
  match e with
  | ⟨.Block stmts _ _ _, src⟩ =>
    if containsExitOrReturn e then
      throw (diagnosticFromSource src blockValueExitMsg .userError)
    hoistBlockValue model e stmts
  | ⟨.IfThenElse c t (some el), src⟩ => do
    let hc ← hoistExpr model c
    if containsBlockWrite t || containsBlockWrite el then
      let ht ← hoistExpr model t
      let he ← hoistExpr model el
      hc.bindM fun c' => return .branch [] c' src ht he
    else
      return hc.map fun c' => ⟨.IfThenElse c' t (some el), src⟩
  | ⟨.StaticCall callee args tyArgs, src⟩ => do
    let lit (b : Bool) : Hoisted StmtExprMd := .done [] ⟨.LiteralBool b, src⟩
    let hs ← args.attach.mapM fun ⟨a, _⟩ => hoistExpr model a
    match Operation.ofProcName? callee.text, hs with
    | some .AndThen, [ha, hb] => ha.bindM fun a' => return .branch [] a' src hb (lit false)
    | some .Implies, [ha, hb] => ha.bindM fun a' => return .branch [] a' src hb (lit true)
    | some .OrElse, [ha, hb] => ha.bindM fun a' => return .branch [] a' src (lit true) hb
    | _, _ =>
      return (← hoistSequence model hs).map fun args' => ⟨.StaticCall callee args' tyArgs, src⟩
  | ⟨.InstanceCall target callee args, src⟩ => do
    let ht ← hoistExpr model target
    let hs ← args.attach.mapM fun ⟨a, _⟩ => hoistExpr model a
    return (← hoistSequence model (ht :: hs)).map fun
      | t' :: args' => ⟨.InstanceCall t' callee args', src⟩
      | [] => e
  | ⟨.ReferenceEquals l r, src⟩ => do
    hoistPair model (← hoistExpr model l) (← hoistExpr model r)
      (fun l' r' => ⟨.ReferenceEquals l' r', src⟩) e
  | ⟨.PureFieldUpdate t f v, src⟩ => do
    hoistPair model (← hoistExpr model t) (← hoistExpr model v)
      (fun t' v' => ⟨.PureFieldUpdate t' f v', src⟩) e
  | ⟨.AsType t ty, src⟩ => do
    return (← hoistExpr model t).map fun t' => ⟨.AsType t' ty, src⟩
  | ⟨.IsType t ty, src⟩ => do
    return (← hoistExpr model t).map fun t' => ⟨.IsType t' ty, src⟩
  | ⟨.Var (.Field t f), src⟩ => do
    return (← hoistExpr model t).map fun t' => ⟨.Var (.Field t' f), src⟩
  | _ => return .done [] e

termination_by (sizeOf e, 1)
decreasing_by
  all_goals simp_wf
  all_goals (try have := List.sizeOf_lt_of_mem ‹_›)
  all_goals (try simp only [Prod.lex_def] at *)
  all_goals omega

/-- The statements of a block value hoisted ahead of its last element, which becomes
    the value. An empty block has no value to become, and is left as it is. -/
private def hoistBlockValue (model : SemanticModel) (orig : StmtExprMd)
    (stmts : List StmtExprMd) : HoistM (Hoisted StmtExprMd) := do
  match stmts with
  | [] => return .done [] orig
  | [tail] => hoistExpr model tail
  | s :: t :: more =>
    let pre ← hoistStmt model s
    return (← hoistBlockValue model orig (t :: more)).prepend pre

termination_by (sizeOf stmts, 2)
decreasing_by
  all_goals simp_wf
  all_goals (try have := List.sizeOf_lt_of_mem ‹_›)
  all_goals (try simp only [Prod.lex_def] at *)
  all_goals omega

/-- `s`, preceded by the statements hoisted out of the expressions it evaluates. -/
private def hoistStmt (model : SemanticModel) (s : StmtExprMd)
    : HoistM (List StmtExprMd) := do
  match _h : s with
  | ⟨.Assign [target] value, src⟩ =>
    match target.val with
    | .Field .. => return [s]
    | _ => return (← hoistExpr model value).toStmts fun v => ⟨.Assign [target] v, src⟩
  | ⟨.Return [value], src⟩ =>
    return (← hoistExpr model value).toStmts fun v => ⟨.Return [v], src⟩
  | ⟨.IfThenElse c t el, src⟩ => do
    let hc ← hoistExpr model c
    let t' := asBranch t (← hoistStmt model t)
    let el' ← match el with
      | some eb => (fun r => some (asBranch eb r)) <$> hoistStmt model eb
      | none => pure none
    return hc.toStmts fun c' => ⟨.IfThenElse c' t' el', src⟩
  | ⟨.Block stmts label invs dec, src⟩ => return [⟨.Block (← hoistStmts model stmts) label invs dec, src⟩]
  | ⟨.While .., _⟩ | ⟨.Var _, _⟩ | ⟨.Goto _ _, _⟩ => return [s]
  | _ => return (← hoistExpr model s).toStmts id

termination_by (sizeOf s, 3)
decreasing_by
  all_goals simp_wf
  all_goals (try have := List.sizeOf_lt_of_mem ‹_›)
  all_goals (try simp only [Prod.lex_def] at *)
  all_goals (try subst_vars)
  all_goals omega

private def hoistStmts (model : SemanticModel) (stmts : List StmtExprMd)
    : HoistM (List StmtExprMd) := do
  match stmts with
  | [] => return []
  | s :: rest => return (← hoistStmt model s) ++ (← hoistStmts model rest)
termination_by (sizeOf stmts, 2)
decreasing_by
  all_goals simp_wf
  all_goals (try have := List.sizeOf_lt_of_mem ‹_›)
  all_goals (try simp only [Prod.lex_def] at *)
  all_goals omega
end

/-- Translate a statement sequence into a single expression, or report the first
    statement that has no functional form.

    `retExpr` is the value of the function at an `exit $return`: a reference to
    the output parameter, resolved against whichever binding is innermost there.
    `k` is the continuation — the value of the sequence when control falls off
    its end.

    `labelConts` maps each enclosing labelled block to its continuation, so an
    `exit L` can evaluate to whatever follows the block labelled `L`. See the
    module docstring for the rules.

    Two things are shaped for the termination proof rather than for brevity. The
    outer match is on `s` (the `AstNode`) rather than `s.val`, so each constructor's
    own `sizeOf` appears in the bound and every recursive call is visibly on a
    subterm. And the recursive calls are spelled out in full rather than wrapped in a
    `recur` helper: a helper takes an *arbitrary* statement list, which makes the
    termination goal `sizeOf stmts < ...` for a universally quantified `stmts` and
    therefore unprovable. The verbosity buys totality — no `partial` here. -/
private def functionalizeStmts (model : SemanticModel) (inputUids : List Nat)
    (retExpr : StmtExprMd) (labelConts : List (String × StmtExprMd))
    (stmts : List StmtExprMd) (k : StmtExprMd)
    : Except Message StmtExprMd :=
  match stmts with
  | [] => .ok k
  | s :: rest =>
    let unsupported (src : FileRange) (msg : String)
        (kind : MessageKind := .userError) : Except Message StmtExprMd :=
      .error (diagnosticFromSource src msg kind)
    -- Bind `param` to `value` for the remaining statements. The declaration goes
    -- inside a fresh block so that re-declaring an already bound name shadows it
    -- instead of colliding with it.
    --
    -- The declaration keeps `param`'s name but its `uniqueId` is stripped later by
    -- `stripLocalUids`, so each of the nested declarations this rule produces for one
    -- variable gets its own fresh id from the re-resolve rather than sharing the
    -- assignment target's. `hoistStmts` has already moved every block that writes out
    -- of `value`, so what is left is an expression.
    let bind (param : Parameter?) (targetSource : FileRange) (value : StmtExprMd)
        : Except Message StmtExprMd := do
      let body ← functionalizeStmts model inputUids retExpr labelConts rest k
      let decl : StmtExprMd :=
        ⟨.Assign [⟨.Declare param, targetSource⟩] value, s.source⟩
      .ok ⟨.Block [decl, body] none [] none, s.source⟩
    match s with
    | ⟨.Goto _ .blockStart, _⟩ =>
      -- `RestructureGotos` has turned every backward jump into a loop already.
      unsupported s.source "a backward goto is not supported in a transparent body"
    | ⟨.Goto label .blockEnd, _⟩ =>
      -- An exit discards `rest`: the statements after it are unreachable. Exiting
      -- the return block yields the output; exiting an enclosing labelled block
      -- yields that block's continuation, i.e. whatever follows it.
      if label == returnLabel then .ok retExpr
      else match labelConts.find? (·.1 == label) with
        | some (_, cont) => .ok cont
        -- A label with no enclosing block here is a loop's break/continue: the
        -- loop itself is rejected, so this is only reachable for a malformed exit.
        | none => unsupported s.source
            s!"exiting the block labelled '{label}' is not supported in a transparent body"
    -- `EliminateReturnStatements` lowers every return, but a return reaching
    -- here would mean the same thing, so it is handled rather than rejected.
    | ⟨.Return [value], _⟩ => .ok value
    | ⟨.Return [], _⟩ => .ok retExpr
    | ⟨.Return values, _⟩ => .ok ⟨.Return values, s.source⟩
    | ⟨.Assign [⟨.Local name, targetSource⟩] value, _⟩ =>
      -- Only an *inout* mutation can reach here: `CopyMutatedInputs` redirects a
      -- plain-input write to a fresh body local well before this pass (and leaves
      -- inouts uncopied), so a write that still targets an input targets an inout.
      --
      -- An *inout* is also an output, so it is not in `inputUids`: an assignment to it
      -- is an ordinary update, and the function's result carries its final value. That
      -- is how a written global or `$heap`, which is threaded through the signature as
      -- an inout, leaves a transparent body.
      --
      -- Compared by `uniqueId`, not by text: a local that shadows an input has the
      -- same name but a different binding, and assigning to *it* is the ordinary
      -- destructive-update case that this pass handles.
      if name.uniqueId.any inputUids.contains then
        unsupported s.source
          s!"a transparent body or contract cannot YET mutate any of its inputs, \
             and this mutates '{name.text}'"
      else
        bind ⟨name, some (model.get name).getType⟩ targetSource value
    | ⟨.Assign [⟨.Declare param, targetSource⟩] value, _⟩ =>
      bind param targetSource value
    | ⟨.Var (.Declare param), _⟩ =>
      -- Bind to a hole so an uninitialized read is arbitrary-but-fixed, and cannot
      -- become a free reference that resolves to an input of the same name — see the
      -- module docstring. `holePrelude` hoists the call; this refers to its binding.
      --
      -- An unresolved declaration (no `uniqueId`) has no stable name to generate a
      -- hole from, so it is skipped and resolution reports the missing id instead.
      match param.name.uniqueId with
      | some uid =>
        bind param s.source ⟨.Var (.Local (declHoleValName uid)), s.source⟩
      | none => functionalizeStmts model inputUids retExpr labelConts rest k
    | ⟨.IfThenElse cond thenBranch elseBranch, _⟩ => do
      -- The continuation is what follows the whole if, so it is duplicated into
      -- both branches (see "Known cost" above).
      let kr ← functionalizeStmts model inputUids retExpr labelConts rest k
      let thenExpr ←
        functionalizeStmts model inputUids retExpr labelConts (bodyStatements thenBranch) kr
      let elseExpr ← match elseBranch with
        | some eb =>
          functionalizeStmts model inputUids retExpr labelConts (bodyStatements eb) kr
        | none => .ok kr
      -- The condition is not descended into: `hoistStmts` has already moved the
      -- blocks that write out of it, and any other assignment nested in an expression
      -- is destructive and must stay rejected.
      .ok ⟨.IfThenElse cond thenExpr (some elseExpr), s.source⟩
    | ⟨.Block stmts' label _ _, _⟩ =>
      match label with
      -- An unlabelled block's statements are in statement position, and every
      -- declaration already opens its own scope, so the block's own scope can be
      -- dropped and its statements prepended.
      | none => functionalizeStmts model inputUids retExpr labelConts (stmts' ++ rest) k
      -- A labelled block introduces a continuation: an `exit L` inside it resumes
      -- at the statements following the block, which is exactly `F(rest, k)`. So
      -- translate `rest` first and bind it to the label while translating the
      -- body. The body's own fall-through continuation is the same thing — running
      -- off the end of the block and exiting it are the same control flow.
      --
      -- Like the if rule, this duplicates the continuation: it appears once per
      -- exit plus once for the fall-through path.
      | some l => do
        let kr ← functionalizeStmts model inputUids retExpr labelConts rest k
        functionalizeStmts model inputUids retExpr ((l, kr) :: labelConts) stmts' kr
    -- A pure expression with nothing following it is discarded, as in the procedure: the
    -- value is the continuation, so an output the body never assigns keeps its hole.
    -- Anything else, or an expression with statements after it, has no functional form.
    | _ =>
      if rest.isEmpty && isPureValue s then .ok k
      else
        let (msg, kind) := unsupportedStmt s
        unsupported s.source msg kind

termination_by sizeOf stmts
decreasing_by
  -- Matching on the `AstNode` wrapper (rather than `s.val`) expands each constructor
  -- into the bound, so every recursive call is visibly on a subterm of `s`.
  all_goals simp_wf
  -- Each goal bounds one recursive call by `sizeOf s + sizeOf rest`. Two facts
  -- cover every shape: `bodyStatements` does not grow its argument, and an append's
  -- size is the sum of the parts. `grind` instantiates them at the terms each goal
  -- actually mentions.
  all_goals
    (first
      | omega
      | grind [bodyStatements_sizeOf_le, sizeOf_append])

private def packagedOutputs (types : List TypeDefinition) (proc : Procedure)
    : Option (List Parameter) :=
  let wanted := multiOutputDatatypeName proc.name.text
  match types.findSome? (fun t => match t with
      | .Datatype dt => if dt.name.text == wanted then some dt else none
      | _ => none) with
  | some dt =>
    match dt.constructors with
    | [ctor] => some ctor.args
    | _ => none
  | none => none

/-- Rewrite a single function body into a pure expression, reporting the reason
    if it has no functional form.

    Returns the uninterpreted hole functions the rewrite refers to alongside the
    rewritten procedure; the caller adds them to the program. -/
private def rewriteFunctionBody (model : SemanticModel)
    (types : List TypeDefinition) (proc : Procedure)
    : Procedure × List Procedure × List Message :=
  match proc.body with
  | .Transparent rawBody =>
    -- Make every declared local's name unique before translating, so extending a
    -- declaration's scope over the continuation cannot capture an outer variable of the
    -- same name. See `alphaConvertLocals`.
    let declaredUids := declaredLocalUids rawBody
    let body := alphaConvertLocals rawBody
    match proc.outputs with
    | [] =>
      -- A void procedure is legal (`valuelessEarlyReturn` is a transparent body with no
      -- outputs that must verify). Its function copy has nothing to evaluate to, so the
      -- body becomes a placeholder; the procedure itself carries the meaning. The
      -- placeholder must be a bool: that is the stand-in `translateType` gives a void
      -- type, and how `computeExprType` types a call to this copy.
      ({ proc with body := .Transparent ⟨.LiteralBool true, body.source⟩ }, [], [])
    | outputs =>
      -- Both the value of an `exit $return` and the value of falling off the end are a
      -- read of the output parameters: an assignment to one became a declaration scoping
      -- over what follows, so the read finds the assigned value. The two cannot differ —
      -- `r := 1` with no explicit exit falls off the end and must still yield 1.
      let packaged? := packagedOutputs types proc
      let effectiveOutputs := packaged?.getD outputs
      let outputRefs : List StmtExprMd :=
        effectiveOutputs.map fun o =>
          ⟨.Var (.Local (renamedLocal declaredUids o.name)), proc.name.source⟩
      let retExpr : StmtExprMd := match packaged?, outputRefs with
        | some _, refs =>
          ⟨.StaticCall (mkId (multiOutputCtorName proc.name.text)) refs [], proc.name.source⟩
        | none, [single] => single
        | none, refs => ⟨.Return refs, proc.name.source⟩
      let outputNames := effectiveOutputs.map (·.name.text)
      let inputUids := proc.inputs.filterMap fun p =>
        if outputNames.contains p.name.text then none else p.name.uniqueId
      -- Collected from the *original* body, whose declarations still carry the
      -- `uniqueId`s the rewrite named its hole references after (`stripLocalUids` clears
      -- them in the result, but the names are already derived).
      let localDecls := bareDecls body
      -- The output starts out unassigned, exactly like a bare local, so it gets a hole
      -- too: bound outermost under its *own* name, so every assignment to it shadows the
      -- hole and only a path that never assigns reads it. Without this, such a path
      -- leaves a free reference to the output and Core reports
      -- `Cannot find this fvar in the context!`, naming neither the procedure nor the
      -- output.
      --
      -- Skipped when the outputs are packaged: `PackageFunctionOutputs` already left a
      -- bare declaration per ex-output in the body, so `localDecls` holds them and each
      -- is holed as an ordinary uninitialized local.
      let outputDecls : List HoleBinding :=
        if packaged?.isNone then
          outputs.filterMap fun output =>
            if proc.inputs.any (·.name.text == output.name.text) then none
            else output.name.uniqueId.map (fun uid => (uid, output.name, output.type))
        else []
      let decls := outputDecls ++ localDecls
      match (hoistStmts model (bodyStatements body)).run' 0 >>= fun stmts =>
          functionalizeStmts model inputUids retExpr [] stmts retExpr with
      | .ok body' =>
        -- The prelude is wrapped around the rewritten body *before* stripping, so its
        -- own declarations lose their ids like every other declaration this pass makes
        -- and the re-resolve mints fresh ones.
        (let prelude := holePrelude proc.name proc.inputs decls body'
         ({ proc with body := .Transparent (stripLocalUids prelude) },
          declHoleProcs proc.name proc.typeArgs proc.inputs decls, []))
      | .error diag => (proc, [], [diag])
  | _ => (proc, [], [])

private def functionalRewrite (uc : LaurelProgram) (model : SemanticModel)
    : LaurelProgram × List Message :=
  -- Every entry of `staticFunctions` is produced by the transparency pass's
  -- `mkFunctionCopy`, so all of them are functions and need rewriting.
  let results := uc.staticFunctions.map (rewriteFunctionBody model uc.types)
  -- The generated hole functions are uninterpreted, so they need no rewriting of
  -- their own and simply join the program alongside the rewritten bodies.
  let holes := results.flatMap (·.2.1)
  ({ uc with staticFunctions := holes ++ results.map (·.1) }, results.flatMap (·.2.2))

public def functionalRewritePass : LaurelPass := .onUnordered {
  name := "FunctionalRewritePass"
  creates := [NodeKind.Pseudo.letExpr]
  removes := [NodeKind.Pseudo.imperativeFunction]
  documentation := "Rewrites a function body from imperative form into a single pure expression by continuation passing: an assignment becomes a shadowing declaration whose scope is the statements that follow it, an `exit $return` becomes a reference to the output parameter (or, for a function whose outputs PackageFunctionOutputs replaced with a single packaged one, a call to that datatype's constructor over the outputs it dropped), an `exit L` becomes the continuation of the block labelled `L`, and an if-then-else becomes an if-expression whose branches each end in the continuation, and every variable the body leaves uninitialized — a declaration without an initializer, and each output parameter that is not an inout — is bound at the top of the body to a deterministic hole (a call to a generated uninterpreted function), so reading one yields an arbitrary-but-fixed value and an assignment shadows it. This removes the label mechanism and so supports early exits and exits to user labels. A body containing a construct with no functional form (a loop, an assignment to several targets) is reported as a user error; a construct an earlier pass should have eliminated (an assert, an assume, a call, a field assignment) is reported as a Strata bug."
  -- The rewrite introduces declarations and strips their ids, so resolution must
  -- run afterwards to mint fresh, unique ones.
  needsResolves := true }
  fun _ uc model =>
    let (uc', diags) := functionalRewrite uc model
    (uc', diags, {})

end -- public section

end Strata.Laurel
