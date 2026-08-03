/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.UnorderedCore
import Strata.Languages.Laurel.TransparencyPass
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.EliminateReturnStatements
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

An uninitialized local in a *polymorphic* transparent body is reported rather than
given a hole: the hole mirrors the enclosing inputs, so it is polymorphic too, and
monomorphization runs much earlier in the pipeline than this pass.

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
to bind it around. Those are left untouched and stay rejected, which is why
neither an if-condition nor a non-block assigned value is descended into.

This is also why a contract is unaffected. Preconditions and postconditions are
`Condition` expressions, not body statements, so they are outside this pass
entirely (`rewriteFunctionBody` matches only on `proc.body`) and a destructive
assignment in one is reported by the Core schema translation.

## Rejecting what has no functional form

A body containing a construct with no functional form — a loop, an assignment to
an input parameter, an assignment to several targets —
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

## Follow-up: multi-variable if-lifting with tuples

Inlining duplicates an initializer at each use, so a branch that assigns a
variable read more than once duplicates work. A `StmtExpr.Tuple` constructor
would let a branch yield several values at once:

    if (b) { x := a + 1; y := x + 10; } else { x := a; y := x; }

    var x, y := if (b) then { var x := a + 1; Tuple [x, x + 10] }
                       else { Tuple [a, x] };

This requires adding `StmtExpr.Tuple (elements : List (AstNode StmtExpr))` to
LaurelAST, updating the MapStmtExpr traversals, and teaching the Core translator
to destructure a tuple into let-bindings. It is subsumed by giving Core a real
`let`.
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
  | ⟨.Block [single] label, _⟩ =>
    if label.all (· == returnLabel) then bodyStatements single else [body]
  | ⟨.Block stmts label, _⟩ =>
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

/-- `dropLast` never grows a list. Used to bound the statements of a block value,
    which are functionalized with the block's last element as the continuation.

    Stated for any element type, as with `sizeOf_append`. -/
private theorem sizeOf_dropLast_le {α : Type} [SizeOf α] (xs : List α) :
    sizeOf xs.dropLast ≤ sizeOf xs := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    cases as with
    | nil => simp
    | cons b bs =>
      simp only [List.dropLast_cons₂, List.cons.sizeOf_spec] at *
      omega

/-- The name of the uninterpreted function standing for the initial value of the
    bare declaration whose `uniqueId` is `uid`, and the name of the local the rewrite
    binds its result to.

    Deriving both from `uniqueId` — unique program-wide after resolution — is what lets
    this pass mint hole names without threading a counter through `functionalizeStmts`,
    keeping that function pure and its termination proof unchanged.

    The prefixes are deliberately *not* `EliminateDeterministicHoles`' `$hole_`: that
    pass numbers its holes from a counter, so sharing a prefix could produce the same
    name twice and resolution would report a duplicate definition. Both start with `$`,
    which a user cannot write, so neither can be shadowed by a program's own name. -/
private def declHoleName (uid : Nat) : Identifier := s!"$declHole_{uid}"

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

    Used to reject one shape rather than mistranslate it: a block *value*, as in
    `r := { if c then { exit L }; 5 }`. The block-value arms translate such a block with
    its last element as the continuation, which turns an `exit` into that label's
    continuation *as the assigned value* — and then the statements after the assignment
    still run. For

        r := 1; { r := { if c then { exit done }; 5 }; r := r + 100 } done; return r

    the `exit done` should leave the labelled block before either assignment, giving 1,
    but yields 1 + 100 instead.

    An exit is control flow that abandons the enclosing statements, and a value's
    continuation is not the statement's continuation, so expressing this needs more than
    the single continuation these arms thread through. Rejecting keeps the rewrite honest
    until then. -/
private def containsExitOrReturn (e : StmtExprMd) : Bool :=
  let check (n : StmtExprMd) : StateM Bool StmtExprMd := do
    match n.val with
    | .Exit _ | .Return _ => set true; pure n
    | _ => pure n
  ((mapStmtExprM check e).run false).2

/-- The message for a block value the rewrite will not translate. -/
private def blockValueExitMsg : String :=
  "an `exit` or `return` inside an assigned block value is not YET supported in transparent bodies or contracts"

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
  let collect (e : StmtExprMd) : StateM (List Nat) StmtExprMd := do
    match e.val with
    | .Var (.Declare p) | .Assign [⟨.Declare p, _⟩] _ =>
      match p.name.uniqueId with
      | none => pure e
      | some uid => modify (uid :: ·); pure e
    | _ => pure e
  let declared := ((mapStmtExprM collect body).run []).2
  let renamed (id : Identifier) : Identifier :=
    match id.uniqueId with
    | some uid => if declared.contains uid then { id with text := s!"$v_{uid}" } else id
    | none => id
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

    `typeArgs` carries the enclosing function's type parameters, for the same reason
    `ContractPass.mkConditionProc` does: in a polymorphic function (`f<T>(x : T)`) the
    mirrored inputs and the declared type mention `T`, so the generated hole must bind
    `T` too, or `T` is a free type variable at Core and the program fails to type-check.
    Empty for a monomorphic function.

    The body is `.Opaque [] none []`, which the Core schema translation turns into a
    function with no body, i.e. an uninterpreted one. That is the already-eliminated
    form of a deterministic hole: this pass runs long after
    `eliminateDeterministicHolesPass`, so emitting a `.Hole` here would never be
    eliminated. -/
private def declHoleProcs (typeArgs : List Identifier) (inputs : List Parameter)
    (decls : List HoleBinding) : List Procedure :=
  decls.map fun (uid, _, ty) =>
    { name := declHoleName uid
      typeArgs := typeArgs
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
private def holePrelude (inputs : List Parameter) (decls : List HoleBinding)
    (body : StmtExprMd) : StmtExprMd :=
  let src := body.source
  let args : List StmtExprMd := inputs.map fun p => ⟨.Var (.Local p.name), src⟩
  decls.foldr (init := body) fun (uid, name, ty) acc =>
    let call : StmtExprMd := ⟨.StaticCall (declHoleName uid) args, src⟩
    let decl : StmtExprMd :=
      ⟨.Assign [⟨.Declare ⟨name, some ty⟩, src⟩] call, src⟩
    ⟨.Block [decl, acc] none, src⟩

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
  -- An assignment to several targets comes from a multi-output call, so making it
  -- functional needs a way for one expression to yield several values (see the
  -- tuple note in the module docstring).
  --
  -- No test reaches this arm from surface Laurel, and none can while the only way to
  -- write one is `assign a, b := f()`: the transparency pass rejects the multi-output
  -- call first, with "calling multi-output procedure 'f' is not (yet) supported from a
  -- transparent procedure or contract". The arm stays because this function is total
  -- over statement shapes, and to give a precise message if a later pass ever
  -- synthesizes the form.
  | .Assign targets _ =>
    if targets.any (fun t => match t.val with | .Field .. => true | _ => false) then
      ("field assignment should have been eliminated by heap parameterization", .strataBug)
    else
      ("assignments to multiple targets are not YET supported in transparent bodies or contracts",
       .userError)
  -- The transparency pass strips asserts and assumes from a function copy
  -- (`stripAssertAssume`) and rewrites calls into functional form
  -- (`rewriteCallsToFunctional`), so none of these can be reached from a
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
    -- assignment target's. `value` has already been functionalized by the caller (see
    -- the block-valued arms of `Assign`/`Return`).
    let bind (param : Parameter?) (targetSource : FileRange) (value : StmtExprMd)
        : Except Message StmtExprMd := do
      let body ← functionalizeStmts model inputUids retExpr labelConts rest k
      let decl : StmtExprMd :=
        ⟨.Assign [⟨.Declare param, targetSource⟩] value, s.source⟩
      .ok ⟨.Block [decl, body] none, s.source⟩
    match s with
    | ⟨.Exit label, _⟩ =>
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
    --
    -- A *block* value is the one exception to "an assignment's value is an
    -- expression": the transparency pass can emit a transparent body as
    -- `$result := { <statements>; <tail expression> }`, whose statements are
    -- genuinely in statement position, so they are functionalized with the block's
    -- own final element as the continuation. These arms are spelled out rather than
    -- funnelled through a helper so that each recursive call is on a structural
    -- subterm of `s`, which is what lets Lean see this function terminates.
    | ⟨.Return (some value@⟨.Block valueStmts _, _⟩), _⟩ =>
      if containsExitOrReturn value then unsupported s.source blockValueExitMsg
      else
      match valueStmts.getLast? with
      -- An empty block has no tail expression to become the value; leave it as-is,
      -- matching what the pre-existing helper did.
      | none => .ok value
      | some tail =>
        functionalizeStmts model inputUids retExpr labelConts valueStmts.dropLast tail
    | ⟨.Return (some value), _⟩ => .ok value
    | ⟨.Return none, _⟩ => .ok retExpr
    | ⟨.Assign [⟨.Local name, targetSource⟩] value, _⟩ =>
      -- Assigning to an input parameter is a destructive assignment the Core
      -- translator must keep rejecting. Turning it into a shadowing declaration
      -- would silently accept the program.
      --
      -- Compared by `uniqueId`, not by text: a local that shadows an input has the
      -- same name but a different binding, and assigning to *it* is the ordinary
      -- destructive-update case that this pass handles.
      if name.uniqueId.any inputUids.contains then
        unsupported s.source
          "destructive assignments are not supported in transparent bodies or contracts"
      else do
        let value ← match value with
          | ⟨.Block valueStmts _, _⟩ =>
            if containsExitOrReturn value then unsupported s.source blockValueExitMsg
            else
            match valueStmts.getLast? with
            | none => .ok value
            | some tail =>
              functionalizeStmts model inputUids retExpr labelConts valueStmts.dropLast tail
          | _ => .ok value
        bind ⟨name, some (model.get name).getType⟩ targetSource value
    | ⟨.Assign [⟨.Declare param, targetSource⟩] value, _⟩ => do
      let value ← match value with
        | ⟨.Block valueStmts _, _⟩ =>
          if containsExitOrReturn value then unsupported s.source blockValueExitMsg
          else
          match valueStmts.getLast? with
          | none => .ok value
          | some tail =>
            functionalizeStmts model inputUids retExpr labelConts valueStmts.dropLast tail
        | _ => .ok value
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
      -- The condition is deliberately not descended into: an assignment nested
      -- in an expression is destructive and must stay rejected.
      .ok ⟨.IfThenElse cond thenExpr (some elseExpr), s.source⟩
    | ⟨.Block stmts' label, _⟩ =>
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
    -- A body that is already a plain expression, with nothing following it: its value
    -- *is* the expression, so there is nothing to translate. `TypeHierarchy`'s downcast
    -- helpers are exactly this shape — `function downcast$C(p: C): C requires (p is C)
    -- { p }` — and so is any transparent body written as a bare expression rather than a
    -- `return`.
    --
    -- Only in tail position. An expression earlier in a statement list is a value
    -- computed and discarded, which is either dead code or a side effect this pass does
    -- not model, so it keeps falling through to the report below.
    | _ =>
      if rest.isEmpty then .ok s
      else
        let (msg, kind) := unsupportedStmt s
        unsupported s.source msg kind

termination_by sizeOf stmts
decreasing_by
  -- Matching on the `AstNode` wrapper (rather than `s.val`) expands each constructor
  -- into the bound, so every recursive call is visibly on a subterm of `s`.
  all_goals simp_wf
  -- Each goal bounds one recursive call by `sizeOf s + sizeOf rest`. Three facts
  -- cover every shape: `dropLast` and `bodyStatements` do not grow their argument,
  -- and an append's size is the sum of the parts. `grind` instantiates them at the
  -- terms each goal actually mentions.
  all_goals
    (first
      | omega
      | grind [sizeOf_dropLast_le, bodyStatements_sizeOf_le, sizeOf_append])

/-- Rewrite a single function body into a pure expression, reporting the reason
    if it has no functional form.

    Returns the uninterpreted hole functions the rewrite refers to alongside the
    rewritten procedure; the caller adds them to the program. -/
private def rewriteFunctionBody (model : SemanticModel) (proc : Procedure)
    : Procedure × List Procedure × List Message :=
  match proc.body with
  | .Transparent rawBody =>
    -- Make every declared local's name unique before translating, so extending a
    -- declaration's scope over the continuation cannot capture an outer variable of the
    -- same name. See `alphaConvertLocals`.
    let body := alphaConvertLocals rawBody
    match proc.outputs with
    | [output] =>
      -- Both the value of an `exit $return` and the value of falling off the end are a
      -- read of the output parameter: an assignment to it became a declaration scoping
      -- over what follows, so the read finds the assigned value. The two cannot differ —
      -- `r := 1` with no explicit exit falls off the end and must still yield 1.
      let retExpr : StmtExprMd := ⟨.Var (.Local output.name), proc.name.source⟩
      let inputUids := proc.inputs.filterMap (·.name.uniqueId)
      -- Collected from the *original* body, whose declarations still carry the
      -- `uniqueId`s the rewrite named its hole references after (`stripLocalUids` clears
      -- them in the result, but the names are already derived).
      let localDecls := bareDecls body
      -- A hole in a *polymorphic* function is itself polymorphic: its parameters mirror
      -- the enclosing inputs, whose types mention the type variables. Monomorphization
      -- runs far earlier in the pipeline than this pass, so such a hole is never
      -- instantiated and reaches SMT with an unresolved type variable — reported there as
      -- an analysis error about polymorphic function bodies, which points nowhere useful.
      -- Report it here instead.
      if !proc.typeArgs.isEmpty && !localDecls.isEmpty then
        (proc, [], [diagnosticFromSource proc.name.source
          s!"a local without an initializer is not YET supported in a transparent body of a polymorphic procedure like '{proc.name.text}'; give it an initializer"])
      else
      -- The output starts out unassigned, exactly like a bare local, so it gets a hole
      -- too: bound outermost under its *own* name, so every assignment to it shadows the
      -- hole and only a path that never assigns reads it. Without this, such a path
      -- leaves a free reference to the output and Core reports
      -- `Cannot find this fvar in the context!`, naming neither the procedure nor the
      -- output.
      --
      -- Skipped for a polymorphic function for the reason above — the hole could not be
      -- monomorphized. Such a body keeps the free-reference behaviour on a fall-through
      -- path, which is the narrow case the restriction above does not already cover.
      let outputDecl : List HoleBinding :=
        if proc.typeArgs.isEmpty then
          match output.name.uniqueId with
          | some uid => [(uid, output.name, output.type)]
          | none => []
        else []
      let decls := outputDecl ++ localDecls
      match functionalizeStmts model inputUids retExpr [] (bodyStatements body) retExpr with
      | .ok body' =>
        -- The prelude is wrapped around the rewritten body *before* stripping, so its
        -- own declarations lose their ids like every other declaration this pass makes
        -- and the re-resolve mints fresh ones.
        ({ proc with body := .Transparent (stripLocalUids (holePrelude proc.inputs decls body')) },
         declHoleProcs proc.typeArgs proc.inputs decls, [])
      | .error diag => (proc, [], [diag])
    | [] =>
      -- A void procedure is legal (`valuelessEarlyReturn` is a transparent body
      -- with no outputs that must verify). There is nothing for its function copy
      -- to evaluate to, so the copy is left untransformed; the procedure itself
      -- carries the meaning.
      (proc, [], [])
    | outputs =>
      -- A function evaluates to a single value, so there is no way for one to
      -- yield several outputs at once. This needs `StmtExpr.Tuple` (see the
      -- module docstring).
      (proc, [], [diagnosticFromSource proc.name.source
        s!"a transparent body with {outputs.length} output parameters is not supported; it must have at most one"])
  | _ => (proc, [], [])

private def functionalRewrite (uc : UnorderedCoreWithLaurelTypes) (model : SemanticModel)
    : UnorderedCoreWithLaurelTypes × List Message :=
  -- Every entry of `functions` is produced by the transparency pass's
  -- `mkFunctionCopy`, so all of them are functions and need rewriting.
  let results := uc.functions.map (rewriteFunctionBody model)
  -- The generated hole functions are uninterpreted, so they need no rewriting of
  -- their own and simply join the program alongside the rewritten bodies.
  let holes := results.flatMap (·.2.1)
  ({ uc with functions := holes ++ results.map (·.1) }, results.flatMap (·.2.2))

public def functionalRewritePass : LaurelPass UnorderedCoreWithLaurelTypes UnorderedCoreWithLaurelTypes where
  name := "FunctionalRewritePass"
  documentation := "Rewrites a function body from imperative form into a single pure expression by continuation passing: an assignment becomes a shadowing declaration whose scope is the statements that follow it, an `exit $return` becomes a reference to the output parameter, an `exit L` becomes the continuation of the block labelled `L`, and an if-then-else becomes an if-expression whose branches each end in the continuation, and every variable the body leaves uninitialized — a declaration without an initializer, and the output parameter — is bound at the top of the body to a deterministic hole (a call to a generated uninterpreted function), so reading one yields an arbitrary-but-fixed value and an assignment shadows it. This removes the label mechanism and so supports early exits and exits to user labels. A body containing a construct with no functional form (a loop, an assignment to an input parameter, an assignment to several targets) is reported as a user error; a construct an earlier pass should have eliminated (an assert, an assume, a call, a field assignment) is reported as a Strata bug."
  comesAfter := [⟨transparencyPass.meta, "Functions are created by the transparency pass"⟩]
  -- The rewrite introduces declarations and strips their ids, so resolution must
  -- run afterwards to mint fresh, unique ones.
  needsResolves := true
  run := fun _ uc model =>
    let (uc', diags) := functionalRewrite uc model
    (uc', diags, {})

end -- public section

end Strata.Laurel
