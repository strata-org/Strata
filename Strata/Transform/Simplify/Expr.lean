/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Function
public import Strata.Languages.Core.Factory
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Lambda.LExprEval

/-! # Simplify: expressions, the value context, and base commands

The part of `simplify` that does not depend on how statements are nested: folding,
the two copying rewrites and the conditions that keep them from compounding,
`simplifyExpr`, the context of known values with its record, invalidate and join
operations, and the simplification of one base command (`simpCmd`). The structured
traversal in `Simplify` is built from these, and a traversal of control-flow-graph
bodies can be built from the same ones.
-/

public section

namespace Core.Simplify

open Lambda Imperative

/-! ## Folding without expansion

Folding runs through `LExpr.eval`. Two of its rewrites have to be withheld from it
so that this phase decides them instead: expansion of a function marked `inline`,
and substitution of a variable's value. The first is withheld by removing the
attribute that drives it, the second by handing it an environment that knows
nothing.

`inlineIfConstr` and `inlineIfAllValues` stay. Both already carry the condition
that makes them worth doing — an argument that is a constructor application, or
arguments that are all canonical — and datatype destructors, testers and regular
expressions do not fold at all without them. -/

/-- Whether expanding this function's calls may be what keeps the term encodable. The
    test is syntactic, on the declaration, so it can say yes where expansion would remove
    nothing, which only keeps `inline` on more functions.

    Expanding an `inline` call does two jobs: it partially evaluates, and it erases what
    the SMT encoder cannot encode, abstractions and operators that need literal
    arguments. Only the first is this phase's business, but the second cannot simply be
    dropped, so the attribute is kept wherever a lambda or such an operator can be
    involved.

    A body that applies a `Core.literalIndexOps` operator is the fifth way, next to the
    four below: `re.loop(r, 1, n)` with a parameter `n` encodes only after expansion puts a
    literal for `n`.

    A lambda can reach a call four ways, all visible in the declaration: a parameter
    whose type is a function type, a parameter whose type carries one inside a datatype
    field, an abstraction the body builds itself, and a call in the body to a function
    that does any of these. `carriers` names the datatypes of the second kind and the
    functions of the last, as `lambdaCarriers` computes them for a program; a datatype
    and a function sharing a name only keep `inline` on more functions. -/
def mayEliminateLambdas (carriers : List String) (fn : Core.Function) : Bool :=
  let types := fn.inputs.values ++ [fn.output]
  types.any LMonoTy.containsArrow
    || types.any (LMonoTy.mentionsTyCon carriers)
    || (fn.body.map LExpr.hasAbs).getD false
    || bodyCalls carriers
    || bodyCalls Core.literalIndexOps
where
  /-- Whether the body applies an operator named in `names`. -/
  bodyCalls (names : List String) : Bool :=
    (fn.body.map fun b => (LExpr.getOps b).any (fun o => names.contains o.name)).getD false

/-- Weaken the unconditional `inline` attribute to `inlineIfAllValues`, from a
    function whose expansion is not what erases a lambda.

    What remains automatic is the case that cannot compound: every argument canonical,
    so the arguments mention no variable and the expanded body folds against closed
    values. Every other expansion becomes this phase's decision. The evaluator already
    implements that condition, which is why it is expressed as an attribute rather than
    as a check of this phase's own. -/
def stripInlineFunc (carriers : List String) (fn : Core.Function) : Core.Function :=
  if mayEliminateLambdas carriers fn || !fn.attr.contains .inline then fn
  else
    let attr := fn.attr.filter (· != .inline)
    { fn with attr := if attr.contains .inlineIfAllValues then attr
                      else attr.push .inlineIfAllValues }

def stripInline (carriers : List String) (fn : LFunc CoreLParams) : LFunc CoreLParams :=
  { fn with toFunc := stripInlineFunc carriers fn.toFunc }

def withoutInline (carriers : List String) (F : Expression.Factory) : Expression.Factory :=
  Factory.ofArray (F.toArray.map (stripInline carriers))

/-! ## The evaluation environments the phase folds in -/

namespace Env

/-- No variable has a value, so evaluation folds and expands but substitutes nothing. -/
def noValues : Lambda.Env CoreLParams := Lambda.Env.mk (fun _ => none)

/-- Only `x` has a value, `v`. -/
def oneValue (x : CoreIdent) (v : Expression.Expr) : Lambda.Env CoreLParams :=
  Lambda.Env.mk (fun y => if y == x then some v else none)

/-- The known values substituted wherever they are read, with no size check: values of
    one node, and canonical values.

    A value of one node (a constant, another variable, a nullary operator) cannot grow
    an expression at all. A canonical value, such as a literal or a constructor applied
    to canonical values, can be larger, but it mentions no variable, so a copy of it
    never exposes another variable whose value would then be copied in turn within one
    expression. It is also what folding needs, since a destructor or tester reduces only
    when its argument is a constructor.

    The size of a recorded canonical value is not bounded, though. A value is recorded
    after substitution, so a chain `t1 := Node(t0, t0)`, `t2 := Node(t1, t1)`, … records a
    value that doubles at each definition, and a read of `t12` copies 4096 leaves. That is
    the size symbolic evaluation reaches on the same program, so it is no regression, but
    the copying rule does not bound it.

    Any other value has to earn its place at each use, which costs a pass per variable,
    so it is left alone here. -/
def smallValues (F : Expression.Factory) (vs : Map CoreIdent Expression.Expr) :
    Lambda.Env CoreLParams :=
  Lambda.Env.mk (fun y =>
    match Map.find? vs y with
    | some v => if LExpr.size _ v ≤ 1 || LExpr.isValue F v then some v else none
    | none => none)

end Env

/-- Simplify `e` by folding without expanding `inline` calls or substituting variable
    values. -/
def fold (stripped : Expression.Factory) (fuel : Nat) (e : Expression.Expr) : Expression.Expr :=
  (LExpr.eval fuel stripped Env.noValues e).fst

def foldWith (stripped : Expression.Factory) (fuel : Nat) (x : CoreIdent) (v : Expression.Expr)
    (e : Expression.Expr) : Expression.Expr :=
  (LExpr.eval fuel stripped (Env.oneValue x v) e).fst

/-! ## Context -/

/-- What the traversal carries.

    `values` is what makes folding under a variable possible: a variable's
    simplified value is available at its uses, and substituting it is considered
    there. -/
structure Ctx where
  /-- Functions in scope, consulted to decide whether a call can be expanded. -/
  factory : Expression.Factory
  /-- `factory` with the unconditional `inline` attribute stripped, which is what
      folding runs against. Carried rather than derived, because
      deriving it rebuilds every function in the factory and folding happens at
      every node of every expression. -/
  foldFactory : Expression.Factory
  /-- Bound on `LExpr.eval`'s own recursion while folding. Exhausting it leaves a term
      partly folded, which is sound but larger, so it is set well above what any
      expression in a translated program needs. -/
  evalFuel : Nat := 100
  /-- Budget for the depth of nested expansions. Expanding a body can expose
      another call to expand, and that descent is not bounded by the term measure,
      so it is bounded here; a recursive `inline` function would otherwise expand
      forever. Each of `simplifyExpr`'s two passes expands at most this many nested
      levels, so a longer chain of `inline` calls on a symbolic argument keeps its
      innermost remaining call, which symbolic evaluation then leaves to the solver as
      a definition. -/
  expandFuel : Nat := 4
  /-- Simplified value of each variable whose definition has been seen. -/
  values : Map CoreIdent Expression.Expr := Map.ofList []
  /-- The datatypes whose values can carry a lambda, computed once per program, so
      that the rule deciding which `inline` attributes to withhold is settled before
      any expression is simplified. -/
  carriers : List String := []

def Ctx.ofFactory (F : Expression.Factory) (carriers : List String := []) : Ctx :=
  { factory := F, foldFactory := withoutInline carriers F, carriers }

def Ctx.spend (ctx : Ctx) : Ctx := { ctx with expandFuel := ctx.expandFuel - 1 }

/-- Drop every recorded value invalidated by mutating the variables `vs`: both a
    binding *of* a mutated variable and a binding whose value *mentions* one.

    The second half is the subtle one. A definition `t := output` records `output`
    as `t`'s value; if `output` is then havoc'd or reassigned, `t`'s recorded value
    is stale, and substituting it into a later use would read `output`'s new value
    instead of the one `t` captured. Erasing only `output`'s own entry is not
    enough. -/
def Ctx.invalidate (ctx : Ctx) (vs : List CoreIdent) : Ctx :=
  let names := vs.map (·.name)
  let kept := ctx.values.toList.filter fun (k, e) =>
    !names.contains k.name && !(HasFvars.getFvars e).any (fun f => names.contains f.name)
  { ctx with values := Map.ofList kept }

/-! ## The two copying rewrites

*The size condition*, referred to below by the substitution rule: the rewrite is kept
only if its simplified result has a strictly smaller `LExpr.size` than what it
replaces. `LExpr.size` counts every node, so a rewrite that duplicates a subterm pays
for each copy out of what the reduction saves. Expansion does not use it; the shape of
the call decides that, before a candidate exists. -/

/-- The body of the function `fn` was called with, with `args` substituted for its
    parameters. `none` when the call cannot be expanded: no body, or a type
    substitution that does not exist (which a well-typed term does not produce). -/
def expandCall (fn : LFunc CoreLParams) (opExpr : Expression.Expr)
    (args : List Expression.Expr) : Option Expression.Expr :=
  match fn.body with
  | none => none
  | some body =>
    match LFunc.computeTypeSubst fn opExpr args with
    | none => none
    | some tySubst =>
      let body := body.applyTypeSubst tySubst
      some (LExpr.substFvarsLifting body (fn.inputs.keys.zip args))

/-- How many times `e` mentions the free variable `x`. -/
def occursCount (x : CoreIdent) (e : Expression.Expr) : Nat :=
  ((HasFvars.getFvars e).filter (fun f => f.name == x.name)).length

/-- Whether expanding `fn` is worth attempting, decided without building anything.

    Building an expansion is expensive -- the argument is substituted into the body,
    the result folded, and that repeated for nested calls -- and the size test then
    discards most of what it built. So the decision is made from two properties that
    need no candidate.

    A body that mentions each parameter at most once copies nothing, so expanding it
    always pays.

    A body that mentions a parameter twice or more copies that argument, and what the
    copy costs is the argument's size. A single node is free -- expanding a bounds
    predicate over a variable, `lo <= x && x <= hi`, adds one node and puts arithmetic
    where a solver can use it. A canonical argument is free for the reason `Env.smallValues`
    substitutes one: it mentions no variable, so its copies cannot compound, and a body
    applied to canonical arguments is what folding reduces. Any other argument larger
    than a node is what doubles per level of nesting, so that is where expansion is
    declined. -/
def worthExpanding (F : Expression.Factory) (fn : LFunc CoreLParams)
    (args : List Expression.Expr) : Bool :=
  match fn.body with
  | none => false
  | some body =>
    -- A call to a function with preconditions is what generates their obligations.
    -- Expanding it away discharges nothing and reports nothing: a narrowing cast
    -- whose range check lives in such a precondition would silently stop being
    -- checked.
    if !fn.preconditions.isEmpty then false else
    let copiesSomethingLarge := (fn.inputs.keys.zip args).any
      (fun (p, a) => occursCount p body > 1 && LExpr.size _ a > 1
        && !LExpr.isValue F a)
    !copiesSomethingLarge

/-- Expand a call at the root of `e` where `worthExpanding` admits it, leaving `e` alone
    otherwise. The expanded body is simplified and folded, which the admission test
    depends on: `dup(3)` becomes `int.add(3, 3)`, larger than the call until folding
    makes it `6`.

    `expandFuel` bounds how deep this may recur. -/
def tryExpand (ctx : Ctx) (simp : Ctx → Expression.Expr → Expression.Expr)
    (e : Expression.Expr) : Expression.Expr :=
  if ctx.expandFuel = 0 then e else
  match ctx.factory.callOfLFunc e with
  | none => e
  | some (opExpr, args, fn) =>
    if !fn.attr.contains .inline then e else
    -- A function, so that a declined call builds nothing: Lean evaluates a `let` eagerly.
    let expand (_ : Unit) : Option Expression.Expr :=
      (expandCall fn opExpr args).map fun x => fold ctx.foldFactory ctx.evalFuel (simp ctx.spend x)
    if worthExpanding ctx.foldFactory fn args then (expand ()).getD e
    -- An argument built by a constructor is what a body's testers and destructors reduce,
    -- so expanding the call can fold away the copies the shape test counts. That is
    -- decided on the result: one trial, made only for such a call and only when the
    -- function has no preconditions, kept when strictly smaller than the call.
    else if fn.preconditions.isEmpty && args.any (LExpr.isConstrApp ctx.foldFactory) then
      match expand () with
      | some r => if LExpr.size _ r < LExpr.size _ e then r else e
      | none => e
    else e

/-- Substitute the known value of each variable `e` mentions whose value is more than
    one node, where doing so shrinks the expression. Whether it shrinks has to be
    checked at the use: a constructor substituted into a destructor collapses, the same
    constructor substituted into an opaque call does not.

    A substitution can expose a variable the expression did not mention before: with
    `z := Cons(1, x)`, folding `List..tail(z)` leaves `x`. Such a variable is tried in
    turn, so a chain of values folds as far as each step shrinks it. Each variable is
    tried at most once, and only a variable with a recorded value spends fuel, so the
    fuel, the number of recorded values, bounds the substitutions tried without
    cutting off one that comes after many unrecorded variables. A variable's
    occurrences are substituted together, so `getFvars`' repetitions are dropped. -/
def trySubstWide (ctx : Ctx) (e : Expression.Expr) : Expression.Expr :=
  let distinct (t : Expression.Expr) := (HasFvars.getFvars t).eraseDups
  let rec go (fuel : Nat) (tried : List String) (todo : List CoreIdent)
      (acc : Expression.Expr) : Expression.Expr :=
    match fuel, todo with
    | 0, _ | _, [] => acc
    | fuel + 1, x :: rest =>
      if tried.contains x.name then go (fuel + 1) tried rest acc else
      let tried := x.name :: tried
      match Map.find? ctx.values x with
      | none => go (fuel + 1) tried rest acc
      | some v =>
        if LExpr.size _ v ≤ 1 then go fuel tried rest acc else
        let cand := foldWith ctx.foldFactory ctx.evalFuel x v acc
        if LExpr.size _ cand < LExpr.size _ acc then
          let exposed := (distinct cand).filter (fun y => !tried.contains y.name)
          go fuel tried (rest ++ exposed) cand
        else go fuel tried rest acc
  termination_by (fuel, todo.length)
  go ctx.values.toList.length [] (distinct e) e

/-! ## Expressions -/

/-- Expand the admissible `inline` calls in `e`, bottom-up.

    Folding is deliberately not done here. `fold` is `LExpr.eval`, which already
    recurses over the whole expression it is given, so calling it at each node would
    re-evaluate every subtree once per level above it — quadratic in the size of the
    expression, and multiplied again by the depth of nested expansion. The caller
    folds once per round instead, which reaches every foldable position anyway.

    The recursion does not descend through `.abs` or `.quant`. A binder's body is
    an open term whose `bvar`s refer to the binder, so folding it in isolation
    would produce dangling de Bruijn indices; keeping the recursion to the
    non-binder positions of a closed expression means every term `fold` sees is
    itself closed. An applied binder — a `have`, which is `.app (.abs ..) v` — is
    still handled: the round's fold beta-reduces it and the body reaches the top
    level, closed, on the second expansion pass of `simplifyExpr`. -/
def tryExpandRecursively (ctx : Ctx) (e : Expression.Expr) : Expression.Expr :=
  let rebuilt := match e with
    | .const _ _ | .op _ _ _ | .bvar _ _ | .fvar _ _ _ => e
    | .abs _ _ _ _ | .quant _ _ _ _ _ _ => e
    | .app m f a => .app m (tryExpandRecursively ctx f) (tryExpandRecursively ctx a)
    | .eq m a b => .eq m (tryExpandRecursively ctx a) (tryExpandRecursively ctx b)
    | .ite m c t f =>
      .ite m (tryExpandRecursively ctx c) (tryExpandRecursively ctx t)
        (tryExpandRecursively ctx f)
  -- `tryExpand` recurses only after spending fuel, so the guard always holds there; it
  -- is what makes the recursion visibly decreasing.
  tryExpand ctx
    (fun c x => if _h : c.expandFuel < ctx.expandFuel then tryExpandRecursively c x else x) rebuilt
  termination_by (ctx.expandFuel, sizeOf e)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.left; assumption)
      | (apply Prod.Lex.right; simp_wf; omega)

def simplifyExpr (ctx : Ctx) (e : Expression.Expr) : Expression.Expr :=
  -- Substitution and folding happen in one traversal: `eval` receives every known
  -- value at once rather than a whole-expression pass per variable.
  --
  -- Two expansion passes rather than a fixpoint. The second one matters: a call over
  -- a symbolic variable may not be worth expanding, and substituting that variable's
  -- value can make it worth expanding -- `dup(a)` with `a` bound to `3` reduces only
  -- once `3` is in place. A fixpoint would keep looking for further such steps at a
  -- cost of one full traversal plus one eval per variable per round, which would
  -- dominate the pipeline.
  let expanded := tryExpandRecursively ctx e
  let substituted :=
    (LExpr.eval ctx.evalFuel ctx.foldFactory
      (Env.smallValues ctx.foldFactory ctx.values) expanded).fst
  -- A multi-node value has to earn its place, so it gets the per-variable check --
  -- but only once, and only for those values. That is a handful of passes over the
  -- expression rather than one per variable per round.
  let substituted := trySubstWide ctx substituted
  fold ctx.foldFactory ctx.evalFuel (tryExpandRecursively ctx substituted)

/-! ## Joins and base commands

What a traversal does between expressions: record a value, forget values a write
invalidates, merge what several predecessors know, and simplify one base command.
None of it depends on how statements are nested, so a traversal of structured bodies
and one of control-flow graphs share it. -/

/-- The context after `x` is written with the simplified value `v`: `x` and every
    value mentioning it are invalidated, and `v` becomes `x`'s value unless it reads
    `x` itself, which would make a later substitution loop. -/
def Ctx.record (ctx : Ctx) (x : CoreIdent) (v : Expression.Expr) : Ctx :=
  let ctx := ctx.invalidate [x]
  if (HasFvars.getFvars (P := Core.Expression) v).any (fun f => f.name == x.name)
    then ctx
    else { ctx with values := ctx.values.insert x v }

/-- The definitions a set of predecessor contexts agree on: for each variable in
    `assigned` that is not in `scopedNames`, the value every context in `live` records for
    it, provided they all record the same one and it mentions none of `scopedNames`. -/
def agreedDefs (live : List Ctx) (assigned : List CoreIdent) (scopedNames : List String) :
    List (CoreIdent × Expression.Expr) :=
  assigned.filterMap fun x =>
    if scopedNames.contains x.name then none else
    match live.map (fun (c : Ctx) => Map.find? c.values x) with
    | some (v : Expression.Expr) :: rest =>
      if rest.all (· == some v) &&
          !(HasFvars.getFvars (P := Core.Expression) v).any
            (fun f => scopedNames.contains f.name)
        then some (x, v) else none
    | _ => none

/-- Record a list of definitions in a context, in order. -/
def recordAgreed (base : Ctx) (agreed : List (CoreIdent × Expression.Expr)) : Ctx :=
  agreed.foldl (fun c (x, v) => { c with values := c.values.insert x v }) base

/-- **Join.** The context after control flow merges: `base` with the variables in
    `assigned` forgotten, then given back the values every live predecessor agrees on.

    Only agreement is recorded. A value the predecessors disagree on could be merged as
    an `ite` over the path taken, but that would enlarge every later use of the name. -/
def Ctx.join (base : Ctx) (live : List Ctx) (assigned : List CoreIdent)
    (scopedNames : List String) : Ctx :=
  recordAgreed (base.invalidate assigned) (agreedDefs live assigned scopedNames)

/-- **One base command.** Simplify its expressions in `ctx`, and return the context
    that follows it: a deterministic write records its simplified value, a
    nondeterministic one forgets the variable, and the other commands change nothing. -/
def simpCmd (ctx : Ctx) (c : Imperative.Cmd Expression) : Imperative.Cmd Expression × Ctx :=
  match c with
  | .init x ty (.det e) md =>
    let e := simplifyExpr ctx e
    (.init x ty (.det e) md, ctx.record x e)
  | .init x ty .nondet md => (.init x ty .nondet md, ctx.invalidate [x])
  | .set x (.det e) md =>
    let e := simplifyExpr ctx e
    (.set x (.det e) md, ctx.record x e)
  | .set x .nondet md => (.set x .nondet md, ctx.invalidate [x])
  | .assert l b md => (.assert l (simplifyExpr ctx b) md, ctx)
  -- An assumption that simplifies to `true` stays: symbolic evaluation adds no path
  -- condition for it, and keeping it keeps the program's events one for one.
  | .assume l b md => (.assume l (simplifyExpr ctx b) md, ctx)
  | .cover l b md => (.cover l (simplifyExpr ctx b) md, ctx)

end Core.Simplify

end
