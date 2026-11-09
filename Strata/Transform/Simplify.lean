/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.Env
public import Strata.Transform.Simplify.Expr

/-! # Simplify

A Core-to-Core phase that replaces a program by a smaller one with the same
meaning.

It rewrites expressions: a call whose arguments are known becomes its value, an
`if-then-else` expression whose condition is known becomes its live branch, a decided equality
becomes a constant, an applied lambda is contracted, a function body is expanded
into its call, and a variable is replaced by its value. It then drops the
definitions nothing reads. Statements keep their shape, an `if` statement keeping both
arms even when its guard folds; only the expressions in them and the set of definitions
change.

Two of those rewrites copy. Expanding a function body substitutes the argument
into every occurrence of the parameter, and replacing a variable by its value
substitutes a whole term into every use. Applied wherever they are possible, they
make term size grow exponentially in the number of nested calls or guarded writes.
`worthExpanding` and `trySubstWide` carry the conditions that stop that, each
admitting its rewrite only where it cannot compound. A call whose expansion is
declined is left for the SMT encoder to emit once as a shared definition.

The phase carries a variable's value forward from its definition and folds under
it, which is what lets `int.add(a, 1)` become `4` when `a` is `3`. It is
model-preserving and establishes no `ProgramFact`. It asks three things of the
program it runs on — structured bodies, no procedure call, and no function
carrying a precondition (`noCFGBodies`, `noCalls`, `noPrecondsFromFuncs`) — so a
pipeline can place it anywhere past those where it wants smaller terms.
-/

public section

namespace Core.Simplify

open Lambda Imperative

/-! ## Inline pruning on a whole program -/

/-- The datatypes a value of which can carry a lambda: those with a function-typed
    constructor field, and those with a field whose type reaches such a datatype.

    A value, not a type, is what carries an abstraction, so a parameter of a plain
    datatype type is enough to bring one into a call. `Transformer`, holding an
    `int -> int` field, is the reason this is computed rather than assumed away. -/
def arrowCarryingDatatypes (p : Program) : List String :=
  let datatypes := p.decls.filterMap fun d =>
    match d with | .type (.data block) _ => some block | _ => none
  let all := datatypes.flatten
  let fieldTypes (d : Lambda.LDatatype Unit) : List LMonoTy :=
    d.constrs.flatMap (fun c => c.args.map (·.2))
  let direct := all.filterMap fun d =>
    if (fieldTypes d).any LMonoTy.containsArrow then some d.name else none
  -- One round per datatype suffices: each round adds at least one name or stops.
  let rec saturate (n : Nat) (acc : List String) : List String :=
    match n with
    | 0 => acc
    | n + 1 =>
      let grown := all.filterMap fun d =>
        if acc.contains d.name then none
        else if (fieldTypes d).any (LMonoTy.mentionsTyCon acc) then some d.name else none
      if grown.isEmpty then acc else saturate n (acc ++ grown)
  saturate all.length direct

/-- The names `mayEliminateLambdas` treats as carrying a lambda: the datatypes of
    `arrowCarryingDatatypes`, and the program's functions whose expansion erases a
    lambda, closed under calls. A function that calls one of them keeps `inline` too,
    since nothing else expands the call that reaches the lambda: `simplify` may decline
    the expansion, and symbolic evaluation then sees the weakened attribute. -/
def lambdaCarriers (p : Program) : List String :=
  let fns := p.decls.flatMap fun d =>
    match d with | .func fn _ => [fn] | .recFuncBlock fns _ => fns | _ => []
  -- Each round adds at least one function or stops.
  let rec saturate (n : Nat) (acc : List String) : List String :=
    match n with
    | 0 => acc
    | n + 1 =>
      let grown := fns.filterMap fun fn =>
        if acc.contains fn.name.name then none
        else if mayEliminateLambdas acc fn then some fn.name.name else none
      if grown.isEmpty then acc else saturate n (acc ++ grown)
  saturate (fns.length + 1) (arrowCarryingDatatypes p)

/-- The program with `stripInlineFunc` applied to the functions it declares, against a
    carrier list the caller already has.

    Those declarations are where the attribute comes from, and symbolic evaluation
    registers them into its factory as it walks the program, so pruning only the factory
    it starts from leaves them untouched. -/
def withoutInlineProgramWith (carriers : List String) (p : Program) : Program :=
  { p with decls := p.decls.map fun d =>
      match d with
      | .func fn md => .func (stripInlineFunc carriers fn) md
      | .recFuncBlock fns md => .recFuncBlock (fns.map (stripInlineFunc carriers)) md
      | other => other }

/-! ## Statements

The traversal threads `Ctx.values` through a statement list. A variable whose value
stops being known — because it is havoc'd, or written in a branch that was not taken
apart — is dropped from the map rather than kept stale. -/

/-- `names` with the names of `vs` added. -/
def insertNames (names : Std.HashSet String) (vs : List CoreIdent) : Std.HashSet String :=
  vs.foldl (fun n y => n.insert y.name) names

def forgetAssigned (ctx : Ctx) (ss : List Statement) : Ctx :=
  let names := ss.foldl (fun n s => insertNames n (Stmt.modifiedOrDefinedVars s false)) {}
  ctx.invalidate names

/-- The arms of a branch that can run, given its simplified guard, in the order
    `[then, else]` they are passed in. A guard folded to a constant rules one arm out;
    anything else, a nondeterministic guard included, leaves both. Never empty. -/
def liveArms {α : Type} (cond : ExprOrNondet Expression) (arms : List α) : List α :=
  match cond, arms with
  | .det c, [thenArm, elseArm] =>
    if c.isTrue then [thenArm] else if c.isFalse then [elseArm] else [thenArm, elseArm]
  | _, arms => arms

/-- What a statement or statement list writes: the names of the variables
    `Stmt.modifiedOrDefinedVars _ false` lists, and the names of those
    `Stmt.definedVars _ false` lists. -/
structure Writes where
  vars : Std.HashSet String := {}
  defined : Std.HashSet String := {}

/-- `w` with what `s` writes, read off the statement itself. -/
def Writes.insertStmt (s : Statement) (w : Writes) : Writes :=
  { vars := insertNames w.vars (Stmt.modifiedOrDefinedVars s (excludeScoped := false))
    defined := insertNames w.defined (Stmt.definedVars s (excludeScoped := false)) }

/-- What two statement lists write together. -/
def Writes.union (a b : Writes) : Writes :=
  { vars := a.vars ∪ b.vars, defined := a.defined ∪ b.defined }

mutual

/-- Simplify one statement, returning the statements it becomes, the context
    that follows it, and the function adding what `s` writes to a write set.

    The write sets are built bottom-up from the nested statements, so a branch reads
    them in time proportional to their size rather than walking its arms again. -/
def simpStmt (ctx : Ctx) (s : Statement) : List Statement × Ctx × (Writes → Writes) :=
  match s with
  | .cmd (.cmd c) =>
    let (c, ctx) := simpCmd ctx c
    ([.cmd (.cmd c)], ctx, .insertStmt s)
  | .cmd (.call pname args md) =>
    let args := args.map fun a =>
      match a with
      | .inArg e => CallArg.inArg (simplifyExpr ctx e)
      | other => other
    ([Statement.call pname args md], forgetAssigned ctx [s], .insertStmt s)
  | .block label ss md =>
    let (ss, inner, w) := simpStmts ctx ss
    -- Declarations inside the block leave scope with it; values that were known
    -- before it survive unless the block wrote them.
    ([.block label ss md], { ctx with values := inner.values }.invalidate w.vars, w.union)
  | .ite cond ts es md =>
    -- A later phase reads a constant guard to decide which arm is unreachable and
    -- what its obligations become, so the branch stays even once the guard folds.
    let cond := match cond with
      | .det c => ExprOrNondet.det (simplifyExpr ctx c)
      | .nondet => .nondet
    let (ts, thenCtx, wt) := simpStmts ctx ts
    let (es, elseCtx, we) := simpStmts ctx es
    let w := wt.union we
    -- What is known after the branch is what every arm that can run agrees on. An
    -- arm whose guard has folded against it cannot run, so a decided branch carries
    -- the live arm's values forward, as evaluating the program would. Neither the
    -- variable nor its value may be arm-local, since both leave scope at the join.
    let ctx := ctx.join (liveArms cond [thenCtx, elseCtx]) w.vars w.defined
    ([.ite cond ts es md], ctx, w.union)
  | .loop guard measure invs body md =>
    -- A body that runs an unknown number of times invalidates what it writes, so
    -- it is simplified knowing nothing about those variables.
    let inner := forgetAssigned ctx body
    -- The guard, measure and invariants are evaluated at the loop head, where the same
    -- holds, so they are simplified in the same context as the body.
    let guard := match guard with
      | .det g => ExprOrNondet.det (simplifyExpr inner g)
      | .nondet => .nondet
    let measure := measure.map (simplifyExpr inner)
    let invs := invs.map fun (l, i) => (l, simplifyExpr inner i)
    let (body, _, w) := simpStmts inner body
    ([.loop guard measure invs body md], ctx.invalidate w.vars, w.union)
  | .exit label md => ([.exit label md], ctx, id)
  | .typeDecl tc md => ([Statement.typeDecl tc md], ctx, id)
  termination_by sizeOf s

/-- `simpStmt` over a list, threading the context, and returning what the list writes. -/
def simpStmts (ctx : Ctx) (ss : List Statement) : List Statement × Ctx × Writes :=
  match ss with
  | [] => ([], ctx, {})
  | s :: rest =>
    let (out, ctx, addWrites) := simpStmt ctx s
    let (outRest, ctx, wRest) := simpStmts ctx rest
    (out ++ outRest, ctx, addWrites wRest)
  termination_by sizeOf ss

end

/-! ## Dead definitions

Substituting a variable's value into its last use leaves the definition behind
with nothing reading it. -/

/-- `e` is a value of the factory `F` (`LExpr.isValue`) of type `ty`: a constant, a
    closed abstraction, or a constructor of `F` applied to values, a nullary one included
    (`None()`). A function of `F` applied to fewer arguments than it takes is
    a value too. The type is checked against `F` (`typeCheckWith`), so an operator whose
    annotation is not an instance of its signature in `F` has no type. This is a syntactic
    check, not `HasVal.valueOfTy` (a predicate on semantic values). -/
def isValueOfTy (F : Lambda.Factory CoreLParams) (ty : Expression.Ty) (e : Expression.Expr) :
    Bool :=
  Lambda.LExpr.isValue F e &&
  (match ty.toMonoType? with
   | some t => Lambda.LExpr.typeCheckWith F [] e == some t
   | none => false)

/-- The variables definitely defined at a point of a body, with their declared types:
    the input parameters the body never writes, and every deterministic `init` before
    the point in the same list or in an enclosing one. A definition inside an arm, a
    block or a loop body does not outlive it. -/
abbrev Defined := Std.HashMap String Expression.Ty

/-- `D` after the statement `s`: a deterministic `init` adds its variable. A dropped
    `init` counts too, since the original program runs it. -/
def Defined.after (D : Defined) : Statement → Defined
  | .cmd (.cmd (.init x ty (.det _) _)) => D.insert x.name ty
  | _ => D

/-- The input parameters the body `ss` never writes, at their declared types: they are
    definitely defined everywhere in the body. -/
def Defined.ofParams (inputs : @LMonoTySignature Unit) (ss : List Statement) : Defined :=
  let written :=
    insertNames {} (Block.modifiedOrDefinedVars (P := Expression) (C := Command) ss false)
  inputs.foldl (fun (D : Defined) (p : CoreIdent × LMonoTy) =>
    if written.contains p.1.name then D else D.insert p.1.name (.forAll [] p.2)) {}

/-- `e` is a variable that `D` records at type `ty`. -/
def isDefinedCopy (D : Defined) (ty : Expression.Ty) : Expression.Expr → Bool
  | .fvar _ y _ => D[y.name]? == some ty
  | _ => false

/-- **The right-hand side of `init x : ty := e` surely evaluates** where `D` holds:
    `e` is a value of type `ty` (`isValueOfTy`), or a variable `D` records at type
    `ty` (`isDefinedCopy`).

    The dead-definition sweep drops a definition only when this holds, because the
    backward simulation has to replay the dropped `init` in the original program, so
    the original must be able to evaluate its right-hand side there. A value evaluates
    to itself in every store, and a variable `D` records holds a value of its declared
    type, since in the single-assignment shape a front end produces nothing writes it
    between its definition and this point. Either way the
    result is a value of type `ty`, which is everything the semantics asks of an `init`.
    Nothing else is known to evaluate: an operator application such as `Real.Add(a, b)`,
    a tester, a destructor or a call may get stuck, and so may a variable defined only
    in one arm of a branch. The check is one pass over `e` with one factory lookup per
    application, or one map lookup. -/
def surelyEvaluates (F : Lambda.Factory CoreLParams) (D : Defined) (ty : Expression.Ty)
    (e : Expression.Expr) : Bool :=
  isValueOfTy F ty e || isDefinedCopy D ty e

/-- The variable a statement defines and the sweep may drop, if there is one: an `init`
    whose right-hand side surely evaluates (`surelyEvaluates`).

    A nondeterministic `init` is kept even when nothing reads it. A `set` is not a
    definition: dropping it would change the value of a variable that outlives it. -/
def definedBy (F : Lambda.Factory CoreLParams) (D : Defined) : Statement → Option CoreIdent
  | .cmd (.cmd (.init x ty (.det e) _)) => if surelyEvaluates F D ty e then some x else none
  | _ => none

/-- Insert `ys` into `live`, consing onto `added` each name that was not in `live`. -/
def insertTracked (live : Std.HashSet String) (added ys : List String) :
    Std.HashSet String × List String :=
  ys.foldl (fun (l, a) y =>
    let (had, l) := l.containsThenInsert y
    (l, if had then a else y :: a)) (live, added)

mutual
/-- `budget` less the number of statements in `s`, nested ones included, or `0` once
    that reaches `0`. -/
def countDownStmt (budget : Nat) (s : Statement) : Nat :=
  match s with
  | .ite _ ts es _ => countDown (countDown (budget - 1) ts) es
  | .block _ ss _ | .loop _ _ _ ss _ => countDown (budget - 1) ss
  | _ => budget - 1
  termination_by sizeOf s

/-- `budget` less the number of statements in `ss`, nested ones included, or `0` once
    that reaches `0`. Takes time proportional to the smaller of the two. -/
def countDown (budget : Nat) (ss : List Statement) : Nat :=
  match budget, ss with
  | 0, _ | _, [] => budget
  | _, s :: rest => countDown (countDownStmt budget s) rest
  termination_by sizeOf ss
end

/-- Whether `a` has fewer statements than `b`, nested ones included. Both are counted
    down from `k = 1, 2, 4, …` until one of them is exhausted, so this takes time
    proportional to the smaller count. -/
def fewerStmts (a b : List Statement) (k : Nat := 1) (fuel : Nat := 64) : Bool :=
  let ra := countDown k a
  let rb := countDown k b
  match ra, rb, fuel with
  | 0, 0, fuel + 1 => fewerStmts a b (2 * k) fuel
  | _, _, _ => ra > rb

mutual
/-- Sweep the blocks nested in `stmt` with `live`, the names live after it, and `D`, the
    names definitely defined before it. Also returns the names live before the swept
    statement, `live` with every variable it reads or writes (`Stmt.getVars`,
    `Stmt.modifiedOrDefinedVars`), and `added` with each name this inserted into `live`
    consed on.

    A nested list's own sweep returns `live` with what the list reads and writes, so a
    compound statement adds only the variables of its guard, measure and invariants to
    what its nested lists return, instead of walking them again. The arms of a branch
    are swept by `dropDeadDefsArms`, the one with fewer statements first. -/
def dropDeadDefsStmt (F : Lambda.Factory CoreLParams) (D : Defined) (live : Std.HashSet String)
    (added : List String) (stmt : Statement) :
    Statement × Std.HashSet String × List String :=
  match stmt with
  | .ite cond thenSs elseSs md =>
    let (thenSs, elseSs, live, added) :=
      if fewerStmts elseSs thenSs then
        let (elseSs, thenSs, live, added) := dropDeadDefsArms F D live added elseSs thenSs
        (thenSs, elseSs, live, added)
      else dropDeadDefsArms F D live added thenSs elseSs
    let (live, added) := insertTracked live added (cond.getVars.map (·.name))
    (.ite cond thenSs elseSs md, live, added)
  | .block label inner md =>
    let (inner, live, added) := dropDeadDefsAux F D live added inner
    (.block label inner md, live, added)
  | .loop guard measure invs body md =>
    let (body, live, added) := dropDeadDefsAux F D live added body
    let heads := Stmt.getVars (.loop guard measure invs [] md : Statement)
    let (live, added) := insertTracked live added (heads.map (·.name))
    (.loop guard measure invs body md, live, added)
  | other =>
    let (live, added) := insertTracked live added ((Stmt.getVars other ++
      Stmt.modifiedOrDefinedVars other (excludeScoped := false)).map (·.name))
    (other, live, added)
  termination_by sizeOf stmt

/-- Sweep `first` and `second`, the two arms of a branch, both with `live`, the names
    live after the branch. Returns them swept, `live` with what either arm reads or
    writes, and `added` with each name this inserted into `live` consed on.

    `live` is updated in place rather than copied: the names the sweep of `first`
    inserts are erased before `second` is swept and inserted again after it, which costs
    time proportional to their number. An empty `first` inserts nothing, so `second` is
    then swept with `live` directly. Passing the arm with fewer statements as `first`
    makes each statement part of an erased arm at most log₂ n times, for n statements
    in all, whichever arms the branches are nested in: each time, the branch around it
    holds at least twice as many statements as the erased arm. -/
def dropDeadDefsArms (F : Lambda.Factory CoreLParams) (D : Defined) (live : Std.HashSet String)
    (added : List String) (first second : List Statement) :
    List Statement × List Statement × Std.HashSet String × List String :=
  if first.isEmpty then
    let (second, live, added) := dropDeadDefsAux F D live added second
    (first, second, live, added)
  else
    let (first, live, addedFirst) := dropDeadDefsAux F D live [] first
    let live := addedFirst.foldl (·.erase ·) live
    let (second, live, added) := dropDeadDefsAux F D live added second
    let (live, added) := insertTracked live added addedFirst
    (first, second, live, added)
  termination_by sizeOf first + sizeOf second
  decreasing_by all_goals cases first <;> cases second <;> simp <;> omega

/-- `dropDeadDefs`, also returning the names live before the swept list, and `added`
    with each name this inserted into `liveOnExit` consed on. -/
def dropDeadDefsAux (F : Lambda.Factory CoreLParams) (D : Defined) (liveOnExit : Std.HashSet String)
    (added : List String) (ss : List Statement) :
    List Statement × Std.HashSet String × List String :=
  match ss with
  | [] => ([], liveOnExit, added)
  | stmt :: rest =>
    let (rest, live, added) := dropDeadDefsAux F (D.after stmt) liveOnExit added rest
    let dead := match definedBy F D stmt with
      | some x => !live.contains x.name
      | none => false
    if dead then (rest, live, added)
    else
      -- A variable read keeps the definition that supplies its value; a
      -- variable assigned keeps the `init` that declares it, since dropping the
      -- declaration would leave a later `set` or `havoc` with nothing to assign.
      let (stmt, live, added) := dropDeadDefsStmt F D live added stmt
      (stmt :: rest, live, added)
  termination_by sizeOf ss
end

/-- Drop definitions nothing reads, given the names live on exit and the names `D`
    definitely defined on entry.

    Only the definitions `definedBy` names are dropped: those whose right-hand side
    surely evaluates (`surelyEvaluates` gives the rule and the reason). A `havoc`'d or
    nondeterministic declaration is kept too: it constrains nothing but it declares a
    variable something later may refer to. One
    backward pass suffices for a statement list in order, and a nested arm, block or loop body is
    swept with the same exit set, since nothing between it and the exit could read a
    definition local to it.

    That holds for a loop body even though it repeats: a declaration inside the body
    is re-executed each iteration, so no later iteration can read the previous one's,
    and a guard or invariant cannot read it either, being outside the body's scope.
    Reads within one iteration are covered by the backward pass over the body. -/
def dropDeadDefs (F : Lambda.Factory CoreLParams) (D : Defined) (liveOnExit : Std.HashSet String)
    (ss : List Statement) : List Statement :=
  (dropDeadDefsAux F D liveOnExit [] ss).1

/-! ## Procedures and programs -/

/-- The factory a program's expressions are simplified against: the factory the
    pipeline has accumulated, plus the constructors, testers and destructors
    generated for every datatype the program declares, plus every function the
    program declares.

    The accumulated factory rather than the pristine `Core.Factory`, because
    earlier phases change it: monomorphization drops polymorphic entries, adds
    specializations under mangled names, and rewrites the program's references to
    match, so a factory rebuilt from scratch would fail to resolve them and fold
    nothing. It is also where a caller's extra functions arrive.

    The datatype-generated functions are what let this phase fold a destructor or
    tester applied to a constructor (`List..head(Cons(x, xs))` to `x`), since those
    functions carry the `inlineIfConstr`/`evalIfConstr` attributes that `fold`
    keeps. Without them the call would find no definition and be left as is.
    Datatype functions are registered the same way `buildEnv` registers them. -/
def programFactory (p : Program) : Transform.CoreTransformM (Lambda.Factory CoreLParams) := do
  -- Datatypes first, so a function declared over them resolves.
  let mut F ← Transform.getFactory
  for decl in p.decls do
    match decl with
    | .type (.data d) _ =>
      let dtF ← Transform.liftDiag (Lambda.genBlockFactory (T := CoreLParams) d)
      F ← Transform.liftDiag (F.addFactory dtF)
    | _ => pure ()
  -- The program's own declaration of a function wins over a factory entry of the same
  -- name: an earlier phase may have registered a copy the program has since changed.
  -- `precondElim` registers each function with its preconditions and strips them from
  -- the declaration, and a function with preconditions is never expanded.
  let declared := p.decls.flatMap fun
    | .func func _ => [func.toLFunc]
    | .recFuncBlock funcs _ => funcs.map (·.toLFunc)
    | _ => []
  let override (fn : Lambda.LFunc CoreLParams) : Lambda.LFunc CoreLParams :=
    (declared.find? (·.name.name == fn.name.name)).getD fn
  F := Lambda.Factory.ofArray (F.toArray.map override)
  return declared.foldl Lambda.Factory.pushIfNew F

/-- Simplify a procedure's specification and body.

    A parameter has no known value, so nothing is substituted for it. The
    specification is simplified with an empty environment, which expands and folds
    without substituting: an `inline` call in a `requires` or `ensures` clause is
    expanded there, so the obligations its body carries — a narrowing cast's range
    check, for instance — are visible in the contract just as they are in the body.

    Liveness for the final sweep is seeded from the outputs and from the free
    variables of the specification, so a definition a contract mentions is never
    dropped. The input parameters the body never writes are definitely defined
    throughout it (`Defined.ofParams`). -/
def simplifyProcedure (base : Ctx) (proc : Procedure) : Procedure :=
  let simpCheck (c : Procedure.Check) : Procedure.Check :=
    { c with expr := simplifyExpr base c.expr }
  let proc := { proc with spec := { proc.spec with
    preconditions := proc.spec.preconditions.map (fun (l, c) => (l, simpCheck c))
    postconditions := proc.spec.postconditions.map (fun (l, c) => (l, simpCheck c)) } }
  match proc.body with
  | .cfg _ => proc
  | .structured ss =>
    let (ss, _, _) := simpStmts base ss
    let specNames := ((proc.spec.preconditions ++ proc.spec.postconditions).flatMap
      (fun (_, c) => HasFvars.getFvars c.expr)).map (·.name)
    let live := (proc.header.outputs.keys.map (·.name) ++ specNames).foldl
      (fun (s : Std.HashSet String) n => s.insert n) {}
    { proc with body :=
      .structured (dropDeadDefs base.factory (Defined.ofParams proc.header.inputs ss) live ss) }

/-- Simplify a lemma's formula under its outer universal quantifiers.

    `simplifyExpr` does not descend under a binder, so a lemma `forall x :: e` would be
    left as written. Each outer `forall` is opened onto a fresh free variable, the body is
    simplified as an assertion's condition would be, and the variable is bound again. The
    trigger is kept as written. -/
def simplifyLemma (base : Ctx) (e : Expression.Expr) : Expression.Expr :=
  go (numForalls e) e
where
  numForalls : Expression.Expr → Nat
    | .quant _ .all _ _ _ body => numForalls body + 1
    | _ => 0
  go : Nat → Expression.Expr → Expression.Expr
    | n + 1, .quant m .all name ty tr body =>
      .quant m .all name ty tr (underBinder ty body fun b => go n b.val).fst
    | _, e => simplifyExpr base e

/-- Simplify every procedure and lemma in a program. The context, and with it the folding factory,
    is built once and shared by every procedure, specification clause and lemma. The flag
    says whether the program changed, so a caller can iterate to a fixpoint. -/
def runSimplify (p : Program) : Transform.CoreTransformM (Bool × Program) := do
  let base := Ctx.ofFactory (← programFactory p) (lambdaCarriers p)
  let decls := p.decls.map fun decl =>
    match decl with
    | .proc proc md => .proc (simplifyProcedure base proc) md
    | .lemma l md => .lemma { l with e := simplifyLemma base l.e } md
    | other => other
  let p' := { p with decls := decls }
  return (decide (p' ≠ p), p')

end Core.Simplify

/-- Simplification pipeline phase.

    Model-preserving: every rewrite replaces an expression by one that is equal in
    every model, and a statement by statements with the same effect. Nothing is
    over-approximated, so no obligation becomes easier than it was.

    It requires bodies without calls; every pipeline that runs it eliminates them first.
    It accepts loops: a loop body is simplified knowing nothing about the variables it
    writes, and the unit tests pin that behavior. Its correctness theorem covers
    loop-free bodies only, and states that as a hypothesis. It also requires that
    no program function carries a precondition: expanding a call replaces it by the
    function's body, which is only right where the precondition holds, and the
    evaluator's own expansion does not look at preconditions. `PrecondElim` runs
    first and turns each precondition into an `assert` at its call sites. It establishes no
    fact: it eliminates no mutation, and it keeps every statement's shape. It preserves
    `staticSingleAssignment` because it introduces no write, which is what lets a pipeline place it anywhere it wants
    smaller terms. It preserves `hasObligationForm` for the same reason: an `assume`,
    `assert`, `cover` or `init` keeps its kind with its expression rewritten, an
    `ite *` keeps its nondeterministic guard and both arms, and the sweep only deletes
    `init`s. A deterministic `if` keeps both arms, and is not in obligation form to begin
    with.

    `noBetaRedexes` is the one fact it cannot claim. Contracting a redex is among
    its rewrites, but expanding a function body whose parameter is applied, given
    an abstraction as the actual argument, leaves an application of an abstraction
    behind.

    `typeAnnotated` has no executable check, so preserving it rests on an argument
    rather than on a test. Every expression this phase emits is built from annotated
    subterms of its input: a body substituted for a call and a value substituted for
    a variable both come from the program, and folding yields constants. No variable
    reference is minted, which is what `CallElim` does when it replaces a callee's
    formals with the caller's variables, and why that phase cannot claim the fact. -/
def Core.simplifyPhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "simplify" Core.Simplify.runSimplify
    (requires := factSet![.noCFGBodies, .noCalls, .noPrecondsFromFuncs])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment,
                         .noPrecondsFromFuncs, .noNondetGuards, .hasObligationForm,
                         .noProcedureContracts,
                         .noPolymorphicProcedures, .noPolymorphicFunctions,
                         .typeAnnotated, .noInits, .treeForm, .exitsCovered])
