/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.Simplify
public import Strata.Transform.ContextualRewrite.Rules

/-! # Contextual rewriting

This phase rewrites the goal of each `assert` under the facts that hold where it is checked,
and replaces the goal by `true` when the rewrite gives `true`. Every other goal, every
`cover`, every label and all metadata are left as written, and no statement or block is
added, removed or reordered. The verifier reports a goal that is literally `true` as passed
without calling a solver. The rewriting is done by the engine of
`ContextualRewrite.Engine` with the rules of `ContextualRewrite.Rules`.

The phase walks each procedure body from its start, keeping the facts that hold in every
state that reaches the current point. At the start of a body, and at a lemma, the facts are
those the ground axioms declared before it give; a lemma's goal is rewritten under them. A
body starts without the facts that mention one of its parameters or a variable it declares,
since an axiom says nothing about those.

Facts are learned from:

* `assume e`: `e`;
* `init x := e`: `x == e`, when `e` does not mention `x` and has no bound variable;
* the condition `c` of an `if`: `c` in the then branch, `¬c` in the else branch;
* the guard `g` of a loop: `g` in the body, `¬g` after the loop.

Facts are forgotten:

* a write to a variable (`set`, `havoc`) forgets the facts that mention it. An `init` forgets
  nothing: its variable is not defined before it, and the facts that hold mention only
  defined variables;
* a call forgets the facts that mention its output and in-out arguments, the only variables
  it writes; the callee's postconditions are not assumed;
* a loop starts from the facts before it without those that mention a variable its body
  writes, since the others hold at the start of every iteration; its invariants are not
  assumed;
* where paths meet, only the facts that hold on each of them are kept: after an `if`, and at
  the end of a `block` that an `exit` can leave early;
* the end of a block, of a branch and of a loop body forgets the facts that mention a
  variable declared in it, since the variable is not defined after it.

A point that no state reaches has every fact, so its goals become `true`: after an
assumption the engine finds contradictory with the facts before it, and after an `exit`.

A procedure whose body is a control-flow graph, and an abstract one, are left as they are.

The phase records these statistics:

* `ContextualRewrite.proved`: the number of `assert` goals and lemmas replaced by `true`;
* `ContextualRewrite.deadPaths`: the number of assumptions, ground axioms, conditions and
  guards that the engine finds contradictory with the facts before them, where those facts
  are not already contradictory;
* `ContextualRewrite.budgetExhausted`: the number of goals not replaced whose rewriting ran
  out of steps;
* `ContextualRewrite.skippedLarge`: the number of goals, assumptions, conditions and ground
  axioms left alone because their trees have more than `maxTreeSize` nodes.

## Correctness

The phase is model-preserving: a goal is replaced by `true` only where it is `true`
(`Core.contextualRewritePhase`). -/

namespace Core.ContextualRewrite

open Lambda Imperative

public section

/-! ## Statistics -/

/-- Statistics keys of the phase. -/
inductive Stats where
  /-- `assert` goals and lemmas replaced by `true`. -/
  | proved
  /-- Assumptions, ground axioms, conditions and guards found contradictory with the facts
      before them. -/
  | deadPaths
  /-- Goals not replaced whose rewriting ran out of steps. -/
  | budgetExhausted
  /-- Goals, assumptions, conditions and ground axioms left alone because their trees are
      larger than `maxTreeSize`. -/
  | skippedLarge

#derive_prefixed_toString Stats "ContextualRewrite"

/-- The counts of a walk: each field counts the statistics key of the same name. -/
structure Counts where
  proved : Nat := 0
  deadPaths : Nat := 0
  budgetExhausted : Nat := 0
  skippedLarge : Nat := 0

/-- The walk's monad: it counts what happens to goals and assumptions. -/
abbrev WalkM := StateM Counts

/-! ## Goals and assumptions -/

/-- The goal `e` under the facts `fs`: `true` when it rewrites to `true`, else `e`. A goal
    that is already `true` is left alone. -/
def replaceGoal (env : Env Theories) (fs : Facts) (e : Expression.Expr) :
    WalkM Expression.Expr := do
  if e.isTrue then return e
  if fs.isDead then
    modify fun c => { c with proved := c.proved + 1 }
    return .true valueLoc
  let (r, st) := rewrite env fs e
  if r.isTrue then
    modify fun c => { c with proved := c.proved + 1 }
    return .true valueLoc
  modify fun c => { c with
    budgetExhausted := c.budgetExhausted + (if st.exhausted then 1 else 0)
    skippedLarge := c.skippedLarge + (if st.tooLarge then 1 else 0) }
  return e

/-- The facts after assuming `e` where `fs` holds (`Facts.assume`). -/
def assumeFact (env : Env Theories) (fs : Facts) (e : Expression.Expr) : WalkM Facts := do
  if fs.isDead then return fs
  let fs' := fs.assume env e
  modify fun c => { c with
    deadPaths := c.deadPaths + (if fs'.isDead then 1 else 0)
    skippedLarge := c.skippedLarge + (if env.enabled && tooLarge e then 1 else 0) }
  return fs'

/-- The facts where the condition `c` has the value `b`, given the facts `fs` before it. A
    nondeterministic condition gives nothing. -/
def assumeCond (env : Env Theories) (fs : Facts) (c : ExprOrNondet Expression) (b : Bool) :
    WalkM Facts :=
  match c with
  | .det e => assumeFact env fs (if b then e else mkNot e)
  | .nondet => pure fs

/-- The facts after `init x : ty := e` where `fs` holds: `fs`, and `x == e` when `e` does not
    mention `x` and has no bound variable. No fact of `fs` that holds mentions `x`, which is not
    defined before its `init`, so none is forgotten. -/
def defineVar (env : Env Theories) (fs : Facts) (x : CoreIdent) (ty : Expression.Ty)
    (e : Expression.Expr) : WalkM Facts :=
  if e.hasBVar || (HasFvars.getFvars (P := Expression) e).contains x then pure fs
  else assumeFact env fs (.eq valueLoc (.fvar valueLoc x ty.toMonoType?) e)

/-- The command `c` with its goal rewritten if it is an `assert`, and the facts after it. -/
def stepCmd (env : Env Theories) (fs : Facts) (c : Command) : WalkM (Command × Facts) :=
  match c with
  | .cmd (.assert l e md) => do return (.cmd (.assert l (← replaceGoal env fs e) md), fs)
  | .cmd (.cover ..) => pure (c, fs)
  | .cmd (.assume _ e _) => do return (c, ← assumeFact env fs e)
  | .cmd (.init x ty (.det e) _) => do return (c, ← defineVar env fs x ty e)
  | .cmd (.init _ _ .nondet _) => pure (c, fs)
  | .cmd (.set x _ _) => pure (c, fs.forget [x])
  | .call _ _ args _ => pure (c, fs.forget (CallArg.getLhs args))

/-! ## Structured bodies -/

/-- The variables a statement writes or declares, at any depth (`Stmt.modifiedOrDefinedVars`),
    with the same for each statement of each statement list nested in it, in order. -/
inductive Writes where
  | mk (vars : Std.HashSet CoreIdent) (inner : List (List Writes))

/-- The variables of `w`. -/
def Writes.vars : Writes → Std.HashSet CoreIdent
  | .mk vs _ => vs

/-- The union of the variables of `ws`. -/
def Writes.union (ws : List Writes) : Std.HashSet CoreIdent :=
  ws.foldl (init := {}) fun acc w => acc.union w.vars

mutual

/-- The variables `s` writes or declares, computed from those of its parts. -/
def Writes.ofStmt (s : Statement) : Writes :=
  match s with
  | .cmd c => .mk (.ofList (Command.modifiedOrDefinedVars c)) []
  | .block _ ss _ | .loop _ _ _ ss _ =>
    let ws := Writes.ofStmts ss
    .mk (Writes.union ws) [ws]
  | .ite _ ts es _ =>
    let wt := Writes.ofStmts ts
    let we := Writes.ofStmts es
    .mk ((Writes.union wt).union (Writes.union we)) [wt, we]
  | .exit .. | .typeDecl .. => .mk {} []
  termination_by sizeOf s

/-- `Writes.ofStmt` of each statement of `ss`. -/
def Writes.ofStmts (ss : List Statement) : List Writes :=
  match ss with
  | [] => []
  | s :: rest => Writes.ofStmt s :: Writes.ofStmts rest
  termination_by sizeOf ss

end

/-- The writes of the statements of the `i`-th statement list nested in a statement whose
    writes are `w`, when `w` is known. -/
def Writes.part (w : Option Writes) (i : Nat) : Option (List Writes) :=
  w.bind fun | .mk _ inner => inner[i]?

/-- The facts at each `exit` that leaves a statement, with the label of the block it
    targets. -/
abbrev Exits := List (String × Facts)

/-- The result `r` of walking the statement list `ss` (the statements, the facts at its end
    and at its exits), with the facts that mention a variable `ss` declares dropped: the
    variable is not defined after the list. When `live` is false, nothing reads the facts at
    the end, and they are left as they are. -/
def closeScope (ss : List Statement) (live : Bool) (r : List Statement × Facts × Exits) :
    List Statement × Facts × Exits :=
  let xs := ss.filterMap fun | .cmd (.cmd (.init x ..)) => some x | _ => none
  if xs.isEmpty then r else
  (r.1, if live then r.2.1.forget xs else r.2.1, r.2.2.map fun (l, f) => (l, f.forget xs))

mutual

/-- Rewrite the goals of `s` under the facts `fs`. Returns the statement, the facts after it,
    and the facts at the exits that leave it. `w` gives the variables `s` and its parts
    write, when they are known; a loop computes those of its body when they are not.

    The facts after a `block` are the join of those at its end and those at each `exit`
    that targets it, and those after an `if` the join of those at the ends of its branches.
    `live` says whether anything after `s` reads the facts after it. When it is false, as for
    the last statement of a procedure body or of a loop body, a `block` and an `if` give no
    facts in place of the join, and the last statements of their lists are walked with `live`
    false too. A join takes time in the size of the facts, so this saves that time at each of
    a chain of nested `if`s, each the last statement of a branch of the one before, as in the
    obligations of the WP phase. -/
def stepStmt (env : Env Theories) (fs : Facts) (s : Statement) (w : Option Writes)
    (live : Bool) : WalkM (Statement × Facts × Exits) :=
  match s with
  | .cmd c => do
    let (c', fs') ← stepCmd env fs c
    return (.cmd c', fs', [])
  | .block l ss md => do
    let (ss', after, exits) := closeScope ss live (← stepStmts env fs ss (Writes.part w 0) live)
    let (mine, others) := exits.partition (·.1 == l)
    return (.block l ss' md,
      if live then mine.foldl (fun acc e => acc.join e.2) after else Facts.empty, others)
  | .ite c ts es md => do
    let (ts', ft, xt) := closeScope ts live
      (← stepStmts env (← assumeCond env fs c true) ts (Writes.part w 0) live)
    -- Release the then branch's facts before the else branch is walked: while they are
    -- held, the else branch shares its starting facts with them, and copies them to add one.
    let ft := if live then ft else Facts.empty
    let (es', fe, xe) := closeScope es live
      (← stepStmts env (← assumeCond env fs c false) es (Writes.part w 1) live)
    return (.ite c ts' es' md, if live then ft.join fe else Facts.empty, xt ++ xe)
  | .loop g m invs body md => do
    let wb := (Writes.part w 0).getD (Writes.ofStmts body)
    let entry := fs.forget (Writes.union wb).toList
    let (body', _, exits) := closeScope body false
      (← stepStmts env (← assumeCond env entry g true) body (some wb) false)
    return (.loop g m invs body' md, ← assumeCond env entry g false, exits)
  | .exit l _ => pure (s, Facts.unreachable, [(l, fs)])
  | .typeDecl .. => pure (s, fs, [])
  termination_by sizeOf s

/-- Rewrite the goals of `ss` in order, threading the facts; `ws` gives the writes of each
    statement, when they are known, and `live` whether anything after `ss` reads the facts
    at its end, as for its last statement (`stepStmt`). -/
def stepStmts (env : Env Theories) (fs : Facts) (ss : List Statement)
    (ws : Option (List Writes)) (live : Bool) : WalkM (List Statement × Facts × Exits) :=
  match ss with
  | [] => pure ([], fs, [])
  | s :: rest => do
    let (w, ws') := match ws with
      | some (w :: ws') => (some w, some ws')
      | _ => (none, none)
    let (s', fs1, x1) ← stepStmt env fs s w (live || !rest.isEmpty)
    let (rest', fs2, x2) ← stepStmts env fs1 rest ws' live
    return (s' :: rest', fs2, x1 ++ x2)
  termination_by sizeOf ss

end

/-! ## Programs -/

/-- The variables the body `b` declares, at any depth. -/
def bodyDeclaredVars : Imperative.Body Expression Command → List CoreIdent
  | .structured ss _ => Block.definedVars ss false
  | .cfg .. | .abstract => []

/-- Rewrite the goals of `proc`'s body under the facts `fs`. A parameter, or a variable the
    body declares (`bodyDeclaredVars`), may share its name with a variable an axiom
    constrains; the axiom says nothing about it, so the facts that mention it are dropped
    first. A body that is a control-flow graph, and an abstract one, are left as they are. -/
def rewriteProc (env : Env Theories) (fs : Facts) (proc : Procedure) : WalkM Procedure := do
  let fs := fs.forget
    (proc.header.inputs.keys ++ proc.header.outputs.keys ++ bodyDeclaredVars proc.body)
  match proc.body with
  | .structured ss opq =>
    let (ss', _, _) ← stepStmts env fs ss none false
    return { proc with body := .structured ss' opq }
  | .cfg .. | .abstract => return proc

/-- The declaration `d` with its goals rewritten under the facts `fs`, and the facts after
    it: a ground axiom adds its facts. -/
def rewriteDecl (env : Env Theories) (fs : Facts) (d : Decl) : WalkM (Decl × Facts) :=
  match d with
  | .proc proc md => do return (.proc (← rewriteProc env fs proc) md, fs)
  | .lemma l md => do return (.lemma { l with e := ← replaceGoal env fs l.e } md, fs)
  | .ax a _ => do return (d, ← if a.e.hasBVar then pure fs else assumeFact env fs a.e)
  | _ => pure (d, fs)

/-- Rewrite the goal of every lemma of `p`, and the goal of every `assert` in its procedure
    bodies. Facts are collected in declaration order, as obligation extraction builds the
    global path condition, so a procedure or lemma sees only the ground axioms declared before
    it. A lemma gives no fact. -/
def rewriteProgram (env : Env Theories) (p : Program) : WalkM Program := do
  let (ds, _) ← p.decls.foldlM (init := ([], Facts.empty)) fun (acc, fs) d => do
    let (d', fs') ← rewriteDecl env fs d
    return (d' :: acc, fs')
  return { p with decls := ds.reverse }

/-- The datatypes `p` declares. -/
def programDatatypes (p : Program) : List (LDatatype Unit) :=
  p.decls.flatMap fun | .type (.data block) _ => block | _ => []

/-- `p` with the copy marks (`FuncAttr.monoCopyOf`) dropped from the functions it declares.
    Monomorphization marks only the copies it adds to the function table, so a mark on a
    declared function, which only a program built through the API can carry, does not make
    it a copy: the theories read it by its own name, as the SMT encoder does. -/
def withoutCopyMarks (p : Program) : Program :=
  let unmark (f : Function) : Function :=
    { f with attr := Strata.DL.Util.FuncAttr.withoutMonoCopyOf f.attr }
  { p with decls := p.decls.map fun
      | .func f md => .func (unmark f) md
      | .recFuncBlock fs md => .recFuncBlock (fs.map unmark) md
      | d => d }

/-- The engine's environment for `p`: its function table, with the functions the program
    declares, without copy marks (`withoutCopyMarks`), and those of its datatypes. -/
def Env.ofProgram (p : Program) : Transform.CoreTransformM (Env Theories) := do
  return Env.ofFactory (← Simplify.programFactory (withoutCopyMarks p)) (programDatatypes p)

/-- Add the counts `n` to the statistics. -/
def recordCounts (n : Counts) : Transform.CoreTransformM Unit := do
  Transform.incrementStat s!"{Stats.proved}" n.proved
  Transform.incrementStat s!"{Stats.deadPaths}" n.deadPaths
  Transform.incrementStat s!"{Stats.budgetExhausted}" n.budgetExhausted
  Transform.incrementStat s!"{Stats.skippedLarge}" n.skippedLarge

/-- Run the phase on `p`. The program changes exactly when a goal is proved. -/
def runContextualRewrite (p : Program) : Transform.CoreTransformM (Bool × Program) := do
  let env ← Env.ofProgram p
  let (p', n) := (rewriteProgram env p).run {}
  recordCounts n
  return (n.proved != 0, p')

end -- public section

end Core.ContextualRewrite

public section

/-- The phase that rewrites each `assert` goal and each lemma under the facts that hold where
    it is checked, and replaces it by `true` when it rewrites to `true`.

    Model-preserving: a goal is replaced by `true` only when it is `true` wherever it has a
    value, in the states a run reaches it in with the assumptions before it holding, in every
    model of the function table where the ground axioms declared before the procedure hold
    and the datatype testers mean what they say; a lemma only when it is `true` wherever it
    has a value in every such model. No
    declaration, statement or block is added, removed or reordered.

    It requires:
    * `noCFGBodies`: the phase rewrites structured bodies, and leaves a control-flow graph as
      it is;
    * `noCalls`: the correctness theorems fix one table of procedures for the original and
      the rewritten program, but the phase rewrites the callees' bodies too. A call-free
      program reads no procedure table. Both default positions of the phase follow call
      elimination;
    * `typeAnnotated`: the engine reads the types of terms from their annotations;
    * `noPrecondsFromFuncs`: `precondElim` has run, so the precondition checks of the calls in
      a goal are separate `assert`s, which replacing the goal by `true` does not drop.

    It preserves every fact, since only the expressions of `assert`s and lemmas change, each to
    the constant `true`:
    * `wellFormedCalls`, `noCalls`: calls are unchanged;
    * `noCFGBodies`, `noCFGCycles`: each body keeps its kind, and each control-flow graph its
      blocks and jumps;
    * `noLoops`, `noLoopInvariants`, `noLoopMeasures`, `noNondetGuards`: loops and conditions
      are unchanged;
    * `uniqueInits`, `loopBodyNoInits`, `noInits`, `staticSingleAssignment`: `init`, `set` and
      `havoc` commands are unchanged;
    * `noBetaRedexes`, `typeAnnotated`: `true` has no redex and needs no annotation;
    * `noPrecondsFromFuncs`, `noPolymorphicFunctions`: functions are unchanged;
    * `noProcedureContracts`, `noPolymorphicProcedures`: procedure headers and contracts are
      unchanged;
    * `hasObligationForm`, `treeForm`, `exitsCovered`, `armsHaveObligations`: each statement
      keeps its kind and place, and an `assert` stays an `assert`.

    On a path whose assumptions the engine finds contradictory, every goal becomes `true`. In
    deductive mode the solver finds such a goal valid too, so the reported result is the same.
    Under `deductiveAssumingSatisfiablePaths`, whose premise is that every path can be taken,
    a goal that reduces to `false` on such a path is reported failing without the phase (at
    `--check-level full`: always false and reachable), and passed with it (at
    `--check-level full`: passed and unreachable), which is right for a goal that no state
    reaches. -/
def Core.contextualRewritePhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "contextualRewrite" Core.ContextualRewrite.runContextualRewrite
    (requires := factSet![.noCFGBodies, .noCalls, .noPrecondsFromFuncs, .typeAnnotated])
    (preserves := factSet![.wellFormedCalls, .noCFGBodies, .noCalls, .noLoops,
                         .noLoopInvariants, .noLoopMeasures, .uniqueInits, .loopBodyNoInits,
                         .staticSingleAssignment, .noBetaRedexes, .noPrecondsFromFuncs,
                         .noNondetGuards, .hasObligationForm, .noProcedureContracts,
                         .noPolymorphicProcedures, .noPolymorphicFunctions, .typeAnnotated,
                         .noInits, .treeForm, .exitsCovered, .armsHaveObligations,
                         .noCFGCycles])

end
