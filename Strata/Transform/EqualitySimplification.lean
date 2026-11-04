/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.Simplify

/-! # Equality simplification

A program often pins terms its goals mention to values: an axiom
`f(x) == "a"`, an `assume o == Some(3)`, a definition `init y := Cons(1, Nil)`, or a
bare boolean fact such as `b` or `!c`. This phase substitutes those values into
the goal of each `assert` and `cover` and folds the result with `LExpr.eval`.
Folding reduces a selector or tester applied to a constructor, so a goal often
becomes `true` or `false`, which the obligation checks then decide without a
solver; a goal that does not still reaches the solver smaller.

The rule is: in a fact `a == b`, a side that is a concrete value (a literal, or a
constructor applied to values) or a constructor application replaces the other
side. A concrete value wins over a constructor application, and two concrete
values give no rewrite.

The facts at a statement are the ground axioms, and the `assume`s and
definitions on the way to it. Each holds in every state that reaches the
statement, so each replacement leaves the goal's value unchanged in those
states, and so does evaluation: the phase is model-preserving. A write to a
variable drops the facts that mention it, and the facts learned inside a block or
branch are forgotten when it ends.

Facts are read as written. An axiom whose value side only appears once it is folded,
such as `g(0) == Box..w(box())` with `box()` an inline function returning `MkBox(5)`,
gives a fact once `foldAxioms` has run before this phase.

## The invariant model preservation rests on

Not yet proved. For every state σ that reaches a statement `s` and in which every
fact of `fs` holds (each recorded value equals its variable or term in σ, each
definition equals its variable in σ, and nothing is claimed when `fs.dead`):

1. a goal `g` of `s` and `rewriteGoal F fs fuel g` evaluate to the same value in σ;
2. every fact of the facts `stepStmt`/`stepStmts` return for `s` holds in each state
   that `s` reaches from σ.

`stepCmd` keeps (2) by adding only what an `assume` or a definition states and by
dropping, on a write, every fact that mentions the written variable; a block or
branch keeps it by returning the facts before it minus what it writes. A change to
how facts are scoped has to keep both.
-/

namespace Core.EqualitySimplification

open Lambda Imperative

public section

/-- The facts a path condition gives. A variable or term mapped to `none` has two
    different values, and is left alone. -/
structure Facts where
  /-- Values the assumptions give variables. -/
  vars : Std.HashMap CoreIdent (Option Expression.Expr) := {}
  /-- Values the assumptions give terms other than variables, bucketed by
      `LExpr.hashExpr`. Neither a term nor its value contains a bound variable. -/
  terms : Std.HashMap UInt64 (List (Expression.Expr × Option Expression.Expr)) := {}
  /-- The path condition's definitions `x := e`. A definition is dropped when its
      variable is defined again or written, so each variable has at most one. -/
  defs : Std.HashMap CoreIdent Expression.Expr := {}
  /-- Whether an assumption already folded to `false` under the earlier facts. Goals on
      such a path are left for the solver, which finds them valid, instead of being
      folded to a `false` that the facts' inconsistency produced. This is a best-effort
      check: an inconsistency that folding does not expose, such as `f(x) == 3` and
      `f(1) == 4` under `x == 1`, leaves `dead` unset, and a goal on that path can still
      fold to `false`. -/
  dead : Bool := false

namespace Facts

def isEmpty (fs : Facts) : Bool := fs.vars.isEmpty && fs.terms.isEmpty && fs.defs.isEmpty

/-- Map `x` to `v` in `m`, or to `none` if it already has a different value. -/
def insertUnique (m : Std.HashMap CoreIdent (Option Expression.Expr)) (x : CoreIdent)
    (v : Expression.Expr) : Std.HashMap CoreIdent (Option Expression.Expr) :=
  match m.get? x with
  | none => m.insert x (some v)
  | some (some v') => if v' == v then m else m.insert x none
  | some none => m

/-- Record that `lhs` equals `rhs`. A variable or term given two different values is
    dropped, as `insertUnique` does, and a term or value with a bound variable is not
    recorded. -/
def insert (fs : Facts) (lhs rhs : Expression.Expr) : Facts :=
  if rhs.hasBVar then fs else
  match lhs with
  | .fvar _ x _ => { fs with vars := insertUnique fs.vars x rhs }
  | _ =>
    if lhs.hasBVar then fs else
    let h := LExpr.hashExpr lhs
    let bucket := fs.terms.getD h []
    match bucket.find? (·.1 == lhs) with
    | none => { fs with terms := fs.terms.insert h ((lhs, some rhs) :: bucket) }
    | some (_, some v) =>
      if v == rhs then fs
      else
        let bucket := bucket.map fun (k, v) => if k == lhs then (k, none) else (k, v)
        { fs with terms := fs.terms.insert h bucket }
    | some (_, none) => fs

/-- The value recorded for the term `e`, whose hash is `h`. -/
def lookupTerm (fs : Facts) (e : Expression.Expr) (h : UInt64) : Option Expression.Expr :=
  (fs.terms.get? h).bind fun bucket => (bucket.find? (·.1 == e)).bind (·.2)

/-- `fs` without the facts that mention one of `xs`: their values, definitions
    and recorded terms, as on either side. -/
def forget (fs : Facts) (xs : List CoreIdent) : Facts :=
  if xs.isEmpty then fs else
  let xs : Std.HashSet CoreIdent := Std.HashSet.ofList xs
  let mentions (e : Expression.Expr) : Bool :=
    (HasFvars.getFvars (P := Expression) e).any (xs.contains ·)
  let keep (x : CoreIdent) (v : Option Expression.Expr) : Bool :=
    !xs.contains x && !(v.map mentions).getD false
  { fs with
    vars := fs.vars.filter keep
    defs := fs.defs.filter fun x v => keep x (some v)
    terms := fs.terms.filterMap fun _ bucket =>
      match bucket.filter (fun (k, v) => !mentions k && !(v.map mentions).getD false) with
      | [] => none
      | b => some b }

/-- The definition of `x`, if the program gives it exactly one. -/
def defOf? (fs : Facts) (x : CoreIdent) : Option Expression.Expr :=
  fs.defs.get? x

/-- `e` read through up to `n` definitions while it is a defined variable. -/
def seeThrough (fs : Facts) : Nat → Expression.Expr → Expression.Expr
  | n + 1, e@(.fvar _ x _) =>
    match fs.defOf? x with
    | some d => fs.seeThrough n d
    | none => e
  | _, e => e

end Facts

variable (F : @Lambda.Factory CoreLParams)

/-- Whether `e` may replace a term equal to it: a value, or a constructor
    application, which is what lets a destructor or tester reduce. -/
def isReplacement (e : Expression.Expr) : Bool :=
  LExpr.isValue F e || LExpr.isConstrApp F e

/-- The fact `l == r` oriented as `(lhs, rhs)`, so that `rhs` replaces `lhs`. Each
    side is read through its definitions: a value replaces a non-value, and
    otherwise a constructor application replaces a term that is not one. -/
def orient (l r : Expression.Expr) (l' r' : Expression.Expr) :
    Option (Expression.Expr × Expression.Expr × Expression.Expr) :=
  -- `l'` and `r'` are `l` and `r` read through their definitions; the result names
  -- the side to replace in both forms, then its replacement.
  match LExpr.isValue F l', LExpr.isValue F r' with
  | false, true => some (l, l', r')
  | true, false => some (r, r', l')
  | true, true => none
  | false, false =>
    match LExpr.isConstrApp F l', LExpr.isConstrApp F r' with
    | false, true => some (l, l', r')
    | true, false => some (r, r', l')
    | _, _ => none

/-- How many definitions are read through in a row, which bounds the work a chain of
    definitions costs. -/
def defDepth : Nat := 16

/-! The connectives are named by the factory functions that build them, so the ops
recognized here cannot drift from the ops the factory emits. -/

def andName : String := (boolAndFunc (T := CoreLParams)).name.name
def notName : String := (boolNotFunc (T := CoreLParams)).name.name

/-- Add the facts the assumption `e` gives: its conjuncts, an equality oriented by
    `orient`, `t ↦ false` for a negation `¬ t`, and `t ↦ true` for any other
    boolean term `t` that is not a literal or a binder. A defined variable also
    gives the facts of its definition, following up to `n` definitions in a row;
    conjunctions spend none, so every conjunct of a long conjunction is recorded. -/
def addAssumption (fs : Facts) (n : Nat) (e : Expression.Expr) : Facts :=
  match e with
  | .eq _ l r =>
    let see := fs.seeThrough defDepth
    match orient F l r (see l) (see r) with
    | some (lhs, lhs', rhs) =>
      let fs := fs.insert lhs rhs
      if lhs' == lhs then fs else fs.insert lhs' rhs
    | none => fs.insert e (.true ())
  | .app _ (.app _ (.op _ o _) a) b =>
    if o.name == andName then addAssumption (addAssumption fs n a) n b
    else fs.insert e (.true ())
  | .app _ (.op _ o _) a =>
    if o.name == notName then
      let fs := fs.insert a (.false ())
      let a' := fs.seeThrough defDepth a
      if a' == a then fs else fs.insert a' (.false ())
    else fs.insert e (.true ())
  | .fvar _ x _ =>
    let fs := fs.insert e (.true ())
    match n, fs.defOf? x with
    | n + 1, some d => addAssumption fs n d
    | _, _ => fs
  | .const _ _ | .abs _ _ _ _ | .quant _ _ _ _ _ _ | .bvar _ _ => fs
  | _ => fs.insert e (.true ())
  termination_by (n, sizeOf e)

/-- What a defined variable is replaced by, once computed, for each remaining depth:
    `none` when its definition does not reduce to a replacement within that depth. Keyed
    on the depth too, since a shallower read can stop before a deeper one would succeed. -/
abbrev DefCache := Std.HashMap (CoreIdent × Nat) (Option Expression.Expr)

/-- The hash `LExpr.hashExpr e`, which `Facts.insert` keys terms by, computed from the
    hashes of `e`'s children. The equation is checked by the type, so that a change to
    either hash cannot silently make lookups miss. -/
abbrev HashOf (e : Expression.Expr) := { h : UInt64 // h = LExpr.hashExpr e }

/-- Replace each subterm of `e` that has a recorded value by that value. Lookups are on
    the original subterms, so when a term and one of its subterms both have a value, the
    larger term wins. Also replace each defined variable whose definition reduces to a
    replacement (see `isReplacement`) by what it reduces to, reading up to `depth`
    definitions in a row. Returns the new term, whether it changed, and the hash of the
    original `e`, so that every subterm is hashed once. -/
def substAux (fs : Facts) (fuel : Nat) (depth : Nat) (e : Expression.Expr) :
    StateM DefCache (Expression.Expr × Bool × HashOf e) :=
  match e with
  | .const _ c => pure (e, false, ⟨LExpr.hashConst (hash c), by simp only [LExpr.hashExpr]⟩)
  | .bvar _ i => pure (e, false, ⟨LExpr.hashBVar (hash i), by simp only [LExpr.hashExpr]⟩)
  | .op m o ty => do
    let h : HashOf (.op m o ty) :=
      ⟨LExpr.hashOp (hash o.name) (LExpr.hashOptTy ty), by simp only [LExpr.hashExpr]⟩
    match fs.lookupTerm e h.val with
    | some v => pure (v, true, h)
    | none => pure (e, false, h)
  | .fvar m x ty => do
    let h : HashOf (.fvar m x ty) :=
      ⟨LExpr.hashFVar (hash x.name) (LExpr.hashOptTy ty), by simp only [LExpr.hashExpr]⟩
    match fs.vars.get? x, depth, fs.defOf? x with
    | some (some v), _, _ => pure (v, true, h)
    | none, d + 1, some body =>
      let v? ← match (← get).get? (x, d) with
        | some v? => pure v?
        | none => do
          let (body', changed, _) ← substAux fs fuel d body
          let body' := if changed then (LExpr.eval fuel F (fun _ => none) body').fst else body'
          let v? := if isReplacement F body' then some body' else none
          modify (·.insert (x, d) v?)
          pure v?
      match v? with
      | some v => pure (v, true, h)
      | none => pure (e, false, h)
    | _, _, _ => pure (e, false, h)
  | .app m fn arg => do
    let (fn', c1, ⟨h1, p1⟩) ← substAux fs fuel depth fn
    let (arg', c2, ⟨h2, p2⟩) ← substAux fs fuel depth arg
    let h : HashOf (.app m fn arg) := ⟨LExpr.hashApp h1 h2, by simp only [LExpr.hashExpr, p1, p2]⟩
    match fs.lookupTerm e h.val with
    | some v => pure (v, true, h)
    | none => pure (if c1 || c2 then (.app m fn' arg', true, h) else (e, false, h))
  | .ite m c t f => do
    let (c', c1, ⟨h1, p1⟩) ← substAux fs fuel depth c
    let (t', c2, ⟨h2, p2⟩) ← substAux fs fuel depth t
    let (f', c3, ⟨h3, p3⟩) ← substAux fs fuel depth f
    let h : HashOf (.ite m c t f) :=
      ⟨LExpr.hashIte h1 h2 h3, by simp only [LExpr.hashExpr, p1, p2, p3]⟩
    match fs.lookupTerm e h.val with
    | some v => pure (v, true, h)
    | none => pure (if c1 || c2 || c3 then (.ite m c' t' f', true, h) else (e, false, h))
  | .eq m e1 e2 => do
    let (e1', c1, ⟨h1, p1⟩) ← substAux fs fuel depth e1
    let (e2', c2, ⟨h2, p2⟩) ← substAux fs fuel depth e2
    let h : HashOf (.eq m e1 e2) := ⟨LExpr.hashEqExpr h1 h2, by simp only [LExpr.hashExpr, p1, p2]⟩
    match fs.lookupTerm e h.val with
    | some v => pure (v, true, h)
    | none => pure (if c1 || c2 then (.eq m e1' e2', true, h) else (e, false, h))
  | .abs m name ty body => do
    -- Recorded terms and their values contain no bound variable, so a match under a
    -- binder captures nothing.
    let (body', c, ⟨hb, pb⟩) ← substAux fs fuel depth body
    let h : HashOf (.abs m name ty body) :=
      ⟨LExpr.hashAbs (hash name) (LExpr.hashOptTy ty) hb, by simp only [LExpr.hashExpr, pb]⟩
    pure (if c then (.abs m name ty body', true, h) else (e, false, h))
  | .quant m k name ty tr body => do
    let (tr', c1, ⟨htr, ptr⟩) ← substAux fs fuel depth tr
    let (body', c2, ⟨hb, pb⟩) ← substAux fs fuel depth body
    let kh : UInt64 := match k with | .all => 0 | .exist => 1
    let h : HashOf (.quant m k name ty tr body) := ⟨LExpr.hashQuantExpr kh (hash name) (LExpr.hashOptTy ty) htr hb,
      by simp only [LExpr.hashExpr, ptr, pb]; rfl⟩
    pure (if c1 || c2 then (.quant m k name ty tr' body', true, h) else (e, false, h))
  termination_by (depth, sizeOf e)

/-- Substitute the facts into `goal` and evaluate the result, for up to `rounds`
    rounds or until nothing changes: evaluation can expose a term with a recorded
    value, such as `f(y)` once `y` is replaced. -/
def simplifyGoal (fs : Facts) (fuel : Nat) :
    Nat → Expression.Expr → StateM DefCache Expression.Expr
  | 0, goal => pure goal
  | rounds + 1, goal => do
    let (goal', changed, _) ← substAux F fs fuel defDepth goal
    if !changed then return goal
    let goal' := (LExpr.eval fuel F (fun _ => none) goal').fst
    if goal'.isTrue || goal'.isFalse then return goal'
    simplifyGoal fs fuel rounds goal'

/-- `goal` rewritten by the facts and folded with `F`. A rewrite that leaves a beta
    redex, which substituting an abstraction or expanding a body can, is discarded,
    so that the phase preserves `noBetaRedexes`. -/
def rewriteGoal (fs : Facts) (fuel : Nat) (goal : Expression.Expr) : Expression.Expr :=
  if fs.dead || fs.isEmpty || goal.isTrue || goal.isFalse then goal
  else
    -- Fold first: a goal arrives with selectors applied to constructor applications
    -- still in it, such as `Egress(SecurityGroup_Cons(.., Some(t), ..))`, and only
    -- once they reduce, to `Some(t)` here, does it mention the terms the facts pin.
    let folded := (LExpr.eval fuel F (fun _ => none) goal).fst
    let goal' := (simplifyGoal F fs fuel 4 folded).run' {}
    if goal'.noBetaRedex then goal' else goal

/-- `fs` with the facts of the assumption `e`, marked contradictory when `e` itself
    rewrites to `false` under `fs`. -/
def assumeFact (fs : Facts) (fuel : Nat) (e : Expression.Expr) : Facts :=
  let dead := fs.dead || (rewriteGoal F fs fuel e).isFalse
  { addAssumption F fs defDepth e with dead }

/-- The facts after the command `c`, and `c` with its goal rewritten if it is an
    `assert` or a `cover`. -/
def stepCmd (fs : Facts) (fuel : Nat) :
    Imperative.Cmd Expression → Imperative.Cmd Expression × Facts
  | .assert l e md => (.assert l (rewriteGoal F fs fuel e) md, fs)
  | .cover l e md => (.cover l (rewriteGoal F fs fuel e) md, fs)
  | c@(.assume _ e _) => (c, assumeFact F fs fuel e)
  | c@(.init x _ (.det v) _) =>
    let fs := fs.forget [x]
    -- A definition that reads the variable it shadows names two variables `x`, so it
    -- is not recorded.
    if (HasFvars.getFvars (P := Expression) v).contains x then (c, fs)
    else (c, { fs with defs := fs.defs.insert x v })
  | c@(.init x _ .nondet _) => (c, fs.forget [x])
  | c@(.set x _ _) => (c, fs.forget [x])

/-- `fs` without the facts the statements `ss` can invalidate. -/
def forgetWritten (fs : Facts) (ss : List Statement) : Facts :=
  fs.forget (ss.flatMap (Stmt.modifiedOrDefinedVars · (excludeScoped := false)))

mutual

/-- Rewrite the goals of `s` under the facts `fs`, and return the facts after it. -/
def stepStmt (fs : Facts) (fuel : Nat) (s : Statement) : Statement × Facts :=
  match s with
  | .cmd (.cmd c) =>
    let (c, fs) := stepCmd F fs fuel c
    (.cmd (.cmd c), fs)
  -- Unreachable under the phase's `noCalls` requirement: a call's callee may write globals
  -- its arguments do not name, so the facts would be unsafe after it. Forgetting
  -- everything keeps the step sound regardless.
  | .cmd (.call ..) => (s, {})
  | .block label ss md =>
    let (ss, _) := stepStmts fs fuel ss
    (.block label ss md, forgetWritten fs [s])
  | .ite cond ts es md =>
    let (ts, _) := stepStmts fs fuel ts
    let (es, _) := stepStmts fs fuel es
    (.ite cond ts es md, forgetWritten fs [s])
  | .loop guard measure invs body md =>
    let (body, _) := stepStmts (forgetWritten fs body) fuel body
    (.loop guard measure invs body md, forgetWritten fs [s])
  | .exit .. | .typeDecl .. => (s, fs)
  termination_by sizeOf s

/-- Rewrite the goals of `ss` in order, threading the facts. -/
def stepStmts (fs : Facts) (fuel : Nat) (ss : List Statement) : List Statement × Facts :=
  match ss with
  | [] => ([], fs)
  | s :: rest =>
    let (s, fs) := stepStmt fs fuel s
    let (rest, fs) := stepStmts fs fuel rest
    (s :: rest, fs)
  termination_by sizeOf ss

end

/-- Rewrite the goals of `proc`'s structured body under the facts `fs`. A parameter may
    share its name with a variable an axiom constrains; the axiom says nothing about the
    parameter, so its facts are dropped first. -/
def rewriteProc (fs : Facts) (fuel : Nat) (proc : Procedure) : Procedure :=
  match proc.body with
  | .structured ss =>
    let fs := fs.forget (proc.header.inputs.keys ++ proc.header.outputs.keys)
    { proc with body := .structured (stepStmts F fs fuel ss).1 }
  | .cfg _ => proc

/-- Rewrite the goal of every `assert` and `cover` in `p`'s procedure bodies. Facts are
    collected in declaration order, as obligation extraction builds the global path
    condition, so a procedure sees only the axioms declared before it. -/
def runEqualitySimplification (p : Program) : Transform.CoreTransformM (Bool × Program) := do
  let ctx := Simplify.Ctx.ofFactory (← Simplify.programFactory p) (Simplify.lambdaCarriers p)
  let F := ctx.foldFactory
  let (_, declsRev) := p.decls.foldl (init := (({} : Facts), ([] : List Decl))) fun (fs, acc) d =>
    match d with
    | .ax a _ => (if a.e.hasBVar then fs else assumeFact F fs ctx.evalFuel a.e, d :: acc)
    | .proc proc md => (fs, .proc (rewriteProc F fs ctx.evalFuel proc) md :: acc)
    | other => (fs, other :: acc)
  let p' := { p with decls := declsRev.reverse }
  return (decide (p' ≠ p), p')

end -- public section

end Core.EqualitySimplification

public section

/-- Equality simplification pipeline phase.

    Model-preserving: each rewrite replaces a goal by one with the same value in every
    state that reaches it, and no statement is added, removed or reordered. It needs
    structured bodies and no calls, since a callee may write globals the call does not
    name, and no function preconditions, since folding can expand a function body, which is
    only right where its precondition holds. It preserves what `simplify` preserves, for the
    same reason: only the expressions of `assert` and `cover` change, and those are built from the
    program's own annotated terms and constants. It also preserves `noBetaRedexes`, which
    `simplify` cannot claim, because a rewritten goal that contains a redex is discarded.

    Limitation: a goal on a path whose assumptions contradict each other can fold to
    `false`. The phase leaves such goals alone only when an assumption itself folds to
    `false` under the earlier facts; it misses contradictions that depend on order
    (`assume int.gt(x, 5); assume x == 1`) or that relate different terms (`f(x) == 2`
    and `f(1) == 3` under `x == 1`). In deductive mode the solver still sees those
    paths and finds the goal valid. Under `deductiveAssumingSatisfiablePaths`, whose
    premise is that every path can be taken, the goal is reported failing. -/
def Core.equalitySimplificationPhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "equalitySimplification"
    Core.EqualitySimplification.runEqualitySimplification
    (requires := factSet![.noCFGBodies, .noCalls, .noPrecondsFromFuncs])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment, .noBetaRedexes,
                         .noPrecondsFromFuncs, .noNondetGuards, .hasObligationForm,
                         .noProcedureContracts,
                         .noPolymorphicProcedures, .noPolymorphicFunctions,
                         .typeAnnotated])

end
