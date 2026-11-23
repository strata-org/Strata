/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.RunTarget
public import Strata.Languages.Core.ConfigWF
public import Strata.Languages.Core.InterpreterReplay
public import Strata.DL.Imperative.Counterexample.Valuation
public import Strata.DL.Imperative.Counterexample.BackLink
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterCall
import all Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.InterpreterReplay
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink
import all Strata.DL.Imperative.Counterexample.RunProps
import all Strata.DL.Imperative.Counterexample.BackLinkProps

/-! # Level-(a) counterexamples of Core: outcome validity and claim validity over targets

Counterexamples live at three *levels*: level (a) is a run of the program (a `CexA`
replayed from a configuration with an oracle), level (b) is a valuation of a proof
obligation's variables, and level (c) is the SMT solver's model.  This module states what a
valid level-(a) counterexample of Core is:

* `CexValidity`, `ValidOutcomeOf`, `ValidOutcome` — outcome validity.
* the target-walk cluster and `genuineFeasibleT` — claim validity over `Target`
  (assertion / loop-VC / point-check / decl-check). -/

namespace Core

open Imperative

public section

/-- A validity predicate for claims: `V t f c` holds when replaying `c` at fuel `f`
    genuinely and feasibly reaches target `t`.  The Core instances are `genuineFeasible π`
    (over assertion ids) and `genuineFeasibleT π` (over `Target`). -/
abbrev CexValidity (Tgt : Type) := Tgt → Nat → CexA Expression Command → Prop

/-- Validity of a back-link outcome for the target `t` at the unit `stmts`, generic over the
    target type and the claim-validity predicate `V`: the chain head (if any) is top-level at
    `stmts`; a claim `(c, f)` satisfies `V t f c`, and is not top-level when unconfirmed slices
    precede it; every element of the chain is well-formed (`CexWF`). -/
@[expose] def ValidOutcomeOf {Tgt : Type} (V : CexValidity Tgt) (t : Tgt)
    (stmts : List (Stmt Expression Command)) (o : BackLinkOutcome Expression Command) : Prop :=
  (∀ h, o.chain.head? = some h → isTopLevelAt stmts h) ∧
  (∀ c f, o.claim = some (c, f) → V t f c ∧ (o.slices ≠ [] → ¬ isTopLevelAt stmts c)) ∧
  (∀ c ∈ o.chain, CexWF c)

/-- Validity of a back-link outcome keyed on the target assertion id: `ValidOutcomeOf` with
    claims validated by `genuineFeasible π` (the claim replays, with callees resolved by `π`,
    genuinely and feasibly to the failing `target`). -/
abbrev ValidOutcome (π : String → Option Procedure) (target : AssertId Expression)
    (stmts : List (Stmt Expression Command))
    (o : BackLinkOutcome Expression Command) : Prop :=
  ValidOutcomeOf (genuineFeasible π) target stmts o

/-! ## Loop heads in a configuration -/

/-- An iteration of a loop that has started and whose body has not finished: the loop's
    metadata, the depth of the loop statement when the iteration started, and the
    measure's value then (if the loop has a measure that evaluated). -/
structure OpenIter where
  md : MetaData Expression
  depth : Nat
  start : Option Expression.Expr

/-- Does `e` evaluate in `env` at fuel `f` to the false literal, up to metadata
    (`Calls.evalsFalse` with the factory and store of `env`)? -/
@[expose] def evalsFalse (f : Nat) (env : IEnv Expression) (e : Expression.Expr) : Bool :=
  Calls.evalsFalse f env.factory env.store.get e

/-- The expression of a loop VC, given the loop's measure and invariants and (for the
    decrease) the measure's value at the iteration start. -/
@[expose] def loopVCExpr (kind : LoopVCKind) (measure : Option Expression.Expr)
    (invs : List (String × Expression.Expr)) (start : Option Expression.Expr) :
    Option Expression.Expr :=
  match kind with
  | .entryInvariant i | .maintainInvariant i => invs[i]?.map (·.2)
  | .measureLowerBound => measure.map fun m =>
      HasBoolOps.not (P := Expression) (HasIntOps.lt (P := Expression) m HasInt.zero)
  | .measureDecrease => do
      let m ← measure
      let v ← start
      some (HasIntOps.lt (P := Expression) m v)

/-- The open iteration of a loop with metadata `md` whose head is now reached again at
    depth `e` (the head of the next iteration sits one level below the started one). -/
@[expose] def findReentry (opens : List OpenIter) (md : MetaData Expression) (e : Nat) :
    Option OpenIter :=
  opens.find? fun o => decide (o.md = md) && o.depth + 1 == e

/-- **Firing at a loop head, before its step.**  The configuration's focus is a loop with
    the target's metadata, and the target's VC fails there: an entry invariant when the
    head is not a re-entry, a maintained invariant or the decrease when it is. -/
@[expose] def loopHeadFires (id : LoopVCId) (f : Nat) (opens : List OpenIter)
    (c : IConfig Expression Command) : Bool :=
  match IConfig.focus c with
  | some (.loop _ m invs _ md, env, e) =>
    decide (md = id.loopMd) &&
    match id.kind, findReentry opens md e with
    | .entryInvariant i, none =>
      match loopVCExpr (.entryInvariant i) m invs none with
      | some x => evalsFalse f env x
      | none => false
    | .maintainInvariant i, some _ =>
      match loopVCExpr (.maintainInvariant i) m invs none with
      | some x => evalsFalse f env x
      | none => false
    | .measureDecrease, some o =>
      match loopVCExpr .measureDecrease m invs o.start with
      | some x => evalsFalse f env x
      | none => false
    | _, _ => false
  | _ => false

/-- Whether an optional sub-configuration is the body block of `lp` followed by `lp`. -/
private def isIterStart (lp : Statement) : Option (IConfig Expression Command) → Bool
  | some (.seq (.block .none _ _) [lp']) => decide (lp' = lp)
  | _ => false

/-- Did the step from `c` to `c'` start an iteration of the loop in `c`'s focus: the
    loop statement's position now holds its body block followed by the loop? -/
@[expose] def iterationStarted (c c' : IConfig Expression Command) : Bool :=
  match IConfig.focus c with
  | some (lp@(.loop _ _ _ _ _), _, e) =>
    match IConfig.subAt c' e with
    | some (.seq (.block .none _ _) [lp']) => decide (lp' = lp)
    | _ => false
  | _ => false

/-- **Firing at an iteration start**: the measure's lower bound fails at the loop head
    whose step entered the body. -/
@[expose] def iterationFires (id : LoopVCId) (f : Nat) (c : IConfig Expression Command) : Bool :=
  match id.kind, IConfig.focus c with
  | .measureLowerBound, some (.loop _ m invs _ md, env, _) =>
    decide (md = id.loopMd) &&
    match loopVCExpr .measureLowerBound m invs none with
    | some x => evalsFalse f env x
    | none => false
  | _, _ => false

/-- Remove the first open iteration with the same metadata and depth as `o`. -/
@[expose] def eraseOpen : List OpenIter → OpenIter → List OpenIter
  | [], _ => []
  | x :: xs, o => if decide (x.md = o.md) && x.depth == o.depth then xs else x :: eraseOpen xs o

/-- The open-iteration bookkeeping across one step from `c` to `c'`: the iterations whose
    loop position no longer exists are dropped (an `exit` left them), the re-entered one
    is closed, and a started one is opened with its measure's value. -/
@[expose] def updateOpens (f : Nat) (opens : List OpenIter) (c c' : IConfig Expression Command) :
    List OpenIter :=
  let opens := opens.filter fun o => o.depth ≤ IConfig.activeDepth c
  match IConfig.focus c with
  | some (.loop _ m _ _ md, env, e) =>
    let opens := match findReentry opens md e with
      | some o => eraseOpen opens o
      | none => opens
    if iterationStarted c c' then
      { md := md, depth := e,
        start := m.bind fun d => evalBounded f env.factory env.store.get d } :: opens
    else opens
  | _ => opens

/-- The iterations already in progress in a start configuration (a counterexample slice may
    start inside a loop body): every position `d` on the active path holding a loop's body
    block followed by the loop.  The body block's parent store is the store at the
    iteration's start, so the measure's value then is the measure evaluated there. -/
@[expose] def initialOpens (f : Nat) : IConfig Expression Command → Nat → List OpenIter
  | .seq inner rest, d =>
    let here : List OpenIter := match inner, rest with
      | .block .none fr blk, [.loop _ m _ _ md] =>
        [{ md := md, depth := d,
           start := m.bind fun D => evalBounded f blk.getEnv.factory fr.parent.get D }]
      | _, _ => []
    here ++ initialOpens f inner (d + 1)
  | .block _ _ inner, d => initialOpens f inner (d + 1)
  | .seqs inner k, d => initialOpens f inner (d + k + 1)
  | _, _ => []

/-- What a target walk watches for: a firing at a configuration about to step, given the
    open iterations (`pre`), and a firing at a step from `c` to `c'` (`post`). -/
structure WalkFire where
  pre : List OpenIter → IConfig Expression Command → Bool
  post : IConfig Expression Command → IConfig Expression Command → Bool

/-- A watch that ignores the monadic interpreter's own bookkeeping: its verdicts on a
    configuration and on that configuration with the bookkeeping forgotten (`IConfig.norm`)
    agree. -/
@[expose] def WalkFire.AbsInvariant (W : WalkFire) : Prop :=
  (∀ opens c, W.pre opens c = W.pre opens c.norm) ∧
    ∀ c c', W.post c c' = W.post c.norm c'.norm

/-- The watch whose verdicts are those of a watch on semantic configurations, applied to the
    configurations the interpreter configurations stand for under the factory `F`. -/
@[expose] noncomputable def WalkFire.ofAbs (F : Expression.Factory)
    (pre : List OpenIter → Config Expression Command → Bool)
    (post : Config Expression Command → Config Expression Command → Bool) : WalkFire where
  pre opens c := pre opens (c.abs F)
  post c c' := post (c.abs F) (c'.abs F)

/-- **The target walk.**  Replay `cex` step by step (strict oracle, callees resolved by
    `π`, eval fuel `f`, at most `f` interpreter steps) from its configuration,
    keeping the open loop iterations: it succeeds at the first configuration (or step) where `W`
    fires, on a feasible path
    (every assumption recorded so far holds).  An engine stop, the end of the run, or exhausted
    fuel ends it unsuccessfully.  The iterations in progress at the start (`initialOpens`) are
    open from the beginning, so a slice starting inside a loop body sees the loop's next head as
    a re-entry. -/
@[expose] def targetWalk (π : String → Option Procedure) (W : WalkFire) (f : Nat)
    (cex : CexA Expression Command) : Bool :=
  go f cex.cfg { remaining := cex.oracle } (initialOpens f cex.cfg 0)
where
  go (budget : Nat) (c : IConfig Expression Command) (st : ReplayState Expression)
      (opens : List OpenIter) : Bool :=
    if W.pre (opens.filter fun o => o.depth ≤ IConfig.activeDepth c) c &&
        PathFeasibleB f st.traceRev then true
    else if c.Done then false
    else
      match budget with
      | 0 => false
      | budget + 1 =>
        match replayRun (stepInterp (replayStepCmd π defaultMaxCallDepth) f c)
            { oracleConfig := .strict } st with
        | (.error _, _) => false
        | (.ok c', st') =>
          if W.post c c' && PathFeasibleB f st.traceRev then true
          else go budget c' st' (updateOpens f opens c c')

/-- What the loop-VC walk watches for: the VC at a loop head (entry, re-entry), and the
    measure's lower bound at an iteration start. -/
@[expose] def loopVCFire (id : LoopVCId) (f : Nat) : WalkFire where
  pre := loopHeadFires id f
  post := fun c c' => iterationStarted c c' && iterationFires id f c

/-- **The loop-VC decision procedure**: the target walk watching the loop VC `id`. -/
@[expose] def loopVCRun (π : String → Option Procedure) (id : LoopVCId) (f : Nat)
    (cex : CexA Expression Command) : Bool :=
  targetWalk π (loopVCFire id f) f cex

/-- **Firing of a point check**: the configuration is about to execute a statement with
    the check's metadata, and the check's expression evaluates to false in its store. -/
@[expose] def pointFires (id : PointCheckId) (f : Nat) (c : IConfig Expression Command) : Bool :=
  match IConfig.focus c with
  | some (s, env, _) => decide (s.getMetaData = id.stmtMd) && evalsFalse f env id.expr
  | none => false

/-- **The point-check decision procedure**: the target walk watching the point check `id`
    before every statement. -/
@[expose] def pointRun (π : String → Option Procedure) (id : PointCheckId) (f : Nat)
    (cex : CexA Expression Command) : Bool :=
  targetWalk π { pre := fun _ c => pointFires id f c, post := fun _ _ => false } f cex

/-! ## Claim validity over targets -/

/-- **Claim validity over `Target`**: an assertion target is `genuineFeasible`; a loop-VC
    target is decided by `loopVCRun`, a point check by `pointRun`; a declaration check is
    its assertion in the derived unit (`genuineFeasible` of `id.check`). -/
@[expose] def genuineFeasibleT (π : String → Option Procedure) : CexValidity Target
  | .assert a, f, c => genuineFeasible π a f c
  | .loopVC id, f, c => loopVCRun π id f c = true
  | .atPoint id, f, c => pointRun π id f c = true
  | .declCheck id, f, c => genuineFeasible π id.check f c

end -- public section

end Core
