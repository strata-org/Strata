/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.DL.Imperative.CFGDominators
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.WF
import all Strata.DL.Imperative.CFG
import all Strata.DL.Imperative.CFGDominators
import Strata.DL.Lambda.LExprT
import Strata.Languages.Core.StatementType
import Strata.Languages.Core.CmdType

---------------------------------------------------------------------

public section

namespace Core

open Std (ToFormat Format format)
open Imperative (MetaData HasVarsImp)
open Imperative.CFG (cycleLabelsWith succMapSize)
open Imperative.CFG.Dom (dominates)
open Strata (Message FileRange)

namespace Procedure

private def checkParamNames (proc : Procedure) (sourceLoc : FileRange) :
    Except Message Unit := do
  if !proc.header.inputs.keys.Nodup then
    .error <| Message.withRange sourceLoc f!"[{proc.header.name}] Duplicates found in the formals!"
  if !proc.header.outputs.keys.Nodup then
    .error <| Message.withRange sourceLoc f!"[{proc.header.name}] Duplicates found in the return variables!"
  -- Names starting with `old ` are reserved for the initial values of in-out parameters.
  match (proc.header.inputs.keys ++ proc.header.outputs.keys).find? CoreIdent.isOldIdent with
  | some id =>
    .error <| Message.withRange sourceLoc
      f!"[{proc.header.name}] Parameter {id}: a name starting with \"old \" denotes the \
         initial value of an in-out parameter!"
  | none => pure ()

private def checkModificationRights (proc : Procedure) (sourceLoc : FileRange) :
    Except Message Unit := do
  let modifiedVars := (HasVarsImp.modifiedVars (P := Expression) proc.body).eraseDups
  let definedVars := (HasVarsImp.definedVars (P := Expression) proc.body false).eraseDups
  let allowedVars := proc.header.outputs.keys ++ definedVars
  let disallowed := modifiedVars.filter (fun v => !allowedVars.contains v)
  if !disallowed.isEmpty then
    .error <| Message.withRange sourceLoc f!"[{proc.header.name}]: This procedure modifies variables it \
              is not allowed to!\n\
              Variables actually modified: {modifiedVars}\n\
              Modification allowed for these variables: {allowedVars}"

/-- Error unless every block label is unique. -/
def checkUniqueLabels (procName : CoreIdent) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except Message Unit := do
  let labels := cfg.labels
  if !labels.nodupB then
    let dups := labels.filter (fun l => labels.countP (· == l) > 1) |>.eraseDups
    .error <| Message.withRange sourceLoc
      f!"[{procName}]: Duplicate block labels in CFG: {dups}"

/-- Error unless the entry label names an existing block. -/
def checkEntryExists (procName : CoreIdent) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except Message Unit := do
  let labels := cfg.labels
  if !labels.contains cfg.entry then
    .error <| Message.withRange sourceLoc
      f!"[{procName}]: Entry label \"{cfg.entry}\" not found in CFG blocks. \
         Available labels: {labels}"

/-- Error unless every transfer target names an existing block. -/
def checkTargetLabels (procName : CoreIdent) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except Message Unit := do
  let labels := cfg.labels
  let labelSet := Std.HashSet.ofList labels
  for (lbl, blk) in cfg.blocks do
    for t in blk.transfer.targets do
      if !labelSet.contains t then
        .error <| Message.withRange sourceLoc
          f!"[{procName}]: Block \"{lbl}\" branches to unknown label \"{t}\". \
             Available labels: {labels}"

/-- Each block-level `init` target paired with its declaring block's label. -/
def cfgInitDeclBlocks (cfg : DetCFG) : List (Expression.Ident × String) :=
  cfg.blocks.flatMap fun (lbl, blk) => (WF.blockInitVars blk).map (·, lbl)

/-- Each block-level `init` target paired with its declared type and its
declaring block's label, so a block's scope can be seeded from its strict
dominators' declarations. -/
def cfgInitDeclTypes (cfg : DetCFG) :
    List (Expression.Ident × Expression.Ty × String) :=
  cfg.blocks.flatMap fun (lbl, blk) =>
    blk.cmds.filterMap fun
      | .cmd (.init x ty _ _) => some (x, ty, lbl)
      | _ => none

/-- No block declares the same `init` target twice. -/
def blockInitsNodupB (cfg : DetCFG) : Bool :=
  cfg.blocks.all fun lb => (WF.blockInitVars lb.2).nodupB

/-- Every CFG-local a *reachable* block reads or assigns has a dominating
declarer. Unreachable blocks are excluded (their dominator set is `⊤`).

Each use of `x` is checked only against the declarers of `x` (`groupValuesByKey`), so
a local with one declarer costs one `dominates` query per use. `dominates`
searches the block's dominator list from `computeDominators`. -/
def domScopedB (dom : Std.HashMap String (List String)) (reachable : Std.HashSet String)
    (cfg : DetCFG) : Bool :=
  let inits := Std.HashSet.ofList (WF.cfgInitVars cfg)
  let groups := (cfgInitDeclBlocks cfg).groupValuesByKey (fun _ => true)
  cfg.blocks.all fun lb =>
    !(reachable.contains lb.1) ||
    (WF.blockReadVars lb.2 ++ WF.blockSetTargets lb.2).all fun x =>
      !(inits.contains x) ||
      (groups.getD x []).any (fun d => dominates dom d lb.1)

/-- Two distinct *reachable* blocks declaring the same local are
dominance-incomparable. Unreachable declarers are excluded (their dominator set
is `⊤`).

Each reachable declarer is compared only with the other declarers of the same
local (`groupValuesByKey`): none of them may dominate it. Running this for
every declarer covers both directions of each pair. A local declared in a single
block makes no `dominates` query, so the check is linear when locals are
distinct. -/
def initsIncomparableB (dom : Std.HashMap String (List String)) (reachable : Std.HashSet String)
    (cfg : DetCFG) : Bool :=
  let ds := cfgInitDeclBlocks cfg
  let groups := ds.groupValuesByKey reachable.contains
  ds.all fun p =>
    !(reachable.contains p.2) ||
      (groups.getD p.1 []).all fun d => d == p.2 || !(dominates dom d p.2)

/-- Error unless no block declares the same local twice. Runs before the
per-block loop so this CFG-level message wins over the low-level "already in
context" error. -/
def checkBlockInitsNodup (procName : CoreIdent) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except Message Unit :=
  if blockInitsNodupB cfg then .ok ()
  else .error <| Message.withRange sourceLoc
    f!"[{procName}]: a block declares the same local more than once."

/-- Error unless every CFG-local read or assigned has a dominating declarer. Runs
before the per-block loop (over the order-independent dominance oracle) so a
genuine scope error surfaces as this CFG-level message ahead of the low-level
in-loop fvar error. -/
def checkDomScoped (dom : Std.HashMap String (List String)) (reachable : Std.HashSet String)
    (procName : CoreIdent) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except Message Unit :=
  if domScopedB dom reachable cfg then .ok ()
  else .error <| Message.withRange sourceLoc
    f!"[{procName}]: a CFG-local is read or assigned on a path where its \
       declaration does not dominate."

/-- Error unless same-local declarers are dominance-incomparable. Runs before the
per-block loop (over the order-independent dominance oracle) so this CFG-level
message surfaces for a comparable pair ahead of the low-level in-loop error. -/
def checkInitsIncomparable (dom : Std.HashMap String (List String)) (reachable : Std.HashSet String)
    (procName : CoreIdent) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except Message Unit :=
  if initsIncomparableB dom reachable cfg then .ok ()
  else .error <| Message.withRange sourceLoc
    f!"[{procName}]: a CFG-local is declared in two dominance-comparable blocks."

/-- No reachable block that lies on a cycle declares a block-level `init`.
`onCyc` is the set of labels on a cycle (`cycleLabelsWith`), computed once by the
caller. -/
def noLoopInitsB (reachable : Std.HashSet String) (onCyc : Std.HashSet String)
    (cfg : DetCFG) : Bool :=
  cfg.blocks.all fun lb =>
    (WF.blockInitVars lb.2).isEmpty || !(reachable.contains lb.1 && onCyc.contains lb.1)

/-- Error unless no reachable block on a cycle declares a block-level `init`.

A local declared in a block that can run more than once would be re-initialized
on re-entry, which the Imperative `init` semantics cannot step (it requires the
variable to be unset). The structured pipeline hoists such declarations out of
the loop (`hoistLoopPrefixInits`); a CFG body has no analogous rewrite here, so a
loop-carried `init` is rejected rather than silently certified. This also covers
the translator-inserted `init $__nondet_N` that a nondeterministic `goto` in a
loop header would introduce. -/
def checkNoLoopInits (procName : CoreIdent) (reachable : Std.HashSet String)
    (onCyc : Std.HashSet String) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except Message Unit :=
  if noLoopInitsB reachable onCyc cfg then .ok ()
  else .error <| Message.withRange sourceLoc
    f!"[{procName}]: a CFG-local is declared in a block that lies on a cycle; \
       a loop-carried declaration would be re-initialized on re-entry."

/-- No two *reachable* blocks declaring the same local are reach-comparable —
i.e. one does not lie on a path from the other. `ds` is the shared
`cfgInitDeclBlocks cfg`, computed once by the caller.

The reachable declarers are grouped by local. A local with a single declarer
needs no search. For a local with declarers `S`, one search runs from all of `S`
at once: each node collects the labels of the declarers that reach it in one or
more steps, keeping at most two. A declarer `t` is reached by another declarer
iff it collects a label other than `t`. Keeping two labels is enough: if `t`
collects fewer than two, it has collected every declarer that reaches it, and if
it collects two, at least one differs from `t`. Each node gains at most two
labels, so each search is linear in the size of `succs`. -/
def initsNotReachableB (ds : List (Expression.Ident × String)) (reachable : Std.HashSet String)
    (succs : Std.HashMap String (List String)) : Bool := Id.run do
  let groups := ds.groupValuesByKey reachable.contains
  -- Each push adds a label to a node, at most two per node.
  let fuel := 2 * succMapSize succs + 1
  for (_, srcs) in groups.toList do
    if srcs.length < 2 then continue
    let mut tags : Std.HashMap String (List String) := {}
    let mut work : List (String × String) := []
    for s in srcs do
      for t in succs.getD s [] do
        let cur := tags.getD t []
        if cur.length < 2 && !cur.contains s then
          tags := tags.insert t (s :: cur)
          work := (t, s) :: work
    for _ in [0:fuel] do
      match work with
      | [] => break
      | (u, s) :: rest =>
        work := rest
        for t in succs.getD u [] do
          let cur := tags.getD t []
          if cur.length < 2 && !cur.contains s then
            tags := tags.insert t (s :: cur)
            work := (t, s) :: work
    for t in srcs do
      if (tags.getD t []).any (· != t) then return false
  return true

/-- Error unless no two reachable same-local declarers are reach-comparable.

`checkInitsIncomparable` only rejects same-local declarers that are
*dominance*-comparable, which leaves a path that runs two `init`s of the same
local when the declarers are dominance-incomparable but one can still reach the
other (e.g. `entry → D → E` plus `entry → E`: `D` and `E` are incomparable, yet
the path through `D` reaches `E`'s `init` while the local is already set). The
Imperative `init` semantics require the variable to be unset, so that path gets
stuck; this guard rejects it with a CFG-level message. -/
def checkInitsNotReachable (procName : CoreIdent)
    (ds : List (Expression.Ident × String)) (reachable : Std.HashSet String)
    (succs : Std.HashMap String (List String)) (sourceLoc : FileRange) :
    Except Message Unit :=
  if initsNotReachableB ds reachable succs then .ok ()
  else .error <| Message.withRange sourceLoc
    f!"[{procName}]: a CFG-local is declared in two blocks where one is \
       reachable from the other; a single path would re-initialize it."

/-- No block-level `init` target collides with a procedure formal, output, or
`old` binding. `headerNames` is the procedure's input, output, and `old`
identifiers. -/
def initsNotHeaderB (headerNames : List Expression.Ident) (cfg : DetCFG) : Bool :=
  let headerSet := Std.HashSet.ofList headerNames
  (WF.cfgInitVars cfg).all fun x => !(headerSet.contains x)

/-- Error unless no block-level `init` target shadows a header binding (a formal,
an output, or an `old` parameter).

A CFG `init` whose name matches a header binding would shadow it, which the
structured path rejects with "already in context". This guard rejects the
collision up front with a CFG-level message. -/
def checkInitsNotHeader (procName : CoreIdent) (headerNames : List Expression.Ident)
    (cfg : DetCFG) (sourceLoc : FileRange) : Except Message Unit :=
  if initsNotHeaderB headerNames cfg then .ok ()
  else .error <| Message.withRange sourceLoc
    f!"[{procName}]: a CFG-local shadows a procedure formal, output, or \
       `old` binding."

/-- A local declared by two blocks at different types, if any. `decls` holds each
`init` target with its resolved type (aliases expanded) and the label of its
block. -/
def initTypeConflict? (decls : List (Expression.Ident × Expression.Ty × String)) :
    Option Expression.Ident := Id.run do
  let mut declared : Std.HashMap Expression.Ident Expression.Ty := {}
  for (x, ty, _) in decls do
    match declared.get? x with
    | some ty0 => if ty0 != ty then return some x
    | none => declared := declared.insert x ty
  return none

/-- Error unless every block that declares a local declares it at the same
type. Unreachable blocks count too, since translation can resolve a use to a
declaration in one.

Translation gives a use of a CFG-local the type of the declaration of that name
that appears last before it in the source, while this checker scopes the use to
the declaration that dominates it. When two declarations of one local have
different types, the two can disagree, so whether a program is accepted would
depend on the order of its blocks. Requiring one type per local, compared after
aliases are resolved, makes the result independent of that order: both choices
resolve to the same type. -/
def checkInitTypesAgree (procName : CoreIdent)
    (decls : List (Expression.Ident × Expression.Ty × String))
    (sourceLoc : FileRange) : Except Message Unit :=
  match initTypeConflict? decls with
  | none => .ok ()
  | some x => .error <| Message.withRange sourceLoc
    f!"[{procName}]: CFG-local `{x}` is declared at different types in different blocks."

end Procedure

namespace CFG

open Procedure

open Lambda Lambda.LTy.Syntax in
/-- Type-check a `.cfg` body.

Scoping rule: a local declared by an `init` in block `D` may be used in a
reachable block `B` only if `D` dominates `B` according to `computeDominators`.
`D` may be `B` itself; a use that comes before the `init` inside `D` is rejected
later, by the per-block check. For example, a local declared on one arm of a
branch cannot be used where the arms merge. Together with the declaration checks
below, this is meant to ensure that on every path a local is set before it is
read and set only once. That holds only as far as `computeDominators` computes
true dominance, which is not proved (see the `Strata.DL.Imperative.CFGDominators`
module header).

Steps, in order:
1. Shape: unique labels (`checkUniqueLabels`), an existing entry
   (`checkEntryExists`), and existing branch targets (`checkTargetLabels`).
2. Scoping:
   * no block declares a local twice (`checkBlockInitsNodup`);
   * two reachable blocks that declare the same local do not dominate each
     other (`checkInitsIncomparable`);
   * every use of a local in a reachable block has a declaration that
     dominates it (`checkDomScoped`);
   * no reachable block that lies on a cycle declares a local
     (`checkNoLoopInits`).
   Dominance is the map from `computeDominators`.
3. Extra rejections:
   * no two declarations of the same local where one block can reach the other
     (`checkInitsNotReachable`);
   * no local named like a formal, output, or `old` binding
     (`checkInitsNotHeader`);
   * no local declared at two different types (`checkInitTypesAgree`).
4. Each reachable block is type-checked against the base environment plus the
   locals declared by its strict dominators. Type information solved in one
   reachable block is carried to the others, and the final substitution is
   applied to every reachable block. An unreachable block is checked against the
   base environment alone, in its own substitution, and is annotated with that
   substitution; only its fresh-name state is carried forward. So an unreachable
   block is checked only in isolation: it may use a polymorphic formal at a type
   that conflicts with the reachable blocks' use, it may not read a local
   declared in any other block (even another unreachable one), and the returned
   body is well-typed as a whole only on its reachable blocks.

Steps 1 and 2 are the conditions of `WF.WFCFGProp`; the step-3 checks are plain
rejections beyond it. -/
def typeCheck (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (P : Program) (proc : Procedure) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except Message (DetCFG × Core.Expression.TyEnv) := do
  checkUniqueLabels proc.header.name cfg sourceLoc
  checkEntryExists proc.header.name cfg sourceLoc
  checkTargetLabels proc.header.name cfg sourceLoc
  -- The reverse postorder and immediate dominators `idoms` feed both the
  -- dominator map `dom` and the scope walk below.
  let idoms := cfg.computeIdoms
  let dom := cfg.dominatorsOfIdoms idoms
  -- Shared by the guards and the per-block loop.
  let reachable := cfg.reachableLabels
  let succs := cfg.succMap
  let declBlocks := cfgInitDeclBlocks cfg
  checkBlockInitsNodup proc.header.name cfg sourceLoc
  checkInitsIncomparable dom reachable proc.header.name cfg sourceLoc
  checkDomScoped dom reachable proc.header.name cfg sourceLoc
  checkNoLoopInits proc.header.name reachable
    (cycleLabelsWith succs cfg.labels) cfg sourceLoc
  checkInitsNotReachable proc.header.name declBlocks reachable succs sourceLoc
  -- Header names a CFG `init` must not shadow: formals, outputs, and the `old`
  -- bindings synthesized for in-out parameters.
  checkInitsNotHeader proc.header.name proc.entryScope cfg sourceLoc
  let initDeclTypes := cfgInitDeclTypes cfg
  -- Resolve each declarer's `init` type once, the same way the declaring `init`
  -- stores it: `Cmd.typeCheck` runs `preprocess`/`postprocess` on the type
  -- (resolving aliases and instantiating). The resolved `(name, type)` is reused
  -- for every block the declarer dominates, rather than re-resolving per
  -- dominated block.
  let mut resolvedDeclsRev : List (Expression.Ident × Core.Expression.Ty × String) := []
  let mut resolveEnv := Env
  for (x, ty, declLbl) in initDeclTypes do
    -- `preprocess`/`postprocess` report type errors via `Message.fromFormat`,
    -- which carries no source range; the declaring `init`'s own `Cmd.typeCheck`
    -- would attach the command's range. Since this resolution runs before that
    -- per-command pass, name the procedure, local, and declaring block and
    -- supply the procedure's range so the diagnostic is locatable.
    let addCtx := fun (e : Message) =>
      let ctx := s!"[{proc.header.name}]: in `init {x}` declared in block \"{declLbl}\": "
      { e with
        message := ctx ++ e.message,
        fileRange := if e.fileRange.range.isNone then sourceLoc else e.fileRange }
    let (ty', env') ← (CmdType.preprocess C resolveEnv ty).mapError addCtx
    let (ty', env') ← (CmdType.postprocess C env' ty').mapError addCtx
    -- Only a reachable declarer's resolution is carried forward; an unreachable
    -- one is resolved for the type-agreement check alone, so dead-code bindings
    -- stay out of the carried substitution.
    if reachable.contains declLbl then resolveEnv := env'
    resolvedDeclsRev := (x, ty', declLbl) :: resolvedDeclsRev
  let resolvedDecls := resolvedDeclsRev.reverse
  checkInitTypesAgree proc.header.name resolvedDecls sourceLoc
  -- Each reachable declarer block ↦ the resolved `(name, type)` pairs it declares.
  let mut declsOf : Std.HashMap String (List (Expression.Ident × Core.Expression.Ty)) := {}
  for (x, ty', declLbl) in resolvedDecls do
    if reachable.contains declLbl then
      declsOf := declsOf.insert declLbl ((x, ty') :: declsOf.getD declLbl [])
  -- Per-block scope: each reachable block ↦ the base context plus the locals
  -- declared by its strict dominators. Built by one walk over the dominator tree
  -- in reverse postorder, where a block's immediate dominator precedes it: a
  -- block's scope is its immediate dominator's scope extended with that
  -- dominator's own locals. The strict dominators of a block are exactly its
  -- immediate dominator and that dominator's strict dominators, so this yields
  -- the same bindings as adding every strict dominator's locals directly. Their
  -- names are distinct (a block declares a local at most once, and two
  -- comparable declarers of one name are rejected above), so the result does not
  -- depend on insertion order.
  --
  -- Extending the parent's newest frame copies it, so on a chain of declaring
  -- blocks this walk is quadratic, like the dominator map itself.
  let (rpo, idom) := idoms
  let mut scopeCtx : Std.HashMap String (type_of% Env.context) := {}
  for lbl in rpo do
    let ctx :=
      if lbl == cfg.entry then Env.context
      else
        let parent := idom.getD lbl cfg.entry
        let parentCtx := scopeCtx.getD parent Env.context
        match declsOf.getD parent [] with
        | [] => parentCtx
        | ds => { parentCtx with
                  types := parentCtx.types.addInNewest (Strata.Util.HMap.ofList ds) }
    scopeCtx := scopeCtx.insert lbl ctx
  let mut annotated : Std.HashMap String (Imperative.DetBlock String Command Expression) := {}
  -- Carries the type substitution and the fresh-name generator state across
  -- blocks (not the variable scope): a procedure type variable solved in one
  -- block must stay solved for the others, and fresh `$__tyN` names must not be
  -- reused between blocks. The *variable scope* is set per block from
  -- `scopeCtx`.
  let mut carryEnv := resolveEnv.updateContext Env.context
  -- Apply a substitution to a block's annotated commands and branch guard.
  let substBlock := fun (S : type_of% Env.stateSubstInfo.subst)
      (blk' : Imperative.DetBlock String Command Expression) =>
    ({ cmds := blk'.cmds.map (Statement.Command.subst S),
       transfer := match blk'.transfer with
         | .condGoto p lt lf md => .condGoto (LExpr.applyTypeSubst p S) lt lf md
         | .finish md => .finish md } : Imperative.DetBlock String Command Expression)
  -- A reachable block's annotated body is stored unsubstituted; the final
  -- whole-body substitution is applied to it after the per-block loop. A block
  -- with a polymorphic op, constructor, `init`, or `call` whose type variables
  -- are solved by a *later* block's unification therefore gets those variables
  -- resolved in its annotated output too, as a structured body's annotations are.
  -- An unreachable block is stored already substituted with its own solution
  -- (see the `else` branch at the end of the loop).
  for (lbl, blk) in cfg.blocks do
    let blockReachable := reachable.contains lbl
    let mut currentEnv :=
      if blockReachable then carryEnv.updateContext (scopeCtx.getD lbl Env.context)
      else (carryEnv.updateContext Env.context).updateSubst Env.stateSubstInfo
    -- Accumulate in reverse and reverse once, avoiding the quadratic tail append.
    let mut cmdsRev := []
    for cmd in blk.cmds do
      let (cmd', newEnv) ← Statement.typeCheckCmd C currentEnv P cmd
      currentEnv := newEnv
      cmdsRev := cmd' :: cmdsRev
    let cmds' := cmdsRev.reverse
    let transfer' ← match blk.transfer with
      | .condGoto p lt lf md =>
        let (pa, newEnv) ← (LExpr.resolve C currentEnv p).mapError fun e =>
          (Message.fromFormat e).withRangeIfUnknown sourceLoc
        -- Unify the condition's type with `bool` rather than compare it, so a
        -- type variable that another block solves later is accepted in any
        -- block order.
        let boolS ← (Constraints.unify [(pa.toLMonoTy, mty[bool])] newEnv.stateSubstInfo).mapError
          fun _ => Message.withRange sourceLoc
            f!"[{proc.header.name}]: Branch condition in block \"{lbl}\" \
               is not of type bool, got {pa.toLMonoTy}"
        currentEnv := newEnv.updateSubst boolS
        pure (Imperative.DetTransferCmd.condGoto pa.unresolved lt lf md)
      | .finish md => pure (.finish md)
    let blk' : Imperative.DetBlock String Command Expression :=
      { cmds := cmds', transfer := transfer' }
    if blockReachable then
      annotated := annotated.insert lbl blk'
      carryEnv := currentEnv
    else
      -- Keep a dead block's solution out of `carryEnv`: otherwise a dead use of a
      -- polymorphic formal at a conflicting type would reject the procedure, and a
      -- binding made only in dead code would leak into the reachable annotations.
      annotated := annotated.insert lbl (substBlock currentEnv.stateSubstInfo.subst blk')
      carryEnv := { carryEnv with genEnv :=
        { carryEnv.genEnv with genState := currentEnv.genEnv.genState } }
  let S := carryEnv.stateSubstInfo.subst
  let annotatedSubst := annotated.fold
    (init := ({} : Std.HashMap String (Imperative.DetBlock String Command Expression)))
    fun acc lbl blk' =>
      acc.insert lbl (if reachable.contains lbl then substBlock S blk' else blk')
  -- Re-emit blocks in the original source order, with their annotated bodies.
  let annotatedBlocks := cfg.blocks.filterMap fun (lbl, _) =>
    (annotatedSubst.get? lbl).map fun blk' => (lbl, blk')
  let annotatedCFG : DetCFG := { entry := cfg.entry, blocks := annotatedBlocks }
  -- Return the base context, without any block's locals, with its type
  -- variables resolved by the final substitution, as the structured path does
  -- before returning its env.
  carryEnv := carryEnv.updateContext (Lambda.TContext.subst Env.context S)
  return (annotatedCFG, carryEnv)

end CFG

namespace Procedure

-- Error message prefix for errors in processing procedure pre/post conditions.
def conditionErrorMsgPrefix (procName : CoreIdent) (condName : CoreLabel)
    (md : MetaData Expression) : Message :=
  md.toDiagnosticF f!"[{procName}:{condName}]:"

-- Type checking procedure pre/post conditions.
open Lambda.LTy.Syntax in
private def typeCheckConditions (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (conditions : ListMap CoreLabel Check) (procName : CoreIdent) :
    Except Message (Array Expression.Expr × Core.Expression.TyEnv) := do
  let mut results := #[]
  let mut currentEnv := Env
  for (name, condition) in (conditions.keys, conditions.values) do
    let errorPrefix := conditionErrorMsgPrefix procName name condition.md
    let (annotatedExpr, newEnv) ← Lambda.LExpr.resolve C currentEnv condition.expr
                                    |>.mapError (fun e => { errorPrefix with message := errorPrefix.message ++ " " ++ toString e })
    if annotatedExpr.toLMonoTy != mty[bool] then
      .error { errorPrefix with message := errorPrefix.message ++ s!": Expected condition to be of type Bool, but got {annotatedExpr.toLMonoTy}!" }
    results := results.push annotatedExpr.unresolved
    currentEnv := newEnv
  return (results, currentEnv)

def typeCheck (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (p : Program)
    (proc : Procedure) (md : MetaData Expression) : Except Message (Procedure × Core.Expression.TyEnv) := do
  let fileRange := Imperative.getFileRange md |>.getD FileRange.unknown

  -- Validate well-formedness of formals and returns.
  checkParamNames proc fileRange
  checkModificationRights proc fileRange

  let (inp_mty_sig, out_mty_sig, Env) ← proc.header.instantiate C Env.pushEmptyContext
                                          |>.mapError (fun e => Message.withRange fileRange e)

  -- Temporarily add the formals into the context.
  let inp_lty_sig := Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig
  let envWithInputs := Env.addInNewestContext (Strata.Util.HMap.ofList inp_lty_sig)

  -- Type check preconditions.
  -- Note: `envWithInputs` does not have the return variables in the context,
  -- which means that the presence of any return variables in the preconditions
  -- will rightfully flag an error.
  let (preconditions, envAfterPreconds) ← typeCheckConditions C envWithInputs
                                            proc.spec.preconditions proc.header.name

  -- Temporarily add returns into the context.
  let out_lty_sig := Lambda.LMonoTySignature.toTrivialLTy out_mty_sig
  let envWithOutputs := envAfterPreconds.addInNewestContext (T := CoreLParams)
                          (Strata.Util.HMap.ofList out_lty_sig)

  -- Add "old" variables for in-out parameters (those in both inputs and outputs)
  -- so that postconditions and body can reference `old x`.
  let oldInoutBindings : List (CoreIdent × Lambda.LTy) :=
    (getInoutParams inp_mty_sig out_mty_sig).toList.map fun (id, ty) =>
      (CoreIdent.mkOld id.name, .forAll [] ty)
  let envWithOldVars := envWithOutputs.addInNewestContext (Strata.Util.HMap.ofList oldInoutBindings)

  -- Type check postconditions.
  let (postconditions, envAfterPostconds) ← typeCheckConditions C envWithOldVars
                                              proc.spec.postconditions proc.header.name

  -- Type check body.
  -- Note that `Statement.typeCheck` already reports source locations in
  -- error messages.
  let (annotated_body, annotated_cfg, finalEnv) ← match proc.body with
    | .structured ss =>
      let (ss', env') ← Statement.typeCheck C envAfterPostconds p (.some proc) ss
      pure (ss', none, env')
    | .cfg cfgBody =>
      let (cfg', env') ← CFG.typeCheck C envAfterPostconds p proc cfgBody fileRange
      pure ([], some cfg', env')

  -- Remove formals and returns from the context -- they ought to be local to
  -- the procedure body.
  let finalEnv := finalEnv.popContext

  -- Construct final result.
  let finalPreconditions := Procedure.Spec.updateCheckExprs preconditions.toList proc.spec.preconditions
  let finalPostconditions := Procedure.Spec.updateCheckExprs postconditions.toList proc.spec.postconditions
  -- Type arguments are empty below because we've replaced polytypes with monotypes.
  let new_hdr := { proc.header with typeArgs := [],
                                    inputs := inp_mty_sig,
                                    outputs := out_mty_sig }
  let new_spec := { proc.spec with preconditions := finalPreconditions,
                                   postconditions := finalPostconditions }
  let new_body := match annotated_cfg with
    | some cfg' => .cfg cfg'
    | none => .structured annotated_body
  let new_proc := { proc with header := new_hdr, spec := new_spec, body := new_body }

  return (new_proc, finalEnv)

---------------------------------------------------------------------

end Procedure
end Core

end -- public section
