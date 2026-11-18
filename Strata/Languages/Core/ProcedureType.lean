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
public import Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.FunctionType
import Strata.Languages.Core.CmdType

---------------------------------------------------------------------

public section

namespace Core

open Std (ToFormat Format format)
open Imperative (MetaData HasVarsImp)
open Imperative.CFG (cycleLabelsWith succMapSize)
open Imperative.CFG.Dom (dominates)
open Strata (Message FileRange)
open Lambda

/-! ## Procedure type checking with rigid type parameters -/

/-- Deskolemize a `Message`, rewriting a rigid-parameter refinement as a "refined to"
    message. -/
def reformatMessage (known : Lambda.KnownTypes) (σ : RigidNames) (m : Message) : Message :=
  { m with message := toString (reformatError known σ m.message) }

/-- The registered types `known` with the types that the statements `ss` declare, so that a
    message from `ss` shows their names. -/
def withLocalTypes (known : Lambda.KnownTypes) (ss : List Statement) : Lambda.KnownTypes :=
  (Imperative.Block.localTypeDecls ss).foldl (fun ks tc => ks.insert tc.name tc.numargs) known

/-- The type names in the procedure signatures of `program`, computed on first use. -/
def procSigTyNameThunk (program : Program) : Thunk (Std.HashSet String) :=
  Thunk.mk fun _ => .ofList program.procSigTyNames

namespace Procedure

/-- The rigid renaming chosen for the type parameters of procedure `proc` checked in `C`: its
    constants avoid the registered types, the names of `scope` and `progSigs`, and the type
    names `tyNames ()` of `proc`. -/
def rigidNames (scope progSigs : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (proc : Procedure) (tyNames : Unit → List String) :
    RigidNames :=
  rigidNamesAvoiding C scope progSigs proc.header.name.name tyNames proc.header.typeArgs

/-- Reject a parameter whose name starts with `old `: such names denote the initial values
    of in-out parameters. -/
private def checkParamNames (proc : Procedure) (sourceLoc : FileRange) :
    Except Message Unit := do
  match (proc.header.inputs.keys ++ proc.header.outputs.keys).find? CoreIdent.isOldIdent with
  | some id =>
    .error <| Message.withRange sourceLoc
      f!"[{proc.header.name}] Parameter {id}: a name starting with \"old \" denotes the \
         initial value of an in-out parameter!"
  | none => pure ()

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
   block is checked only in isolation: it may use a written type variable of its
   own local at a type that conflicts with the reachable blocks' use of that
   variable, it may not read a local declared in any other block (even another
   unreachable one), and the returned body is well-typed as a whole only on its
   reachable blocks.

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
  -- blocks (not the variable scope): a written type variable of a local solved in
  -- one block must stay solved for the others, and fresh `$__tyN` names must not be
  -- reused between blocks. The *variable scope* is set per block from
  -- `scopeCtx`.
  let mut carryEnv := resolveEnv.updateContext Env.context
  -- Apply a substitution to a block's annotated commands and branch guard.
  let substBlock := fun (S : type_of% Env.stateSubstInfo.subst)
      (blk' : Imperative.DetBlock String Command Expression) => Statement.DetBlock.subst S blk'
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
        -- Resolve as a structured guard is, so a quantifier binder cannot capture an
        -- undeclared free variable of the guard.
        let (pa, newEnv) ←
          (SourceExpr.orFreeVarError
            (fun _ => currentEnv.freeVarCheck p (fun _ => f!"[{proc.header.name}]"))
            (SourceExpr.resolve C currentEnv p)).mapError fun e =>
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
      -- written type variable at a conflicting type would reject the procedure, and a
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

/-- The prefix of an error message about procedure `procName`. -/
def procedureMsgPrefix (procName : CoreIdent) : String :=
  s!"Procedure '{procName.name}': "

/-- Error message prefix for a procedure condition, located at its source range. -/
def conditionErrorMsgPrefix (procName : CoreIdent) (condName : CoreLabel)
    (md : MetaData Expression) : Message :=
  md.toDiagnosticF f!"Procedure '{procName.name}', condition '{condName}': "

/-- Deskolemize a condition-checking failure, rewriting a rigid-parameter refinement as a
    "refined to" message, and prefix it with the procedure and condition name. -/
def conditionErrorMessage (known : Lambda.KnownTypes) (procName : CoreIdent) (σ : RigidNames)
    (label : CoreLabel) (md : MetaData Expression) (e : Format) : Message :=
  let pfx := conditionErrorMsgPrefix procName label md
  { pfx with message := pfx.message ++ toString (reformatError known σ e) }

/-- Deskolemize an error from checking the body of procedure `procName` and prefix it with the
    procedure name, keeping its source location. -/
def bodyErrorMessage (known : Lambda.KnownTypes) (procName : CoreIdent) (σ : RigidNames)
    (m : Message) : Message :=
  let m' := reformatMessage known σ m
  { m' with message := procedureMsgPrefix procName ++ m'.message }

/-- Whether `S` leaves every variable of `rigidVars` unchanged. -/
def ambientRigidVarsFixed (rigidVars : List TyIdentifier) (S : Subst) : Bool :=
  rigidVars.all fun v => LMonoTy.subst S (.ftvar v) == .ftvar v

/-- The failure reason when an inference result refined an ambient rigid type variable. -/
def ambientRigidRefinedMsg : Format := "an ambient rigid type variable was refined"

/-- Reject an inference result that refined an ambient rigid type variable. -/
def ensureAmbientRigidVarsFixed (procName : CoreIdent)
    (rigidVars : List TyIdentifier) (S : Subst) : Except Message Unit :=
  if ambientRigidVarsFixed rigidVars S then
    .ok ()
  else
    throw (Message.fromFormat f!"{procedureMsgPrefix procName}{ambientRigidRefinedMsg}")

/-- Resolve a condition at type `bool` in `Env`, returning it elaborated and deskolemized. -/
private def checkCondition (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (procName : CoreIdent) (σ : RigidNames) (label : CoreLabel) (chk : Check) :
    Except Message Check := do
  let (expr, _, EnvR) ←
    (Function.checkBoolProp C Env (σ.map Prod.fst) σ (format chk.expr) (fun _ => true)
      chk.expr).mapError
      (conditionErrorMessage C.knownTypes procName σ label chk.md)
  unless ambientRigidVarsFixed C.rigidTypeVars EnvR.stateSubstInfo.subst do
    throw (conditionErrorMessage C.knownTypes procName σ label chk.md ambientRigidRefinedMsg)
  .ok { chk with expr := expr }

/-- Check the names of a procedure header (`checkSignatureNames`). -/
def checkHeaderNames (C : Core.Expression.TyContext) (h : Procedure.Header) :
    Except Format Unit :=
  checkSignatureNames (· ∈ C.functions) "Procedure" h.name.name h.typeArgs
    (LMonoTys.freeVars (h.inputs.values ++ h.outputs.values)) (h.inputs.keys ++ h.outputs.keys)

/-- Type check a `Procedure` whose header names passed `checkHeaderNames`: validate the rest of
    its header, then check its conditions and body with the type parameters as rigid constants,
    returning them elaborated and deskolemized. The rigid constants avoid the names of `scope`
    and `progSigs` and the type names `tyNames ()` of `proc`. -/
def typeCheckCore (scope progSigs : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (p : Program)
    (proc : Procedure) (md : MetaData Expression) (tyNames : Unit → List String) :
    Except Message (Procedure × Core.Expression.TyEnv) := do
  let fileRange := Imperative.getFileRange md |>.getD FileRange.unknown
  let h := proc.header
  let name := h.name
  -- Signature well-formedness.
  if !(decide h.inputs.keys.Nodup) then
    throw (md.toDiagnosticF
      f!"{procedureMsgPrefix name}duplicate input parameter names {h.inputs.keys}")
  if !(decide h.outputs.keys.Nodup) then
    throw (md.toDiagnosticF
      f!"{procedureMsgPrefix name}duplicate output parameter names {h.outputs.keys}")
  checkParamNames proc fileRange
  -- Signature well-kindedness.
  let notRegistered := fun ty => f!"{procedureMsgPrefix name}signature type {ty} is not a \
    registered type"
  let (insR, Env) ← (resolveKnownTys C notRegistered h.inputs.values Env).mapError
    md.toDiagnosticF
  let (outsR, Env) ← (resolveKnownTys C notRegistered h.outputs.values Env).mapError
    md.toDiagnosticF
  let h := { h with inputs := h.inputs.keys.zip insR, outputs := h.outputs.keys.zip outsR }
  let allowed := h.outputs.keys ++ HasVarsImp.definedVars (P := Expression) proc.body false
  for v in HasVarsImp.modifiedVars (P := Expression) proc.body do
    if !allowed.contains v then
      throw (md.toDiagnosticF f!"{procedureMsgPrefix name}variable '{v.name}' is modified \
               but is not an output parameter or a local variable")
  -- Check conditions and body with the type parameters as rigid constants.
  let sk := Procedure.rigidNames scope progSigs C proc tyNames
  let C' := addSkolemTypes C sk
  -- Preconditions: input context only.
  let preEnv := Function.formalsEnv Env sk h.inputs
  let preconds' ← proc.spec.preconditions.mapM (fun (label, chk) => do
    let chk' ← checkCondition C' preEnv name sk label chk
    .ok (label, chk'))
  -- Postconditions and body: body context (inputs, outputs, and `old` bindings).
  let inoutOld : @LMonoTySignature Unit :=
    h.getInoutParams.map (fun (id, mty) => (CoreIdent.mkOld id.name, mty))
  let bodyEnv := Function.formalsEnv Env sk (inoutOld ++ h.outputs ++ h.inputs)
  let postconds' ← proc.spec.postconditions.mapM (fun (label, chk) => do
    let chk' ← checkCondition C' bodyEnv name sk label chk
    .ok (label, chk'))
  let body' ← match proc.body with
    | .cfg c => do
      let cSk := if sk.isEmpty then c
        else DetCFG.mapCmdsGuards c (skolemizeCmd none sk) (skolemizeBody none sk)
      let (cOut, bodyEnv') ← (CFG.typeCheck C' bodyEnv p proc cSk fileRange).mapError
        (bodyErrorMessage C'.knownTypes name sk)
      let _ ← ensureAmbientRigidVarsFixed name C'.rigidTypeVars bodyEnv'.stateSubstInfo.subst
      .ok (Procedure.Body.cfg (if sk.isEmpty then cOut
        else DetCFG.mapCmdsGuards cOut (mapCmdTys (deskolemizeTy sk))
          (mapExprTys (deskolemizeTy sk))))
    | .structured ss => do
      let ssSk := if sk.isEmpty then ss else skolemizeStmts none sk ss
      let (ssOut, bodyEnv') ← (Statement.typeCheck C' bodyEnv p (some proc) ssSk).mapError
        (bodyErrorMessage (withLocalTypes C'.knownTypes ss) name sk)
      let _ ← ensureAmbientRigidVarsFixed name C'.rigidTypeVars bodyEnv'.stateSubstInfo.subst
      .ok (Procedure.Body.structured
        (if sk.isEmpty then ssOut else mapStmtsTys (deskolemizeTy sk) ssOut))
  let proc' : Procedure :=
    { proc with
      header := h,
      spec := { preconditions := preconds', postconditions := postconds' },
      body := body' }
  .ok (proc', Env)

/-- Type check a `Procedure` after renaming its reserved type parameters
    (`Procedure.renameReservedTypeArgs`) away from the type variables in scope (`scopeTyVars`)
    and those of the inference substitution, with rigid constants that avoid the names of
    `scope` and `progSigs`. Unlike a function or a lemma, a procedure body is checked under the
    substitution of `Env`, which must not bind or mention the procedure's type parameters; the
    new names keep this. The header names are first checked as written, so that a message shows
    the names the user wrote. The types the procedure writes are collected once, on demand, for
    both the renaming and the rigid constants: renaming type parameters does not change the type
    names a procedure mentions. -/
def typeCheckIn (scope progSigs : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (p : Program)
    (proc : Procedure) (md : MetaData Expression) :
    Except Message (Procedure × Core.Expression.TyEnv) := do
  (checkHeaderNames C proc.header).mapError md.toDiagnosticF
  let annot := Thunk.mk fun _ => procAnnotTys proc
  typeCheckCore scope progSigs C Env p
    (proc.renameReservedTypeArgs (fun _ => Statement.substTyVars Env ++ scopeTyVars C Env)
      fun _ => annot.get) md
    fun _ => procTyNames proc annot.get

/-- Type check a `Procedure` (`typeCheckIn`) with rigid constants that avoid the type names in
    scope in `C` and `Env` and those of the procedure signatures of `p`. Both sets are built
    only for a polymorphic procedure. -/
def typeCheck (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (p : Program)
    (proc : Procedure) (md : MetaData Expression) :
    Except Message (Procedure × Core.Expression.TyEnv) :=
  typeCheckIn (scopeTyNameThunk C Env)
    (procSigTyNameThunk p) C Env p proc md

---------------------------------------------------------------------

end Procedure
end Core

end -- public section
