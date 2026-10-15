/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0

  Copyright (c) 2024 Damiano Testa. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Damiano Testa
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public meta import Lean.Server.InfoUtils
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.Tactic.SimpTrace
public meta import Lean.Meta.Tactic.TryThis
public import Lean.Parser.Term

/-!
# The "flexible" linter

The "flexible" linter makes sure that a "rigid" tactic (such as `rw`) does not act on the
output of a "flexible" tactic (such as `simp`).

For example, this ensures that, if you want to use `simp [...]` in the middle of a proof,
then you should replace `simp [...]` by one of
* a `suffices \"expr after simp\" by simpa` line;
* the output of `simp? [...]`, so that the final code contains `simp only [...]`;
* something else that does not involve `simp`!

Otherwise, the linter will complain.

Simplifying and appealing to a geometric intuition, you can imagine a (tactic) proof like a
directed graph, where
* each node is a local hypothesis or a goal in some metavariable and
* two hypotheses/goals are connected by an arrow if there is a tactic that modifies the source
  of the arrow into the target (this does not apply well to all tactics, but it does apply to
  a large number of them).

With this in mind, a tactic like `rw [lemma]` takes a *very specific* input and return a
*very predictable* output.
Such a tactic is "rigid". Any tactic is rigid, unless it is in `flexible` or `stoppers`.
Conversely, a tactic like `simp` acts on a wide variety of inputs and returns an output that
is possibly unpredictable: if later modifications adds a `simp`-lemma or some internals of
`simp` changes, the output of `simp` may change as well.
Such a tactic is `flexible`. Other examples are `split`, `norm_cast`,...
Let's go back to the graph picture above.
* ✅️ [`rigid` --> `flexible`]
  A sequence `rw [lemma]; simp` is unlikely to break, since `rw [lemma]` produces the same output
  unless some *really major* change happens!
* ❌️ [`flexible` --> `rigid`]
  A sequence `simp; rw [lemma]` is instead more likely to break, since the goal after `simp` is
  subject to change by even a small, likely, modification of the `simp` set.
* ✅️ [`flexible` --> `flexible`]
  A sequence `simp; omega` is also quite stable, since if `omega` was able to close the
  goal with a "weaker" `simp`, it will likely still be able to close the goal with a `simp`
  that takes one further step.
* ✅️ [`flexible` --> `stopper`]
  Finally, a sequence `simp; <stopper>` is stable: a stopper (such as a finishing tactic)
  either produces a normal form or closes the goal outright, so its result is likely to be
  unchanged even if the input differs from the proof in its initial form.
  A stopper can be followed by a rigid tactic, "stopping" the spread of the flexible reach.

What the linter does is keeping track of nodes that are connected by `flexible` tactics and
makes sure that only `flexible` or `stoppers` follow them.
Such nodes are `Stained`.
Whenever it reaches a `stopper` edge, the target node is no longer `Stained` and it is
available again to `rigid` tactics.

Currently, the only tactics that "start" the bookkeeping are most forms of non-`only` `simp`s.
These are encoded by the `flexible?` predicate.
Future modifications of the linter may increase the scope of the `flexible?` predicate and
forbid a wider range of combinations.

## Detecting uses of stained locations

A rigid tactic uses a stained location if its syntax names it (as in `rw [h]` or `rw [] at h`).
The detection is purely syntactic: the linter looks at the identifiers and `at` locations that
the tactic mentions, not at the proof term it assigns to the goal.

## TODO

The example
```lean
example (h : 0 = 0) : True := by
  simp at h
  assumption
```
should trigger the linter, since `assumption` uses `h` that has been "stained" by `simp at h`.
However, `assumption` contains no syntax information for the location `h`, so the linter in its
current, syntax-only form does not catch this.

## Implementation notes

A large part of the code is devoted to tracking `FVar`s and `MVar`s between tactics.

For the `FVar`s, this follows the following heuristic:
* if the unique name of the `FVar` is preserved, then we use that;
* otherwise, if the `userName` of the `FVar` is preserved, then we use that;
* if neither is preserved, we drop the ball and stop tracking the `FVarId`.

For the `MVar`s, we use the information of `Lean.Elab.TacticInfo.goalsBefore` and
`Lean.Elab.TacticInfo.goalsAfter`.
By looking at the `mvar`s that are either only "before" or only "after", we focus on the
"active" goals.
We then propagate all the `FVarId`s that were present in the "before" goals to the "after" goals,
while leaving untouched the ones in the "inert" goals.
-/

meta section

open Lean Elab Command Linter

namespace Strata.Linter

/-- The flexible linter makes sure that "rigid" tactics do not follow "flexible" tactics. -/
public register_option linter.strata.flexible : Bool := {
  defValue := false
  descr := "enable the flexible linter"
}

/-- `flexible? stx` is `true` if `stx` is syntax for a tactic that takes a "wide" variety of
inputs and modifies them in possibly unpredictable ways.

The prototypical flexible tactic is `simp`.
The prototypical non-flexible tactic `rw`.
`simp only` is also non-flexible. -/
--  TODO: adding more entries here, allows to consider more tactics to be flexible
def flexible? : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.simp #[_, _, _, only?, _, _] => only?[0].getAtomVal != "only"
  | .node _ ``Lean.Parser.Tactic.simpAll #[_, _, _, only?, _] => only?[0].getAtomVal != "only"
  | _ => false


/-!
### Heuristics for determining goals that a tactic modifies and what they become

The two definitions `goalsTargetedBy`, `goalsCreatedBy` extract a list of
`MVarId`s attempting to determine on which goals the tactic `t` is acting and what are the
resulting modified goals.
This is mostly based on the heuristic that the tactic will "change" an `MVarId`.
-/

open Lean Elab in
/-- `goalsTargetedBy t` are the `MVarId`s before the `TacticInfo` `t` that "disappear" after it.
They should correspond to the goals in which the tactic `t` performs some action. -/
def goalsTargetedBy (t : TacticInfo) : List MVarId :=
  t.goalsBefore.filter (·.name ∉ t.goalsAfter.map (·.name))

open Lean Elab in
/-- `goalsCreatedBy t` are the `MVarId`s after the `TacticInfo` `t` that were not present before.
They should correspond to the goals created or changed by the tactic `t`. -/
def goalsCreatedBy (t : TacticInfo) : List MVarId :=
  t.goalsAfter.filter (·.name ∉ t.goalsBefore.map (·.name))

end Strata.Linter

namespace Strata.Linter.Flexible

/-- Data extracted from an InfoTree for each tactic. -/
structure TacticData where
  stx : Syntax
  /-- ContextInfo for running MetaM -/
  ci : ContextInfo
  mctxBefore : MetavarContext
  mctxAfter : MetavarContext
  /-- Goals the tactic acted on (present before, gone after); see `Strata.Linter.goalsTargetedBy`. -/
  goalsTargetedBy : List MVarId
  /-- Goals the tactic produced (absent before, present after); see `Strata.Linter.goalsCreatedBy`. -/
  goalsCreatedBy : List MVarId

/-- `extractTacticData tree` extracts tactic information from an `InfoTree`,
including the `ContextInfo` needed to run `MetaM` computations.
-/
def extractTacticData (tree : InfoTree) : Array TacticData :=
  tree.foldInfo (init := #[]) fun ci info acc =>
    match info with
    | .ofTacticInfo i =>
      if (i.stx.getRange? true).isSome then
        acc.push {
          stx := i.stx
          ci := ci
          mctxBefore := i.mctxBefore
          mctxAfter := i.mctxAfter
          goalsTargetedBy := Strata.Linter.goalsTargetedBy i
          goalsCreatedBy := Strata.Linter.goalsCreatedBy i
        }
      else acc
    | _ => acc

/-- `Stained` is the type of the stained locations: it can be
* a `Name` (typically of associated to the `FVarId` of a local declaration);
* the goal (`⊢`);
* the "wildcard" -- all the declaration in context (`*`).
-/
inductive Stained
  | name     : Name → Stained
  | goal     : Stained
  | wildcard : Stained
  deriving Repr, Inhabited, DecidableEq, Hashable

/-- Converting a `Stained` to a `String`:
* a `Name` is represented by the corresponding string;
* `goal` is represented by `⊢`;
* `wildcard` is represented by `*`.
-/
instance : ToString Stained where
  toString | .name n => n.toString | .goal => "⊢" | .wildcard => "*"

/--
`toStained stx` scans the input `Syntax` `stx` extracting identifiers and atoms, making an effort
to convert them to `Stained`.
The function is used to extract "location" information about `stx`: either explicit locations as in
`rw [] at locations` or implicit ones as `rw [h]`.

Whether or not what this function extracts really is a location will be determined by the linter
using data embedded in the `InfoTree`s. -/
partial def toStained : Syntax → Std.HashSet Stained
  | .node _ _ arg => (arg.map toStained).foldl (.union) {}
  | .ident _ _ val _ => {.name val}
  | .atom _ val => match val with
                  | "*" => {.wildcard}
                  | "⊢" => {.goal}
                  | "|" => {.goal}
                  | _ => {}
  | _ => {}

/-- `getStained stx` expects `stx` to be an argument of a node of `SyntaxNodeKind`
`Lean.Parser.Tactic.location`.
Typically, we apply `getStained` to the output of `getLocs`.

See `getStained!` for a similar function. -/
partial
def getStained (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : Std.HashSet Stained :=
  match stx with
    | stx@(.node _ ``Lean.Parser.Tactic.location loc) =>
      if all? stx then {} else (loc.map toStained).foldl (·.union) {}
    | .node _ _ args => (args.map (getStained · all?)).foldl (·.union) {}
    | _ => default

/-- `getStainedInOrder stx` lists the locations of the `at` clause(s) of `stx` in source order
(`getStained` returns a `HashSet`, which loses that order). It mirrors `getStained` without the
`all?` filter. Used only to order the warning message, whose locations are taken from the stains
themselves, so a mismatch with `getStained` can only affect the order, never what is reported. -/
partial def getStainedInOrder : Syntax → Array Stained
  | .node _ ``Lean.Parser.Tactic.location loc => loc.flatMap leaves
  | .node _ _ args => args.flatMap getStainedInOrder
  | _ => #[]
where
  /-- `toStained` returns at most one location per leaf, so flattening leaves keeps source order. -/
  leaves : Syntax → Array Stained
    | .node _ _ args => args.flatMap leaves
    | stx => (toStained stx).toArray

/-- `getStained! stx` expects `stx` to be an argument of a node of `SyntaxNodeKind`
`Lean.Parser.Tactic.location`.
Typically, we apply `getStained!` to the output of `getLocs`.

It returns the `HashSet` of `Stained` determined by the locations in `stx`.

The only difference with `getStained stx`, is that `getStained!` never returns `{}`:
if `getStained stx = {}`, then `getStained' stx = {.goal}`.

This means that tactics that do not have an explicit "`at`" in their syntax will be treated as
acting on the main goal. -/
def getStained! (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : Std.HashSet Stained :=
  let out := getStained stx all?
  if out.size == 0 then {.goal} else out

/-- `Stained.toFMVarId mv lctx st` takes a metavariable `mv`, a local context `lctx` and
a `Stained` `st` and returns the array of pairs `(FVarId, mv)`s that `lctx` assigns to `st`
(the second component is always `mv`):
* if `st` "is" a `Name`, returns the singleton of the `FVarId` with the name carried by `st`;
* if `st` is `.goal`, returns the singleton `#[default]`;
* if `st` is `.wildcard`, returns the array of all the `FVarId`s in `lctx` with also `default`
  (to keep track of the `goal`).
-/
def Stained.toFMVarId (mv : MVarId) (lctx: LocalContext) : Stained → Array (FVarId × MVarId)
  | name n   => match lctx.findFromUserName? n with
                  | none => #[]
                  | some decl => #[(decl.fvarId, mv)]
  | goal     => #[(default, mv)]
  | wildcard => (lctx.getFVarIds.push default).map (·, mv)

/-- `SyntaxNodeKind`s that are mostly "formatting": mostly they are ignored
because we do not want the linter to spend time on them.
The nodes that they contain will be visited by the linter anyway.
The nodes that *follow* them, though, will *not* be visited by the linter.
-/
def stoppers : Std.HashSet Name :=
  { -- "properly stopper tactics": the effect of these tactics is to return a normal form
    -- (or possibly be finishing tactics -- the ultimate normal form!
    -- finishing tactics could equally well be considered as `flexible`, but as there is
    -- no possibility of a follower anyway, it does not make a big difference.)
    ``Lean.Parser.Tactic.tacticSorry,
    ``Lean.Parser.Tactic.tacticRepeat_,
    ``Lean.Parser.Tactic.tacticStop_,
    -- "continuators": the *effect* of these tactics is similar the "properly stoppers" above,
    -- though they typically wrap other tactics inside them.
    -- The linter ignores the wrapper, but does recurse into the enclosed tactics
    ``Lean.Parser.Tactic.tacticSeq1Indented,
    ``Lean.Parser.Tactic.tacticSeq,
    ``Lean.Parser.Term.byTactic,
    `by,
    ``Lean.Parser.Tactic.tacticTry_,
    ``Lean.Parser.Tactic.allGoals,
    ``Lean.Parser.Tactic.«tactic_<;>_»,
    -- pure delegating wrappers: they do not themselves act on a stained location, they only
    -- run the tactic(s) nested inside them, which the linter visits on their own turn.
    ``Lean.Parser.Tactic.«tacticNext_=>_»,
    ``Lean.Parser.Tactic.paren,
    ``Lean.Parser.Tactic.focus,
    ``Lean.Parser.Tactic.first,
    `choice, -- involved in `first`
    ``Lean.Parser.Tactic.case,
    -- `next`/`case` elaborate to a goal-tagging step wrapped in an anonymous `null` node that
    -- carries a synthetic `TacticInfo`; it is pure structure, never a user-written rigid tactic.
    Lean.nullKind,
    ``cdotTk,
    ``cdot }

/-- `SyntaxNodeKind`s that are allowed to follow a flexible tactic:
  `simp`, `simp_all`, `simpa`, `simpa!`, `dsimp`, `constructor`, `congr`, `done`, `rfl`, `ac_rfl`,
  `omega`, `grind`, `grobner`, `lia`, `norm_cast`, `split`.
-/
def flexible : Std.HashSet Name :=
  { ``Lean.Parser.Tactic.simp,
    ``Lean.Parser.Tactic.simpAll,
    ``Lean.Parser.Tactic.simpa,
    ``Lean.Parser.Tactic.simpaUsingBang,
    ``Lean.Parser.Tactic.dsimp,
    ``Lean.Parser.Tactic.constructor,
    ``Lean.Parser.Tactic.congr,
    ``Lean.Parser.Tactic.done,
    ``Lean.Parser.Tactic.tacticRfl,
    ``Lean.Parser.Tactic.acRfl,
    ``Lean.Parser.Tactic.omega,
    ``Lean.Parser.Tactic.grind,
    ``Lean.Parser.Tactic.grobner,
    ``Lean.Parser.Tactic.lia,
    ``Lean.Parser.Tactic.tacticNorm_cast__,
    ``Lean.Parser.Tactic.split
  }

/-- By default, if a `SyntaxNodeKind` is not special-cased here, then the linter assumes that
the tactic will use the goal as well: this heuristic works well with `exact`, `refine`, `apply`.
For tactics such as `cases` this is not true: for these tactics, `usesGoal?` yields `false`. -/
def usesGoal? : SyntaxNodeKind → Bool
  | ``Lean.Parser.Tactic.cases => false
  | ``Lean.Parser.Tactic.obtain => false
  | ``Lean.Parser.Tactic.tacticHave__ => false
  | ``Lean.Parser.Tactic.rcases => false
  | ``Lean.Parser.Tactic.specialize => false
  | ``Lean.Parser.Tactic.subst => false
  | ``«tacticBy_cases_:_» => false
  | ``Lean.Parser.Tactic.induction => false
  | ``Lean.Parser.Tactic.funInduction => false
  | ``Lean.Parser.Tactic.funCases => false
  | _ => true

/-- `delegatesGoalViaBy stx` is `true` when the tactic `stx` discharges the goal through a `by`
tactic block, supplied as its *direct* term argument, **whose first tactic is itself `flexible`
or a `stopper`** (as in `exact by omega`, `exact by rfl`, `exact (by simp)`).

The subtlety motivating the first-tactic check: the `by` block runs on a *fresh* metavariable
that was never stained, so simply exempting every outer `exact by …` would silence the very
flexible→rigid pattern this linter exists to catch -- `simp; exact by exact hb` would slip
through even though the inner `exact hb` consumes the stained goal. We only exempt when the inner
block *starts* with an allowed closer (`flexible`/`stoppers`), i.e. the kind of tactic the stain
is permitted to flow into; a block starting with a rigid tactic (`exact`, `rw`, …) keeps the
outer tactic subject to the stained-goal check.

A `by` buried deeper in a larger term is also excluded -- in `exact (by … ) ▸ h` or
`refine ⟨by …, _⟩` the outer tactic still genuinely uses the goal. Explicitly named locations in
`stx` (e.g. `exact (by simp) h`) are detected separately regardless. -/
partial def delegatesGoalViaBy (stx : Syntax) : Bool :=
  stx.getArgs.any directByDelegates
where
  /-- `true` when `s` is a `by` block (possibly wrapped only in parentheses or a type ascription)
  whose first tactic is `flexible` or a `stopper`. -/
  directByDelegates : Syntax → Bool
    | .node _ ``Lean.Parser.Term.byTactic args => (firstTacticKind? args).any innerDelegates
    | .node _ ``Lean.Parser.Term.paren args => args.any directByDelegates
    | .node _ ``Lean.Parser.Term.typeAscription args => args.any directByDelegates
    | _ => false
  /-- The inner block's first tactic is one the stain may legitimately flow into. -/
  innerDelegates (k : SyntaxNodeKind) : Bool := flexible.contains k || stoppers.contains k
  /-- The `SyntaxNodeKind` of the first tactic inside a `by` block's argument array. The shape is
  `byTactic → tacticSeq → tacticSeq1Indented → null → [tac, (`;`), …]`, so we descend to the first
  element of that `null` list. -/
  firstTacticKind? (byArgs : Array Syntax) : Option SyntaxNodeKind := do
    let seq ← byArgs.find? (·.isOfKind ``Lean.Parser.Tactic.tacticSeq)
    let seq1 ← seq.getArgs.find? (·.isOfKind ``Lean.Parser.Tactic.tacticSeq1Indented)
    let lst ← seq1.getArgs.find? (·.isOfKind Lean.nullKind)
    let fst ← lst.getArgs[0]?
    return fst.getKind

/-- `getFVarIdCandidates fv name lctx` takes an input an `FVarId`, a `Name` and a `LocalContext`.
It returns an array of guesses for a "best fit" `FVarId` in the given `LocalContext`.
The first entry of the array is the input `FVarId` `fv`, if it is present.
The next entry of the array is the `FVarId` with the given `Name`, if present.

Usually, the first entry of the returned array is "the best approximation" to `(fv, name)`. -/
def getFVarIdCandidates (fv : FVarId) (name : Name) (lctx : LocalContext) : Array FVarId :=
  #[lctx.find? fv, lctx.findFromUserName? name].reduceOption.map (·.fvarId)

/-!
Tactics often change the name of the current `MVarId`, as well as the names of the `FVarId`s
appearing in their local contexts.
The function `reallyPersist` makes an attempt at "tracking" pairs `(fvar, mvar)` across a
simultaneous change represented by an "old" list of `MVarId`s and the corresponding
`MetavarContext` and a new one.

This arises in the context of the information encoded in the `InfoTree`s when processing a
tactic proof.
-/

/-- `persistFVars` is one step in persisting: track a single `FVarId` between two `LocalContext`s.
If an `FVarId` with the same unique name exists in the new context, use it.
Otherwise, if an `FVarId` with the same `userName` exists in the new context, use it.
If both of these fail, return `default` (i.e. "fail"). -/
def persistFVars (fv : FVarId) (before after : LocalContext) : FVarId :=
  let ldecl := (before.find? fv).getD default
  (getFVarIdCandidates fv ldecl.userName after).getD 0 default

/-- `reallyPersist` converts an array of pairs `(fvar, mvar)` to another array of the same type. -/
def reallyPersist
    (fmvars : Array (FVarId × MVarId)) (mvs0 mvs1 : List MVarId) (ctx0 ctx1 : MetavarContext) :
    Array (FVarId × MVarId) := Id.run do
  -- split the input `fmvars` into
  -- * the `active` ones, whose `mvar` appears in `mvs0` and
  -- * the `inert` ones, the rest.
  -- `inert` gets copied unchanged, while we transform `active`
  let (active, inert) := fmvars.partition fun (_, mv) => mvs0.contains mv
  let mut new := #[]
  for (fvar, mvar) in active do       -- for each `active` pair `(fvar, mvar)`
    match ctx0.decls.find? mvar with  -- check if `mvar` is managed by `ctx0` (it should be)
      | none => -- the `mvar` is not managed by `ctx0`: no change
        new := new.push (fvar, mvar)
      | some mvDecl0 => -- the `mvar` *is* managed by `ctx0`: push the pair `(fvar, mvar)` through
        for mv1 in mvs1 do  -- for each new `MVarId` in `mvs1`
          match ctx1.decls.find? mv1 with  -- check if `mv1` is managed by `ctx1` (it should be)
            | none => pure () -- `mv1` is not managed by `ctx1`: nothing to persist
            | some mvDecl1 =>  -- we found a "new" declaration
              let persisted_fv := persistFVars fvar mvDecl0.lctx mvDecl1.lctx  -- persist `fv`
              new := new.push (persisted_fv, mv1)
  return inert ++ new

/-- Data stored for each "stained" location. -/
structure StainData where
  /-- The stained location -/
  stained : Stained
  /-- The syntax of the flexible tactic that caused the stain -/
  stx : Syntax
  /-- ContextInfo for running MetaM -/
  ci : ContextInfo
  /-- MetavarContext before the flexible tactic -/
  mctx : MetavarContext
  /-- Goals before the flexible tactic -/
  goals : List MVarId
  /-- Index of the flexible tactic's `TacticInfo` node among the extracted `TacticData`.
  `StainData`s with the same `runIdx` come from the same run, so they share `mctx`, `ci` and
  `goals`. The same syntax can run several times on the same goal under different `mctx`s
  (e.g. when backtracking through `first`), so these runs are kept apart. -/
  runIdx : Nat

/-- Re-run the `simp`/`simp_all` call `stx` on `goal` exactly as the user wrote it (lemmas,
erasures, `[*]`, config, discharger and `at` location) and return the lemmas it used.
This mirrors `evalSimp`/`evalSimpAll` in `Lean.Elab.Tactic.Simp`. -/
def rerunSimp (stx : Syntax) (goal : MVarId) : TermElabM Meta.Simp.UsedSimps := do
  let used ← IO.mkRef ({} : Meta.Simp.UsedSimps)
  discard <| Tactic.run goal do
    let stats ← match stx.getKind with
      | ``Lean.Parser.Tactic.simp =>
        let { ctx, simprocs, dischargeWrapper, .. } ←
          Tactic.mkSimpContext stx (eraseLocal := false)
        dischargeWrapper.with fun discharge? =>
          Tactic.simpLocation ctx simprocs discharge? (Tactic.expandOptLocation stx[5])
      | ``Lean.Parser.Tactic.simpAll =>
        let { ctx, simprocs, .. } ← Tactic.mkSimpContext stx (eraseLocal := true)
          (kind := .simpAll) (ignoreStarArg := true)
        pure (← Meta.simpAll (← Tactic.getMainGoal) ctx simprocs).2
      | _ => throwUnsupportedSyntax
    used.set stats.usedTheorems
  used.get

/-- Generate a `simp only [...]`/`simp_all only [...]` suggestion for a flexible
`simp`/`simp_all` call, by re-running it in the context where it originally ran and
keeping only the lemmas it used, as `simp?` does.

One flexible-tactic range can be reached on several goals that were created at *different* times
(e.g. `all_goals (constructor; simp)`, where each `constructor` makes a fresh goal). Such goals
live in different `MetavarContext`s, so each `StainData` in `stains` carries its *own* `mctx`,
`ci` and goal list. We re-run `simp` for each goal under *that goal's* context and union the
lemmas used, so the suggestion covers every branch. The re-run is guarded *per goal* with
`tryCatchRuntimeEx`, so a goal we cannot re-run (missing from its context, or running out of
heartbeats) drops only its own lemmas rather than the entire suggestion.

The single suggestion replaces the tactic in *every* branch, so it must read the same in each.
`mkSimpCallStx` names used local hypotheses by their user name in the current local context and
silently drops those absent from it. So we build the call in every goal's context and give up if
any two differ: e.g. `refine ⟨fun e1 => ?_, fun e2 => ?_⟩; all_goals simp [*]` uses `e1` in one
branch and `e2` in the other, and no single `simp only [...]` names both. (Hypotheses with the
same name in every branch, like `fun e => ?_` twice, give identical calls and are kept.)
Returns `none` if the tactic is not `simp`/`simp_all`, if no goal yielded any lemmas, or if the
branches disagree on the call. -/
def generateSimpSuggestion (stainList : Array StainData) (stainStx : Syntax) :
    CoreM (Option Syntax) := do
  unless stainStx.getKind matches ``Lean.Parser.Tactic.simp | ``Lean.Parser.Tactic.simpAll do
    return none
  let mut used : Meta.Simp.UsedSimps := {}
  -- Every goal resolvable in its own context, each paired with that context; the final call
  -- syntax is built in each of them.
  let mut ctxs : Array (StainData × LocalContext) := #[]
  -- `warnData` records one `StainData` per rigid *use* of the flexible tactic, and several uses
  -- can come from the same run (e.g. one per location of `simp at h ⊢`). Re-running `simp` is the
  -- expensive part, so we re-run each goal at most once per run. Keying on the `MVarId` alone is
  -- not enough: backtracking (`first | (..; simp; ..) | (..; simp; ..)`) runs the same syntax on
  -- the same goal under different `mctx`s, which can make `simp` use different lemmas.
  let mut seenGoals : Std.HashSet (Nat × MVarId) := {}
  for stainData in stainList do
    for goal in stainData.goals do
      let key := (stainData.runIdx, goal)
      if seenGoals.contains key then continue
      let some mvDecl := stainData.mctx.decls.find? goal | continue
      seenGoals := seenGoals.insert key
      ctxs := ctxs.push (stainData, mvDecl.lctx)
      -- Re-run this goal under its *own* `StainData`'s context, not a shared one.
      -- `tryCatchRuntimeEx` rather than `try`: a plain `catch` lets runtime exceptions
      -- (e.g. `maxHeartbeats`) escape, and the re-run spends the command's heartbeat budget.
      let goalUsed? ← tryCatchRuntimeEx
        (some <$> stainData.ci.runMetaM mvDecl.lctx do
          Meta.withMCtx stainData.mctx (rerunSimp stainStx goal).run')
        (fun _ => pure none)
      let some goalUsed := goalUsed? | continue
      for thm in goalUsed.toArray do
        used := used.insert thm
  if used.map.isEmpty then
    return none
  let mut callStx? : Option Syntax := none
  for (stainData, lctx) in ctxs do
    let callStx ← stainData.ci.runMetaM lctx do
      Meta.withMCtx stainData.mctx do
        Tactic.mkSimpCallStx stainStx used
    match callStx? with
    | none => callStx? := some callStx
    -- `==` on `Syntax` is `structEq`, which ignores source info.
    | some prev => if prev != callStx then return none
  return callStx?

/-- The main implementation of the flexible linter. -/
def flexibleLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterValue linter.strata.flexible (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let tacticData := trees.foldl (init := #[]) fun acc tree => acc ++ extractTacticData tree
  -- `stains` records pairs `(location, mvar)`, where
  -- * `location` is either a hypothesis or the main goal modified by a flexible tactic and
  -- * `mvar` is the metavariable containing the modified location
  -- We also track the ContextInfo and MetavarContext for generating suggestions
  let mut stains : Array ((FVarId × MVarId) × StainData) := #[]
  let mut msgs : Array (Syntax × StainData) := #[]
  for (td, runIdx) in tacticData.zipIdx do
    let s := td.stx
    let ctx0 := td.mctxBefore
    let ctx1 := td.mctxAfter
    let mvs0 := td.goalsTargetedBy
    let mvs1 := td.goalsCreatedBy
    let skind := s.getKind
    let shouldStain? := flexible? s && mvs1.length == mvs0.length
    if !shouldStain? && stains.isEmpty then continue
    if stoppers.contains skind then continue
    for d in getStained! s do
      if shouldStain? then
        for currMVar1 in mvs1 do
          let lctx1 := (ctx1.decls.findD currMVar1 default).lctx
          let locsAfter := d.toFMVarId currMVar1 lctx1
          -- Store ContextInfo, mctxBefore, and goals for generating suggestions later
          let stainData : StainData := {
            stained := d, stx := s, ci := td.ci, mctx := ctx0, goals := mvs0, runIdx
          }
          stains := stains ++ locsAfter.map (fun l ↦ (l, stainData))
      else
        -- A rigid tactic is assumed to use the goal (`usesGoal?`), unless it merely delegates the
        -- goal to a nested `by` block (`exact by omega`), whose inner tactics are linted on their
        -- own turn. Named locations in its syntax are always collected.
        let stained_in_syntax :=
          if usesGoal? skind && !delegatesGoalViaBy s then (toStained s).insert d else toStained s
        if !flexible.contains skind then
          for currMv0 in mvs0 do
            let lctx0 := (ctx0.decls.findD currMv0 default).lctx
            -- An `Array` rather than a `HashSet`: `FVarId`/`MVarId` hashes come from fresh unique
            -- names, which differ between the language server and batch `lean`, so iterating a
            -- `HashSet` here would make the message order (and `#guard_msgs`) mode-dependent.
            let mut foundFvs : Array (FVarId × MVarId) := #[]
            for st in stained_in_syntax do
              for d in st.toFMVarId currMv0 lctx0 do
                if !foundFvs.contains d then foundFvs := foundFvs.push d
            for l in foundFvs do
              if let some (_stdLoc, stainData) := stains.find? (Prod.fst · == l) then
                msgs := msgs.push (s, stainData)

      -- tactics often change the name of the current `MVarId`, so we migrate the `FvarId`s
      -- in the "old" `mvars` to the "same" `FVarId` in the "new" `mvars`
      let mut new : Array ((FVarId × MVarId) × StainData) := .empty
      for (fv, stainData) in stains do
        let psisted := reallyPersist #[fv] mvs0 mvs1 ctx0 ctx1
        if psisted == #[] && mvs1 != [] then
          new := new.push (fv, stainData)
        for p in psisted do new := new.push (p, stainData)
      stains := new

  -- One rigid tactic can match several stained locations (e.g. `simp at *` stains the goal and
  -- every hypothesis, so a later `exact h` matches more than one), and one flexible tactic can
  -- feed several rigid tactics (`simp at h; rw [..] at h; exact h`) or several goals
  -- (`all_goals simp`). We report two things with different granularity:
  --   * the warning on the flexible tactic and its `Try this:` suggestion render only from the
  --     flexible tactic itself, so they are *identical* across every rigid use it feeds -- emit
  --     them once per flexible-tactic range, unioning the goals of all its uses so the
  --     `simp only [...]` suggestion covers every goal's lemmas; otherwise, under
  --     `warningAsError`, one flexible tactic feeding two rigid uses raises duplicate errors and
  --     each suggestion lists only its own goal's lemmas (applying either breaks the other goal);
  --   * the per-rigid-tactic info line names the specific stained location ("uses `h`" vs
  --     "modifies the current goal"), so it stays distinct per (rigid, flexible, location) triple.
  -- `none` for syntax without a canonical range. `extractTacticData` already drops such tactics,
  -- but we must not fold them all into one shared key if that ever changes: a flexible tactic
  -- without a range is skipped entirely, while a rigid one only loses its info line.
  let posOf (stx : Syntax) : Option (Nat × Nat) :=
    (stx.getRange? true).map fun r => (r.start.byteIdx, r.stop.byteIdx)
  let mut seenInfo : Std.HashSet ((Nat × Nat) × (Nat × Nat) × Stained) := {}
  let mut infoMsgs : Array (Syntax × StainData) := #[]
  let mut warnOrder : Array (Nat × Nat) := #[]
  let mut warnData : Std.HashMap (Nat × Nat) (Syntax × Array StainData) := {}
  for (s, stainData) in msgs do
    let some flexKey := posOf stainData.stx | continue
    if let some rigidKey := posOf s then
      let infoKey := (rigidKey, flexKey, stainData.stained)
      if !seenInfo.contains infoKey then
        seenInfo := seenInfo.insert infoKey
        infoMsgs := infoMsgs.push (s, stainData)
    match warnData.get? flexKey with
    | none =>
      warnOrder := warnOrder.push flexKey
      warnData := warnData.insert flexKey (s, #[stainData])
    | some (s0, sds) =>
      -- Same flexible tactic reached again (another goal/location): keep this use's own
      -- `StainData` (its `mctx`/`ci`/goals) alongside the others, so the suggestion can re-run
      -- each goal under its *own* context rather than a single shared one.
      warnData := warnData.insert flexKey (s0, sds.push stainData)

  -- Emit one warning + one `Try this:` suggestion per flexible-tactic use.
  for flexKey in warnOrder do
    let some (_s, flexStains) := warnData.get? flexKey | continue
    let some stainData := flexStains[0]? | continue
    let stainStx := stainData.stx
    -- A flexible tactic can modify several locations at once (`simp at h ⊢`), each recorded as a
    -- separate `StainData`. List every distinct one that a rigid tactic later used, in the order
    -- they appear in the tactic's `at` clause; anything not written there (the implicit `⊢` of a
    -- plain `simp`) goes last. All of them come from `getStained!` on this one syntax, so `*` never
    -- appears alongside other locations.
    let used := flexStains.map (·.stained)
    let mut stainedLocs : Array Stained := #[]
    for d in getStainedInOrder stainStx ++ used do
      if used.contains d && !stainedLocs.contains d then stainedLocs := stainedLocs.push d
    let hasWildcard := stainedLocs.contains .wildcard
    -- `` `a`, `b` `` for the message, listing each location backticked.
    let locList : MessageData :=
      MessageData.joinSep (stainedLocs.toList.map (m!"`{·}`")) m!", "
    let stainStr := (stainStx.reprint.getD s!"{stainStx}").trimAscii
    let msg := match stainStx.getKind with
      | ``Lean.Parser.Tactic.simp =>
        if hasWildcard then
          m!"`{stainStr}` is a flexible tactic that potentially modifies all \
          hypotheses and the current goal with a wildcard `*`. \
          Try `simp?` and use the suggested `simp only [...]`. \
          Alternatively, use `suffices` to explicitly state the simplified form."
        else
          m!"`{stainStr}` is a flexible tactic modifying {locList}. \
          Try `simp?` and use the suggested `simp only [...]`. \
          Alternatively, use `suffices` to explicitly state the simplified form."
      | ``Lean.Parser.Tactic.simpAll =>
        m!"`{stainStr}` is a flexible tactic modifying {locList}. \
          Try `simp_all?` and use the suggested `simp_all only [...]`. \
          Alternatively, use `suffices` to explicitly state the simplified form."
      | _ =>
        m!"`{stainStr}` is a flexible tactic modifying {locList}."
    Linter.logLint linter.strata.flexible stainStx msg
    -- Built only after the warning is logged, and fully guarded: a failure here (including a
    -- runtime exception) drops just the `Try this:` suggestion, never the warning itself.
    let suggestion? ← liftCoreM <| tryCatchRuntimeEx
      (generateSimpSuggestion flexStains stainStx) (fun _ => pure none)
    if let some suggStx := suggestion? then
      liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion stainStx
        { suggestion := .tsyntax (kind := `tactic) ⟨suggStx⟩ } (origSpan? := stainStx)

  -- Emit the per-rigid-tactic info line once per distinct stained location.
  for (s, stainData) in infoMsgs do
    let stainStx := stainData.stx
    let d := stainData.stained
    let fm ← getFileMap
    let stainLine? := stainStx.getPos?.map (Position.line ∘ fm.toPosition)
    let lineStr := if let some line := stainLine? then s!" on line {line}" else ""
    let atomStr := match stainStx[0] with
      | .atom _ val => "the flexible tactic " ++ m!"`{val}`"
      | _ => "a flexible tactic"
    logInfoAt s <| match d with
    | .name _ => m!"`{.group s}`\nuses `{d}`, which was modified by {atomStr}{lineStr}."
    | .goal =>
      m!"`{.group s}`\nmodifies the current goal, which was modified by {atomStr}{lineStr}."
    | .wildcard => m!"`{.group s}`\nuses a rigid tactic. Previously, {atomStr}, which \
        potentially modified all hypotheses and the goal with a wildcard `*`, was used{lineStr}."

initialize addLinter flexibleLinter

end Strata.Linter.Flexible
