/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.PassiveVCGenCoreProgram
public import Strata.Languages.Core.InterpreterReplay
public import Strata.Languages.Core.InterpreterEval
public import Strata.Languages.Core.InterpreterCFG
public import Strata.Languages.Core.SMTEncoder
public import Strata.Transform.CallElim

/-! # Validating a model of a cut loop by replay

CFG loop elimination replaces a loop by an arbitrary iteration that satisfies the
invariant, so a model of an obligation resting on the cut need not be a run of the
program. `replayValidates` checks it against the program before the cut: it takes the
model's values of the procedure's parameters on entry, runs the procedure's CFG
concretely from them (with its preconditions assumed and its postconditions
asserted, as the passive VC phase brackets the body), and accepts the model when that
run reaches the obligation's check with the value the model's query gives it: failing,
for a model of the validity query; holding, for one of the satisfiability query.

Replay (`runReplay`) enforces every `assume` on the run, and a nondeterministic value
the model does not supply gets its type's default, which a run may take. So a run it
accepts is a run of the procedure, whatever values were chosen: the verdict does not
depend on reading the model's entry values right, only its completeness does. The
program before the cut has been through the phases before it, so it may hold the
assumptions of an abstraction, such as the contract call elimination puts in place of
a call (`havoc y; assume post`): a run that executes such an assumption (`abstracted`
holds of its label) runs the abstraction rather than the program, and is not
accepted. A run
that stops (the fuel runs out, an expression does not evaluate, an assumption fails)
is not accepted, and the result stays unknown.

Every procedure the run calls first assumes each of its preconditions, free ones
included (`asCalled`), and the run stops at a check other than the target that fails,
so every procedure in an accepted run, the check's own included, is entered in a state
that meets its preconditions. The target is marked in its own procedure only
(`tagTargetIn`), so a check of another procedure with the same label and metadata, which
the run may reach in a call, does not confirm it, while a recursive call of the
procedure can. The assertion call elimination puts in place of a callee's precondition
(`callElimAssert_`) is replayed as that precondition at the call it comes from, which a
copy of the callee, with the precondition marked, takes in its place.

## What a generator's models must provide

This validation reads a model and an obligation's check as the passive VC phase
produces them, and another generator whose models it checks must produce them the same
way:
- a parameter `x`'s value on entry is the model's value of the name `x` followed by one
  or more `@` and a number, the smallest such number (`entryValue`); a parameter with
  no such name takes its type's default;
- the check's metadata names the procedure it comes from (`PassiveVC.sourceProcKey`);
  without it every CFG procedure is searched for the check, by label and range;
- for the counterexample to show the run's values, the check's metadata maps each
  variable to its name in the model (`PassiveVCGen.varAtPrefix`). -/

namespace Core.CFGLoopElim

open Imperative Lambda

@[expose] public section

/-- The incarnation number `n` if `name` is `x` followed by one or more `@` and the
    digits of `n`. -/
def incarnationOf (x name : String) : Option Nat := do
  let rest ← (name.dropPrefix? x).map (·.toString.toList)
  let digits := rest.dropWhile (· == '@')
  if digits.length < rest.length && !digits.isEmpty && digits.all Char.isDigit then
    (String.ofList digits).toNat?
  else none

/-- The model's value of `x` on entry: its value for `x`'s incarnation with the
    smallest number. -/
def entryValue (constructors : Std.HashSet String) (model : SMT.Model Expression.Ident)
    (x : String) : Option Expression.Expr :=
  let cands := model.filterMap fun (k, t) => (incarnationOf x k.name).map (·, t)
  let best := cands.foldl (init := none) fun best c =>
    match best with
    | some b => if c.1 < b.1 then some c else best
    | none => some c
  best.map fun (_, t) => smtTermToLExpr t constructors

/-- `e` with each unannotated operator that names a monomorphic function of `F` (a
    datatype constructor, in a model's value) annotated with that function's type, as
    the evaluator needs of a value in its store. A polymorphic one is left as it is. -/
def annotateOps (F : Lambda.Factory CoreLParams) : Expression.Expr → Expression.Expr
  | .op m o none =>
    match F[o.name]? with
    | some fn => match fn.type with
      | .ok (.forAll [] ty) => .op m o (some ty)
      | _ => .op m o none
    | none => .op m o none
  | .app m f a => .app m (annotateOps F f) (annotateOps F a)
  | e => e

/-- A value as an SMT term, for the literals a counterexample shows: integers, Booleans
    and strings. -/
def termOfValue? : Expression.Expr → Option Strata.SMT.Term
  | .const _ (.intConst i) => some (.prim (.int i))
  | .const _ (.boolConst b) => some (.prim (.bool b))
  | .const _ (.strConst s) => some (.prim (.string s))
  | _ => none

/-- `model` with each variable's incarnation at the check (`md`'s
    `PassiveVCGen.varAtPrefix` entries) given that variable's value in `store`, the
    replayed run's store at the check, where it is a literal (`termOfValue?`). A
    counterexample read through the check (`LExprModel.atCheck`) then shows the run's
    values rather than the cut program's. -/
def refineModel (md : MetaData Expression) (store : RStore Expression)
    (model : SMT.Model Expression.Ident) : SMT.Model Expression.Ident :=
  md.toList.foldl (init := model) fun m e => match e.fld, e.value with
    | .label l, .msg inc =>
      match l.dropPrefix? PassiveVCGen.varAtPrefix with
      | some x =>
        match (store ⟨x.toString, ()⟩).bind termOfValue? with
        | some t =>
          let l := Map.toList m
          let key := ((l.find? fun p => p.1.name == inc).map (·.1)).getD ⟨inc, ()⟩
          Map.ofList ((l.filter fun p => p.1 != key) ++ [(key, t)])
        | none => m
      | none => m
    | _, _ => m

/-- Does the run reach `target` with its condition holding? -/
def targetHoldsHalt (target : AssertId Expression) (fuel : Nat) : IEvent Expression → Bool
  | .assert arg =>
      target.label == arg.label && decide (target.md = arg.metadata) &&
      (match InterpLang.boundedEval (P := Expression) fuel arg.factory arg.store arg.expr with
       | some v => InterpLang.eqModuloMeta v (HasBool.tt (P := Expression))
       | none => false)
  | _ => false

/-- The checked condition of `arg` evaluates to false. -/
def failsUnder (fuel : Nat) (arg : REventArg Expression (InterpLang.RFactory Expression)) : Bool :=
  match InterpLang.boundedEval (P := Expression) fuel arg.factory arg.store arg.expr with
  | some v => InterpLang.eqModuloMeta v (HasBool.ff (P := Expression))
  | none => false

/-- `cfg` with a fresh entry block, under a label no block has, that runs `cmds` and then
    goes to the old entry. -/
def withEntryBlock (cfg : Imperative.DetCFG Core.Expression Command) (cmds : List Command) :
    Imperative.DetCFG Core.Expression Command :=
  let entry := Strata.Name.freshName (Std.HashSet.ofList (cfg.blocks.map (·.1))) "$entry"
  { entry, blocks := (entry, { cmds, transfer := .goto cfg.entry .empty }) :: cfg.blocks }

/-- The CFG a procedure's run follows: a fresh entry block declaring the parameters
    (`init x : ty`, unconstrained), taking the `old` snapshots and assuming the
    preconditions, then the body, with the postconditions asserted where it returns
    (`PassiveVC.bracketCfgSpec`). -/
def bracketed (p : Procedure) (cfg : Imperative.DetCFG Core.Expression Command) :
    Imperative.DetCFG Core.Expression Command :=
  let reqs := PassiveVC.headerTypeDecls p.header ++ PassiveVC.oldSnapshotDecls p.header ++
    PassiveVC.requiresAssumes p.spec
  withEntryBlock (PassiveVC.bracketCfgSpec cfg [] (PassiveVC.ensuresCmds p.spec)) reqs

/-- The metadata field that marks the replay's target check, so that a check with the same
    label and metadata in another procedure, which a run may reach in a call, does not
    match it. -/
def replayTargetKey : String := "$replayTarget"

/-- `md` marked as the target's (`replayTargetKey`). -/
def tagTarget (md : MetaData Expression) : MetaData Expression :=
  md.pushElem (.label replayTargetKey) (.msg "")

/-- The label prefix of the assumptions `asCalled` adds to a callee: one per precondition,
    and, in an abstract callee, one per postcondition or one that stops the run. -/
def replayRequiresPrefix : String := "$replayRequires_"

/-- `q` as a run calls it: its body first assumes each of its preconditions, free ones
    included, so a run that enters `q` in a state outside its contract, or in one where a
    precondition does not evaluate, stops there (`enforceInterrupt`). The interpreter emits
    only the non-free ones, as assertions, and runs the body whatever they give. An opaque
    procedure (`Body.isOpaque`: abstract, or with a flagged body) means its contract: a call
    returns any outputs the contract allows. One without outputs (no `out` or `inout`
    parameter) changes no variable, so its run is exact: its body becomes the assumption of
    its postconditions, free ones included, which stops the run if one is false or does not
    evaluate. For one with outputs, a run of a body need not be a run of the contract, so its
    body stops the run after the preconditions (`assume false`). -/
def asCalled (q : Procedure) : Procedure :=
  let assumes : List Command := q.spec.preconditions.toList.map fun (l, c) =>
    .cmd (.assume s!"{replayRequiresPrefix}{l}" c.expr c.md)
  let stop : Command := .cmd (.assume s!"{replayRequiresPrefix}abstract"
    (HasBool.ff (P := Expression)) .empty)
  let posts : List Command := q.spec.postconditions.toList.map fun (l, c) =>
    .cmd (.assume s!"{replayRequiresPrefix}ensures_{l}" c.expr c.md)
  match q.body with
  | .structured ss false => { q with body := .structured (assumes.map .cmd ++ ss) false }
  | .cfg cfg false => { q with body := .cfg (withEntryBlock cfg assumes) false }
  | _ =>
    let rest := if q.header.outputs.isEmpty then posts else [stop]
    { q with body := .structured ((assumes ++ rest).map .cmd) false }

/-- The label `l` of `callee`'s checked precondition whose assertion call elimination labels
    `label` (`callElimAssert_` ++ `l` ++ `_` and a number), if any. -/
def callElimPreconditionOf (callee : Procedure) (label : String) : Option String :=
  callee.spec.preconditions.toList.findSome? fun (l, c) =>
    if c.attr == .Free then none else
    match label.dropPrefix? s!"{CallElim.callElimAssertPrefix}{l}_" with
    | some rest =>
      let rest := rest.toString
      if !rest.isEmpty && rest.all Char.isDigit then some l else none
    | none => none

/-- Where the obligation's check is in the program before the cut: an assertion or a
    checked postcondition of the procedure, by its label and metadata, or, for the
    assertion call elimination puts in place of a callee's precondition, the call it comes
    from, by the callee, the precondition's label and the call's metadata. -/
inductive ReplayTarget where
  | check (label : String) (md : MetaData Expression)
  | precondition (callee : Procedure) (label : String) (callMd : MetaData Expression)

/-- `p` with its target marked (`tagTarget`): the matching assertions and postconditions of
    a `check` target, or, for a `precondition` target, the call it comes from redirected to
    `clone`, a copy of the callee whose precondition is marked. Every activation of `p` runs
    this copy, so a recursive call of `p` can confirm the check, and a check of another
    procedure cannot. -/
def tagTargetIn (target : ReplayTarget) (clone : String) (p : Procedure) : Procedure :=
  match target with
  | .check l md =>
    let tagCmd : Command → Command := fun c => match c with
      | .cmd (.assert l' e md') => if l' == l && md' == md then .cmd (.assert l' e (tagTarget md'))
        else c
      | _ => c
    let posts := p.spec.postconditions.toList.map fun (l', c) =>
      (l', if l' == l && c.md == md then { c with md := tagTarget c.md } else c)
    let body := match p.body with
      | .cfg cfg o => .cfg { cfg with blocks := cfg.blocks.map fun (lbl, b) =>
          (lbl, { b with cmds := b.cmds.map tagCmd }) } o
      | b => b
    { p with body, spec := { p.spec with postconditions := ListMap.ofList posts } }
  | .precondition callee _ callMd =>
    let redirect : Command → Command := fun c => match c with
      | .call f tys args md =>
        if f == callee.header.name.name && md == callMd then .call clone tys args md else c
      | _ => c
    match p.body with
    | .cfg cfg o => { p with body := .cfg { cfg with blocks := cfg.blocks.map fun (lbl, b) =>
        (lbl, { b with cmds := b.cmds.map redirect }) } o }
    | _ => p

/-- Does replaying the model of obligation `ob` through the CFG procedures of `input`
    reach `ob`'s check holding (when `holds`: a model of the satisfiability query) or
    failing (otherwise: a model of the validity query)? If so, the model refined with
    the run's values at the check (`refineModel`), and otherwise `none`. Only assertions
    are replayed. -/
def replayValidates (abstracted : String → Bool) (input : Program)
    (ob : ProofObligation Expression) (holds : Bool)
    (model : SMT.Model Expression.Ident) (fuel : Nat := 10000) :
    Option (SMT.Model Expression.Ident) := Id.run do
  if ob.property != .assert then return none
  let range := getFileRange ob.metadata
  -- The procedure the check comes from, when the passive VC phase named it: a check of
  -- another procedure with the same label and range must not confirm the model.
  let source := PassiveVC.sourceProcOf ob.metadata
  -- The datatypes' generated function names, so that a model's constructor values are
  -- read back as constructors (`smtTermToLExpr`).
  let constructors : Std.HashSet String := .ofList <| input.decls.flatMap fun d =>
    match d with
    | .type (.data _) _ => d.funcNames.map (·.name)
    | _ => []
  let procs : List Procedure := input.decls.filterMap fun
    | .proc q _ => some q
    | _ => none
  -- Each check of the CFG procedures (only the source one, when the check names it) with
  -- the obligation's label and range, with its procedure: an assertion or postcondition
  -- of the procedure, or a callee's precondition at a call when call elimination made
  -- the obligation.
  let candidates : List (Procedure × ReplayTarget) := procs.flatMap fun p =>
    if source.any (· != p.header.name.name) then [] else
    match p.body with
    | .cfg cfg _ =>
      let g := bracketed p cfg
      let checks := g.blocks.flatMap fun (_, b) => b.cmds.filterMap fun c => match c with
        | .cmd (.assert l _ md) =>
          if l == ob.label && getFileRange md == range then some (p, .check l md) else none
        | _ => none
      let pres := cfg.blocks.flatMap fun (_, b) => b.cmds.filterMap fun c => match c with
        | .call f _ _ callMd => do
          let callee ← procs.find? (·.header.name.name == f)
          let l ← callElimPreconditionOf callee ob.label
          let check ← callee.spec.preconditions.find? l
          if getFileRange (check.md.setCallSiteFileRange callMd) == range then
            some (p, .precondition callee l callMd)
          else none
        | _ => none
      checks ++ pres
    | _ => []
  -- A target that is not unique, within the source procedure or, when the check does not
  -- name one, across all of them (two checks with one label and no distinguishing range),
  -- could be confirmed by the wrong check.
  let [(p0, kind)] := candidates | return none
  do
    -- The copy of a precondition target's callee whose precondition is marked, under a
    -- name no procedure has.
    let clone := Strata.Name.freshName (Std.HashSet.ofList (procs.map (·.header.name.name)))
      "$replayCallee"
    let p := tagTargetIn kind clone p0
    let .cfg cfg _ := p.body | return none
    let g := bracketed p cfg
    let target : AssertId Expression := match kind with
      | .check l md => { label := l, md := tagTarget md }
      | .precondition callee l callMd =>
        let md := ((callee.spec.preconditions.find? l).map (·.md)).getD .empty
        { label := l, md := (tagTarget md).setCallSiteFileRange callMd }
    let cloned : Option Procedure := match kind with
      | .precondition callee l _ =>
        let pres := callee.spec.preconditions.toList.map fun (l', c) =>
          (l', if l' == l then { c with md := tagTarget c.md } else c)
        some { callee with
          header := { callee.header with name := ⟨clone, ()⟩ }
          spec := { callee.spec with preconditions := ListMap.ofList pres } }
      | .check .. => none
    -- The runtime factory: the functions declared before the procedure, and those of
    -- its datatypes (constructors, selectors, testers), which a run evaluates.
    let F := (input.declsBeforeProcedure p.header.name.name).foldl
      Decl.addToRuntimeFactory Core.Factory
    -- The parameters' entry values, in the order the entry block declares them.
    -- An input takes the model's value; an output-only parameter, whose value on entry
    -- no run reads, its type's default.
    let some inputs := p.header.inputs.toList.mapM (fun (x, ty) =>
        ((entryValue constructors model x.name).map (annotateOps F)).orElse fun _ =>
          defaultValueIn F ty) | return none
    let some outputs := p.header.getOutputOnlyParams.toList.mapM (fun (_, ty) =>
        defaultValueIn F ty) | return none
    let oracle := inputs ++ outputs
    let getDefault : InterpLang.RFactory Expression → RStore Expression → Expression.Ty →
        Option Expression.Expr := fun _ _ ty => ty.toMonoType?.bind (defaultValueIn F)
    -- Each procedure as a call runs it (`asCalled`): `p` with its target marked, and the
    -- marked copy of a precondition target's callee.
    let π : String → Option Procedure := fun n =>
      if n == clone then cloned.map asCalled
      else if n == p.header.name.name then some (asCalled p)
      else (procs.find? (·.header.name.name == n)).map asCalled
    let env : IEnv Expression := { store := .ofStore (fun _ => none), factory := F }
    -- Stop at an abstraction's assumption, before it can confirm the target. Stop
    -- also at another check that fails: past it the run is not one the target's
    -- verdict is about (past a callee's failed precondition, say, the callee runs
    -- from a state outside its contract, and may reach the target in that call).
    let interruptOn : IEvent Expression → Option StopReason := fun ev => match ev with
      | .assume arg =>
        if abstracted arg.label then some (.interrupted s!"abstraction {arg.label}")
        else enforceInterrupt target fuel ev
      | .assert arg =>
        if !targetReached target ev && failsUnder fuel arg then
          some (.interrupted s!"check {arg.label} fails before the target")
        else enforceInterrupt target fuel ev
      | _ => enforceInterrupt target fuel ev
    let config : ReplayCfg Expression :=
      { oracleConfig := .withDefaults getDefault, interruptOn }
    let run : ReplayM Expression (IConfig Expression Command) :=
      (fun c => .terminal c.env) <$>
        runCoreInterpCFG (m := ReplayM Expression) π fuel (.atBlock g g.entry env)
    let halt := if holds then targetHoldsHalt target fuel else assertFailureHalt target fuel
    -- As `runReplay` classifies a run: genuine iff an event fires `halt`. That event's
    -- store is the run's state at the check.
    let (_, st) := runReplayRun run config oracle
    if let some ev := st.traceRev.reverse.find? halt then
      match ev with
      | .assert arg => return some (refineModel ob.metadata arg.store model)
      | _ => return some model
  return none

end -- public section

end Core.CFGLoopElim
