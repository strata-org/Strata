/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Options
public import Strata.DL.Imperative.PassiveVCGen
public import Strata.DL.Imperative.StructuredToPassiveCFG
public import Strata.Transform.WP.WPCoreProgram
public import Strata.Transform.StructuredToUnstructured
public import Strata.Transform.ProcBodyVerify
public import Strata.Languages.Core.ProcedureType

/-! # Passive VC generation on Core procedures and programs (`--vcgen uwp/usp`)

`Imperative.PassiveVCGen` lifted to Core: a program-to-program transform whose
output is an obligation program, the form the back end's obligation extraction
reads (`hasObligationForm`). For each procedure other than an obligation unit
(`WP.isObligationUnit`, already in that form):

1. Lower the body to a deterministic CFG. A structured body first has
   same-named declarations in sibling scopes renamed apart (`uniquifyInits`), is
   checked for the shape the lowering needs, and is lowered with `stmtsToCFG`; a
   CFG body is used as is. The specification is added at the CFG level
   (`bracketCfgSpec`): at the entry, typed declarations of the parameters,
   snapshots `old g` of the in-out parameters and `assume`s of the `requires`;
   at every exit, an `assert` of each checked `ensures`. These are the commands
   `ProcBodyVerify` puts around a structured body.
2. Convert it to a nondeterministic CFG (`StructuredToPassiveCFG.convert`, which
   turns branch guards into `assume`s), and generate its obligations
   (`PassiveVCGen.defObligations`), in the WP or SP calculus (`vcModeToMethod`).
3. Emit the obligation procedure (`obligationProc`).

Every other declaration is kept, so the back end encodes the program's functions
and axioms, and lemmas reach it as the obligation units the declaration phase
builds. -/

namespace Core
namespace PassiveVC

open Lambda
open Imperative

public section

/-- The location of the expressions this phase builds. -/
abbrev passiveVCLoc : ExprSourceLoc := ExprSourceLoc.synthesized "passiveVC"

/-- The calculus of a `--vcgen` mode: `usp` is strongest postconditions, `uwp`
    weakest preconditions. The other modes do not run this transform; they map
    to `.wp`. -/
def vcModeToMethod : VCGenMode → PassiveVCGen.VcMethod
  | .usp => .sp
  | _    => .wp

/-- Does a block contain `assume false`? No execution gets past it. -/
def endsPath (blk : Imperative.DetBlock String Command Expression) : Bool :=
  blk.cmds.any fun c => match c with
    | .cmd (.assume _ (.const _ (.boolConst Bool.false)) _) => true
    | _ => false

/-- Add a procedure's specification to its CFG body: `reqs` before the entry
    block's commands, and `ens` after the commands of the block that returns. With
    several returning blocks, each goes instead to one fresh exit block holding
    `ens`, so a postcondition is one obligation, as for a structured body (whose
    lowering has one end block). A returning block that contains
    `assume false` gets no `ens`, and does not go to the exit: no execution
    returns through it (CFG loop elimination ends each back edge this way).

    The test is on the command, not on a marker of the block: whoever wrote the
    `assume false`, no execution gets past it, so leaving out `ens` there is sound.
    A block metadata marker would not be, since a user can write any key
    (`@[key]`) and so could drop a postcondition. A phase that rewrites the
    `assume false` into some other false assumption only makes `ens` appear after
    it, where it holds vacuously. -/
def bracketCfgSpec (cfg : Imperative.DetCFG Core.Expression Command)
    (reqs ens : List Command) : Imperative.DetCFG Core.Expression Command :=
  let returns (blk : Imperative.DetBlock String Command Core.Expression) : Bool :=
    match blk.transfer with
    | .finish _ => !endsPath blk
    | _         => false
  let exits := cfg.blocks.filter fun (_, blk) => returns blk
  let exitLbl : Option String :=
    if exits.length ≤ 1 || ens.isEmpty then none
    else some (Strata.Name.freshName (Std.HashSet.ofList (cfg.blocks.map (·.1))) "$return")
  let blocks := cfg.blocks.map (fun (lbl, blk) =>
    let isEntry := lbl == cfg.entry
    let pre := if isEntry then reqs else []
    if returns blk then
      match exitLbl with
      | some x => (lbl, { blk with cmds := pre ++ blk.cmds, transfer := .goto x blk.transfer.md })
      | none => (lbl, { blk with cmds := pre ++ blk.cmds ++ ens })
    else (lbl, { blk with cmds := pre ++ blk.cmds }))
  { cfg with blocks := match exitLbl with
      | some x => blocks ++ [(x, { cmds := ens, transfer := .finish .empty })]
      | none => blocks }

/-- The `assume`s of a procedure's preconditions (checked or free), as
    `ProcBodyVerify` makes them (`Imperative.Check.assumes`). -/
def requiresAssumes (spec : Procedure.Spec) : List Command :=
  Imperative.Check.assumes spec.preconditions

/-- An `assert` of each checked `ensures`, under its own label, as
    `ProcBodyVerify` makes them (`Imperative.Check.asserts`). A free `ensures` is
    not checked, and not assumed either: the body does not establish it. It is left
    out rather than turned into `assume true`, so the VCs do not change. -/
def ensuresCmds (spec : Procedure.Spec) : List Command :=
  Imperative.Check.asserts (spec.postconditions.toList.filter (·.2.attr = .Default))

/-- An unconstrained, typed declaration of each input and output parameter
    (`ProcBodyVerify.paramInits`). The type is what passification gives every
    incarnation of the parameter. -/
def headerTypeDecls (header : Procedure.Header) : List Command :=
  Statements.commands (ProcBodyVerify.paramInits header)

/-- `init (old g) := g` for each in-out parameter `g` (`ProcBodyVerify.oldInits`).
    The translator turns `old(g)` into the variable `old g`, and type checking
    binds `old g` only for in-out parameters, so these are the snapshots a
    postcondition can read. -/
def oldSnapshotDecls (header : Procedure.Header) : List Command :=
  Statements.commands (ProcBodyVerify.oldInits header)

/-- The renamings `uniquifyInits` has in effect: each renamed variable's new
    identifier and its type, by its old name. -/
abbrev Renames := Std.HashMap String (Expression.Ident × Option Lambda.LMonoTy)

/-- `e` with every variable of `env` renamed, in one traversal. -/
def Renames.expr (env : Renames) (e : Expression.Expr) : Expression.Expr :=
  if env.isEmpty then e else
  Lambda.LExpr.substFvarsBy e fun x =>
    (env.get? x.name).map fun (x', ty) => Lambda.LExpr.fvar passiveVCLoc x' ty

/-- A written variable of `env`, renamed. -/
def Renames.ident (env : Renames) (x : Expression.Ident) : Expression.Ident :=
  match env.get? x.name with
  | some (x', _) => x'
  | none => x

/-- Give a fresh name to every declaration of a name declared earlier in the
    traversal, in the rest of its block. Core forbids shadowing, so such a name
    was declared in a sibling scope, whose declaration is out of scope here.
    Lowering to a CFG flattens the scopes, and passification gives a variable one
    type, so sibling declarations must not share a name.

    `env` holds the renamings in effect, which each statement gets as it is
    reached, so the traversal is linear however many declarations are renamed.
    A renaming lasts to the end of the block of its declaration. The state is the
    names declared so far, the names a fresh name must not take (those, and every
    name of the procedure), and per name the next suffix to try. A fresh name has
    the form `x$u`, `x$u_1`, …, which no incarnation takes (`PassiveVCGen.Naming`). -/
def uniquifyInits (env : Renames) : Statements →
    StateM (Std.HashSet String × Std.HashSet String × Std.HashMap String Nat) Statements
  | [] => pure []
  | s :: rest => do
    let ex := env.expr
    let id := env.ident
    match s with
    | .init x ty e md =>
      let e := e.map ex
      let (declared, taken, next) ← get
      if declared.contains x.name then
        -- `x$u`, then `x$u_1`, `x$u_2`, …, resuming after the last one taken for `x`,
        -- so d renamings of one name probe d names in all.
        let base := s!"{x.name}$u"
        let name := fun (k : Nat) => if k == 0 then base else s!"{base}_{k}"
        let k := Id.run do
          let mut k := next.getD x.name 0
          for _ in [0:taken.size + 1] do
            if !taken.contains (name k) then break
            k := k + 1
          return k
        let x' : Expression.Ident := ⟨name k, x.metadata⟩
        set (declared.insert x'.name, taken.insert x'.name, next.insert x.name (k + 1))
        return .init x' ty e md :: (← uniquifyInits (env.insert x.name (x', ty.toMonoType?)) rest)
      else
        set (declared.insert x.name, taken.insert x.name, next)
        return .init x ty e md :: (← uniquifyInits env rest)
    | .set x e md => return .set (id x) (ex e) md :: (← uniquifyInits env rest)
    | .havoc x md => return .havoc (id x) md :: (← uniquifyInits env rest)
    | .assert l e md => return .assert l (ex e) md :: (← uniquifyInits env rest)
    | .assume l e md => return .assume l (ex e) md :: (← uniquifyInits env rest)
    | .cover l e md => return .cover l (ex e) md :: (← uniquifyInits env rest)
    | .call pname tyArgs args md =>
      let args := args.map fun
        | .inArg e => .inArg (ex e)
        | .inoutArg x => .inoutArg (id x)
        | .outArg x => .outArg (id x)
      return .call pname tyArgs args md :: (← uniquifyInits env rest)
    | .block l b md =>
      let b' ← uniquifyInits env b
      return .block l b' md :: (← uniquifyInits env rest)
    | .ite c t f md =>
      let t' ← uniquifyInits env t
      let f' ← uniquifyInits env f
      return .ite (c.map ex) t' f' md :: (← uniquifyInits env rest)
    | .loop g m i b md =>
      let b' ← uniquifyInits env b
      return .loop (g.map ex) (m.map ex) (i.map fun (l, e) => (l, ex e)) b' md ::
        (← uniquifyInits env rest)
    | s => return s :: (← uniquifyInits env rest)

/-- Rename block labels so that no two blocks share one and none ends in
    `_<digits>` (the shape of the labels the lowering generates), and every
    `exit` names the nearest enclosing block of its label. A renamed label is
    `l$b0`, `l$b1`, …; the state holds the labels a new one must not take, and
    for each label the next suffix to try, so that d blocks sharing a label cost
    d probes in all. `env` maps each enclosing block's original label to its new
    one. -/
def uniquifyLabels (env : List (String × String)) : Statements →
    StateM (Std.HashSet String × Std.HashMap String Nat) Statements
  | [] => pure []
  | s :: rest => do
    let s' ← match s with
      | .block l b md =>
        let (taken, next) ← get
        if taken.contains l || l.endsWithUnderscoreDigits then
          let k := Id.run do
            let mut k := next.getD l 0
            for _ in [0:taken.size + 1] do
              if !taken.contains s!"{l}$b{k}" then break
              k := k + 1
            return k
          let l' := s!"{l}$b{k}"
          set (taken.insert l', next.insert l (k + 1))
          pure (.block l' (← uniquifyLabels ((l, l') :: env) b) md)
        else
          set (taken.insert l, next)
          pure (.block l (← uniquifyLabels ((l, l) :: env) b) md)
      | .exit l md => pure (.exit ((env.lookup l).getD l) md)
      | .ite c t f md => pure (.ite c (← uniquifyLabels env t) (← uniquifyLabels env f) md)
      | .loop g m i b md => pure (.loop g m i (← uniquifyLabels env b) md)
      | s => pure s
    return s' :: (← uniquifyLabels env rest)

/-- Lower a structured body to a deterministic CFG, as the
    `structuredToUnstructured` phase does: after `uniquifyLabels` and
    `uniquifyInits`, the body must pass that phase's shape checks
    (`StructuredToUnstructured.shapeError?`). -/
def lowerStructured (procName : String) (params : List String) (ss : Statements) :
    Except String (Imperative.DetCFG Core.Expression Command) := do
  let names := Statements.varNames ss ++ params
  let (ss, _) := (uniquifyLabels [] ss).run ({}, {})
  let (ss, _) := (uniquifyInits {} ss).run ({}, Std.HashSet.ofList names, {})
  if let some msg := StructuredToUnstructured.shapeError? procName ss then throw msg
  pure (Imperative.stmtsToCFG (P := Core.Expression) (CmdT := Command) ss)

/-- Fail if two declarations of one variable have different types: passification
    gives all incarnations of a variable one type (keyed, as there, by
    `toString`, which for a Core identifier is its name, so the key of
    `Procedure.initTypeConflict?` agrees). `uniquifyInits` and the CFG type checker
    already rule this out, so this guards against a gap in either rather than a
    user error. -/
def checkInitTypes (procName : String) (cfg : Imperative.DetCFG Core.Expression Command) :
    Except String Unit := do
  let decls := cfg.blocks.flatMap fun (lbl, blk) => blk.cmds.filterMap fun c =>
    match c with
    | .cmd (.init x ty _ _) => some (x, ty, lbl)
    | _ => none
  if let some x := Procedure.initTypeConflict? decls then
    throw s!"procedure '{procName}' declares '{x.name}' at two types"

/-- Is `l` a label the translator gives an `assume` written without one
    (`assume_<N>`)? -/
def isAutoAssumeLabel (l : String) : Bool :=
  match l.dropPrefix? "assume_" with
  | some rest => !rest.isEmpty && rest.all Char.isDigit
  | none => false

/-- The key under which an assumption's label is marked on an obligation's
    paths; empty for no mark. A phase recognizes the assumptions it made by a
    label prefix (`obligationHasLabelPrefix`), so the key of a label with one of
    the known `prefixes` is that prefix: each obligation then has one mark per
    known phase, rather than one per assumption it made. A label `unmarked` holds
    of gets no mark: the labels of the source's own assumptions (the translator's
    `assume_<N>`, the procedure's `requires`), which no phase validates by, and of
    which a procedure may have many. Any other label is its own key, so whatever
    prefix a phase not among `prefixes` recognizes its labels by, it finds them.
    The empty label gets no mark. -/
def labelKey (prefixes : List String) (unmarked : String → Bool := fun _ => false)
    (l : String) : String :=
  match prefixes.find? (fun pfx => l.startsWith pfx) with
  | some pfx => pfx
  | none => if unmarked l then "" else l

/-- Is a variable of this type inlined? Passification inlines the writes of
    function-typed variables (a local function, a copy of one, a conditional of
    two, any other function-valued expression) instead of equating them with an
    incarnation, which an SMT solver cannot do for functions. -/
def isFunctionTy (ty : Lambda.LTy) : Bool :=
  match ty with
  | .forAll _ (.tcons "arrow" _) => true
  | _ => false

/-- The label of the metadata entry naming, at each check of an obligation procedure,
    the procedure the check comes from (`.msg` its name), for a phase that reads the
    source of an obligation (CFG loop elimination's replay). -/
def sourceProcKey : String := "passiveVCSourceProc"

/-- The procedure a check's metadata names as its source (`sourceProcKey`). -/
def sourceProcOf (md : Imperative.MetaData Expression) : Option String :=
  md.toList.findSome? fun e => match e.fld, e.value with
    | .label l, .msg p => if l == sourceProcKey then some p else none
    | _, _ => none

/-- The names of a program that the names the passive VC phase introduces must avoid:
    every name it declares (`Decl.names`), and every function name (`Decl.funcNames`).
    The obligation procedures declare the incarnations and definitions as variables,
    and an SMT encoding gives a variable and a function of one name one symbol. -/
def programNames (program : Program) : List String :=
  program.decls.flatMap fun d => (d.names ++ d.funcNames).map (·.name)

/-- Lower one procedure to a passification CFG and generate its obligations in
    the chosen calculus; an abstract procedure has none. Fails if the body still
    contains a call, a structured loop or a cycle, or fails a shape check. The pipeline removes loops first;
    the check here guards a direct caller. The names the obligations introduce
    avoid `avoid` (`programNames`) and the procedure's variables
    (`PassiveVCGen.Naming.avoiding`). -/
def procObligations (method : PassiveVCGen.VcMethod) (prefixes : List String)
    (proc : Procedure) (avoid : List String := []) :
    Except String (PassiveVCGen.DefVC Core.Expression) := do
  let name := proc.header.name.name
  let params := (proc.header.inputs.keys ++ proc.header.outputs.keys).map (·.name)
  let detCfg ← match proc.body with
    | .abstract => return { defs := [], obligations := [] }
    | .structured ss _ =>
      if !Imperative.Block.noLoops ss then
        throw s!"procedure '{name}' has a structured loop, which loop elimination \
                 (`insertLoopInvariantAsserts` and `loopElim`) removes before this phase"
      lowerStructured name params ss
    | .cfg cfg _     => do
      -- Passification relies on the CFG body's scoping (`declaredBeforeUse` below):
      -- every read of a local is dominated by its declaration, and no path declares
      -- a local twice. The CFG type checker establishes this; checked here too, so
      -- that a caller that did not run it gets an error rather than a wrong result.
      let dom := cfg.computeDominators
      let reachable := cfg.reachableLabels
      unless Procedure.domScopedB dom reachable cfg &&
          Procedure.initsIncomparableB dom reachable cfg &&
          Procedure.initsNotReachableB (Procedure.cfgInitDeclBlocks cfg) reachable
            cfg.succMap do
        throw s!"procedure '{name}': a CFG-local is read where no declaration of it \
                 dominates, or declared twice on one path (the CFG type checker \
                 rejects such a body)"
      pure cfg
  let reqs := headerTypeDecls proc.header ++ oldSnapshotDecls proc.header ++
    requiresAssumes proc.spec
  let bracketed := bracketCfgSpec detCfg reqs (ensuresCmds proc.spec)
  checkInitTypes name bracketed
  let inProc := fun (e : String) => s!"procedure '{name}': {e}"
  let pcfg ← (StructuredToPassiveCFG.convert (P := Core.Expression) bracketed).mapError inProc
  -- The procedure's own assumptions are not marked (`labelKey`).
  let reqLabels : Std.HashSet String :=
    Std.HashSet.ofList proc.spec.preconditions.keys
  let unmarked := fun (l : String) => isAutoAssumeLabel l || reqLabels.contains l
  let vars := pcfg.blocks.flatMap fun (_, b) =>
    b.cmds.flatMap fun c => (c.definedVars ++ c.getVars).map (·.name)
  let naming := PassiveVCGen.Naming.avoiding (avoid ++ vars)
  (PassiveVCGen.defObligations (P := Core.Expression) method pcfg (labelKey prefixes unmarked)
    -- Two inlined definitions agree when equal up to source locations, which
    -- say where each was written and not what it is.
    isFunctionTy (fun a b => a.beqIgnoringMetadata b)
    (declaredBeforeUse := true) naming).mapError inProc

/-- The free variables of `exprs`, other than `defined`, each with its type, in
    first-use order. Each is an incarnation of a typed variable (a parameter's,
    through `headerTypeDecls`, or a local's, through its `init`), so an untyped
    one is an error rather than given a default type. -/
def obligationVars (procName : String) (defined : List Expression.Ident)
    (exprs : List Expression.Expr) :
    Except String (List (Expression.Ident × Lambda.LMonoTy)) := do
  let mut seen : Std.HashSet String := Std.HashSet.ofList (defined.map (·.name))
  let mut out : Array (Expression.Ident × Lambda.LMonoTy) := #[]
  for e in exprs do
    for (x, ty?) in Lambda.LExpr.freeVars e do
      if seen.contains x.name then continue
      seen := seen.insert x.name
      match ty? with
      | some ty => out := out.push (x, ty)
      | none => throw s!"procedure '{procName}': variable '{x.name}' has no type annotation"
  return out.toList

/-- The obligation procedure of a procedure: the same name and metadata, no
    parameters and no contract, and a body that declares every variable the
    obligations read (`init x : ty`, unconstrained), then one `if *` arm per
    obligation, in program order. The definitions the obligations share
    (`init $__vc… : bool := e`, in dependency order) come between the arms, each
    in front of the first arm that reads it, together with those before it, so an
    obligation's paths carry the definitions up to the ones it needs and not the
    ones after.

    An arm defines what only its goal uses (under WP, the target's `W` chain),
    assumes the obligation's path facts and precondition, then asserts (or
    covers) its goal, with the label and metadata of the command it checks. The
    precondition is the condition of reaching the command, so the back end's
    reachability checks (`--check-level full`) and check modes classify the
    result as under `--vcgen symbolic`. For each key (`labelKey`) of the labels of the
    labelled `assume`s on the command's paths, the arm has an
    `assume [key] true`: it adds nothing, but puts the key on the path,
    where a phase whose assumptions abstract the program (a callee's contract, an
    arbitrary loop iteration) finds it and has a counterexample validated rather
    than reported as definite. Each obligation has its own arm, so these marks do
    not reach the other obligations. -/
def obligationProc (method : PassiveVCGen.VcMethod) (prefixes : List String)
    (p : Procedure) (avoid : List String := []) : Except String Procedure := do
  let vc ← procObligations method prefixes p avoid
  let obs := vc.obligations
  let vars ← obligationVars p.header.name.name
    (vc.defs.map (·.1) ++ obs.flatMap (·.goalDefs.map (·.1)))
    (vc.defs.map (·.2) ++
      obs.flatMap fun o => o.goalDefs.map (·.2) ++ [o.facts, o.pre, o.goal])
  let decls : List Statement := vars.map fun (x, ty) =>
    Statement.init x (Lambda.LTy.forAll [] ty) .nondet .empty
  let defStmt := fun ((x, e) : Expression.Ident × Expression.Expr) =>
    Statement.init x (Lambda.LTy.forAll [] .bool) (.det e) .empty
  let defIdx : Std.HashMap String Nat :=
    vc.defs.zipIdx.foldl (fun m ((x, _), i) => m.insert x.name i) {}
  let needed := fun (o : PassiveVCGen.DefObligation Core.Expression) =>
    (o.facts :: o.pre :: o.goal :: (o.goalDefs.map (·.2))).foldl (fun acc e =>
      (Lambda.LExpr.freeVars e).foldl (fun acc (x, _) =>
        match defIdx.get? x.name with
        | some i => max acc (i + 1)
        | none => acc) acc) 0
  let defArr := vc.defs.toArray
  let mut body : Array Statement := decls.toArray
  let mut emitted := 0
  for o in obs do
    let upto := max emitted (needed o)
    body := body ++ (defArr.extract emitted upto).map defStmt
    emitted := upto
    let md := o.md.pushElem (.label sourceProcKey) (.msg p.header.name.name)
    let check := if o.isCover then Statement.cover o.label o.goal md
      else Statement.assert o.label o.goal md
    let marks := o.assumeLabels.map fun l =>
      Statement.assume l (Lambda.LExpr.boolConst passiveVCLoc true) .empty
    body := body.push (.ite .nondet (marks ++ o.goalDefs.map defStmt ++
      [Statement.assume "" o.facts .empty, Statement.assume "" o.pre .empty, check]) [] .empty)
  pure { header := { p.header with inputs := [], outputs := [] },
         spec := { preconditions := [], postconditions := [] },
         body := .structured body.toList false }

/-- The passive VC phase of a program: every procedure that is not an obligation
    unit becomes its obligation procedure (`obligationProc`), except an abstract
    procedure, which has no body to check and is dropped; every other declaration is
    kept, in order. `prefixes` are the assumption-label prefixes
    the pipeline's phases validate by (`labelKey`). The names it introduces avoid the
    program's (`programNames`) and `reserved`, the names of functions given outside
    the program (the verifier's extra factory functions), which the SMT encoding
    names the same way. -/
def passiveVCProgram (method : PassiveVCGen.VcMethod) (program : Program)
    (prefixes : List String := []) (reserved : List String := []) : Except String Program := do
  let avoid := programNames program ++ reserved
  let decls ← program.decls.mapM fun d => match d with
    | .proc p md =>
      if WP.isObligationUnit p then pure (some d)
      else if p.body matches .abstract then pure none
      else do pure (some (.proc (← obligationProc method prefixes p avoid) md))
    | d => pure (some d)
  pure { decls := decls.filterMap id }

end -- public section

end PassiveVC
end Core
