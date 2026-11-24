/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.ToCore
public import Strata.Languages.Cortex.LowerDispatch
public import Strata.Languages.Cortex.LowerExceptions
public import Strata.Languages.Cortex.PruneUnreachable
public import Strata.Languages.Cortex.LowerCTE
public import Strata.Languages.Cortex.LowerHeapExec
public import Strata.Languages.Cortex.LowerHeap
public import Strata.Languages.Cortex.LowerDynamic
public import Strata.Languages.Cortex.LowerComposites
public import Strata.Languages.Cortex.LowerGlobals
public import Strata.Languages.Cortex.FieldCasts
public import Strata.Languages.Cortex.InoutArgs
public import Strata.Languages.Cortex.Ordering
public import Strata.Languages.Cortex.CopyAssignedInputs
public import Strata.Languages.Cortex.Cleanup

namespace Cortex

public section

def thrownType (prog : UnorderedProgram) (p : Procedure) (throwing : Std.HashMap String TypeName) :
    Option TypeName :=
  match p.body with
  | none => none
  | some b =>
    let declared : Std.HashMap String TypeName := b.cfg.blocks.foldl (init := {}) fun m (_, blk) =>
      blk.cmds.foldl (init := m) fun m c => match c with
        | .cmd (.init x t _ _) => match conTyName? t with
          | some n => m.insert x.name n
          | none => m
        | _ => m
    let escapes := fun (l : Label) (ty : TypeName) =>
      !b.handlers.any fun h => h.covered.contains l && h.catches prog (tcon ty)
    let raised : IRCmd → Option TypeName := fun c => match c with
      | .throw (.fvar _ x _) _ => some ((declared.get? x.name).getD LowerExceptions.anyExnName)
      | .throw _ _ => some LowerExceptions.anyExnName
      | .call _ q _ _ => throwing.get? q
      | _ => none
    let tys := b.cfg.blocks.flatMap fun (l, blk) => blk.cmds.filterMap fun c =>
      (raised c).filter (escapes l)
    match tys with
    | [] => none
    | _ => some ((tys.find? fun t => tys.all (prog.isSubtype · t)).getD LowerExceptions.anyExnName)

def inferThrows (prog : UnorderedProgram) : UnorderedProgram := Id.run do
  let mut procs := prog.procedures
  let declared := (prog.procedures.filter (·.throws.isSome)).map (·.name)
  for _ in [0:procs.length * (prog.composites.length + 2) + 1] do
    let throwing : Std.HashMap String TypeName := procs.foldl (init := {}) fun m p =>
      match p.throws with
      | some t => m.insert p.name t
      | none => m
    let next := procs.map fun p => if declared.contains p.name then p else { p with throws := thrownType prog p throwing }
    if next.all (fun p => procs.any fun q => q.name == p.name && q.throws == p.throws) then break
    procs := next
  return { prog with procedures := procs }

def inferThrowsPass : Pass := Pass.onUnordered "InferThrows" fun p => .ok (inferThrows p)

def entriesDoNotThrow : Pass := Pass.onUnordered "EntriesDoNotThrow" fun p =>
  .ok (p.mapProcedures fun q => if LowerGlobals.isEntry q then { q with throws := none } else q)

def entriesNotCalled : Pass := Pass.onUnordered "EntriesNotCalled" fun p =>
  let entries := (p.procedures.filter LowerGlobals.isEntry).map (·.name)
  let called := p.procedures.findSome? fun pr => pr.body.bind fun b =>
    b.cfg.blocks.findSome? fun (_, blk) => blk.cmds.findSome? fun c =>
      (c.callees p).find? entries.contains
  match called with
  | some q => .error s!"call of '{q}': entry procedures cannot be called"
  | none => .ok p

/-- The passes that both the route to Core and the Cortex interpreter run first: they lower
the Cortex features that Core does not have to Core commands and calls. With `inferThrows`, the
procedures that throw without declaring it first get a `throws` type; only the interpreter does
this. -/
def sharedPasses (inferThrows : Bool) : List Pass :=
  [entriesNotCalled, LowerDispatch.pass] ++ (if inferThrows then [inferThrowsPass] else []) ++
  [InoutArgs.pass, entriesDoNotThrow, LowerExceptions.pass, PruneUnreachable.pass, LowerComposites.pass]

/-- The passes the Cortex interpreter runs after `sharedPasses true`, before LowerCTE: an executable
heap, then the globals. -/
def interpreterPasses : List Pass :=
  [Pass.onUnordered "FieldCasts" FieldCasts.run, LowerHeapExec.pass, LowerGlobals.pass]

/-- The passes that lower a Cortex program to the form `ToCore` translates. -/
def loweringPasses : List Pass :=
  sharedPasses false ++ [LowerHeap.pass, LowerGlobals.pass, LowerCTE.pass, LowerDynamic.pass, Ordering.pass,
    CopyAssignedInputs.pass]

/-- The passes of the route to Core: the cleanup, then the lowering passes. -/
def passes : List Pass := Cleanup.pass :: loweringPasses

def runPasses (ps : List Pass) (prog : Program) : Except String Program :=
  ps.foldlM (fun prog p => match p.run prog with
    | .ok prog' => .ok prog'
    | .error e => .error s!"{p.name}: {e}") prog

/-- Lower a Cortex program and translate it to Core, with each procedure body
emitted as a Core CFG body. With `cleanup := false` the cleanup passes are
skipped, for comparing the two results. -/
def toCoreProgram (prog : UnorderedProgram) (cleanup : Bool := true) : Except String Core.Program := do
  ToCore.programToCore (← runPasses (if cleanup then passes else loweringPasses) (.unordered prog))

end

end Cortex
