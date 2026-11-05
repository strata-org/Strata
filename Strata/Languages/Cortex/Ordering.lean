/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module

namespace Cortex.Ordering

open Imperative Lambda

public section

partial def tyNames : LMonoTy → List String
  | .tcons n args => n :: args.flatMap tyNames
  | _ => []

def dtDeps (dt : LDatatype Unit) : List String :=
  dt.constrs.flatMap fun c => c.args.flatMap fun (_, t) => tyNames t

partial def reach (deps : String → List String) (start : String) : Std.HashSet String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut work := deps start
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => break
    | x :: rest =>
      work := rest
      if seen.contains x then continue
      seen := seen.insert x
      work := deps x ++ work
  return seen

def sccOrder (names : List String) (deps : String → List String) : List (List String) := Id.run do
  let inNames := fun (n : String) => names.contains n
  let deps' := fun n => (deps n).filter inNames
  let reachOf : Std.HashMap String (Std.HashSet String) := names.foldl (fun m n => m.insert n (reach deps' n)) {}
  let reaches := fun (a b : String) => ((reachOf.getD a {}).contains b)
  let mut sccs : List (List String) := []
  let mut assigned : Std.HashSet String := {}
  for n in names do
    if assigned.contains n then continue
    let comp := n :: names.filter fun m => m != n && reaches n m && reaches m n
    for c in comp do assigned := assigned.insert c
    sccs := sccs ++ [comp]
  let mut out : List (List String) := []
  let mut done : Std.HashSet String := {}
  let mut fuel := sccs.length + 2
  let mut remaining := sccs
  while !remaining.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let (ready, notReady) := remaining.partition fun comp =>
      comp.all fun c => (deps' c).all fun d => comp.contains d || done.contains d
    let forced := ready.isEmpty
    let ready := if forced then remaining.take 1 else ready
    let notReady := if forced then remaining.drop 1 else notReady
    for comp in ready do
      for c in comp do done := done.insert c
    out := out ++ ready
    remaining := notReady.filter fun comp => !comp.all done.contains
  return out

def callees (prog : Program) (p : Procedure) : List String :=
  match p.body with
  | none => []
  | some b => b.cfg.blocks.flatMap fun (_, blk) => blk.cmds.flatMap (IRCmd.callees prog)

def run (m : Module) : Except String Module :=
  let dts : List (LDatatype Unit) := m.decls.flatMap fun
    | .type (.data ds) _ => ds
    | _ => []
  let dtNames := dts.map (·.name)
  let dtMap : Std.HashMap String (LDatatype Unit) := dts.foldl (fun s d => s.insert d.name d) {}
  let groups := sccOrder dtNames fun n => ((dtMap.get? n).map dtDeps).getD []
  let dataDecls : List Core.Decl := groups.filterMap fun g =>
    match g.filterMap dtMap.get? with
    | [] => none
    | ds => some (.type (.data ds) .empty)
  let typeDecls := m.decls.filter fun
    | .type (.con _) _ | .type (.syn _) _ => true
    | _ => false
  let rest := m.decls.filter fun
    | .type _ _ => false
    | _ => true
  let procs := m.program.procedures
  let pmap : Std.HashMap String Procedure := procs.foldl (fun s p => s.insert p.name p) {}
  let pgroups := sccOrder (procs.map (·.name)) fun n => ((pmap.get? n).map (callees m.program)).getD []
  let ordered := pgroups.flatten.filterMap pmap.get?
  .ok { program := { m.program with procedures := ordered }, decls := typeDecls ++ dataDecls ++ rest }

def pass : Pass := { name := "Ordering", run }

end

end Cortex.Ordering
