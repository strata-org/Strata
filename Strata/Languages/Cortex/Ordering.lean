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

def datatypeGroups (dts : List (LDatatype Unit)) : List (List (LDatatype Unit)) :=
  let dtMap : Std.HashMap String (LDatatype Unit) := dts.foldl (fun s d => s.insert d.name d) {}
  let groups := sccOrder (dts.map (·.name)) fun n => ((dtMap.get? n).map dtDeps).getD []
  groups.filterMap fun g =>
    match g.filterMap dtMap.get? with
    | [] => none
    | ds => some ds

def order (prog : UnorderedProgram) : Except String OrderedProgram := do
  unless prog.composites.isEmpty do throw "composites must be lowered before Ordering"
  unless prog.constrained.isEmpty do throw "constrained types must be lowered before Ordering"
  unless prog.globals.isEmpty do throw "globals must be lowered before Ordering"
  unless prog.globalInit.isEmpty do throw "global initialization must be lowered before Ordering"
  return { decls := prog.opaqueTypes.map .opaqueType ++ (datatypeGroups prog.datatypes).map .datatypes ++
    prog.procedures.map .procedure }

def run : Program → Except String Program
  | .unordered p => .ordered <$> order p
  | .ordered _ => .error "Internal error: pass 'Ordering' cannot run on an ordered Cortex program"

def pass : Pass := { name := "Ordering", run }

end

end Cortex.Ordering
