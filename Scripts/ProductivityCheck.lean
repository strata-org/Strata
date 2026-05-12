/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DDM.Analysis.Productivity
import Strata.DDM.BundledDialects

/-! Quick CLI: `lake exe productivityCheck [<DialectName>|--all]`.
The only trusted base is `frameworkAtomicCategories`; every other
category must derive its productivity from operator chains rooted in
those atoms. -/

open Strata

private def runOn (name : DialectName) : IO UInt32 := do
  let dialects : DialectMap := DialectMap.ofList! bundledDialects.toList
  if name ∉ dialects then
    IO.eprintln s!"ERR: unknown dialect '{name}'"
    IO.eprintln "Bundled dialects:"
    for d in bundledDialects do
      IO.eprintln s!"  {d.name}"
    return 1
  let r := Strata.DDM.Productivity.check dialects name
  IO.println r.format
  return (if r.isOk then 0 else 1)

private def runAll : IO UInt32 := do
  let dialects : DialectMap := DialectMap.ofList! bundledDialects.toList
  let mut bad : Nat := 0
  for d in bundledDialects do
    let r := Strata.DDM.Productivity.check dialects d.name
    let mark := if r.isOk then "✓" else "✗"
    IO.println s!"{mark} {d.name}: {r.productive.size} productive, {r.unproductive.size} unproductive"
    if !r.isOk then
      bad := bad + 1
      for u in r.unproductive do
        IO.println s!"    - {u.category.fullName} ({u.blockers.size} blocker(s))"
        for b in u.blockers do
          let parts := String.intercalate ", " (b.unmetArgCats.toList.map QualifiedIdent.fullName)
          IO.println s!"        op {b.opName} blocked on: {parts}"
  IO.println ""
  if bad == 0 then
    IO.println s!"All {bundledDialects.size} dialects productive."
    return 0
  else
    IO.println s!"{bad} of {bundledDialects.size} dialects have unproductive categories."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] =>
    IO.println "Usage: lake exe productivityCheck [<DialectName>|--all]"
    IO.println ""
    IO.println "Bundled dialects:"
    for d in bundledDialects do
      IO.println s!"  {d.name}"
    return 0
  | ["--all"] => runAll
  | [name] => runOn name
  | _ =>
    IO.eprintln "ERR: expected exactly one dialect name, --all, or --help"
    return 1
