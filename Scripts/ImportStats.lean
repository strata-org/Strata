/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata
import Lean.Environment
import Lean.Util.Path

open Lean System

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← do
    let imports := #[{ module := `Strata : Import }]
    Lean.importModules imports {} 0

  let header := env.header
  let moduleNames := header.moduleNames
  let moduleData := header.moduleData

  -- Build name → index map and Strata membership set
  let mut name2idx : Std.HashMap Name Nat := {}
  let mut isStrata : Std.HashSet Nat := {}
  for h : i in [:moduleNames.size] do
    name2idx := name2idx.insert moduleNames[i] i
    if moduleNames[i].getRoot == `Strata then
      isStrata := isStrata.insert i

  -- Build direct-import adjacency lists (index → indices)
  let mut directImports : Array (Array Nat) := .replicate moduleNames.size #[]
  for h : i in [:moduleData.size] do
    let md := moduleData[i]
    let mut deps : Array Nat := #[]
    for imp in md.imports do
      if let some j := name2idx[imp.module]? then
        deps := deps.push j
    directImports := directImports.set! i deps

  -- Compute transitive closure via BFS for each module
  -- Track both total and Strata-only transitive import counts
  let mut totalTransCounts : Array Nat := .replicate moduleNames.size 0
  let mut strataTransCounts : Array Nat := .replicate moduleNames.size 0
  for h : i in [:moduleNames.size] do
    let mut visited : Std.HashSet Nat := {}
    let mut queue : Array Nat := directImports[i]!
    for j in directImports[i]! do
      visited := visited.insert j
    while queue.size > 0 do
      let cur := queue.back!
      queue := queue.pop
      for next in directImports[cur]! do
        if !visited.contains next then
          visited := visited.insert next
          queue := queue.push next
    totalTransCounts := totalTransCounts.set! i visited.size
    let strataCount := visited.fold (init := 0) fun acc idx =>
      if isStrata.contains idx then acc + 1 else acc
    strataTransCounts := strataTransCounts.set! i strataCount

  -- Filter to Strata modules only
  let mut strataModules : Array (Name × Nat × Nat) := #[]
  for h : i in [:moduleNames.size] do
    let n := moduleNames[i]
    if isStrata.contains i then
      strataModules := strataModules.push (n, totalTransCounts[i]!, strataTransCounts[i]!)

  -- Compute and print stats for both total and Strata-only
  for (label, getCount) in [
    ("all (including Lean/Std)", fun (x : Name × Nat × Nat) => x.2.1),
    ("Strata-only",             fun (x : Name × Nat × Nat) => x.2.2)
  ] do
    let sorted := strataModules.qsort (fun a b => getCount a > getCount b)
    let total := strataModules.foldl (init := 0) fun acc m => acc + getCount m
    let count := strataModules.size
    let avg : Float := if count > 0 then total.toFloat / count.toFloat else 0.0
    let max := strataModules.foldl (init := 0) fun acc m => Nat.max acc (getCount m)
    let min := strataModules.foldl (init := total) fun acc m => Nat.min acc (getCount m)
    let median := if sorted.size > 0 then getCount sorted[sorted.size / 2]! else 0

    IO.println s!"=== Transitive imports ({label}) for {count} Strata modules ==="
    IO.println s!"  Average: {Float.toString avg}"
    IO.println s!"  Median:  {median}"
    IO.println s!"  Min:     {min}"
    IO.println s!"  Max:     {max}"
    IO.println s!"  Total:   {total}"
    IO.println ""
    IO.println "  Top 20:"
    for i in [:Nat.min 20 sorted.size] do
      let m := sorted[i]!
      IO.println s!"    {getCount m}\t{m.1}"
    IO.println ""
    IO.println "  Bottom 10:"
    let start := if sorted.size > 10 then sorted.size - 10 else 0
    for i in [start:sorted.size] do
      let m := sorted[i]!
      IO.println s!"    {getCount m}\t{m.1}"

    IO.println ""
    IO.println "  Histogram (bucket size = 10):"
    let bucketSize := 10
    let numBuckets := max / bucketSize + 1
    let mut buckets : Array Nat := .replicate numBuckets 0
    for m in strataModules do
      let b := getCount m / bucketSize
      buckets := buckets.set! b (buckets[b]! + 1)
    for b in [:numBuckets] do
      let lo := b * bucketSize
      let hi := lo + bucketSize - 1
      let cnt := buckets[b]!
      if cnt > 0 then
        let bar := String.ofList (List.replicate (Nat.min cnt 60) '█')
        let suffix := if cnt > 60 then "…" else ""
        IO.println s!"    {lo}-{hi}\t{cnt}\t{bar}{suffix}"
    IO.println ""

  return 0
