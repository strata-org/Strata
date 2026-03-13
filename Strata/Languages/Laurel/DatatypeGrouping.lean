/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public import Strata.Languages.Laurel.Laurel
import Strata.DL.Lambda.LExpr
import Strata.DDM.Util.Graph.Tarjan

/-!
## Datatype Grouping via Tarjan's SCC

Groups `LDatatype Unit` values by strongly connected components of their direct type
references, so that mutually recursive datatypes share a single `.data` declaration.
-/

namespace Strata.Laurel

open Lambda (LMonoTy LExpr)

/-- Collect all `UserDefined` type names referenced in a `HighType`, including nested ones. -/
def collectTypeRefs : HighTypeMd → List String
  | ⟨.UserDefined name, _⟩ => [name.text]
  | ⟨.TSet elem, _⟩ => collectTypeRefs elem
  | ⟨.TMap k v, _⟩ => collectTypeRefs k ++ collectTypeRefs v
  | ⟨.TTypedField vt, _⟩ => collectTypeRefs vt
  | ⟨.Applied base args, _⟩ =>
      collectTypeRefs base ++ args.flatMap collectTypeRefs
  | ⟨.Pure base, _⟩ => collectTypeRefs base
  | ⟨.Intersection ts, _⟩ => ts.flatMap collectTypeRefs
  | _ => []

/-- Get all datatype names that a `DatatypeDefinition` references in its constructor args. -/
def datatypeRefs (dt : DatatypeDefinition) : List String :=
  dt.constructors.flatMap fun c => c.args.flatMap fun p => collectTypeRefs p.type

/--
Group `LDatatype Unit` values by strongly connected components of their direct type references.
Datatypes in the same SCC (mutually recursive) share a single `.data` declaration.
Non-recursive datatypes each get their own singleton `.data` declaration.
The returned groups are in dependency order (leaves first).
-/
public def groupDatatypes (dts : List DatatypeDefinition)
    (ldts : List (Lambda.LDatatype Unit)) : List (List (Lambda.LDatatype Unit)) :=
  let n := dts.length
  if n = 0 then [] else
  let nameToIdx : Std.HashMap String Nat :=
    dts.foldlIdx (fun m i dt => m.insert dt.name.text i) {}
  -- Build OutGraph: nodesOut returns in-edges, so to traverse successors we store
  -- edges as (j → i) for each reference i → j (dt[i] references dt[j]).
  let edges : List (Nat × Nat) :=
    dts.foldlIdx (fun acc i dt =>
      (datatypeRefs dt).filterMap nameToIdx.get? |>.foldl (fun acc j => (j, i) :: acc) acc) []
  let g := OutGraph.ofEdges! n edges
  let sccs := OutGraph.tarjan g
  -- Map indices back to LDatatype Unit values
  let ldtMap : Std.HashMap String (Lambda.LDatatype Unit) :=
    ldts.foldl (fun m ldt => m.insert ldt.name ldt) {}
  let dtsArr := dts.toArray
  -- Restore original input order: sort each SCC's members by their input index,
  -- then sort the SCCs themselves by the minimum input index they contain.
  let groups : List (Nat × List (Lambda.LDatatype Unit)) :=
    sccs.toList.filterMap fun comp =>
      let sorted := comp.toList.mergeSort (· < ·)
      let members := sorted.filterMap fun idx =>
        dtsArr[idx]? |>.bind fun dt => ldtMap.get? dt.name.text
      match sorted, members with
      | minIdx :: _, _ :: _ => some (minIdx.val, members)
      | _, _ => none
  (groups.mergeSort (fun a b => a.1 < b.1)).map (·.2)

end Strata.Laurel
