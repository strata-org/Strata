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
SCCs are emitted in dependency order: dependencies (leaves) before dependents (roots).
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
  | ⟨.TCore name, _⟩ => [name]
  | _ => []

/-- Get all datatype names that a `DatatypeDefinition` references in its constructor args. -/
def datatypeRefs (dt : DatatypeDefinition) : List String :=
  dt.constructors.flatMap fun c => c.args.flatMap fun p => collectTypeRefs p.type

/--
Group `LDatatype Unit` values by strongly connected components of their direct type references.
Datatypes in the same SCC (mutually recursive) share a single `.data` declaration.
Non-recursive datatypes each get their own singleton `.data` declaration.
The returned groups are in topological order: leaves (no dependencies) first, roots last.
-/
public def groupDatatypes (dts : List DatatypeDefinition)
    (ldts : List (Lambda.LDatatype Unit)) : List (List (Lambda.LDatatype Unit)) :=
  let n := dts.length
  if n = 0 then [] else
  let nameToIdx : Std.HashMap String Nat :=
    dts.foldlIdx (fun m i dt => m.insert dt.name.text i) {}
  -- dt[i] references dt[j] means i depends on j (j must be declared first).
  -- tarjan guarantees: if there's a path A→B, B appears after A in the output.
  -- So we add edge j→i (j has a path to i), ensuring i (the dependent) appears after j (the dependency).
  let edges : List (Nat × Nat) :=
    dts.foldlIdx (fun acc i dt =>
      (datatypeRefs dt).filterMap nameToIdx.get? |>.foldl (fun acc j => (j, i) :: acc) acc) []
  let g := OutGraph.ofEdges! n edges
  let ldtMap : Std.HashMap String (Lambda.LDatatype Unit) :=
    ldts.foldl (fun m ldt => m.insert ldt.name ldt) {}
  let dtsArr := dts.toArray
  OutGraph.tarjan g |>.toList.filterMap fun comp =>
    let members := comp.toList.filterMap fun idx =>
      dtsArr[idx]? |>.bind fun dt => ldtMap.get? dt.name.text
    if members.isEmpty then none else some members

end Strata.Laurel
