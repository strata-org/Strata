/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public import Strata.Languages.Laurel.Laurel
import Strata.DL.Lambda.LExpr

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

/-! ### Tarjan's SCC -/

structure TarjanState where
  nextIndex : Nat := 0
  stack : List Nat := []
  indices : Std.HashMap Nat Nat := {}
  lowlinks : Std.HashMap Nat Nat := {}
  onStack : Std.HashSet Nat := {}
  components : Array (Array Nat) := #[]

/--
Tarjan's SCC algorithm on an adjacency list indexed by `Nat`.

Termination: each node is visited at most once (guarded by `s.indices.contains` at the
call sites), so the recursion is bounded by the number of nodes even though it is `partial`.
-/
partial def tarjanVisit (adj : Std.HashMap Nat (List Nat))
    (v : Nat) (s : TarjanState) : TarjanState :=
  let s := { s with
    indices := s.indices.insert v s.nextIndex
    lowlinks := s.lowlinks.insert v s.nextIndex
    nextIndex := s.nextIndex + 1
    stack := v :: s.stack
    onStack := s.onStack.insert v }
  let neighbors := adj.getD v []
  let s := neighbors.foldl (fun s w =>
    if !s.indices.contains w then
      let s := tarjanVisit adj w s
      let vLow := s.lowlinks.getD v 0
      let wLow := s.lowlinks.getD w 0
      { s with lowlinks := s.lowlinks.insert v (min vLow wLow) }
    else if s.onStack.contains w then
      let vLow := s.lowlinks.getD v 0
      let wIdx := s.indices.getD w 0
      { s with lowlinks := s.lowlinks.insert v (min vLow wIdx) }
    else s) s
  if s.lowlinks.getD v 0 == s.indices.getD v 0 then
    -- Pop the SCC from the stack
    let rec popLoop (stack : List Nat) (comp : Array Nat) (onStack : Std.HashSet Nat)
        : List Nat × Array Nat × Std.HashSet Nat :=
      match stack with
      | [] => ([], comp, onStack)
      | w :: rest =>
        let comp := comp.push w
        let onStack := onStack.erase w
        if w == v then (rest, comp, onStack)
        else popLoop rest comp onStack
    let (stack', comp, onStack') := popLoop s.stack #[] s.onStack
    { s with stack := stack', onStack := onStack', components := s.components.push comp }
  else s

/--
Group `LDatatype Unit` values by strongly connected components of their direct type references.
Datatypes in the same SCC (mutually recursive) share a single `.data` declaration.
Non-recursive datatypes each get their own singleton `.data` declaration.
The returned groups are in dependency order (leaves first).
-/
public def groupDatatypes (dts : List DatatypeDefinition)
    (ldts : List (Lambda.LDatatype Unit)) : List (List (Lambda.LDatatype Unit)) :=
  -- All datatypes participate in grouping (zero-constructor ones get a synthetic unit
  -- constructor in translateDatatypeDefinition, so they always have at least one constructor)
  let withConstrs := dts
  let nameToIdx : Std.HashMap String Nat :=
    withConstrs.foldlIdx (fun m i dt => m.insert dt.name.text i) {}
  -- Build directed adjacency list: dt[i] → dt[j] if dt[i] directly references dt[j]
  let adj : Std.HashMap Nat (List Nat) :=
    withConstrs.foldlIdx (fun m i dt =>
      let refs := (datatypeRefs dt).filterMap nameToIdx.get?
      m.insert i refs) {}
  -- Run Tarjan's SCC
  let finalState := withConstrs.foldlIdx (fun s i _ =>
    if s.indices.contains i then s else tarjanVisit adj i s) ({} : TarjanState)
  -- Map indices back to LDatatype Unit values
  let ldtMap : Std.HashMap String (Lambda.LDatatype Unit) :=
    ldts.foldl (fun m ldt => m.insert ldt.name ldt) {}
  finalState.components.toList.filterMap fun comp =>
    let members := comp.toList.filterMap fun idx =>
      withConstrs[idx]? |>.bind fun dt => ldtMap.get? dt.name.text
    if members.isEmpty then none else some members

end Strata.Laurel
