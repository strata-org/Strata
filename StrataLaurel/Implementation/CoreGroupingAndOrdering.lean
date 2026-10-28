/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.CoreWithLaurelTypes
public import StrataLaurel.Implementation.LaurelPass
import Strata.DL.Lambda.LExpr
import StrataDDM.Util.Graph.Tarjan
import StrataLaurel.Implementation.Grammar.AbstractToConcreteTreeTranslator
import StrataLaurel.Implementation.MapStmtExpr
import Strata.Util.Tactics
open StrataDDM

/-!
## Grouping and Ordering for Core Translation

Utilities for computing the grouping and topological ordering of Laurel
declarations before they are emitted as Strata Core declarations.

- `computeSccDecls` — builds the procedure call graph, runs Tarjan's SCC
  algorithm, and returns each SCC as a list of procedures paired with a flag
  indicating whether the SCC is recursive. The result is in reverse topological
  order (dependencies before dependents), which is the order required by Core.
-/

namespace Strata.Laurel

open Lambda (LMonoTy LExpr)
open Std (Format ToFormat)

/-- Collect all `UserDefined` type names referenced in a `HighType`, including nested ones. -/
def collectTypeRefs : HighTypeMd → List String
  | ⟨.UserDefined name, _⟩ => [name.text]
  | ⟨.TSet elem, _⟩ => collectTypeRefs elem
  | ⟨.TMap k v, _⟩ => collectTypeRefs k ++ collectTypeRefs v
  | ⟨.Applied base args, _⟩ => collectTypeRefs base ++ args.flatMap collectTypeRefs
  | ⟨.Intersection ts, _⟩ => ts.flatMap collectTypeRefs
  | _ => []

/-- Get all datatype names that a `DatatypeDefinition` references in its constructor args. -/
def datatypeRefs (dt : DatatypeDefinition) : List String :=
  dt.constructors.flatMap fun c => c.args.flatMap fun p => collectTypeRefs p.type

/--
Collect all `StaticCall` callee names referenced anywhere in a `StmtExpr`.
Used to build the call graph for SCC-based procedure ordering. Recursion into
child nodes is handled by `collectStmtExprList`.
-/
def collectStaticCallNames (expr : StmtExprMd) : List String :=
  collectStmtExprList (fun e => match e.val with
    | .StaticCall callee _ _ => [callee.text]
    | _ => []) expr

/--
Build the procedure call graph, run Tarjan's SCC algorithm, and return each SCC
as a list of procedures paired with a flag indicating whether the SCC is recursive.
Results are in reverse topological order: dependencies before dependents.

Procedures with axioms are placed as early as possible — before
unrelated procedures without them — by stably partitioning them first before building
the graph. Tarjan then naturally assigns them lower indices, causing them to appear
earlier in the output.
-/
public def computeSccDecls (program : LaurelProgram) : List (List Procedure × Bool) :=
  -- Stable partition: procedures with axioms come first, preserving relative
  -- order within each group. Tarjan then places them earlier in the topological output.
  let allProcs := program.staticFunctions ++ program.staticProcedures
  let (withAxioms, withoutAxioms) :=
    allProcs.partition (fun p => !p.axioms.isEmpty)
  let orderedProcs : List Procedure := withAxioms ++ withoutAxioms

  -- Build a call-graph over all procedures.
  -- An edge proc → callee means proc's body/contracts contain a StaticCall to callee.
  let procsArr : Array Procedure := orderedProcs.toArray
  let nameToIdx : Std.HashMap String Nat :=
    procsArr.foldl (fun (acc : Std.HashMap String Nat × Nat) proc =>
      (acc.1.insert proc.name.text acc.2, acc.2 + 1)) ({}, 0) |>.1

  -- Collect all callee names from a procedure's body and contracts.
  let procCallees (proc : Procedure) : List String :=
    let bodyExprs : List StmtExprMd := match proc.body with
      | .Transparent b => [b]
      | .Opaque postconds impl modifies =>
        -- A modifies group contributes both its targets and its guard as expressions
        -- that may hold `StaticCall`s.
        let modifiesExprs := modifies.flatMap (fun g => g.targets ++ g.guard.toList)
        postconds.map (·.condition) ++ impl.toList ++ modifiesExprs
      | .Abstract postconds => postconds.map (·.condition)
      | .External => []
    let contractExprs : List StmtExprMd :=
      proc.preconditions.map (·.condition) ++
      proc.invokeOn.toList ++
      proc.axioms
    (bodyExprs ++ contractExprs).flatMap collectStaticCallNames

  -- Build the OutGraph for Tarjan.
  let n := procsArr.size
  let graph : OutGraph n :=
    procsArr.foldl (fun (acc : OutGraph n × Nat) proc =>
      let callerIdx := acc.2
      let g := acc.1
      let callees := procCallees proc
      let g' := callees.foldl (fun g callee =>
        match nameToIdx.get? callee with
        | some calleeIdx => g.addEdge! calleeIdx callerIdx
        | none => g) g
      (g', callerIdx + 1)) (OutGraph.empty n, 0) |>.1

  -- Run Tarjan's SCC algorithm. Results are in reverse topological order
  -- (a node appears after all nodes that have paths to it).
  let sccs := OutGraph.tarjan graph

  sccs.toList.filterMap fun scc =>
    let procs := scc.toList.filterMap fun idx =>
      procsArr[idx.val]?
    if procs.isEmpty then none else
    let isRecursive := procs.length > 1 ||
      (match scc.toList.head? with
        | some node => (graph.nodesOut node).contains node
        | none => false)
    some (procs, isRecursive)

/--
Produce a `CoreWithLaurelTypes` from a `LaurelProgram` by
computing a combined ordering of functions and proofs using the call graph,
then collecting datatypes and constants.

Functions are grouped into SCCs (for mutual recursion). Proofs are emitted
as individual `procedure` decls. Both participate in the topological ordering
so that axioms are available to functions that need them.
-/
def orderFunctionsAndProcedures (program : LaurelProgram) : CoreWithLaurelTypes :=
  let opaqueDecls := program.types.filterMap fun
    | .Opaque ot => some (OrderedDecl.opaqueType ot)
    | _ => none
  let datatypeDecls := (groupDatatypesByScc' program).map OrderedDecl.datatypes
  let constantDecls := program.constants.map OrderedDecl.constant
  let funcNames : Std.HashSet String :=
    program.staticFunctions.foldl (fun s p => s.insert p.name.text) {}
  let orderedDecls := (computeSccDecls program).flatMap fun (procs, isRecursive) =>
    -- Split the SCC into functions and proofs
    let (funcs, proofs) := procs.partition (fun p => funcNames.contains p.name.text)
    let funcDecl := if funcs.isEmpty then [] else [OrderedDecl.funcs funcs isRecursive]
    let proofDecls := proofs.map OrderedDecl.procedure
    funcDecl ++ proofDecls
  { decls := opaqueDecls ++ datatypeDecls ++ constantDecls ++ orderedDecls }
where
  /-- Group the datatypes of a `LaurelProgram` by SCC. -/
  groupDatatypesByScc' (program : LaurelProgram) : List (List DatatypeDefinition) :=
    let laurelDatatypes := program.types.filterMap fun
      | .Datatype dt => some dt
      | _ => none
    let n := laurelDatatypes.length
    if n == 0 then [] else
    let nameToIdx : Std.HashMap String Nat :=
      laurelDatatypes.foldlIdxVal (fun m i dt => m.insert dt.name.text i) {}
    let edges : List (Nat × Nat) :=
      laurelDatatypes.foldlIdxVal (fun acc i dt =>
        (datatypeRefs dt).filterMap nameToIdx.get? |>.foldl (fun acc j => (j, i) :: acc) acc) []
    let g := OutGraph.ofEdges! n edges
    let dtsArr := laurelDatatypes.toArray
    OutGraph.tarjan g |>.toList.filterMap fun comp =>
      let members := comp.toList.filterMap fun idx => dtsArr[idx]?
      if members.isEmpty then none else some members

public def orderingPass : LaurelPass where
  name := "Ordering"
  removes := [
      NodeKind.Program.Unordered
    ]
  creates := [
      NodeKind.Program.Ordered,
      NodeKind.OrderedProgram.WithLaurelTypes
    ]
  documentation := "Produce a `CoreWithLaurelTypes` from a `LaurelProgram` by
computing a combined ordering of functions and proofs using the call graph,
then collecting datatypes and constants.
Functions are grouped into SCCs (for mutual recursion). Proofs are emitted
as individual `procedure` decls. Both participate in the topological ordering
so that axioms are available to functions that need them."
  run := fun _ input _ =>
    match input with
    | .Unordered p =>
      let unlifted := p.types.flatMap fun
        | .Composite ct => ct.instanceProcedures.map fun proc =>
          diagnosticFromSource proc.name.source
            s!"Instance procedure '{proc.name.text}' on composite type '{ct.name.text}' was not lifted before Core translation (pipeline-ordering bug)"
            MessageKind.strataBug
        | _ => []
      (.Ordered (.WithLaurelTypes (orderFunctionsAndProcedures p)), unlifted, {})
    | other => wrongProgram "Ordering" other

end Strata.Laurel
