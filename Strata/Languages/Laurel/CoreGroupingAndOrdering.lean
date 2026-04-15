/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public import Strata.Languages.Laurel.FunctionsAndProofs
import Strata.DL.Lambda.LExpr
import Strata.DDM.Util.Graph.Tarjan

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
Collect all `StaticCall` callee names referenced anywhere in a `StmtExpr`.
Used to build the call graph for SCC-based procedure ordering.
-/
def collectStaticCallNames (expr : StmtExprMd) : List String :=
  match expr with
  | WithMetadata.mk val _ =>
  match val with
  | .StaticCall callee args =>
      callee.text :: args.flatMap (fun a => collectStaticCallNames a)
  | .PrimitiveOp _ args => args.flatMap (fun a => collectStaticCallNames a)
  | .IfThenElse cond t e =>
      collectStaticCallNames cond ++
      collectStaticCallNames t ++
      match e with
      | some eelse => collectStaticCallNames eelse
      | none => []
  | .Block stmts _ => stmts.flatMap (fun s => collectStaticCallNames s)
  | .Assign targets v =>
      targets.flatMap (fun t => collectStaticCallNames t) ++
      collectStaticCallNames v
  | .LocalVariable _ _ initOption =>
      match initOption with
      | some init => collectStaticCallNames init
      | none => []
  | .Return v =>
      match v with
      | some x => collectStaticCallNames x
      | none => []
  | .While cond invs dec body =>
      collectStaticCallNames cond ++
      invs.flatMap (fun i => collectStaticCallNames i) ++
      (match dec with
      | some d => collectStaticCallNames d
      | none => []) ++
      collectStaticCallNames body
  | .Forall _ trig body =>
      (match trig with
      | some t => collectStaticCallNames t
      | none => []) ++
      collectStaticCallNames body
  | .Exists _ trig body =>
      (match trig with
      | some t => collectStaticCallNames t
      | none => []) ++
      collectStaticCallNames body
  | .FieldSelect t _ => collectStaticCallNames t
  | .PureFieldUpdate t _ v => collectStaticCallNames t ++ collectStaticCallNames v
  | .InstanceCall t _ args =>
      collectStaticCallNames t ++ args.flatMap (fun a => collectStaticCallNames a)
  | .Old v | .Fresh v | .Assert v | .Assume v => collectStaticCallNames v
  | .ProveBy v p => collectStaticCallNames v ++ collectStaticCallNames p
  | .ReferenceEquals l r => collectStaticCallNames l ++ collectStaticCallNames r
  | .AsType t _ | .IsType t _ => collectStaticCallNames t
  | .ContractOf _ f => collectStaticCallNames f
  | .Assigned v => collectStaticCallNames v
  | _ => []
termination_by sizeOf expr

/--
Build the procedure call graph, run Tarjan's SCC algorithm, and return each SCC
as a list of procedures paired with a flag indicating whether the SCC is recursive.
Results are in reverse topological order: dependencies before dependents.

Procedures with an `invokeOn` trigger are placed as early as possible — before
unrelated procedures without one — by stably partitioning them first before building
the graph. Tarjan then naturally assigns them lower indices, causing them to appear
earlier in the output.
-/
public def computeSccDecls (program : FunctionsAndProofsProgram) : List (List Procedure × Bool) :=
  -- Stable partition: procedures with invokeOn come first, preserving relative
  -- order within each group. Tarjan then places them earlier in the topological output.
  let allProcs := program.functions ++ program.proofs
  let (withInvokeOn, withoutInvokeOn) :=
    allProcs.partition (fun p => p.invokeOn.isSome)
  let nonExternal : List Procedure := withInvokeOn ++ withoutInvokeOn

  -- Build a call-graph over all non-external procedures.
  -- An edge proc → callee means proc's body/contracts contain a StaticCall to callee.
  let nonExternalArr : Array Procedure := nonExternal.toArray
  let nameToIdx : Std.HashMap String Nat :=
    nonExternalArr.foldl (fun (acc : Std.HashMap String Nat × Nat) proc =>
      (acc.1.insert proc.name.text acc.2, acc.2 + 1)) ({}, 0) |>.1

  -- Collect all callee names from a procedure's body and contracts.
  let procCallees (proc : Procedure) : List String :=
    let bodyExprs : List StmtExprMd := match proc.body with
      | .Transparent b => [b]
      | .Opaque postconds (some impl) _ => postconds ++ [impl]
      | .Opaque postconds none _ => postconds
      | _ => []
    let contractExprs : List StmtExprMd :=
      proc.preconditions ++
      proc.invokeOn.toList
    (bodyExprs ++ contractExprs).flatMap collectStaticCallNames

  -- Build the OutGraph for Tarjan.
  let n := nonExternalArr.size
  let graph : Strata.OutGraph n :=
    nonExternalArr.foldl (fun (acc : Strata.OutGraph n × Nat) proc =>
      let callerIdx := acc.2
      let g := acc.1
      let callees := procCallees proc
      let g' := callees.foldl (fun g callee =>
        match nameToIdx.get? callee with
        | some calleeIdx => g.addEdge! calleeIdx callerIdx
        | none => g) g
      (g', callerIdx + 1)) (Strata.OutGraph.empty n, 0) |>.1

  -- Run Tarjan's SCC algorithm. Results are in reverse topological order
  -- (a node appears after all nodes that have paths to it).
  let sccs := Strata.OutGraph.tarjan graph

  sccs.toList.filterMap fun scc =>
    let procs := scc.toList.filterMap fun idx =>
      nonExternalArr[idx.val]?
    if procs.isEmpty then none else
    let isRecursive := procs.length > 1 ||
      (match scc.toList.head? with
        | some node => (graph.nodesOut node).contains node
        | none => false)
    some (procs, isRecursive)

/--
A single declaration in a CoreWithLaurelTypes program. Declarations are in
dependency order (dependencies before dependents).
-/
public inductive OrderedDecl where
  /-- A group of functions (single non-recursive, or mutually recursive). -/
  | funcs (funcs : List Procedure) (isRecursive : Bool)
  /-- A single (non-functional) procedure. -/
  | procedure (procedure : Procedure)
  /-- A group of (possibly mutually recursive) datatypes. -/
  | datatypes (dts : List DatatypeDefinition)
  /-- A named constant. -/
  | constant (c : Constant)

/--
A program whose declarations have been grouped and topologically ordered,
using Laurel types. Produced by `orderFunctionsAndProofs` from a
`FunctionsAndProofsProgram`.
-/
public structure CoreWithLaurelTypes where
  decls : List OrderedDecl

/--
Produce a `CoreWithLaurelTypes` from a `FunctionsAndProofsProgram` by
computing a combined ordering of functions and proofs using the call graph,
then collecting datatypes and constants.

Functions are grouped into SCCs (for mutual recursion). Proofs are emitted
as individual `procedure` decls. Both participate in the topological ordering
so that `invokeOn` axioms are available to functions that need them.
-/
public def orderFunctionsAndProofs (program : FunctionsAndProofsProgram) : CoreWithLaurelTypes :=
  let datatypeDecls := (groupDatatypesByScc' program).map OrderedDecl.datatypes
  let constantDecls := program.constants.map OrderedDecl.constant
  let funcNames : Std.HashSet String :=
    program.functions.foldl (fun s p => s.insert p.name.text) {}
  let orderedDecls := (computeSccDecls program).flatMap fun (procs, isRecursive) =>
    -- Split the SCC into functions and proofs
    let (funcs, proofs) := procs.partition (fun p => funcNames.contains p.name.text)
    let funcDecl := if funcs.isEmpty then [] else [OrderedDecl.funcs funcs isRecursive]
    let proofDecls := proofs.map OrderedDecl.procedure
    funcDecl ++ proofDecls
  { decls := datatypeDecls ++ constantDecls ++ orderedDecls }
where
  /-- Group datatypes from a FunctionsAndProofsProgram by SCC. -/
  groupDatatypesByScc' (program : FunctionsAndProofsProgram) : List (List DatatypeDefinition) :=
    let laurelDatatypes := program.datatypes
    let n := laurelDatatypes.length
    if n == 0 then [] else
    let nameToIdx : Std.HashMap String Nat :=
      laurelDatatypes.foldlIdx (fun m i dt => m.insert dt.name.text i) {}
    let edges : List (Nat × Nat) :=
      laurelDatatypes.foldlIdx (fun acc i dt =>
        (datatypeRefs dt).filterMap nameToIdx.get? |>.foldl (fun acc j => (j, i) :: acc) acc) []
    let g := OutGraph.ofEdges! n edges
    let dtsArr := laurelDatatypes.toArray
    OutGraph.tarjan g |>.toList.filterMap fun comp =>
      let members := comp.toList.filterMap fun idx => dtsArr[idx]?
      if members.isEmpty then none else some members

end Strata.Laurel
