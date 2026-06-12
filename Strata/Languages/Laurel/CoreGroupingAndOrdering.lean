/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.LaurelPass
import Strata.DL.Lambda.LExpr
import StrataDDM.Util.Graph.Tarjan
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
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

/--
An intermediate representation produced by the transparency pass.
Functions are pure computational procedures (suffixed `$asFunction`);
coreProcedures are the original procedures with any free postconditions
embedded in their `Body.Opaque` postcondition lists.
-/
public structure UnorderedCoreWithLaurelTypes where
  functions : List Procedure
  coreProcedures : List Procedure
  datatypes : List DatatypeDefinition
  constants : List Constant

public def formatUnorderedCoreWithLaurelTypes (p : UnorderedCoreWithLaurelTypes) : Format :=
  let datatypeFmts := p.datatypes.map ToFormat.format
  let constantFmts := p.constants.map ToFormat.format
  let functionFmts := p.functions.map ToFormat.format
  let procFmts := p.coreProcedures.map ToFormat.format
  Format.joinSep (datatypeFmts ++ constantFmts ++ functionFmts ++ procFmts) "\n\n"

public instance : ToFormat UnorderedCoreWithLaurelTypes where
  format := formatUnorderedCoreWithLaurelTypes

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
  | AstNode.mk val _ =>
  match val with
  | .StaticCall callee args =>
      callee.text :: args.flatMap (fun a => collectStaticCallNames a)
  | .PrimitiveOp _ args _ => args.flatMap (fun a => collectStaticCallNames a)
  | .IfThenElse cond t e =>
      collectStaticCallNames cond ++
      collectStaticCallNames t ++
      match e with
      | some eelse => collectStaticCallNames eelse
      | none => []
  | .Block stmts _ => stmts.flatMap (fun s => collectStaticCallNames s)
  | .Assign targets v =>
      -- Field targets contain StmtExpr children; defensively recurse into them
      -- even though field-target assigns are currently eliminated before this pass.
      let targetCalls := targets.attach.flatMap fun ⟨t, _⟩ => match _htv : t.val with
        | .Field inner _fieldName => collectStaticCallNames inner
        | _ => []
      targetCalls ++ collectStaticCallNames v
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
  | .Quantifier _ _ trig body =>
      (match trig with
      | some t => collectStaticCallNames t
      | none => []) ++
      collectStaticCallNames body
  | .Var (.Field t _) => collectStaticCallNames t
  | .PureFieldUpdate t _ v => collectStaticCallNames t ++ collectStaticCallNames v
  | .InstanceCall t _ args =>
      collectStaticCallNames t ++ args.flatMap (fun a => collectStaticCallNames a)
  | .Old v | .Fresh v | .Assume v => collectStaticCallNames v
  | .Assert ⟨cond, _summary, _⟩ => collectStaticCallNames cond
  | .ProveBy v p => collectStaticCallNames v ++ collectStaticCallNames p
  | .ReferenceEquals l r => collectStaticCallNames l ++ collectStaticCallNames r
  | .AsType t _ | .IsType t _ => collectStaticCallNames t
  | .ContractOf _ f => collectStaticCallNames f
  | .Assigned v => collectStaticCallNames v
  | _ => []
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try term_by_mem)
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := Variable.sizeOf_field_target_lt_of_eq _htv
    omega))
  all_goals omega

/--
Build the procedure call graph, run Tarjan's SCC algorithm, and return each SCC
as a list of procedures paired with a flag indicating whether the SCC is recursive.
Results are in reverse topological order: dependencies before dependents.

Procedures with axioms are placed as early as possible — before
unrelated procedures without them — by stably partitioning them first before building
the graph. Tarjan then naturally assigns them lower indices, causing them to appear
earlier in the output.
-/
public def computeSccDecls (program : UnorderedCoreWithLaurelTypes) : List (List Procedure × Bool) :=
  -- Stable partition: procedures with axioms come first, preserving relative
  -- order within each group. Tarjan then places them earlier in the topological output.
  let allProcs := program.functions ++ program.coreProcedures
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
      | .Opaque postconds (some impl) _ => postconds.map (·.condition) ++ [impl]
      | .Opaque postconds none _ => postconds.map (·.condition)
      | _ => []
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
A single declaration in a CoreWithLaurelTypes program. Declarations are in
dependency order (dependencies before dependents).
-/
public inductive OrderedDecl where
  /-- A group of functions (single non-recursive, or mutually recursive).
      Invariant: `funcs.length > 1 → isRecursive = true`. -/
  | funcs (funcs : List Procedure) (isRecursive : Bool)
  /-- A single (non-functional) procedure. -/
  | procedure (procedure : Procedure)
  /-- A group of (possibly mutually recursive) datatypes. -/
  | datatypes (dts : List DatatypeDefinition)
  /-- A named constant. -/
  | constant (c : Constant)

/--
A program whose declarations have been grouped and topologically ordered,
using Laurel types. Produced by `orderFunctionsAndProcedures` from a
`UnorderedCoreWithLaurelTypes`.
-/
public structure CoreWithLaurelTypes where
  decls : List OrderedDecl

open Std (Format ToFormat)

public section

def formatOrderedDecl : OrderedDecl → Format
  | .funcs funcs _ => Format.joinSep (funcs.map ToFormat.format) "\n\n"
  | .procedure proc => ToFormat.format proc
  | .datatypes dts => Format.joinSep (dts.map ToFormat.format) "\n\n"
  | .constant c => ToFormat.format c

instance : ToFormat OrderedDecl where
  format := formatOrderedDecl

def formatCoreWithLaurelTypes (p : CoreWithLaurelTypes) : Format :=
  Format.joinSep (p.decls.map formatOrderedDecl) "\n\n"

instance : ToFormat CoreWithLaurelTypes where
  format := formatCoreWithLaurelTypes

end -- public section

/--
Produce a `CoreWithLaurelTypes` from a `UnorderedCoreWithLaurelTypes` by
computing a combined ordering of functions and proofs using the call graph,
then collecting datatypes and constants.

Functions are grouped into SCCs (for mutual recursion). Proofs are emitted
as individual `procedure` decls. Both participate in the topological ordering
so that axioms are available to functions that need them.
-/
def orderFunctionsAndProcedures (program : UnorderedCoreWithLaurelTypes) : CoreWithLaurelTypes :=
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
  /-- Group datatypes from a UnorderedCoreWithLaurelTypes by SCC. -/
  groupDatatypesByScc' (program : UnorderedCoreWithLaurelTypes) : List (List DatatypeDefinition) :=
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

public def orderingPass : LaurelPass UnorderedCoreWithLaurelTypes CoreWithLaurelTypes where
  name := "OrderingPass"
  comesBefore := []
  documentation := "Produce a `CoreWithLaurelTypes` from a `UnorderedCoreWithLaurelTypes` by
computing a combined ordering of functions and proofs using the call graph,
then collecting datatypes and constants.

Functions are grouped into SCCs (for mutual recursion). Proofs are emitted
as individual `procedure` decls. Both participate in the topological ordering
so that axioms are available to functions that need them."
  run := fun p _ =>
    (orderFunctionsAndProcedures p, [], {})

end Strata.Laurel
