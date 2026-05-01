/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program

---------------------------------------------------------------------

public section

namespace Core

/-- Generic call graph structure -/
structure CallGraph where
  -- A map from caller to a list of (callee, # of calls)
  callees : Std.HashMap String (Std.HashMap String Nat)
  -- A map from callee to a list of (caller, # of calls)
  callers : Std.HashMap String (Std.HashMap String Nat)
deriving Inhabited, BEq

namespace CallGraph

def sortedEntries (m : Std.HashMap String α) : List (String × α) :=
  m.toList.mergeSort (·.1 < ·.1)

def reprMap (m : Std.HashMap String (Std.HashMap String Nat)) : Std.Format :=
  let fmtInner (vs : List (String × Nat)) : Std.Format :=
    Std.Format.joinSep (vs.map fun p => f!"(\"{p.1}\", {p.2})") ", "
  let entries := sortedEntries m
  let parts := entries.map fun p => f!"(\"{p.1}\", [{fmtInner (sortedEntries p.2)}])"
  Std.Format.joinSep parts ("," ++ Std.Format.line)

instance : Repr CallGraph where
  reprPrec cg _ :=
    f!"CallGraph(callees: [{reprMap cg.callees}],"
    ++ Std.Format.line
    ++ f!"         callers: [{reprMap cg.callers}])"

end CallGraph

def CallGraph.empty : CallGraph :=
  { callees := Std.HashMap.emptyWithCapacity,
    callers := Std.HashMap.emptyWithCapacity }

def CallGraph.getCallees (cg : CallGraph) (name : String) : List String :=
  if h : cg.callees.contains name then (cg.callees[name]'h).keys else []

def CallGraph.getCalleesWithCount (cg : CallGraph) (name : String)
  : Std.HashMap String Nat :=
  if h : cg.callees.contains name then (cg.callees[name]'h) else {}

def CallGraph.getCallers (cg : CallGraph) (name : String) : List String :=
  if h : cg.callers.contains name then (cg.callers[name]'h).keys else []

def CallGraph.getCallersWithCount (cg : CallGraph) (name : String)
  : Std.HashMap String Nat :=
  if h : cg.callers.contains name then (cg.callers[name]'h) else {}

/-- Decrement the number on edge (caller -> callee) by 1. If the result is 0,
  erase the empty entry -/
def CallGraph.decrementEdge (cg : CallGraph) (caller : String) (callee : String)
  : Except String CallGraph :=
  let decrement_count (m : Std.HashMap String Nat) (key : String)
    : Except String (Std.HashMap String Nat) := do
    let some v := m[key]? | throw s!"{key} not available at {repr m}"
    if v == 1 then
      return m.erase key
    else
      return m.insert key (v - 1)
  let modify {β} [Repr β] (m : Std.HashMap String β) (key : String)
      (fn : β → Except String β) : Except String (Std.HashMap String β) := do
    let some v := m[key]? | throw s!"{key} not available at {repr m}"
    let v' ← fn v
    return m.insert key v'

  do
  let new_callees ← modify cg.callees caller (decrement_count · callee)
  let new_callers ← modify cg.callers callee (decrement_count · caller)
  return {
    callees := new_callees
    callers := new_callers
  }

/-- Add a node with no callees to the call graph. -/
def CallGraph.addLeafNode (cg : CallGraph) (name : String) : CallGraph :=
  { cg with
    callees := cg.callees.insert name {}
    callers := cg.callers.insert name {} }

/-- BFS worker for transitive closure. `getNeighbors` provides the edges.
`allNodes` is a fixed universe of node names (all keys in the graph);
termination is proved via the lexicographic measure
`(allNodes.length - visited.length, toVisit.length)`:
- When `head ∈ visited`: `toVisit` shrinks (second component decreases).
- When `head ∉ visited`: `visited` grows (first component decreases). -/
private def CallGraph.closureGo (getNeighbors : String → List String)
    (allNodes : List String) (visited : List String) (toVisit : List String)
    : List String :=
  match toVisit with
  | [] => visited
  | head :: tail =>
    if visited.contains head then
      closureGo getNeighbors allNodes visited tail
    else
      -- This guard is needed for the termination proof: it gives Lean the fact
      -- `visited.length < allNodes.length` in the else branch.  Semantically it
      -- could be hoisted to the top of the function, but keeping it here avoids
      -- an extra comparison on every call (the guard only fires in the rare case
      -- that visited has grown to cover the entire universe).
      if allNodes.length ≤ visited.length then visited
      else
        closureGo getNeighbors allNodes (head :: visited) (getNeighbors head ++ tail)
termination_by (allNodes.length - visited.length, toVisit.length)

/-- Compute transitive closure of callees; the result does not contain `name`. -/
def CallGraph.getCalleesClosure (cg : CallGraph) (name : String) : List String :=
  let allNodes := cg.callees.toList.map Prod.fst
  (closureGo cg.getCallees allNodes [] [name]).filter (· ≠ name)

/-- True when `name` is part of a (possibly self-referencing) cycle in the
    call graph — i.e., it can transitively reach itself through callees. -/
def CallGraph.isRecursive (cg : CallGraph) (name : String) : Bool :=
  cg.getCallees name |>.any fun callee =>
    callee == name || (cg.getCalleesClosure callee).contains name

/-- Compute transitive closure of callees for multiple `names`. -/
def CallGraph.getAllCalleesClosure (cg : CallGraph) (names : List String) : List String :=
  names.flatMap (cg.getCalleesClosure ·)

/-- Compute transitive closure of callers; the result does not contain `name`. -/
def CallGraph.getCallersClosure (cg : CallGraph) (name : String) : List String :=
  let allNodes := cg.callers.toList.map Prod.fst
  (closureGo cg.getCallers allNodes [] [name]).filter (· ≠ name)


/-- Pick the SCC representative: prefer the alphabetically smallest node
    among `preferredRoots`, falling back to the alphabetically smallest
    among all `remaining`.  `first` is the head of `remaining` (passed
    explicitly to avoid `head!`). -/
private def pickPreferredOrLexicographicallySmallest
    (first : String) (remaining : List String)
    (preferredSet : Std.HashSet String) : String :=
  let preferred := remaining.filter preferredSet.contains
  match preferred with
  | p :: ps => ps.foldl (fun best n => if n < best then n else best) p
  | [] => remaining.foldl (fun best n => if n < best then n else best) first

/-- Worker for `computeRoots`.  `fuel` bounds the number of iterations;
    it is initialised to `nodes.length` which is always sufficient because
    each iteration removes at least one node. -/
private def CallGraph.computeRootsAux (cg : CallGraph)
    (preferredSet : Std.HashSet String)
    : Nat → List String → List String → List String
  | 0, remaining, roots => roots ++ remaining
  | _ + 1, [], roots => roots
  | fuel + 1, first :: rest, roots =>
    let remaining := first :: rest
    let remainingSet := Std.HashSet.ofList remaining
    let noIncoming := remaining.filter fun name =>
      (cg.getCallers name).all fun caller => !remainingSet.contains caller
    let (newRoots, starts) :=
      if noIncoming.isEmpty then
        -- All remaining form SCCs; pick representative
        let pick := pickPreferredOrLexicographicallySmallest first remaining preferredSet
        (roots ++ [pick], [pick])
      else
        (roots ++ noIncoming, noIncoming)
    let reachable := starts ++ cg.getAllCalleesClosure starts
    let newRemaining := remaining.filter (fun n => !(reachable.contains n))
    cg.computeRootsAux preferredSet fuel newRemaining newRoots

/-- Compute "root" nodes of the call graph.

    A root is a node with no incoming edges from other nodes in the
    remaining set.  When only strongly connected components remain (every
    node has at least one incoming edge), the alphabetically smallest node
    among `preferredRoots` is chosen first; if none are in the SCC the
    overall alphabetically smallest node is used.  The algorithm iteratively
    removes roots and their reachable descendants until no nodes remain. -/
def CallGraph.computeRoots (cg : CallGraph)
    (preferredRoots : List String := []) : List String :=
  let nodes := (cg.callees.toList.map Prod.fst).mergeSort (· < ·)
  cg.computeRootsAux (.ofList preferredRoots) nodes.length nodes []

/-- Build call graph from name-callees pairs -/
def buildCallGraph (items : List (String × List String)) : CallGraph :=
  let calleeMap := items.foldl (fun acc (name, calls) =>
    acc.insert name (Std.HashMap.ofList calls.occurrences))
    Std.HashMap.emptyWithCapacity

  let emptyCallerMap := items.foldl (fun acc (name, _) =>
    acc.insert name ([] : List String)) Std.HashMap.emptyWithCapacity
  let callerMapNodedup :=
    items.foldl (fun acc ⟨caller,callees⟩ =>
      callees.foldl (fun acc' callee =>
        let existingCallers := Option.getD (acc'.get? callee) []
        acc'.insert callee (caller :: existingCallers))
      acc)
      emptyCallerMap
  let callerMap := callerMapNodedup.map
    (fun _ v => Std.HashMap.ofList v.occurrences)

  { callees := calleeMap, callers := callerMap }

/--
Extract function calls from an expression. We ignore builtin functions
(`Core.builtinFunctions`) here.
-/
def extractFunctionCallsFromExpr (expr : Expression.Expr) : List String :=
  match expr with
  | .fvar _ _ _ => []
  | .bvar _ _ => []
  | .op _ fname _ =>
    let fname := CoreIdent.toPretty fname
    if builtinFunctions.contains fname then [] else [fname]
  | .const _ _ => []
  | .app _ fn arg => extractFunctionCallsFromExpr fn ++ extractFunctionCallsFromExpr arg
  | .ite _ c t e => extractFunctionCallsFromExpr c ++ extractFunctionCallsFromExpr t ++ extractFunctionCallsFromExpr e
  | .eq _ e1 e2 => extractFunctionCallsFromExpr e1 ++ extractFunctionCallsFromExpr e2
  | .abs _ _ _ body => extractFunctionCallsFromExpr body
  | .quant _ _ _ _ trigger body => extractFunctionCallsFromExpr trigger ++ extractFunctionCallsFromExpr body

def extractCallsFromFunction (func : Function) : List String :=
  match func.body with
  | some body => extractFunctionCallsFromExpr body
  | none => []

mutual
/-- Extract procedure calls from a single statement -/
def extractCallsFromStatement (stmt : Statement) : List String :=
  match stmt with
  | .cmd (.call procName _ _) => [procName]
  | .cmd _ => []
  | .block _ body _ => extractCallsFromStatements body
  | .ite _ thenBody elseBody _ =>
    extractCallsFromStatements thenBody ++
    extractCallsFromStatements elseBody
  | .loop _ _ _ body _ => extractCallsFromStatements body
  | .exit _ _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []

/-- Extract procedure calls from a list of statements -/
def extractCallsFromStatements (stmts : List Statement) : List String :=
  match stmts with
  | [] => []
  | s :: rest => extractCallsFromStatement s ++
                 extractCallsFromStatements rest
end

/-- Extract all procedure calls from a procedure's body -/
def extractCallsFromProcedure (proc : Procedure) : List String :=
  extractCallsFromStatements proc.body

@[expose] abbrev ProcedureCG := CallGraph
@[expose] abbrev FunctionCG := CallGraph

def Program.toProcedureCG (prog : Program) : ProcedureCG :=
  let procedures := prog.decls.filterMap (fun decl =>
    match decl with
    | .proc p _ => some (CoreIdent.toPretty p.header.name, extractCallsFromProcedure p)
    | _ => none)
  buildCallGraph procedures

def Program.toFunctionCG (prog : Program) : FunctionCG :=
  let functions := prog.decls.flatMap (fun decl =>
    match decl with
    | .func f _ => [(CoreIdent.toPretty f.name, extractCallsFromFunction f)]
    | .recFuncBlock fs _ => fs.map (fun f =>
        (CoreIdent.toPretty f.name, extractCallsFromFunction f))
    | _ => [])
  buildCallGraph functions

---------------------------------------------------------------------

/--
Map from user-defined functions to their _immediately_ relevant axiom names.
An axiom `a` is immediately relevant for a function `f` if `f` occurs in the
body of `a`, including in any trigger expressions.

Builtin functions (e.g. `Bool.And`, `Bool.Implies`, arithmetic operators) are
excluded from the map keys. Because builtins appear in nearly every axiom body,
including them would make almost every axiom "immediately relevant" to any goal
that touches a builtin, collapsing the relevance filter entirely.

Future improvement: quantifier triggers could make relevance analysis more
precise — an axiom is only instantiable via its triggers, so only the trigger
functions should create relevance edges (see Boogie PR #427).
-/
abbrev FuncAxMap := Std.HashMap String (List String)

def Program.functionImmediateAxiomMap (prog : Program) : FuncAxMap :=
  let axioms := prog.decls.filterMap (fun decl =>
    match decl with
    | .ax a _ => some a
    | _ => none)

  let functionAxiomPairs := axioms.flatMap (fun ax =>
    let ops := Lambda.LExpr.getOps ax.e
    ops.filterMap (fun op =>
      let fname := CoreIdent.toPretty op
      if builtinFunctions.contains fname then none else some (fname, ax)))

  functionAxiomPairs.foldl
    (fun acc (funcName, ax) =>
      let existing := Option.getD (acc.get? funcName) []
      acc.insert funcName (ax.name :: existing).dedup)
    Std.HashMap.emptyWithCapacity

/--
Fixed-point computation for axiom relevance. An axiom `a` is relevant to
a function `f` if:

1. `f` is present in the body of `a`.
2. A callee of `f` is present in the body of `a`.
3. A caller of `f` is present in the body of `a`.
4. There exists an axiom `b` such that `b` contains a function `g` that is
   itself relevant to `f`.

Starting from `relevantFunctions`, this function finds all axioms that
immediately mention those functions, then expands the relevant-function set
with functions appearing in those newly discovered axioms (and their
call-graph neighbors), repeating until no new axioms are found.

`allAxiomNames` is the fixed universe of axiom names in the program.
Terminates because each iteration strictly grows `discoveredAxioms`
(checked via `newAxioms.isEmpty`), so
`allAxiomNames.length - discoveredAxioms.length` decreases.
-/
def computeRelevantAxioms (prog : Program) (cg : FunctionCG)
    (fmap : FuncAxMap) (allAxiomNames : List String)
    (relevantFunctions discoveredAxioms : List String) : List String :=
  let newAxioms := relevantFunctions.flatMap (fun fn => fmap.getD fn []) |>.dedup
  let newAxioms := newAxioms.filter (fun a => a ∉ discoveredAxioms)
  if newAxioms.isEmpty then discoveredAxioms
  else if allAxiomNames.length ≤ discoveredAxioms.length then discoveredAxioms
  else
    -- `newAxioms` is non-empty and disjoint from `discoveredAxioms`, so
    -- appending strictly grows the list.
    let newDiscoveredAxioms := discoveredAxioms ++ newAxioms
    -- Find functions mentioned in newly discovered axioms (excluding builtins).
    let newFunctions := newAxioms.flatMap (fun axName =>
      match prog.getAxiom? ⟨axName, ()⟩ with
      | some ax => (Lambda.LExpr.getOps ax.e).filterMap (fun op =>
          let fname := CoreIdent.toPretty op
          if builtinFunctions.contains fname then none else some fname)
      | none => [])
    -- Expand with call graph neighbors.
    let expandedFunctions := newFunctions.flatMap (fun fn =>
      fn :: cg.getCalleesClosure fn ++ cg.getCallersClosure fn) |>.dedup
    let updatedRelevantFunctions := (relevantFunctions ++ expandedFunctions).dedup
    computeRelevantAxioms prog cg fmap allAxiomNames updatedRelevantFunctions
                          newDiscoveredAxioms
termination_by allAxiomNames.length - discoveredAxioms.length
decreasing_by
  have hne : newAxioms.length ≥ 1 := by
    match newAxioms with
    | _ :: _ => simp
  show allAxiomNames.length - (discoveredAxioms ++ newAxioms).length
     < allAxiomNames.length - discoveredAxioms.length
  simp only [List.length_append]
  omega

---------------------------------------------------------------------

end Core

end -- public section
