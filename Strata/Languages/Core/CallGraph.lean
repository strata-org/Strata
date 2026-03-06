/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program

---------------------------------------------------------------------
namespace Core

/-- Generic call graph structure -/
structure CallGraph where
  -- A map from caller to a list of (callee, # of calls)
  callees : Std.HashMap String (Std.HashMap String Nat)
  -- A map from callee to a list of (caller, # of calls)
  callers : Std.HashMap String (Std.HashMap String Nat)
deriving Repr

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

/-- Compute transitive closure of callees; the result does not contain `name`. -/
def CallGraph.getCalleesClosure (cg : CallGraph) (name : String) : List String :=
  -- Fuel bound: initially 1 item is enqueued; processing each new node `n`
  -- enqueues |callees(n)| more. Total enqueued ≤ 1 + Σ |callees(n)| ≤ 1 + totalEdges.
  let fuel := cg.callees.toList.foldl (fun acc (_, v) => acc + v.size) 0 + 1
  let rec go (fuel : Nat) (visited : List String) (toVisit : List String) : List String :=
    match toVisit with
    | [] => visited
    | head :: tail =>
      match fuel with
      | 0 => visited
      | n + 1 =>
        if visited.contains head then go n visited tail
        else go n (head :: visited) (cg.getCallees head ++ tail)
  (go fuel [] [name]).filter (· ≠ name)

/-- Compute transitive closure of callees for multiple `names`. -/
def CallGraph.getAllCalleesClosure (cg : CallGraph) (names : List String) : List String :=
  names.flatMap (cg.getCalleesClosure ·)

/-- Compute transitive closure of callers; the result does not contain `name`. -/
def CallGraph.getCallersClosure (cg : CallGraph) (name : String) : List String :=
  -- Fuel bound: symmetric to `getCalleesClosure` but over the callers graph.
  let fuel := cg.callers.toList.foldl (fun acc (_, v) => acc + v.size) 0 + 1
  let rec go (fuel : Nat) (visited : List String) (toVisit : List String) : List String :=
    match toVisit with
    | [] => visited
    | head :: tail =>
      match fuel with
      | 0 => visited
      | n + 1 =>
        if visited.contains head then go n visited tail
        else go n (head :: visited) (cg.getCallers head ++ tail)
  (go fuel [] [name]).filter (· ≠ name)

/-- Compute transitive closure of callers for multiple `names`. -/
def CallGraph.getAllCallersClosure (cg : CallGraph) (names : List String) : List String :=
  names.flatMap (cg.getCallersClosure ·)

/-- Build call graph from name-callees pairs -/
def buildCallGraph (items : List (String × List String)) : CallGraph :=
  let calleeMap := items.foldl (fun acc (name, calls) =>
    acc.insert name (Std.HashMap.ofList calls.occurrences))
    Std.HashMap.emptyWithCapacity

  let callerMapNodedup :=
    items.foldl (fun acc ⟨caller,callees⟩ =>
      callees.foldl (fun acc' callee =>
        let existingCallers := Option.getD (acc'.get? callee) []
        acc'.insert callee (caller :: existingCallers))
      acc)
      Std.HashMap.emptyWithCapacity
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
  | .cmd (.call _ procName _ _) => [procName]
  | .cmd _ => []
  | .block _ body _ => extractCallsFromStatements body
  | .ite _ thenBody elseBody _ =>
    extractCallsFromStatements thenBody ++
    extractCallsFromStatements elseBody
  | .loop _ _ _ body _ => extractCallsFromStatements body
  | .exit _ _ => []
  | .funcDecl _ _ => []
termination_by sizeOf stmt

/-- Extract procedure calls from a list of statements -/
def extractCallsFromStatements (stmts : List Statement) : List String :=
  match stmts with
  | [] => []
  | s :: rest => extractCallsFromStatement s ++ extractCallsFromStatements rest
termination_by sizeOf stmts
end

/-- Extract all procedure calls from a procedure's body -/
def extractCallsFromProcedure (proc : Procedure) : List String :=
  extractCallsFromStatements proc.body

abbrev ProcedureCG := CallGraph
abbrev FunctionCG := CallGraph

def Program.toProcedureCG (prog : Program) : ProcedureCG :=
  let procedures := prog.decls.filterMap (fun decl =>
    match decl with
    | .proc p _ => some (CoreIdent.toPretty p.header.name, extractCallsFromProcedure p)
    | _ => none)
  buildCallGraph procedures

def Program.toFunctionCG (prog : Program) : FunctionCG :=
  let functions := prog.decls.filterMap (fun decl =>
    match decl with
    | .func f _ => some (CoreIdent.toPretty f.name, extractCallsFromFunction f)
    | _ => none)
  buildCallGraph functions

---------------------------------------------------------------------

abbrev FuncAxMap := Std.HashMap String (List String)

/--
Map from functions to their _immediately_ relevant axioms. An axiom `a` is
_immediately_ relevant for a function `f` if `f` occurs in the body of `a`,
including in any trigger expressions. Callees and callers of `f` are not
associated with `a` in this map.
-/
def Program.functionImmediateAxiomMap (prog : Program) : FuncAxMap :=
  let axioms := prog.decls.filterMap (fun decl =>
    match decl with
    | .ax a _ => some a
    | _ => none)

  let functionAxiomPairs := axioms.flatMap (fun ax =>
    let ops := Lambda.LExpr.getOps ax.e
    ops.map (fun op => (CoreIdent.toPretty op, ax)))

  functionAxiomPairs.foldl
    (fun acc (funcName, ax) =>
      let existing := Option.getD (acc.get? funcName) []
      acc.insert funcName (ax.name :: existing).dedup)
    Std.HashMap.emptyWithCapacity

/-- Fixed-point computation for axiom relevance. Starting from
  `relevantFunctions`, finds all axioms that immediately mention those
  functions, then expands the relevant-function set with functions appearing
  in those newly discovered axioms (and their call-graph neighbors), repeating
  until no new axioms are found.

  Terminates because each recursive call strictly grows `discoveredAxioms`
  by at least one element (checked via `newAxioms.isEmpty`), and the total
  number of axioms is bounded by `fuel` (initially `prog.decls.length`).
-/
private def computeRelevantAxiomsAux (prog : Program) (cg : FunctionCG) (fmap : FuncAxMap)
    (fuel : Nat) (relevantFunctions discoveredAxioms : List String) : List String :=
  match fuel with
  | 0 => discoveredAxioms
  | n + 1 =>
    -- Get axioms immediately relevant to the current relevant functions.
    let newAxioms := relevantFunctions.flatMap (fun fn => fmap.getD fn []) |>.dedup
    let newAxioms := newAxioms.filter (fun a => a ∉ discoveredAxioms)

    if newAxioms.isEmpty then discoveredAxioms
    else
      let allAxioms := (discoveredAxioms ++ newAxioms).dedup

      -- Find functions mentioned in newly discovered axioms.
      let newFunctions := newAxioms.flatMap (fun axName =>
        match prog.getAxiom? ⟨axName, ()⟩ with
        | some ax => (Lambda.LExpr.getOps ax.e).map CoreIdent.toPretty
        | none => [])

      -- Expand with call graph neighbors.
      let expandedFunctions := newFunctions.flatMap (fun fn =>
        fn :: cg.getCalleesClosure fn ++ cg.getCallersClosure fn) |>.dedup

      let updatedRelevantFunctions := (relevantFunctions ++ expandedFunctions).dedup
      computeRelevantAxiomsAux prog cg fmap n updatedRelevantFunctions allAxioms
termination_by fuel

def computeRelevantAxioms (prog : Program) (cg : FunctionCG) (fmap : FuncAxMap)
    (relevantFunctions discoveredAxioms : List String) : List String :=
  -- Each iteration adds ≥1 new axiom; total axioms ≤ total declarations.
  computeRelevantAxiomsAux prog cg fmap prog.decls.length relevantFunctions discoveredAxioms

/-- Compute all axioms relevant to function `f`. An axiom `a` is relevant to
  function `f` if:

1. `f` is present in the body of `a`.
2. A callee of `f` is present in the body of `a`.
3. A caller of `f` is present in the body of `a`.
4. There exists an axiom `b` such that `b` contains a function `g` that is
   itself relevant to `f`.
-/
def Program.getRelevantAxioms (prog : Program) (f : String) : List String :=
  let cg := Program.toFunctionCG prog
  let fmap := Program.functionImmediateAxiomMap prog
  -- Start with `f` and its call graph neighbors.
  let initialFunctions := (f :: cg.getCalleesClosure f ++ cg.getCallersClosure f).dedup
  computeRelevantAxioms prog cg fmap initialFunctions []

def Program.getIrrelevantAxioms (prog : Program) (functions : List String) : List String :=
  let allAxioms := prog.decls.filterMap (fun decl =>
    match decl with
    | .ax a _ => some a.name
    | _ => none)
  let relevantAxioms := functions.flatMap (fun f => prog.getRelevantAxioms f) |>.dedup
  allAxioms.filter (fun a => a ∉ relevantAxioms)

---------------------------------------------------------------------

end Core
