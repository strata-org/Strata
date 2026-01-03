/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Program

---------------------------------------------------------------------
namespace Boogie

/-- Generic call graph structure -/
structure CallGraph where
  callees : Std.HashMap String (List String)
  callers : Std.HashMap String (List String)

def CallGraph.empty : CallGraph :=
  { callees := Std.HashMap.emptyWithCapacity,
    callers := Std.HashMap.emptyWithCapacity }

def CallGraph.getCallees (cg : CallGraph) (name : String) : List String :=
  if h : cg.callees.contains name then cg.callees[name]'h else []

def CallGraph.getCallers (cg : CallGraph) (name : String) : List String :=
  if h : cg.callers.contains name then cg.callers[name]'h else []

/-- Compute transitive closure of callees; the result does not contain `name`. -/
partial def CallGraph.getCalleesClosure (cg : CallGraph) (name : String) : List String :=
  let rec go (visited : List String) (toVisit : List String) : List String :=
    match toVisit with
    | [] => visited
    | head :: tail =>
      if visited.contains head then go visited tail
      else
        let newCallees := cg.getCallees head
        go (head :: visited) (newCallees ++ tail)
  (go [] [name]).filter (· ≠ name)

/-- Compute transitive closure of callees for multiple `names`. -/
def CallGraph.getAllCalleesClosure (cg : CallGraph) (names : List String) : List String :=
  names.flatMap (cg.getCalleesClosure ·)

/-- Compute transitive closure of callers; the result does not contain `name`. -/
partial def CallGraph.getCallersClosure (cg : CallGraph) (name : String) : List String :=
  let rec go (visited : List String) (toVisit : List String) : List String :=
    match toVisit with
    | [] => visited
    | head :: tail =>
      if visited.contains head then go visited tail
      else
        let newCallers := cg.getCallers head
        go (head :: visited) (newCallers ++ tail)
  (go [] [name]).filter (· ≠ name)

/-- Compute transitive closure of callers for multiple `names`. -/
def CallGraph.getAllCallersClosure (cg : CallGraph) (names : List String) : List String :=
  names.flatMap (cg.getCallersClosure ·)

/-- Build call graph from name-calls pairs -/
def buildCallGraph (items : List (String × List String)) : CallGraph :=
  let calleeMap := items.foldl (fun acc (name, calls) =>
    acc.insert name calls.dedup) Std.HashMap.emptyWithCapacity

  let callerMap :=
    calleeMap.fold (fun acc caller callees =>
      callees.foldl (fun acc' callee =>
        let existingCallers := Option.getD (acc'.get? callee) []
        acc'.insert callee (caller :: existingCallers).dedup)
      acc)
      Std.HashMap.emptyWithCapacity

  { callees := calleeMap, callers := callerMap }

/--
Extract function calls from an expression. We ignore Boogie's builtin functions
(`Boogie.builtinFunctions`) here.
-/
def extractFunctionCallsFromExpr (expr : Expression.Expr) : List String :=
  match expr with
  | .fvar _ _ _ => []
  | .bvar _ _ => []
  | .op _ fname _ =>
    let fname := BoogieIdent.toPretty fname
    if builtinFunctions.contains fname then [] else [fname]
  | .const _ _ => []
  | .app _ fn arg => extractFunctionCallsFromExpr fn ++ extractFunctionCallsFromExpr arg
  | .ite _ c t e => extractFunctionCallsFromExpr c ++ extractFunctionCallsFromExpr t ++ extractFunctionCallsFromExpr e
  | .eq _ e1 e2 => extractFunctionCallsFromExpr e1 ++ extractFunctionCallsFromExpr e2
  | .abs _ _ body => extractFunctionCallsFromExpr body
  | .quant _ _ _ trigger body => extractFunctionCallsFromExpr trigger ++ extractFunctionCallsFromExpr body

def extractCallsFromFunction (func : Function) : List String :=
  match func.body with
  | some body => extractFunctionCallsFromExpr body
  | none => []

mutual
/-- Extract procedure calls from a single statement -/
partial def extractCallsFromStatement (stmt : Statement) : List String :=
  match stmt with
  | .cmd (.call _ procName _ _) => [procName]
  | .cmd _ => []
  | .block _ body _ => extractCallsFromStatements body
  | .ite _ thenBody elseBody _ =>
    extractCallsFromStatements thenBody ++
    extractCallsFromStatements elseBody
  | .loop _ _ _ body _ => extractCallsFromStatements body
  | .goto _ _ => []

/-- Extract procedure calls from a list of statements -/
partial def extractCallsFromStatements (stmts : List Statement) : List String :=
  stmts.flatMap extractCallsFromStatement

/-- Extract all procedure calls from a procedure's body -/
partial def extractCallsFromProcedure (proc : Procedure) : List String :=
  extractCallsFromStatements proc.body
end

abbrev ProcedureCG := CallGraph
abbrev FunctionCG := CallGraph

def Program.toProcedureCG (prog : Program) : ProcedureCG :=
  let procedures := prog.decls.filterMap (fun decl =>
    match decl with
    | .proc p _ => some (BoogieIdent.toPretty p.header.name, extractCallsFromProcedure p)
    | _ => none)
  buildCallGraph procedures

def Program.toFunctionCG (prog : Program) : FunctionCG :=
  let functions := prog.decls.filterMap (fun decl =>
    match decl with
    | .func f _ => some (BoogieIdent.toPretty f.name, extractCallsFromFunction f)
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
    ops.map (fun op => (BoogieIdent.toPretty op, ax)))

  functionAxiomPairs.foldl
    (fun acc (funcName, ax) =>
      let existing := Option.getD (acc.get? funcName) []
      acc.insert funcName (ax.name :: existing).dedup)
    Std.HashMap.emptyWithCapacity

/-- Fixed-point computation for axiom relevance. -/
private partial def computeRelevantAxioms (prog : Program) (cg : CallGraph) (fmap : FuncAxMap)
    (relevantFunctions discoveredAxioms : List String) : List String :=
  -- Get axioms for current relevant functions.
  let newAxioms := relevantFunctions.flatMap (fun fn => fmap.getD fn []) |>.dedup
  let newAxioms := newAxioms.filter (fun a => a ∉ discoveredAxioms)

  if newAxioms.isEmpty then discoveredAxioms
  else
    let allAxioms := (discoveredAxioms ++ newAxioms).dedup

    -- Find functions mentioned in newly discovered axioms.
    let newFunctions := newAxioms.flatMap (fun axName =>
      match prog.getAxiom? ⟨axName, .unres⟩ with
      | some ax => (Lambda.LExpr.getOps ax.e).map (fun x => BoogieIdent.toPretty x)
      | none => [])

    -- Expand with call graph neighbors.
    let expandedFunctions := newFunctions.flatMap (fun fn =>
      fn :: cg.getCalleesClosure fn ++ cg.getCallersClosure fn) |>.dedup

    let updatedRelevantFunctions := (relevantFunctions ++ expandedFunctions).dedup
    computeRelevantAxioms prog cg fmap updatedRelevantFunctions allAxioms

/-- Compute all axioms relevant to function `f`. An axiom `a` is relevant to a
  function `f` if:

1. `f` is present in the body of `a`.
2. A callee of `f` is present in the body of `a`.
3. A caller of `f` is present in the body of `a`.
4. If there exists an axiom `b` such that `b` contains a function `g` relevant
   to `a`.
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
end Boogie
