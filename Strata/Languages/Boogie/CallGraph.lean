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

/-- Compute transitive closure of callees -/
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

/-- Compute transitive closure of callees for multiple names -/
def CallGraph.getAllCalleesClosure (cg : CallGraph) (names : List String) : List String :=
  (names ++ names.flatMap (cg.getCalleesClosure ·)).dedup

/-- Compute transitive closure of callers -/
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

/-- Build call graph from name-calls pairs -/
def buildCallGraph (items : List (String × List String)) : CallGraph :=
  let calleeMap := items.foldl (fun acc (name, calls) =>
    acc.insert name calls.dedup) Std.HashMap.emptyWithCapacity

  let callerMap :=
    calleeMap.fold (fun acc caller callees =>
      callees.foldl (fun acc' callee =>
        let existingCallers := (acc'.filter (fun e _ => e == callee)).values.flatten
        acc'.insert callee (caller :: existingCallers).dedup)
      acc)
      Std.HashMap.emptyWithCapacity

  { callees := calleeMap, callers := callerMap }

/-- Extract function calls from an expression -/
def extractFunctionCallsFromExpr (expr : Expression.Expr) : List String :=
  match expr with
  | .fvar _ _ => []
  | .bvar _ => []
  | .mdata _ e => extractFunctionCallsFromExpr e
  | .op fname _ => [BoogieIdent.toPretty fname]
  | .const _ _ => []
  | .app fn arg => extractFunctionCallsFromExpr fn ++ extractFunctionCallsFromExpr arg
  | .ite c t e => extractFunctionCallsFromExpr c ++ extractFunctionCallsFromExpr t ++ extractFunctionCallsFromExpr e
  | .eq e1 e2 => extractFunctionCallsFromExpr e1 ++ extractFunctionCallsFromExpr e2
  | .abs _ body => extractFunctionCallsFromExpr body
  | .quant _ _ trigger body => extractFunctionCallsFromExpr trigger ++ extractFunctionCallsFromExpr body

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
  | .block _ body _ => extractCallsFromStatements body.ss
  | .ite _ thenBody elseBody _ =>
    extractCallsFromStatements thenBody.ss ++
    extractCallsFromStatements elseBody.ss
  | .loop _ _ _ body _ => extractCallsFromStatements body.ss
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

/--
Function to _relevant_ axioms mapping

An axiom `a` is _relevant_ for a function `f` if `f` occurs in the body of `a`,
including in any trigger expressions.
-/
def Program.toFunctionAxiomMap (prog : Program) : Std.HashMap String (List String) :=
  let axioms := prog.decls.filterMap (fun decl =>
    match decl with
    | .ax a _ => some a
    | _ => none)

  let functionAxiomPairs := axioms.flatMap (fun ax =>
    let ops := Lambda.LExpr.getOps ax.e
    ops.map (fun op => (BoogieIdent.toPretty op, ax)))

  functionAxiomPairs.foldl
    (fun acc (funcName, ax) =>
      let existing := (acc.filter (fun a _ => a == funcName)).values.flatten
      acc.insert funcName (ax.name :: existing).dedup)
    Std.HashMap.emptyWithCapacity

instance : Std.ToFormat (Std.HashMap String (List Axiom)) where
  format m :=
    let entries :=
      m.toList.map
        (fun (k, v) => f!"{k}: [{Std.Format.joinSep (v.map Std.format) ", "}]")
    f!"{Std.Format.joinSep entries ", \n"}"

def Program.getRelevantAxioms (prog : Program) (functions : List String) : List String :=
  let axiomMap := prog.toFunctionAxiomMap
  functions.flatMap (fun f =>
  (axiomMap.filter (fun k _ => k == f)).values.flatten) |>.dedup

def Program.getIrrelevantAxioms (prog : Program) (functions : List String) : List String :=
  let allAxioms := prog.decls.filterMap (fun decl =>
    match decl with
    | .ax a _ => some a.name
    | _ => none)
  let relevantAxioms := prog.getRelevantAxioms functions
  allAxioms.filter (fun ax => !relevantAxioms.contains ax)

---------------------------------------------------------------------

end Boogie
