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

/--
Function to _relevant_ axioms mapping

For now, our definition of a "relevant axiom" is quite weak: an axiom `a` is
relevant for a function `f` if `f` occurs in the body of `a`, including in any
trigger expressions.

Eventually, we will compute a transitive closure involving both axioms and
functions. E.g., consider the following example that we don't handle yet:

```
axiom1 : forall x :: g(x) == false
axiom2 : forall x :: f(x) == g(x)
----------------------------------
goal : forall x, f(x) == true
```

Right now, we will determine that only `axiom2` is relevant for the goal, which
means that the solver will return `unknown` in this case instead of `failed`.

Note: one way to make the dependency analysis better right now is to use the
triggers to mention relevant functions. E.g., now `axiom1` has `f` in its body,
so it is relevant for the goal.

```
axiom1 : forall x :: {f(x)} g(x) == false
axiom2 : forall x :: f(x) == g(x)
----------------------------------
goal : forall x, f(x) == true
```
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
      let existing := Option.getD (acc.get? funcName) []
      acc.insert funcName (ax.name :: existing).dedup)
    Std.HashMap.emptyWithCapacity

instance : Std.ToFormat (Std.HashMap String (List Axiom)) where
  format m :=
    let entries :=
      m.toList.map
        (fun (k, v) => f!"{k}: [{Std.Format.joinSep (v.map Std.format) ", "}]")
    f!"{Std.Format.joinSep entries ", \n"}"

def Program.getIrrelevantAxioms (prog : Program) (functions : List String) : List String :=
  let functionsSet := functions.toArray.qsort (· < ·) -- Sort for binary search
  prog.decls.filterMap (fun decl =>
    match decl with
    | .ax a _ =>
      let ops := Lambda.LExpr.getOps a.e
      let hasRelevantOp := ops.any (fun op =>
        functionsSet.binSearch (BoogieIdent.toPretty op) (· < ·) |>.isSome)
      if hasRelevantOp then none else some a.name
    | _ => none)

---------------------------------------------------------------------

end Boogie
