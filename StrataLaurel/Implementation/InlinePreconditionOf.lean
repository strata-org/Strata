/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.MapStmtExpr
public import StrataLaurel.Implementation.LaurelPass

namespace Strata.Laurel

public section

private def freeLocalNames (e : StmtExprMd) : List String :=
  collectStmtExprList (fun n => match n.val with
    | .Var (.Local id) => [id.text]
    | _ => []) e

private def binderNames (e : StmtExprMd) : List String :=
  collectStmtExprList (fun n => (boundNamesOfNode n).map (·.text)) e

private def substParam (param : Identifier) (arg : StmtExprMd) (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun n => match n.val with
    | .Var (.Local id) =>
      let same := match id.uniqueId, param.uniqueId with
        | some a, some b => a == b
        | _, _ => id.text == param.text
      if same then arg else n
    | _ => n) e

private def calleeOf (procs : List Procedure) (callee : Identifier) : Option Procedure :=
  match callee.uniqueId with
  | some uid => procs.find? (·.name.uniqueId == some uid)
  | none => procs.find? (·.name.text == callee.text)

private def instantiate (callee : Procedure) (args : List StmtExprMd) (source : FileRange)
    (site : Nat) : Except String StmtExprMd := do
  let conds := (nonFreeConditions callee.preconditions).zipIdx.map
    fun (c, i) => freshenDeclared s!"$pre{site}_{i}" c.condition
  let argNames := args.flatMap freeLocalNames
  if conds.any (fun c => (binderNames c).any argNames.contains) then
    throw s!"the precondition of '{callee.name.text}' binds a name that an argument uses"
  let pairs := callee.inputs.zip args
  pure (conjoinAnd source (conds.map fun c =>
    pairs.foldl (fun acc (p, a) => substParam p.name a acc) c))

private def report (source : FileRange) (msg : String) : StateM (Nat × List Message) Unit :=
  modify fun (k, ds) => (k, ds ++ [diagnosticFromSource source msg])

private def sameProcedure (a b : Identifier) : Bool :=
  a.text == b.text && a.uniqueId == b.uniqueId

private partial def inlineNode (procs : List Procedure) (chain : List Identifier) (e : StmtExprMd) :
    StateM (Nat × List Message) StmtExprMd := do
  match e.val with
  | .ContractOf .Precondition ⟨.StaticCall callee args _, _⟩ =>
    match calleeOf procs callee with
    | none =>
      report e.source s!"preconditionOf names '{callee.text}', which has no procedure"
      pure ⟨.LiteralBool true, e.source⟩
    | some proc =>
      if chain.any (sameProcedure proc.name) then
        report e.source s!"preconditionOf of '{callee.text}' refers back to itself"
        pure ⟨.LiteralBool true, e.source⟩
      else
        let (site, _) ← get
        modify fun (k, ds) => (k + 1, ds)
        match instantiate proc args e.source site with
        | .ok v => mapStmtExprM (inlineNode procs (proc.name :: chain)) v
        | .error msg =>
          report e.source msg
          pure ⟨.LiteralBool true, e.source⟩
  | .ContractOf .Precondition _ =>
    report e.source "preconditionOf expects a call to a procedure"
    pure ⟨.LiteralBool true, e.source⟩
  | _ => pure e

def inlinePreconditionOf (program : LaurelProgram) : LaurelProgram × List Message :=
  let procs := program.staticProcedures ++ program.staticFunctions
  let (p, _, diags) := (mapLaurelProgramProceduresM (mapProcedureM (mapStmtExprM (inlineNode procs []))) program).run (0, [])
  (p, diags)

def inlinePreconditionOfPass : LaurelPass := .onUnordered {
  name := "InlinePreconditionOf"
  needsResolves := true
  documentation := "Replaces each `contractOf(precondition, f(args))` with `f`'s checked preconditions, conjoined, its parameters substituted by `args`. Runs after LiftInstanceProcedures, so every call names a static procedure."
  creates := [NodeKind.StmtExpr.StaticCall, NodeKind.StmtExpr.LiteralBool] }
  fun _ p _ => let (p', diags) := inlinePreconditionOf p; (p', diags, {})

end

end Strata.Laurel
