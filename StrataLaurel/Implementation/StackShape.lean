/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.MapStmtExpr

namespace Strata.Laurel

public section

def isStackVar (v : VariableMd) : Bool := v.val matches .Stack _

def isStackPushTarget (targets : List VariableMd) : Bool := targets.any isStackVar

def nodeTouchesStack (e : StmtExprMd) : Bool :=
  match e.val with
  | .Var (.Stack _) => true
  | .Assign targets _ => isStackPushTarget targets
  | .IncrDecr _ _ target | .CompoundAssign _ target _ => isStackVar target
  | _ => false

def hasStackPush (e : StmtExprMd) : Bool :=
  anyStmtExpr (fun n => match n.val with
    | .Assign targets _ => isStackPushTarget targets
    | .IncrDecr _ _ target | .CompoundAssign _ target _ => isStackVar target
    | _ => false) e

def stackPermutation (targets : List VariableMd) (value : StmtExprMd) : Option (List Nat) :=
  match value.val with
  | .Call none callee args _ =>
    match callee.text.splitOn "_" with
    | "$permute" :: indices =>
      let order := indices.filterMap String.toNat?
      if targets.all isStackVar && args.all (·.val matches .Var (.Stack _))
          && order.length == targets.length && order.length == indices.length
          && order.all (· < args.length) then some order else none
    | _ => none
  | _ => none

partial def endsAbruptly (s : StmtExprMd) : Bool :=
  match s.val with
  | .Return _ | .Throw _ | .Goto .. => true
  | .Block stmts none _ _ => (stmts.getLast?.map endsAbruptly).getD false
  | .IfThenElse _ th (some el) => endsAbruptly th && endsAbruptly el
  | _ => false

def withoutQuantifierBodies (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun n => if n.val matches .Quantifier .. then ⟨.LiteralBool true, n.source⟩ else n) e

def countStackReads (e : StmtExprMd) : Nat :=
  foldStmtExpr (fun n acc => if n.val matches .Var (.Stack _) then acc + 1 else acc) 0 (withoutQuantifierBodies e)

def stackWindow (s : StmtExprMd) : Option StmtExprMd :=
  match s.val with
  | .Assign [⟨.Stack _, _⟩] v => some v
  | .IfThenElse c _ _ => some c
  | .While c .. => some c
  | .Block .. | .Try .. | .Goto .. => none
  | _ => some s

def stackWindowReads (s : StmtExprMd) : Nat :=
  match stackWindow s with
  | some w => countStackReads w
  | none => 0

def procedureTouchesStack (proc : Procedure) : Bool :=
  ((foldProcedureExprsM (m := StateM Bool)
    (fun n => do if nodeTouchesStack n then set true) proc).run false).2

def programReadsStackUnderOld (program : LaurelProgram) : Bool :=
  ((mapLaurelProgramProceduresM (m := StateM Bool)
    (fun proc => do
      foldProcedureExprsM (fun n => do
        if let .Old inner _ := n.val then
          if countStackReads inner > 0 then set true) proc
      pure proc) program).run false).2

def programUsesStackInQuantifier (program : LaurelProgram) : Bool :=
  ((mapLaurelProgramProceduresM (m := StateM Bool)
    (fun proc => do
      foldProcedureExprsM (fun n => do
        if let .Quantifier _ _ _ body := n.val then
          if anyStmtExpr nodeTouchesStack body then set true) proc
      pure proc) program).run false).2

def programTouchesStack (program : LaurelProgram) : Bool :=
  ((mapLaurelProgramProceduresM (m := StateM Bool)
    (fun proc => do
      if procedureTouchesStack proc then set true
      pure proc) program).run false).2

end -- public section

end Strata.Laurel
