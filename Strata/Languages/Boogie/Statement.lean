/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.Expressions
import Strata.DL.Imperative.PureExpr
import Strata.Languages.Boogie.Identifiers
import Strata.Languages.Boogie.Factory
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.HasVars
import Strata.DL.Lambda.LExpr

namespace Boogie
open Imperative
open Std (ToFormat Format format)
---------------------------------------------------------------------

/--
Extend Imperative's commands by adding a procedure call.
-/
inductive CmdExt (P : PureExpr) where
  | cmd (c : Imperative.Cmd P)
  /--
  Procedure calls, where `lhs` refers to the variables modified by the call.
  -/
  -- Note: currently the procName in call statement is a String.
  -- Maybe procedure names should just be plain strings since there is no
  -- "scoped procedures" or "generated procedures"
  | call (lhs : List P.Ident) (procName : String) (args : List P.Expr)
         (md : MetaData P := .empty)

/--
We parameterize Boogie's Commands with Lambda dialect's expressions.
-/
abbrev Command := CmdExt Expression

def CmdExt.sizeOf (c : CmdExt P) : Nat :=
  match c with
  | .cmd c => SizeOf.sizeOf c
  | .call l p a _ => 3 + l.length + SizeOf.sizeOf p + a.length

instance : SizeOf (CmdExt P) where
  sizeOf := CmdExt.sizeOf

instance [ToFormat (Cmd P)] [ToFormat (MetaData P)]
    [ToFormat (List P.Ident)] [ToFormat (List P.Expr)] :
    ToFormat (CmdExt P) where
  format c := match c with
    | .cmd c => format c
    | .call lhs pname args md =>
      f!"{md}call " ++ (if lhs.isEmpty then f!"" else f!"{lhs} := ") ++
      f!"{pname}({args})"

---------------------------------------------------------------------

abbrev Statement := Imperative.Stmt Boogie.Expression Boogie.Command
abbrev Statements := List Statement

@[match_pattern]
abbrev Statement.init (name : Expression.Ident) (ty : Expression.Ty) (expr : Expression.Expr)
    (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.init name ty expr md))
@[match_pattern]
abbrev Statement.set (name : Expression.Ident) (expr : Expression.Expr)
    (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.set name expr md))
@[match_pattern]
abbrev Statement.havoc (name : Expression.Ident) (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.havoc name md))
@[match_pattern]
abbrev Statement.assert (label : String) (b : Expression.Expr) (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.assert label b md))
@[match_pattern]
abbrev Statement.assume (label : String) (b : Expression.Expr) (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.assume label b md))
@[match_pattern]
abbrev Statement.call (lhs : List Expression.Ident) (pname : String) (args : List Expression.Expr)
    (md : MetaData Expression := .empty) :=
  @Stmt.cmd Expression Command (CmdExt.call lhs pname args md)

---------------------------------------------------------------------

def Command.eraseTypes (c : Command) : Command :=
  match c with
  | .cmd c =>
    match c with
    | .init name ty e md => .cmd $ .init name ty e.eraseTypes md
    | .set name e md => .cmd $ .set name e.eraseTypes md
    | .havoc name md => .cmd $ .havoc name md
    | .assert label b md => .cmd $ .assert label b.eraseTypes md
    | .assume label b md => .cmd $ .assume label b.eraseTypes md
  | .call lhs pname args md =>
    .call lhs pname (args.map Lambda.LExpr.eraseTypes) md

mutual
def Statement.eraseTypes (s : Statement) : Statement :=
  match s with
  | .cmd c => .cmd (Command.eraseTypes c)
  | .block label { ss } md =>
    let ss' := Statements.eraseTypes ss
    .block label { ss := ss' } md
  | .ite cond thenb elseb md =>
    let thenb' := { ss := Statements.eraseTypes thenb.ss }
    let elseb' := { ss := Statements.eraseTypes elseb.ss }
    .ite cond thenb' elseb' md
  | .loop guard measure invariant body md =>
    let body' := { ss := Statements.eraseTypes body.ss }
    .loop guard measure invariant body' md
  | .goto l md => .goto l md
  termination_by (sizeOf s)
  decreasing_by
  all_goals simp_wf <;> simp [sizeOf] <;> omega

def Statements.eraseTypes (ss : Statements) : Statements :=
  match ss with
  | [] => []
  | s :: srest => Statement.eraseTypes s :: Statements.eraseTypes srest
  termination_by (sizeOf ss)
  decreasing_by all_goals simp [sizeOf] <;> omega
end

---------------------------------------------------------------------

def Command.getVars (c : Command) : List Expression.Ident :=
  match c with
  | .cmd c => c.getVars
  | .call _ _ args _ => args.flatMap HasVarsPure.getVars

instance : HasVarsPure Expression Command where
  getVars := Command.getVars

def Command.definedVars (c : Command) : List Expression.Ident :=
  match c with
  | .cmd c => c.definedVars
  | _ => []

def Command.modifiedVars (c : Command) : List Expression.Ident :=
  match c with
  | .cmd c => c.modifiedVars
  | .call lhs _ _ _ => lhs

def Command.touchedVars (c : Command) : List Expression.Ident :=
  Command.definedVars c ++ Command.modifiedVars c

instance : HasVarsImp Expression Command where
  definedVars := Command.definedVars
  modifiedVars := Command.modifiedVars
  touchedVars := Command.touchedVars

instance : HasVarsImp Expression Statement where
  definedVars := Stmt.definedVars
  modifiedVars := Stmt.modifiedVars
  touchedVars := Stmt.touchedVars

instance : HasVarsImp Expression (List Statement) where
  definedVars := Stmts.definedVars
  modifiedVars := Stmts.modifiedVars
  -- order matters for Havoc, so needs to override the default
  touchedVars := Stmts.touchedVars

---------------------------------------------------------------------

def Command.modifiedVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (c : Command)
  : List Expression.Ident := match c with
  | .cmd c => Cmd.modifiedVars (P:=Expression) c
  | .call lhs f _ _ => match π f with
    | some proc => lhs ++ HasVarsTrans.modifiedVarsTrans π proc
    | none => lhs -- TODO: throw error?

mutual
/-- Get all variables modified by the statement `s`. -/
def Statement.modifiedVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (s : Statement)
  : List Expression.Ident := match s with
  | .cmd cmd => Command.modifiedVarsTrans π cmd
  | .goto _ _ => []
  | .block _ b _ => Statements.modifiedVarsTrans π b.ss
  | .ite _ tb eb _ =>
    Statements.modifiedVarsTrans π tb.ss ++ Statements.modifiedVarsTrans π eb.ss
  | .loop _ _ _ b _ =>
    Statements.modifiedVarsTrans π b.ss
  termination_by (Stmt.sizeOf s)
  decreasing_by
  all_goals simp_wf
  cases tb; omega
  cases eb; omega

def Statements.modifiedVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (ss : List (Statement))
  : List Expression.Ident := match ss with
  | [] => []
  | s :: ss => Statement.modifiedVarsTrans π s ++ Statements.modifiedVarsTrans π ss
  termination_by (Stmts.sizeOf ss)
end

def Command.getVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (c : Command)
  : List Expression.Ident := match c with
  | .cmd c => Cmd.getVars (P:=Expression) c
  | .call lhs f args _ =>
    args.flatMap HasVarsPure.getVars ++
    match π f with
    | some proc => lhs ++ HasVarsTrans.getVarsTrans π proc
    | none => [] -- TODO: throw error?

mutual
/-- Get all variables get by the statement `s`. -/
def Statement.getVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (s : Statement)
  : List Expression.Ident := match s with
  | .cmd cmd => Command.getVarsTrans π cmd
  | .goto _ _ => []
  | .block _ b _ => Statements.getVarsTrans π b.ss
  | .ite _ tb eb _ =>
    Statements.getVarsTrans π tb.ss ++ Statements.getVarsTrans π eb.ss
  | .loop _ _ _ b _ =>
    Statements.getVarsTrans π b.ss
  termination_by (Stmt.sizeOf s)
  decreasing_by
  all_goals simp_wf
  cases tb; omega
  cases eb; omega

def Statements.getVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (ss : List (Statement))
  : List Expression.Ident := match ss with
  | [] => []
  | s :: ss => Statement.getVarsTrans π s ++ Statements.getVarsTrans π ss
  termination_by (Stmts.sizeOf ss)
end

-- don't need to transitively lookup for procedures
-- since call statement does not define any new variables
def Command.definedVarsTrans
  (_ : String → Option ProcType) (c : Command) :=
  Command.definedVars c

-- don't need to transitively lookup for procedures
-- since call statement does not define any new variables
def Statement.definedVarsTrans
  (_ : String → Option ProcType) (s : Statement) :=
  Stmt.definedVars s

-- don't need to transitively lookup for procedures
-- since call statement does not define any new variables
def Statements.definedVarsTrans
  (_ : String → Option ProcType) (s : Statements) :=
  Stmts.definedVars s

mutual
/-- get all variables touched by the statement `s`. -/
def Statement.touchedVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (s : Statement)
  : List Expression.Ident :=
  match s with
  | .cmd cmd => Command.definedVarsTrans π cmd ++ Command.modifiedVarsTrans π cmd
  | .goto _ _ => []
  | .block _ b _ => Statements.touchedVarsTrans π b.ss
  | .ite _ tb eb _ => Statements.touchedVarsTrans π tb.ss ++ Statements.touchedVarsTrans π eb.ss
  | .loop _ _ _ b _ => Statements.touchedVarsTrans π b.ss
  termination_by (Stmt.sizeOf s)
  decreasing_by
  all_goals simp_wf
  cases tb; omega
  cases eb; omega

def Statements.touchedVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (ss : Statements)
  : List Expression.Ident :=
  match ss with
  | [] => []
  | s :: srest => Statement.touchedVarsTrans π s ++ Statements.touchedVarsTrans π srest
  termination_by (Stmts.sizeOf ss)
end

def Statement.allVarsTrans
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (s : Statement) :=
  Statement.getVarsTrans π s ++ Statement.touchedVarsTrans π s

def Statements.allVarsTrans
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (ss : Statements) := match ss with
  | [] => []
  | s :: ss => Statement.allVarsTrans π s ++ Statements.allVarsTrans π ss

partial
def Statement.removeLoopsM (s : Boogie.Statement) : StateM Nat Boogie.Statement :=
  let incState : StateM Nat Unit := StateT.modifyGet (fun x => ((), x + 1))
  let trueExpr : Expression.Expr := .const "true" (some .bool)
  let intZero : Expression.Expr := .const "0" (some .int)
  match s with
  | .loop guard measure invariant body _ =>
    match measure, invariant with
    | .some measure, some invariant => do
      let loop_num ← StateT.get
      let neg_guard : Expression.Expr := .app boolNotOp guard
      let assigned_vars := (Stmts.modifiedVars body.ss).map (λ s => (Visibility.unres, s))
      let havocd : Statement :=
        .block s!"loop_havoc_{loop_num}" {ss:= assigned_vars.map (λ (_, n) => Statement.havoc n {})} {}
      let measure_pos :=
        .app (.app intGeOp measure) intZero
      let entry_invariant : Statement :=
        .assert s!"entry_invariant_{loop_num}" invariant {}
      let assert_measure_positive : Statement :=
        .assert s!"assert measure_pos_{loop_num}" measure_pos {}
      let first_iter_facts : Statement :=
        .block s!"first_iter_asserts_{loop_num}" {ss := [entry_invariant, assert_measure_positive]} {}
      let arbitrary_iter_assumes := .block s!"arbitrary_iter_assumes_{loop_num}" {
        ss := [(Statement.assume s!"assume_guard_{loop_num}" guard {}),
               (Statement.assume s!"assume_invariant_{loop_num}" invariant {}),
               (Statement.assume s!"assume_measure_pos_{loop_num}" measure_pos {})]} {}
      let measure_old_value_assign : Statement :=
        .init s!"special_name_for_old_measure_value_{loop_num}" (.forAll [] .int) measure {}
      let measure_decreases : Statement :=
        .assert s!"measure_decreases_{loop_num}" (.app (.app intLtOp measure) (.fvar s!"special_name_for_old_measure_value_{loop_num}" none)) {}
      let measure_imp_not_guard : Statement :=
        .assert s!"measure_imp_not_guard_{loop_num}" (.ite (.app (.app intLeOp measure) intZero) neg_guard trueExpr) {}
      let maintain_invariant : Statement :=
        .assert s!"arbitrary_iter_maintain_invariant_{loop_num}" invariant {}
      incState
      let body_statements ← body.ss.mapM removeLoopsM
      let arbitrary_iter_facts : Statement := .block s!"arbitrary_iter_facts_{loop_num}" {
        ss := [havocd, arbitrary_iter_assumes, measure_old_value_assign] ++
              body_statements ++
              [measure_decreases, measure_imp_not_guard, maintain_invariant]
      } {}
      let not_guard : Statement := .assume s!"not_guard_{loop_num}" neg_guard {}
      let invariant : Statement := .assume s!"invariant_{loop_num}" invariant {}

      pure (.ite guard {ss := [first_iter_facts, arbitrary_iter_facts, havocd, not_guard, invariant]} {ss := []} {})
    | _, _ => panic! s!"Loop elimination requires measure and invariant, got: {measure} {invariant}"
  | .ite c t e md => do
    incState
    let tss ← t.ss.mapM removeLoopsM
    incState
    let ess ← e.ss.mapM removeLoopsM
    pure (.ite c {ss := tss } {ss := ess } md)
  | .block label b md => do
    incState
    let bss ← b.ss.mapM removeLoopsM
    pure (.block label {ss := bss } md)
  | .cmd _ => pure s
  | .goto _ _ => pure s

def Statement.removeLoops (s : Boogie.Statement) : Boogie.Statement :=
  (StateT.run (removeLoopsM s) 0).fst

end Boogie
