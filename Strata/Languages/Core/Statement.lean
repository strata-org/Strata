/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Expressions
import Strata.DL.Imperative.PureExpr
import Strata.Languages.Core.Identifiers
import Strata.Languages.Core.Factory
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.HasVars
import Strata.DL.Lambda.LExpr
import Strata.Util.Tactics

namespace Core
open Imperative
open Std (ToFormat Format format)
open Std.Format

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
         (md : MetaData P)

/--
We parameterize Strata Core's Commands with Lambda dialect's expressions.
-/
abbrev Command := CmdExt Expression

instance : HasPassiveCmds Expression Command where
  assert l e md := .cmd (.assert l e md)
  assume l e md := .cmd (.assume l e md)

instance : HasHavoc Expression Command where
  havoc x md := .cmd (.havoc x md)

instance [ToFormat (Cmd P)] [ToFormat (MetaData P)]
    [ToFormat (List P.Ident)] [ToFormat P.Expr] :
    ToFormat (CmdExt P) where
  format c := match c with
    | .cmd c => format c
    | .call lhs pname args _md =>
      f!"call " ++ (if lhs.isEmpty then f!"" else f!"{lhs} := ") ++
      f!"{pname}({nestD <| group <| joinSep args ("," ++ line)})"

---------------------------------------------------------------------

abbrev Statement := Imperative.Stmt Core.Expression Core.Command
abbrev Statements := List Statement

@[match_pattern]
abbrev Statement.init (name : Expression.Ident) (ty : Expression.Ty) (expr : Option Expression.Expr)
    (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.init name ty expr md))
@[match_pattern]
abbrev Statement.set (name : Expression.Ident) (expr : Expression.Expr)
    (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.set name expr md))
@[match_pattern]
abbrev Statement.havoc (name : Expression.Ident) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.havoc name md))
@[match_pattern]
abbrev Statement.assert (label : String) (b : Expression.Expr) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.assert label b md))
@[match_pattern]
abbrev Statement.assume (label : String) (b : Expression.Expr) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.assume label b md))
@[match_pattern]
abbrev Statement.call (lhs : List Expression.Ident) (pname : String) (args : List Expression.Expr)
    (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.call lhs pname args md)
@[match_pattern]
abbrev Statement.cover (label : String) (b : Expression.Expr) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.cover label b md))

---------------------------------------------------------------------

abbrev Block := Imperative.Block Core.Expression Core.Command

---------------------------------------------------------------------

def Command.eraseTypes (c : Command) : Command :=
  match c with
  | .cmd c =>
    match c with
    | .init name ty e md => .cmd $ .init name ty (e.map Lambda.LExpr.eraseTypes) md
    | .set name e md => .cmd $ .set name e.eraseTypes md
    | .havoc name md => .cmd $ .havoc name md
    | .assert label b md => .cmd $ .assert label b.eraseTypes md
    | .assume label b md => .cmd $ .assume label b.eraseTypes md
    | .cover label b md => .cmd $ .cover label b.eraseTypes md
  | .call lhs pname args md =>
    .call lhs pname (args.map Lambda.LExpr.eraseTypes) md

mutual
def Statement.eraseTypes (s : Statement) : Statement :=
  match s with
  | .cmd c => .cmd (Command.eraseTypes c)
  | .block label bss md =>
    let ss' := Statements.eraseTypes bss
    .block label ss' md
  | .ite cond tss ess md =>
    let thenb' := Statements.eraseTypes tss
    let elseb' := Statements.eraseTypes ess
    .ite cond thenb' elseb' md
  | .loop guard measure invariant bss md =>
    let body' := Statements.eraseTypes bss
    .loop guard measure invariant body' md
  | .goto l md => .goto l md
  | .funcDecl decl md =>
    let decl' := { decl with
      body := decl.body.map Lambda.LExpr.eraseTypes,
      axioms := decl.axioms.map Lambda.LExpr.eraseTypes,
      preconditions := decl.preconditions.map fun p => { p with expr := p.expr.eraseTypes } }
    .funcDecl decl' md

def Statements.eraseTypes (ss : Statements) : Statements :=
  match ss with
  | [] => []
  | s :: srest => Statement.eraseTypes s :: Statements.eraseTypes srest
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
  definedVars := Block.definedVars
  modifiedVars := Block.modifiedVars
  -- order matters for Havoc, so needs to override the default
  touchedVars := Block.touchedVars

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
  | .block _ bss _ => Statements.modifiedVarsTrans π bss
  | .ite _ tbss ebss _ =>
    Statements.modifiedVarsTrans π tbss ++ Statements.modifiedVarsTrans π ebss
  | .loop _ _ _ bss _ =>
    Statements.modifiedVarsTrans π bss
  | .funcDecl _ _ => []  -- Function declarations don't modify variables

def Statements.modifiedVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (ss : List (Statement))
  : List Expression.Ident := match ss with
  | [] => []
  | s :: ss => Statement.modifiedVarsTrans π s ++ Statements.modifiedVarsTrans π ss
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
  | .block _ bss _ => Statements.getVarsTrans π bss
  | .ite _ tbss ebss _ =>
    Statements.getVarsTrans π tbss ++ Statements.getVarsTrans π ebss
  | .loop _ _ _ bss  _ =>
    Statements.getVarsTrans π bss
  | .funcDecl decl _ =>
    -- Get free variables from function body, excluding formal parameters
    match decl.body with
    | none => []
    | some body =>
      let bodyVars := HasVarsPure.getVars body
      let formals := decl.inputs.map (·.1)
      bodyVars.filter (fun v => formals.all (fun f => v.name != f.name))

def Statements.getVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (ss : List (Statement))
  : List Expression.Ident := match ss with
  | [] => []
  | s :: ss => Statement.getVarsTrans π s ++ Statements.getVarsTrans π ss
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
  Block.definedVars s

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
  | .block _ bss _ => Statements.touchedVarsTrans π bss
  | .ite _ tbss ebss _ => Statements.touchedVarsTrans π tbss ++ Statements.touchedVarsTrans π ebss
  | .loop _ _ _ bss _ => Statements.touchedVarsTrans π bss
  | .funcDecl decl _ => [decl.name]  -- Function declaration touches (defines) the function name

def Statements.touchedVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (ss : Statements)
  : List Expression.Ident :=
  match ss with
  | [] => []
  | s :: srest => Statement.touchedVarsTrans π s ++ Statements.touchedVarsTrans π srest
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

---------------------------------------------------------------------

mutual
def Block.substFvar (b : Block) (fr:Expression.Ident)
      (to:Expression.Expr) : Block :=
  List.map (fun s => Statement.substFvar s fr to) b

def Statement.substFvar (s : Core.Statement)
      (fr:Expression.Ident)
      (to:Expression.Expr) : Statement :=
  match s with
  | .init lhs ty rhs metadata =>
    .init lhs ty (rhs.map (Lambda.LExpr.substFvar · fr to)) metadata
  | .set lhs rhs metadata =>
    .set lhs (Lambda.LExpr.substFvar rhs fr to) metadata
  | .havoc _ _ => s
  | .assert lbl b metadata =>
    .assert lbl (Lambda.LExpr.substFvar b fr to) metadata
  | .assume lbl b metadata =>
    .assume lbl (Lambda.LExpr.substFvar b fr to) metadata
  | .cover lbl b metadata =>
    .cover lbl (Lambda.LExpr.substFvar b fr to) metadata
  | .call lhs pname args metadata =>
    .call lhs pname (List.map (Lambda.LExpr.substFvar · fr to) args) metadata

  | .block lbl b metadata =>
    .block lbl (Block.substFvar b fr to) metadata
  | .ite cond thenb elseb metadata =>
    .ite (Lambda.LExpr.substFvar cond fr to) (Block.substFvar thenb fr to)
          (Block.substFvar elseb fr to) metadata
  | .loop guard measure invariant body metadata =>
    .loop (Lambda.LExpr.substFvar guard fr to)
          (Option.map (Lambda.LExpr.substFvar · fr to) measure)
          (invariant.map (Lambda.LExpr.substFvar · fr to))
          (Block.substFvar body fr to)
          metadata
  | .goto _ _ => s
  | .funcDecl decl md =>
    -- Substitute in function body and axioms
    let decl' := { decl with
      body := decl.body.map (Lambda.LExpr.substFvar · fr to),
      axioms := decl.axioms.map (Lambda.LExpr.substFvar · fr to) }
    .funcDecl decl' md
end

---------------------------------------------------------------------

mutual
def Block.renameLhs (b : Block)
    (fr: Lambda.Identifier Visibility) (to: Lambda.Identifier Visibility) : Block :=
  List.map (fun s => Statement.renameLhs s fr to) b

def Statement.renameLhs (s : Core.Statement)
    (fr: Lambda.Identifier Visibility) (to: Lambda.Identifier Visibility)
    : Statement :=
  match s with
  | .init lhs ty rhs metadata =>
    .init (if lhs.name == fr then to else lhs) ty rhs metadata
  | .set lhs rhs metadata =>
    .set (if lhs.name == fr then to else lhs) rhs metadata
  | .call lhs pname args metadata =>
    .call (lhs.map (fun l =>
      if l.name == fr  then to else l)) pname args metadata
  | .block lbl b metadata =>
    .block lbl (Block.renameLhs b fr to) metadata
  | .ite x thenb elseb m =>
    .ite x (Block.renameLhs thenb fr to) (Block.renameLhs elseb fr to) m
  | .loop m g i b md =>
    .loop m g i (Block.renameLhs b fr to) md
  | .havoc l md => .havoc (if l.name == fr then to else l) md
  | .funcDecl decl md =>
    -- Rename function name if it matches
    let decl' := if decl.name == fr then { decl with name := to } else decl
    .funcDecl decl' md
  | .assert _ _ _ | .assume _ _ _ | .cover _ _ _ | .goto _ _ => s
end

---------------------------------------------------------------------


end Core
