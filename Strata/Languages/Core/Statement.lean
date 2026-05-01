/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Expressions
public import Strata.DL.Imperative.PureExpr
public import Strata.Languages.Core.Identifiers
public import Strata.Languages.Core.Factory
public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.HasVars
public import Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.TypeConstructor
import Strata.Util.Tactics

namespace Core
open Imperative
open Std (ToFormat Format format)
open Std.Format

-- nosourcerange-file: typeclass defaults and operator constructors use ExprSourceLoc.none
-- because they build expressions programmatically, not from parsed source.

public section

---------------------------------------------------------------------

/--
A call argument is either an input expression, an in-out variable, or an
output variable.
-/
inductive CallArg (P : PureExpr) where
  | inArg (e : P.Expr)
  | inoutArg (id : P.Ident)
  | outArg (id : P.Ident)

/--
Extend Imperative's commands by adding a procedure call.
-/
inductive CmdExt (P : PureExpr) where
  | cmd (c : Imperative.Cmd P)
  | call (procName : String) (args : List (CallArg P))
         (md : MetaData P)

/--
We parameterize Strata Core's Commands with Lambda dialect's expressions.
-/
@[expose]
abbrev Command := CmdExt Expression

instance : HasPassiveCmds Expression Command where
  assert l e md := .cmd (.assert l e md)
  assume l e md := .cmd (.assume l e md)

instance : HasHavoc Expression Command where
  havoc x md := .cmd (.set x .nondet md)

instance : HasInit Expression Command where
  init x ty e md := .cmd (.init x ty e md)

namespace CallArg

def getInArgs (args : List (CallArg P)) : List P.Expr :=
  args.filterMap fun | .inArg e => some e | _ => none

def getInoutArgs (args : List (CallArg P)) : List P.Ident :=
  args.filterMap fun | .inoutArg id => some id | _ => none

def getOutArgs (args : List (CallArg P)) : List P.Ident :=
  args.filterMap fun | .outArg id => some id | _ => none

def getLhs (args : List (CallArg P)) : List P.Ident :=
  args.filterMap fun | .inoutArg id | .outArg id => some id | _ => none

def getOutOnly (args : List (CallArg P)) : List P.Ident :=
  args.filterMap fun | .outArg id => some id | _ => none

def replaceInArgs (args : List (CallArg P)) (newExprs : List P.Expr) : List (CallArg P) :=
  go args newExprs
where
  go : List (CallArg P) → List P.Expr → List (CallArg P)
  | [], _ => []
  | .inArg _ :: rest, e :: es => .inArg e :: go rest es
  | .inArg e :: rest, [] => .inArg e :: go rest []
  | a :: rest, es => a :: go rest es

theorem replaceInArgs_length (args : List (CallArg P)) (newExprs : List P.Expr) :
    (replaceInArgs args newExprs).length = args.length := by
  simp [replaceInArgs]
  suffices ∀ es, (replaceInArgs.go args es).length = args.length from this newExprs
  induction args with
  | nil => simp [replaceInArgs.go]
  | cons a rest ih =>
    intro es
    match a, es with
    | .inArg _, e :: es => simp [replaceInArgs.go, ih]
    | .inArg _, [] => simp [replaceInArgs.go, ih]
    | .inoutArg _, es => simp [replaceInArgs.go, ih]
    | .outArg _, es => simp [replaceInArgs.go, ih]

def getInputExprs (args : List (CallArg Expression)) : List Expression.Expr :=
  args.filterMap fun
    | .inArg e => some e
    -- Synthesized variable reference from an identifier; no source location available
    | .inoutArg id => some (Lambda.LExpr.fvar ExprSourceLoc.none id none)
    | .outArg _ => none

end CallArg
---------------------------------------------------------------------

@[expose]
abbrev Statement := Imperative.Stmt Core.Expression Core.Command
@[expose]
abbrev Statements := List Statement

@[expose, match_pattern]
abbrev Statement.init (name : Expression.Ident) (ty : Expression.Ty) (expr : ExprOrNondet Expression)
    (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.init name ty expr md))
@[expose, match_pattern]
abbrev Statement.set (name : Expression.Ident) (expr : Expression.Expr)
    (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.set name (.det expr) md))
@[expose, match_pattern]
abbrev Statement.havoc (name : Expression.Ident) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.set name .nondet md))
@[expose, match_pattern]
abbrev Statement.assert (label : String) (b : Expression.Expr) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.assert label b md))
@[expose, match_pattern]
abbrev Statement.assume (label : String) (b : Expression.Expr) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.assume label b md))
@[expose, match_pattern]
abbrev Statement.call (pname : String) (args : List (CallArg Expression))
    (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.call pname args md)
@[expose, match_pattern]
abbrev Statement.cover (label : String) (b : Expression.Expr) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.cover label b md))
@[expose, match_pattern]
abbrev Statement.typeDecl (tc : TypeConstructor) (md : MetaData Expression) :=
  @Stmt.typeDecl Expression Command tc md

---------------------------------------------------------------------

@[expose]
abbrev Block := Imperative.Block Core.Expression Core.Command

---------------------------------------------------------------------

def Command.eraseTypes (c : Command) : Command :=
  match c with
  | .cmd c =>
    match c with
    | .init name ty e md => .cmd $ .init name ty (e.map Lambda.LExpr.eraseTypes) md
    | .set name e md => .cmd $ .set name (e.map Lambda.LExpr.eraseTypes) md
    | .assert label b md => .cmd $ .assert label b.eraseTypes md
    | .assume label b md => .cmd $ .assume label b.eraseTypes md
    | .cover label b md => .cmd $ .cover label b.eraseTypes md
  | .call pname args md =>
    .call pname (args.map fun
      | .inArg e => .inArg (Lambda.LExpr.eraseTypes e)
      | .inoutArg id => .inoutArg id
      | .outArg id => .outArg id) md

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
  | .exit l md => .exit l md
  | .funcDecl decl md =>
    let decl' := { decl with
      body := decl.body.map Lambda.LExpr.eraseTypes,
      axioms := decl.axioms.map Lambda.LExpr.eraseTypes,
      preconditions := decl.preconditions.map fun p => { p with expr := p.expr.eraseTypes } }
    .funcDecl decl' md
  | .typeDecl tc md => .typeDecl tc md

def Statements.eraseTypes (ss : Statements) : Statements :=
  match ss with
  | [] => []
  | s :: srest => Statement.eraseTypes s :: Statements.eraseTypes srest
end

---------------------------------------------------------------------

def Command.getVars (c : Command) : List Expression.Ident :=
  match c with
  | .cmd c => c.getVars
  | .call _ args _ => (CallArg.getInputExprs args).flatMap HasVarsPure.getVars

instance : HasVarsPure Expression Command where
  getVars := Command.getVars

def Command.definedVars (c : Command) : List Expression.Ident :=
  match c with
  | .cmd c => c.definedVars
  | _ => []

def Command.modifiedVars (c : Command) : List Expression.Ident :=
  match c with
  | .cmd c => c.modifiedVars
  | .call _ args _ => CallArg.getLhs args

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
  | .call f args _ =>
    let lhs := CallArg.getLhs args
    match π f with
    | some proc => lhs ++ HasVarsTrans.modifiedVarsTrans π proc
    | none => lhs

mutual
/-- Get all variables modified by the statement `s`. -/
def Statement.modifiedVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (s : Statement)
  : List Expression.Ident := match s with
  | .cmd cmd => Command.modifiedVarsTrans π cmd
  | .exit _ _ => []
  | .block _ bss _ => Statements.modifiedVarsTrans π bss
  | .ite _ tbss ebss _ =>
    Statements.modifiedVarsTrans π tbss ++ Statements.modifiedVarsTrans π ebss
  | .loop _ _ _ bss _ =>
    Statements.modifiedVarsTrans π bss
  | .funcDecl _ _ => []  -- Function declarations don't modify variables
  | .typeDecl _ _ => []  -- Type declarations don't modify variables

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
  | .call f args _ =>
    let lhs := CallArg.getLhs args
    (CallArg.getInputExprs args).flatMap HasVarsPure.getVars ++
    match π f with
    | some proc => lhs ++ HasVarsTrans.getVarsTrans π proc
    | none => []

mutual
/-- Get all variables get by the statement `s`. -/
def Statement.getVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (s : Statement)
  : List Expression.Ident := match s with
  | .cmd cmd => Command.getVarsTrans π cmd
  | .exit _ _ => []
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
  | .typeDecl _ _ => []  -- Type declarations don't reference variables

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
  | .exit _ _ => []
  | .block _ bss _ => Statements.touchedVarsTrans π bss
  | .ite _ tbss ebss _ => Statements.touchedVarsTrans π tbss ++ Statements.touchedVarsTrans π ebss
  | .loop _ _ _ bss _ => Statements.touchedVarsTrans π bss
  | .funcDecl decl _ => [decl.name]  -- Function declaration touches (defines) the function name
  | .typeDecl _ _ => []  -- Type declarations don't touch variables

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
  | .init lhs ty e metadata =>
    .init lhs ty (e.map (Lambda.LExpr.substFvar · fr to)) metadata
  | .set lhs rhs metadata =>
    .set lhs (Lambda.LExpr.substFvar rhs fr to) metadata
  | .havoc _ _ => s
  | .assert lbl b metadata =>
    .assert lbl (Lambda.LExpr.substFvar b fr to) metadata
  | .assume lbl b metadata =>
    .assume lbl (Lambda.LExpr.substFvar b fr to) metadata
  | .cover lbl b metadata =>
    .cover lbl (Lambda.LExpr.substFvar b fr to) metadata
  | .call pname args metadata =>
    .call pname (args.map fun
      | .inArg e => .inArg (Lambda.LExpr.substFvar e fr to)
      | .inoutArg id => .inoutArg id
      | .outArg id => .outArg id) metadata

  | .block lbl b metadata =>
    .block lbl (Block.substFvar b fr to) metadata
  | .ite cond thenb elseb metadata =>
    .ite (cond.map (Lambda.LExpr.substFvar · fr to)) (Block.substFvar thenb fr to)
          (Block.substFvar elseb fr to) metadata
  | .loop guard measure invariant body metadata =>
    .loop (guard.map (Lambda.LExpr.substFvar · fr to))
          (Option.map (Lambda.LExpr.substFvar · fr to) measure)
          (invariant.map (fun (l, e) => (l, Lambda.LExpr.substFvar e fr to)))
          (Block.substFvar body fr to)
          metadata
  | .exit _ _ => s
  | .funcDecl decl md =>
    -- Substitute in function body and axioms
    let decl' := { decl with
      body := decl.body.map (Lambda.LExpr.substFvar · fr to),
      axioms := decl.axioms.map (Lambda.LExpr.substFvar · fr to) }
    .funcDecl decl' md
  | .typeDecl _ _ => s  -- Type declarations don't contain expressions
end

---------------------------------------------------------------------

mutual
def Block.renameLhs (b : Block)
    (fr: CoreIdent) (to: CoreIdent) : Block :=
  List.map (fun s => Statement.renameLhs s fr to) b

def Statement.renameLhs (s : Core.Statement)
    (fr: CoreIdent) (to: CoreIdent)
    : Statement :=
  match s with
  | .init lhs ty rhs metadata =>
    .init (if lhs.name == fr then to else lhs) ty rhs metadata
  | .set lhs rhs metadata =>
    .set (if lhs.name == fr then to else lhs) rhs metadata
  | .call pname args metadata =>
    .call pname (args.map fun
      | .inArg e => .inArg e
      | .inoutArg l => .inoutArg (if l.name == fr then to else l)
      | .outArg l => .outArg (if l.name == fr then to else l)) metadata
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
  | .typeDecl _ _ => s  -- Type declarations don't have lhs variables
  | .assert _ _ _ | .assume _ _ _ | .cover _ _ _ | .exit _ _ => s
end

---------------------------------------------------------------------


end
end Core
