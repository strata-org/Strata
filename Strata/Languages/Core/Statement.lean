/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Expressions
public import Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Stmt
import Std.Tactic.BVDecide.Normalize.Prop

namespace Core
open Imperative
open Std (ToFormat Format format)
open Std.Format

public section

---------------------------------------------------------------------

/--
A call argument is either an input expression, an in-out variable, or an
output variable.
-/
inductive CallArg (P : PureExpr) where
  /-- An input argument: a by-value expression. -/
  | inArg (e : P.Expr)
  /-- An input-output argument: a mutable variable passed by reference. -/
  | inoutArg (id : P.Ident)
  /-- An output-only argument: a variable whose final value is returned to the caller. -/
  | outArg (id : P.Ident)

/--
Extend Imperative's commands by adding a procedure call.
-/
@[grind] def CallArg.beq [BEq P.Expr] [BEq P.Ident] (a b : CallArg P) : Bool :=
  match a, b with
  | .inArg e1, .inArg e2 => e1 == e2
  | .inoutArg id1, .inoutArg id2 => id1 == id2
  | .outArg id1, .outArg id2 => id1 == id2
  | _, _ => false

instance [BEq P.Expr] [BEq P.Ident] : BEq (CallArg P) where
  beq := CallArg.beq

theorem CallArg.beq_eq {P : PureExpr} [DecidableEq P.Expr] [DecidableEq P.Ident]
    (a b : CallArg P) : CallArg.beq a b = true ↔ a = b := by
  solve_beq a b

instance [DecidableEq P.Expr] [DecidableEq P.Ident] : DecidableEq (CallArg P) :=
  beq_eq_DecidableEq CallArg.beq CallArg.beq_eq

instance [DecidableEq P.Expr] [DecidableEq P.Ident] : LawfulBEq (CallArg P) where
  eq_of_beq h := (CallArg.beq_eq _ _).mp h
  rfl := (CallArg.beq_eq _ _).mpr rfl

/--
Extend Imperative's commands by adding a procedure call.
-/
inductive CmdExt (P : PureExpr) where
  /-- A standard imperative command. -/
  | cmd (c : Imperative.Cmd P)
  /-- A procedure call with the given name and arguments. -/
  | call (procName : String) (args : List (CallArg P))
         (md : MetaData P)

@[grind] def CmdExt.beq [BEq P.Ident] [BEq P.Ty] [BEq P.Expr] [BEq (MetaData P)]
    (a b : CmdExt P) : Bool :=
  match a, b with
  | .cmd c1, .cmd c2 => c1 == c2
  | .call n1 args1 md1, .call n2 args2 md2 => n1 == n2 && args1 == args2 && md1 == md2
  | _, _ => false

instance [BEq P.Ident] [BEq P.Ty] [BEq P.Expr] [BEq (MetaData P)] : BEq (CmdExt P) where
  beq := CmdExt.beq

theorem CmdExt.beq_eq {P : PureExpr} [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr]
    (a b : CmdExt P) : CmdExt.beq a b = true ↔ a = b := by
  solve_beq a b

instance [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr] : DecidableEq (CmdExt P) :=
  beq_eq_DecidableEq CmdExt.beq CmdExt.beq_eq

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
  -- `getInputExprs` emits a slot for each `inoutArg` too; consume it (keeping
  -- the id) so the cursor stays aligned with the `inArg` positions.
  | .inoutArg id :: rest, _ :: es => .inoutArg id :: go rest es
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
    | .inoutArg _, e :: es => simp [replaceInArgs.go, ih]
    | .inoutArg _, [] => simp [replaceInArgs.go, ih]
    | .outArg _, es => simp [replaceInArgs.go, ih]

def getInputExprs (args : List (CallArg Expression)) : List Expression.Expr :=
  args.filterMap fun
    | .inArg e => some e
    | .inoutArg id => some (Lambda.LExpr.fvar () id none)
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

mutual
/--
Collect the `AssertId Expression` of every reachable assertion in `s`:
`.assert` commands and each entry of a `.loop`'s invariant list. Mirrors
the shape of `coreIsAtAssert`.

NOTE: Once loop invariant is dropped from coreIsAtAssert, this will be a simple
filtering of .assert commands.
-/
def Statement.collectAssertIds (s : Statement) : List (Imperative.AssertId Expression) :=
  match s with
  | .cmd (.cmd (.assert label expr _)) => [⟨label, expr⟩]
  | .cmd _ => []
  | .block _ inner_ss _ => Statements.collectAssertIds inner_ss
  | .ite _ then_ss else_ss _ =>
    Statements.collectAssertIds then_ss ++ Statements.collectAssertIds else_ss
  | .loop _ _ inv body_ss _ =>
    inv.map (fun lp => ⟨lp.1, lp.2⟩) ++ Statements.collectAssertIds body_ss
  | .funcDecl _ _ | .exit _ _ | .typeDecl _ _ => []
  termination_by Imperative.Stmt.sizeOf s

/-- Collect all `AssertId Expression`s in a list of statements. -/
def Statements.collectAssertIds (ss : Statements) : List (Imperative.AssertId Expression) :=
  match ss with
  | [] => []
  | s :: ss => Statement.collectAssertIds s ++ Statements.collectAssertIds ss
  termination_by Imperative.Block.sizeOf ss
end

---------------------------------------------------------------------

@[expose] def Command.getVars (c : Command) : List Expression.Ident :=
  match c with
  | .cmd c => c.getVars
  | .call _ args _ => (CallArg.getInputExprs args).flatMap HasFvars.getFvars

@[expose] def Command.getOps (c : Command) : List Expression.Ident :=
  match c with
  | .cmd c => Cmd.getOps c
  | .call _ args _ => (CallArg.getInputExprs args).flatMap HasOps.getOps

instance : HasOpsImp Expression Command where
  getOps := Command.getOps

@[expose] def Command.definedVars (c : Command) : List Expression.Ident :=
  match c with
  | .cmd c => c.definedVars
  | _ => []

@[expose] def Command.modifiedVars (c : Command) : List Expression.Ident :=
  match c with
  | .cmd c => c.modifiedVars
  | .call _ args _ => CallArg.getLhs args

def Command.modifiedOrDefinedVars (c : Command) : List Expression.Ident :=
  Command.definedVars c ++ Command.modifiedVars c

instance : HasVarsImp Expression Command where
  definedVars c _ := Command.definedVars c
  modifiedVars := Command.modifiedVars
  readVars := Command.getVars

instance : HasVarsImp Expression Statement where
  definedVars := Stmt.definedVars
  modifiedVars := Stmt.modifiedVars
  readVars := Stmt.getVars

instance : HasVarsImp Expression (List Statement) where
  definedVars := Block.definedVars
  modifiedVars := Block.modifiedVars
  readVars := Block.getVars

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
    (CallArg.getInputExprs args).flatMap HasFvars.getFvars ++
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
      let bodyVars := HasFvars.getFvars body
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
  Stmt.definedVars s false

-- don't need to transitively lookup for procedures
-- since call statement does not define any new variables
def Statements.definedVarsTrans
  (_ : String → Option ProcType) (s : Statements) :=
  Block.definedVars s false

mutual
/-- get all variables modified or defined by the statement `s` (write-set, transitive). -/
def Statement.modifiedOrDefinedVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (s : Statement)
  : List Expression.Ident :=
  match s with
  | .cmd cmd => Command.definedVarsTrans π cmd ++ Command.modifiedVarsTrans π cmd
  | .exit _ _ => []
  | .block _ bss _ => Statements.modifiedOrDefinedVarsTrans π bss
  | .ite _ tbss ebss _ => Statements.modifiedOrDefinedVarsTrans π tbss ++ Statements.modifiedOrDefinedVarsTrans π ebss
  | .loop _ _ _ bss _ => Statements.modifiedOrDefinedVarsTrans π bss
  | .funcDecl decl _ => [decl.name]  -- Function declaration touches (defines) the function name
  | .typeDecl _ _ => []  -- Type declarations don't touch variables

def Statements.modifiedOrDefinedVarsTrans
  {ProcType : Type}
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (ss : Statements)
  : List Expression.Ident :=
  match ss with
  | [] => []
  | s :: srest => Statement.modifiedOrDefinedVarsTrans π s ++ Statements.modifiedOrDefinedVarsTrans π srest
end

def Statement.allVarsTrans
  [HasVarsProcTrans Expression ProcType]
  (π : String → Option ProcType) (s : Statement) :=
  Statement.getVarsTrans π s ++ Statement.modifiedOrDefinedVarsTrans π s

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
          (measure.map (Lambda.LExpr.substFvar · fr to))
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

/-- Apply a function to all user-facing expressions in a Core command. -/
def Command.mapExpr (f : Expression.Expr → Expression.Expr) : Command → Command
  | .cmd (.assert l e md) => .cmd (.assert l (f e) md)
  | .cmd (.assume l e md) => .cmd (.assume l (f e) md)
  | .cmd (.cover l e md) => .cmd (.cover l (f e) md)
  | .cmd (.init n ty (.det e) md) => .cmd (.init n ty (.det (f e)) md)
  | .cmd (.set n (.det e) md) => .cmd (.set n (.det (f e)) md)
  | .call pname args md => .call pname (args.map fun
      | .inArg e => .inArg (f e)
      | a => a) md
  | c => c

/-- Apply a function to all user-facing expressions in a statement. -/
def Statement.mapExprs (f : Expression.Expr → Expression.Expr) (s : Statement) : Statement :=
  Imperative.Stmt.mapExpr f (Command.mapExpr f) s

/-- Apply a function to all user-facing expressions in a list of statements. -/
def Statements.mapExprs (f : Expression.Expr → Expression.Expr)
    (ss : Statements) : Statements :=
  ss.map (Statement.mapExprs f)

def Command.mapExprM {M : Type → Type} [Monad M] (f : Expression.Expr → M Expression.Expr) :
    Command → M Command
  | .cmd (.assert l e md) => do return .cmd (.assert l (← f e) md)
  | .cmd (.assume l e md) => do return .cmd (.assume l (← f e) md)
  | .cmd (.cover l e md) => do return .cmd (.cover l (← f e) md)
  | .cmd (.init n ty (.det e) md) => do return .cmd (.init n ty (.det (← f e)) md)
  | .cmd (.set n (.det e) md) => do return .cmd (.set n (.det (← f e)) md)
  | .call pname args md => do
    return .call pname (← args.mapM fun
      | .inArg e => do return .inArg (← f e)
      | a => pure a) md
  | c => pure c

def Statement.mapExprsM {M : Type → Type} [Monad M] (f : Expression.Expr → M Expression.Expr)
    (s : Statement) : M Statement :=
  Imperative.Stmt.mapExprM f (Command.mapExprM f) s

def Statements.mapExprsM {M : Type → Type} [Monad M] (f : Expression.Expr → M Expression.Expr)
    (ss : Statements) : M Statements :=
  ss.mapM (Statement.mapExprsM f)

/-- Collect all user-facing expressions from a statement. With
    `visitFuncDecl`, the expressions of the functions it declares are collected
    too; without it, a `funcDecl` contributes nothing, which is what a caller
    rewriting expressions in place needs, since a local function's body mentions
    its formals. -/
def Statement.collectExprs (visitFuncDecl : Bool) :
    Statement → List Expression.Expr
  | .cmd (.cmd (.assert _ e _)) => [e]
  | .cmd (.cmd (.assume _ e _)) => [e]
  | .cmd (.cmd (.cover _ e _)) => [e]
  | .cmd (.cmd (.init _ _ (.det e) _)) => [e]
  | .cmd (.cmd (.set _ (.det e) _)) => [e]
  | .cmd (.call _ args _) => args.filterMap fun
      | .inArg e => some e
      | _ => none
  | .block _ ss _ => ss.flatMap (Statement.collectExprs visitFuncDecl)
  | .ite (.det c) tss ess _ =>
    [c] ++ tss.flatMap (Statement.collectExprs visitFuncDecl) ++
    ess.flatMap (Statement.collectExprs visitFuncDecl)
  | .ite .nondet tss ess _ =>
    tss.flatMap (Statement.collectExprs visitFuncDecl) ++
    ess.flatMap (Statement.collectExprs visitFuncDecl)
  | .loop (.det g) measure inv body _ =>
    [g] ++ measure.toList ++
    inv.map Prod.snd ++ body.flatMap (Statement.collectExprs visitFuncDecl)
  | .loop .nondet measure inv body _ =>
    measure.toList ++
    inv.map Prod.snd ++ body.flatMap (Statement.collectExprs visitFuncDecl)
  | .cmd (.cmd (.init _ _ .nondet _)) => []
  | .cmd (.cmd (.set _ .nondet _)) => []
  | .exit _ _ => []
  | .funcDecl d _ => if visitFuncDecl then d.exprs else []
  | .typeDecl _ _ => []

/-- Collect all user-facing expressions from a list of statements. -/
def Statements.collectExprs (ss : Statements)
    (visitFuncDecl : Bool := false) : List Expression.Expr :=
  ss.flatMap (Statement.collectExprs visitFuncDecl)

---------------------------------------------------------------------

/-! ## Statement shapes

Predicates on a single statement's own form. Nesting is
`Imperative.Block.allSubstmts`' business, so each of these is a match with no
recursion of its own. The predicates that inspect only guards, invariants and
measures are command-independent and live in `Imperative.Stmt`, which Core uses
directly; what is left here is what genuinely mentions a Core command. -/

/-- Not a procedure call. -/
@[expose] def Statement.isNotCall (s : Statement) : Bool :=
  match s with
  | .cmd (.call ..) => false
  | _ => true

/-- Does `ss` make no procedure call, at any nesting depth? -/
@[expose] def Statements.noCalls (ss : Statements) : Bool :=
  Imperative.Block.allSubstmts Statement.isNotCall ss

/-- Not an overwrite: `init` introduces a variable, `set` re-assigns one.
    `havoc` is a `set` to a nondeterministic value, so it is an overwrite
    too; an `init` to a nondeterministic value is not. -/
@[expose] def Statement.isNotReassignment (s : Statement) : Bool :=
  match s with
  | .cmd (.cmd (.set ..)) => false
  | _ => true

/-- Does every variable in `ss` get its value once, at `init`? -/
@[expose] def Statements.staticSingleAssignment (ss : Statements) : Bool :=
  Imperative.Block.allSubstmts Statement.isNotReassignment ss

/-- Is this statement anything other than a function declaration? -/
@[expose] def Statement.isNotFuncDecl (s : Statement) : Bool :=
  match s with
  | .funcDecl _ _ => false
  | _ => true

/-- Does `ss` declare no function inside a procedure body? -/
@[expose] def Statements.noFuncDecls (ss : Statements) : Bool :=
  Imperative.Block.allSubstmts Statement.isNotFuncDecl ss

/-- Is the function this statement declares, if any, monomorphic? -/
@[expose] def Statement.funcDeclMonomorphic (s : Statement) : Bool :=
  match s with
  | .funcDecl d _ => d.typeArgs.isEmpty
  | _ => true

/-- Is every function declared anywhere in `ss` monomorphic? -/
@[expose] def Statements.funcDeclsMonomorphic (ss : Statements) : Bool :=
  Imperative.Block.allSubstmts Statement.funcDeclMonomorphic ss

/-- Does the function this statement declares, if any, carry no precondition?
    A precondition on a partial function is a proof obligation, and nothing
    downstream of `PrecondElim` generates one. -/
@[expose] def Statement.funcDeclNoPreconditions (s : Statement) : Bool :=
  match s with
  | .funcDecl d _ => d.preconditions.isEmpty
  | _ => true

/-- Does no function declared anywhere in `ss` carry a precondition? -/
@[expose] def Statements.funcDeclsNoPreconditions (ss : Statements) : Bool :=
  Imperative.Block.allSubstmts Statement.funcDeclNoPreconditions ss

---------------------------------------------------------------------

/-! ## Expressions of local functions

`Statement.collectExprs` visits a `funcDecl`'s expressions only when asked, so a
property of *every* expression in a program passes `visitFuncDecl := true`, while
a caller rewriting expressions in place leaves them alone — a local function's
body mentions its formals. -/

/-- Every expression in `ss`, including those of the functions it declares. -/
@[expose] def Statements.allExprs (ss : Statements) : List Expression.Expr :=
  Statements.collectExprs ss (visitFuncDecl := true)

---------------------------------------------------------------------


end
end Core
