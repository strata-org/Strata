/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Expressions
public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.CmdCallFormals
import all Strata.DL.Imperative.Stmt
import Std.Tactic.BVDecide.Normalize.Prop

namespace Core
open Imperative
open Std (ToFormat Format format)
open Std.Format

public section

---------------------------------------------------------------------

/--
We parameterize Strata Core's Commands with Lambda dialect's expressions.
-/
abbrev Command := CmdExt Expression

namespace CallArg

/-- The expressions passed at a call: each `inArg`, plus a variable reference
    for every `inoutArg`.  The generic `Calls.getInputExprs` at `Expression`. -/
abbrev getInputExprs (args : List (CallArg Expression)) : List Expression.Expr :=
  Calls.getInputExprs args

end CallArg
---------------------------------------------------------------------

abbrev Statement := Imperative.Stmt Core.Expression Core.Command
abbrev Statements := List Statement

@[match_pattern]
abbrev Statement.init (name : Expression.Ident) (ty : Expression.Ty) (expr : ExprOrNondet Expression)
    (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.init name ty expr md))
@[match_pattern]
abbrev Statement.set (name : Expression.Ident) (expr : Expression.Expr)
    (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.set name (.det expr) md))
@[match_pattern]
abbrev Statement.havoc (name : Expression.Ident) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.set name .nondet md))
@[match_pattern]
abbrev Statement.assert (label : String) (b : Expression.Expr) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.assert label b md))
@[match_pattern]
abbrev Statement.assume (label : String) (b : Expression.Expr) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.assume label b md))
@[match_pattern]
abbrev Statement.call (pname : String) (args : List (CallArg Expression))
    (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.call pname args md)
@[match_pattern]
abbrev Statement.cover (label : String) (b : Expression.Expr) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.cmd (Cmd.cover label b md))
@[match_pattern]
abbrev Statement.typeDecl (tc : TypeConstructor) (md : MetaData Expression) :=
  @Stmt.typeDecl Expression Command tc md

---------------------------------------------------------------------

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
  | .exit _ _ | .typeDecl _ _ => []
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

/-- Collect all user-facing expressions from a statement. -/
def Statement.collectExprs :
    Statement → List Expression.Expr
  | .cmd (.cmd (.assert _ e _)) => [e]
  | .cmd (.cmd (.assume _ e _)) => [e]
  | .cmd (.cmd (.cover _ e _)) => [e]
  | .cmd (.cmd (.init _ _ (.det e) _)) => [e]
  | .cmd (.cmd (.set _ (.det e) _)) => [e]
  | .cmd (.call _ args _) => args.filterMap fun
      | .inArg e => some e
      | _ => none
  | .block _ ss _ => ss.flatMap Statement.collectExprs
  | .ite (.det c) tss ess _ =>
    [c] ++ tss.flatMap Statement.collectExprs ++
    ess.flatMap Statement.collectExprs
  | .ite .nondet tss ess _ =>
    tss.flatMap Statement.collectExprs ++
    ess.flatMap Statement.collectExprs
  | .loop (.det g) measure inv body _ =>
    [g] ++ measure.toList ++
    inv.map Prod.snd ++ body.flatMap Statement.collectExprs
  | .loop .nondet measure inv body _ =>
    measure.toList ++
    inv.map Prod.snd ++ body.flatMap Statement.collectExprs
  | .cmd (.cmd (.init _ _ .nondet _)) => []
  | .cmd (.cmd (.set _ .nondet _)) => []
  | .exit _ _ => []
  | .typeDecl _ _ => []

/-- Collect all user-facing expressions from a list of statements. -/
def Statements.collectExprs (ss : Statements) : List Expression.Expr :=
  ss.flatMap Statement.collectExprs

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

/-- Is this statement an `assume`, `assert`, `cover`, `init`, or `ite *`?
    These are the statements obligation extraction accepts. -/
@[expose] def Statement.isObligationForm (s : Statement) : Bool :=
  match s with
  | .cmd (.cmd (.assert ..)) | .cmd (.cmd (.assume ..))
  | .cmd (.cmd (.cover ..)) | .cmd (.cmd (.init ..)) => true
  | .ite .nondet _ _ _ => true
  | _ => false

/-- Does `ss` contain only `assume`, `assert`, `cover` and `init`, nested under
    `ite *` to any depth? -/
@[expose] def Statements.hasObligationForm (ss : Statements) : Bool :=
  Imperative.Block.allSubstmts Statement.isObligationForm ss

---------------------------------------------------------------------

/-! ## Expressions of statements

`Statements.allExprs` collects every expression appearing in a list of
statements. It is a named entry point used by the whole-program expression
facts. -/

/-- Every expression in `ss`. -/
@[expose] def Statements.allExprs (ss : Statements) : List Expression.Expr :=
  Statements.collectExprs ss

---------------------------------------------------------------------

/-! ## The calls of statements -/

/-- A call: the callee's name, the arguments and the call's metadata. -/
structure CallSite where
  procName : String
  args : List (CallArg Expression)
  md : MetaData Expression

/-- The call that a command is, if it is one. -/
def Command.callSites : Command → List CallSite
  | .call procName args md => [{ procName, args, md }]
  | .cmd _ => []

mutual
/-- The calls in a statement, at any nesting depth, in order. -/
def Statement.callSites : Statement → List CallSite
  | .cmd c => Command.callSites c
  | .block _ body _ => Statements.callSites body
  | .ite _ thenBody elseBody _ => Statements.callSites thenBody ++ Statements.callSites elseBody
  | .loop _ _ _ body _ => Statements.callSites body
  | .exit _ _ => []
  | .typeDecl _ _ => []

/-- The calls in statements, at any nesting depth, in order. -/
def Statements.callSites : Statements → List CallSite
  | [] => []
  | s :: rest => Statement.callSites s ++ Statements.callSites rest
end

/-- The procedure names a single extended command can call. -/
def CmdExt.calledProcedureNames (c : Command) : List String :=
  (Command.callSites c).map (·.procName)

/-- The procedure names a statement can call. -/
def Statement.calledProcedureNames (s : Statement) : List String :=
  (Statement.callSites s).map (·.procName)

/-- The procedure names a statement list can call. -/
def Statements.calledProcedureNames (ss : List Statement) : List String :=
  (Statements.callSites ss).map (·.procName)

---------------------------------------------------------------------

end
end Core
