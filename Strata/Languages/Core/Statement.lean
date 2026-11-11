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
abbrev Statement.call (pname : String) (tyArgs : Option (List Expression.Ty))
    (args : List (CallArg Expression)) (md : MetaData Expression) :=
  @Stmt.cmd Expression Command (CmdExt.call pname tyArgs args md)
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
  | .call pname _ args md =>
    .call pname none (args.map fun
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
`.assert` commands (their label and metadata) and each entry of a `.loop`'s
invariant list (its label and `MetaData.invariantMd`, the metadata that loop
invariant elimination gives the asserts it generates for that invariant).
-/
def Statement.collectAssertIds (s : Statement) : List (Imperative.AssertId Expression) :=
  match s with
  | .cmd (.cmd (.assert label _ md)) => [⟨label, md⟩]
  | .cmd _ => []
  | .block _ inner_ss _ => Statements.collectAssertIds inner_ss
  | .ite _ then_ss else_ss _ =>
    Statements.collectAssertIds then_ss ++ Statements.collectAssertIds else_ss
  | .loop _ _ inv body_ss md =>
    inv.mapIdx (fun i lp => ⟨lp.1, md.invariantMd i⟩) ++
      Statements.collectAssertIds body_ss
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

/-- Variables read by a Core command. -/
abbrev Command.readVars : Command → List Expression.Ident :=
  CmdExt.readVars

/-- Operator/function names referenced by a Core command. -/
abbrev Command.getOps : Command → List Expression.Ident :=
  CmdExt.getOps

instance : HasOpsImp Expression Command := inferInstance

/-- Variables defined by a Core command. -/
abbrev Command.definedVars : Command → List Expression.Ident :=
  CmdExt.definedVars

/-- Variables modified by a Core command. -/
abbrev Command.modifiedVars : Command → List Expression.Ident :=
  CmdExt.modifiedVars

/-- Variables modified or defined by a Core command. -/
def Command.modifiedOrDefinedVars (c : Command) : List Expression.Ident :=
  Command.definedVars c ++ Command.modifiedVars c

instance : HasVarsImp Expression Command := inferInstance

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
  | .call pname tyArgs args metadata =>
    .call pname tyArgs (args.map fun
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
  | .call pname tyArgs args metadata =>
    .call pname tyArgs (args.map fun
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
  | .call pname tyArgs args md => .call pname tyArgs (args.map (CallArg.mapInput f)) md
  | c => c

/-- Erase every annotation of a command: expression types, the declared type of `init` and the
    type arguments of a `call`. -/
def Command.eraseAnnots (c : Command) : Command :=
  Command.mapExpr Lambda.LExpr.eraseTypes
    (match c with
      | .cmd (.init name _ e md) => .cmd (.init name Lambda.LTy.erased e md)
      | .call pname _ args md => .call pname none args md
      | c => c)

/-- Erase every annotation of a statement, including guards, measures and invariants. -/
def Statement.eraseAnnots (s : Statement) : Statement :=
  Imperative.Stmt.mapExpr Lambda.LExpr.eraseTypes Command.eraseAnnots s

/-- Erase every annotation of a list of statements. -/
def Statements.eraseAnnots (ss : Statements) : Statements :=
  Imperative.Block.mapExpr Lambda.LExpr.eraseTypes Command.eraseAnnots ss

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
  | .call pname tyArgs args md => do
    return .call pname tyArgs (← args.mapM fun
      | .inArg e => do return .inArg (← f e)
      | a => pure a) md
  | c => pure c

def Statement.mapExprsM {M : Type → Type} [Monad M] (f : Expression.Expr → M Expression.Expr)
    (s : Statement) : M Statement :=
  Imperative.Stmt.mapExprM f (Command.mapExprM f) s

def Statements.mapExprsM {M : Type → Type} [Monad M] (f : Expression.Expr → M Expression.Expr)
    (ss : Statements) : M Statements :=
  ss.mapM (Statement.mapExprsM f)

section TypeAnnotations

open Lambda

/-- Apply `fe` to every expression of a command and `ft` to the declared type of an `init`
    and to the type arguments of a `call`. -/
def mapCmdWith (fe : Expression.Expr → Expression.Expr) (ft : LMonoTy → LMonoTy)
    (c : Command) : Command :=
  match c with
  | .cmd cc =>
    match cc with
    | .init x ty e md => .cmd (.init x (mapLTyTys ft ty) (e.map fe) md)
    | .set x e md => .cmd (.set x (e.map fe) md)
    | .assert l b md => .cmd (.assert l (fe b) md)
    | .assume l b md => .cmd (.assume l (fe b) md)
    | .cover l b md => .cmd (.cover l (fe b) md)
  | .call pname tyArgs args md =>
    .call pname (tyArgs.map (·.map (mapLTyTys ft))) (args.map (CallArg.mapInput fe)) md

/-- Apply `f` to every type annotation in a command. -/
def mapCmdTys (f : LMonoTy → LMonoTy) (c : Command) : Command :=
  mapCmdWith (mapExprTys f) f c

/-- Apply `f` to every type annotation in a statement. -/
def mapStmtTys (f : LMonoTy → LMonoTy) (s : Statement) : Statement :=
  Stmt.mapExpr (mapExprTys f) (mapCmdTys f) s

/-- Apply `f` to every type annotation in a list of statements. -/
def mapStmtsTys (f : LMonoTy → LMonoTy) (ss : List Statement) : List Statement :=
  Block.mapExpr (mapExprTys f) (mapCmdTys f) ss

/-- Does every type annotation in an expression-or-nondeterministic-value
    satisfy `p`? -/
def allExprOrNondetTys (p : LMonoTy → Bool) (e : ExprOrNondet Expression) : Bool :=
  match e with
  | .det e => allExprTys p e
  | .nondet => true

/-- Does every type annotation in a command satisfy `p`? -/
def allCmdTys (p : LMonoTy → Bool) (c : Command) : Bool :=
  match c with
  | .cmd cc =>
    match cc with
    | .init _ ty e _ => allLTyTys p ty && allExprOrNondetTys p e
    | .set _ e _ => allExprOrNondetTys p e
    | .assert _ b _ => allExprTys p b
    | .assume _ b _ => allExprTys p b
    | .cover _ b _ => allExprTys p b
  | .call _ tyArgs args _ =>
    tyArgs.all (·.all (allLTyTys p)) && args.all fun
      | .inArg e => allExprTys p e
      | .inoutArg _ => true
      | .outArg _ => true

mutual
/-- Does every type annotation in a statement satisfy `p`? -/
def allStmtTys (p : LMonoTy → Bool) (s : Statement) : Bool :=
  match s with
  | .cmd c => allCmdTys p c
  | .block _ bss _ => allStmtsTys p bss
  | .ite cond tss ess _ =>
    allExprOrNondetTys p cond && allStmtsTys p tss && allStmtsTys p ess
  | .loop g m i bss _ =>
    allExprOrNondetTys p g && m.all (allExprTys p)
      && i.all (fun (_, e) => allExprTys p e) && allStmtsTys p bss
  | .exit _ _ => true
  | .typeDecl _ _ => true
/-- Does every type annotation in a list of statements satisfy `p`? -/
def allStmtsTys (p : LMonoTy → Bool) (ss : List Statement) : Bool :=
  match ss with
  | [] => true
  | s :: rest => allStmtTys p s && allStmtsTys p rest
end

mutual

/-- Every type an `init` in the statement declares a variable at, and every type argument a
    call in it carries, satisfies `p`. -/
@[expose] def Statement.AllDeclTys (p : LTy → Prop) : Statement → Prop
  | .cmd (.cmd (.init _ ty _ _)) => p ty
  | .cmd (.cmd _) => True
  | .cmd (.call _ tyArgs _ _) => ∀ tys, tyArgs = some tys → ∀ ty ∈ tys, p ty
  | .block _ body _ => Statements.AllDeclTys p body
  | .ite _ thenb elseb _ => Statements.AllDeclTys p thenb ∧ Statements.AllDeclTys p elseb
  | .loop _ _ _ body _ => Statements.AllDeclTys p body
  | .exit _ _ => True
  | .typeDecl _ _ => True

/-- Every statement of the list satisfies `Statement.AllDeclTys p`. -/
@[expose] def Statements.AllDeclTys (p : LTy → Prop) : List Statement → Prop
  | [] => True
  | s :: ss => Statement.AllDeclTys p s ∧ Statements.AllDeclTys p ss

end

/-- Every `init` in the statement declares a ground monotype, and every call that carries type
    arguments carries ground monotypes. -/
@[expose] def Statement.Ground (s : Statement) : Prop :=
  Statement.AllDeclTys LTy.GroundMono s

/-- Every statement of the list is ground (`Statement.Ground`). -/
@[expose] def Statements.Ground (ss : List Statement) : Prop :=
  Statements.AllDeclTys LTy.GroundMono ss

/-! ## Collectors over commands and statements

Each collector lists, in syntax order, what `fe` gives for the expressions of a command or
statement and what `ft` gives for the declared types of its `init`s and the type arguments of its
calls. -/

namespace Statement

/-- The guard, measure and invariants of a loop. -/
def loopExprs (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
    (invariant : List (String × Expression.Expr)) : List Expression.Expr :=
  guard.toList ++ measure.toList ++ invariant.map (·.2)

/-- The expressions a command reads. -/
def cmdExprs (c : Command) : List Expression.Expr :=
  match c with
  | .cmd c => c.readExprs
  | .call _ _ args _ => CallArg.getInputExprs args

/-- The type arguments a command stores: those of a type-annotated call, and none otherwise. -/
def cmdTyArgs (c : Command) : List Expression.Ty :=
  match c with
  | .call _ tyArgs _ _ => tyArgs.getD []
  | .cmd _ => []

end Statement

section Collect

variable {β : Type} (fe : Expression.Expr → List β) (ft : LMonoTy → List β)

/-- What `fe` and `ft` collect from a command: `ft` of a declared variable type, then `ft` of
    each type argument of a call, then `fe` of each expression the command reads. -/
def cmdCollect (c : Command) : List β :=
  (CmdExt.initTypes c).flatMap (fun ty => ft ty.toMonoTypeUnsafe) ++
    (Statement.cmdTyArgs c).flatMap (fun ty => ft ty.toMonoTypeUnsafe) ++
    (Statement.cmdExprs c).flatMap fe

/-- What `fe` and `ft` collect from `s` itself, outside any statement list nested in `s`. -/
def stmtOwnCollect : Statement → List β
  | .cmd c => cmdCollect fe ft c
  | .ite cond _ _ _ => cond.toList.flatMap fe
  | .loop g m i _ _ => (Statement.loopExprs g m i).flatMap fe
  | .block _ _ _ | .exit _ _ | .typeDecl _ _ => []

mutual
/-- What `fe` and `ft` collect from a statement and the statement lists nested in it. -/
def stmtCollect (s : Statement) : List β :=
  stmtOwnCollect fe ft s ++
    match s with
    | .block _ bss _ | .loop _ _ _ bss _ => stmtsCollect bss
    | .ite _ tss ess _ => stmtsCollect tss ++ stmtsCollect ess
    | .cmd _ | .exit _ _ | .typeDecl _ _ => []
/-- What `fe` and `ft` collect from a list of statements. -/
def stmtsCollect (ss : List Statement) : List β :=
  match ss with
  | [] => []
  | s :: rest => stmtCollect s ++ stmtsCollect rest
end

end Collect

mutual
/-- The commands of a statement and of the statement lists nested in it, in order. -/
def stmtCmds (s : Statement) : List Command :=
  match s with
  | .cmd c => [c]
  | .block _ bss _ | .loop _ _ _ bss _ => stmtsCmds bss
  | .ite _ tss ess _ => stmtsCmds tss ++ stmtsCmds ess
  | .exit _ _ | .typeDecl _ _ => []
/-- The commands of a list of statements, in order. -/
def stmtsCmds (ss : List Statement) : List Command :=
  match ss with
  | [] => []
  | s :: rest => stmtCmds s ++ stmtsCmds rest
end

end TypeAnnotations

/-- Push `e`'s expression onto `acc`, if it has one. -/
private def pushExprOrNondet (acc : Array Expression.Expr) (e : ExprOrNondet Expression) :
    Array Expression.Expr :=
  match e with
  | .det e => acc.push e
  | .nondet => acc

mutual
/-- Push the user-facing expressions of `s` onto `acc`, in program order: a
    guard before its branches or body, a loop's measure and invariants before
    its body. An accumulator rather than concatenation, because nested blocks
    concatenated with `++` at every level cost time quadratic in the nesting
    depth, and symbolic evaluation nests a block per path split. -/
def Statement.collectExprsInto (acc : Array Expression.Expr) (s : Statement) :
    Array Expression.Expr :=
  match s with
  | .cmd (.cmd (.assert _ e _)) => acc.push e
  | .cmd (.cmd (.assume _ e _)) => acc.push e
  | .cmd (.cmd (.cover _ e _)) => acc.push e
  | .cmd (.cmd (.init _ _ e _)) => pushExprOrNondet acc e
  | .cmd (.cmd (.set _ e _)) => pushExprOrNondet acc e
  | .cmd (.call _ _ args _) => args.foldl (fun acc a => match a with
      | .inArg e => acc.push e
      | _ => acc) acc
  | .block _ ss _ => Statements.collectExprsInto acc ss
  | .ite c tss ess _ =>
    Statements.collectExprsInto (Statements.collectExprsInto (pushExprOrNondet acc c) tss) ess
  | .loop g measure inv body _ =>
    let acc := pushExprOrNondet acc g
    let acc := match measure with | some m => acc.push m | none => acc
    Statements.collectExprsInto (inv.foldl (fun acc p => acc.push p.2) acc) body
  | .exit _ _ => acc
  | .typeDecl _ _ => acc

/-- `Statement.collectExprsInto` over a list of statements, in order. -/
def Statements.collectExprsInto (acc : Array Expression.Expr) (ss : List Statement) :
    Array Expression.Expr :=
  match ss with
  | [] => acc
  | s :: rest => Statements.collectExprsInto (Statement.collectExprsInto acc s) rest
end

/-- Collect all user-facing expressions from a statement. -/
def Statement.collectExprs (s : Statement) : List Expression.Expr :=
  (Statement.collectExprsInto #[] s).toList

/-- Collect all user-facing expressions from a list of statements. -/
def Statements.collectExprs (ss : Statements) : List Expression.Expr :=
  (Statements.collectExprsInto #[] ss).toList

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

/-- Does `s` make no procedure call, at any nesting depth? -/
@[expose] def Statement.noCalls (s : Statement) : Bool :=
  Imperative.Stmt.allSubstmts Statement.isNotCall s

/-- The commands of a list of statements, in order; other statements are
    dropped. -/
def Statements.commands (ss : Statements) : List Command :=
  ss.filterMap fun s => match s with
    | .cmd c => some c
    | _ => none

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

/-- Not a declaration: `init` introduces a variable. -/
@[expose] def Statement.isNotInit (s : Statement) : Bool :=
  match s with
  | .cmd (.cmd (.init ..)) => false
  | _ => true

/-- Does `ss` declare no variable, at any depth? -/
@[expose] def Statements.noInits (ss : Statements) : Bool :=
  Imperative.Block.allSubstmts Statement.isNotInit ss

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

/-- Is this statement an `init`, `set`, `assume`, `assert`, `cover`, or `ite *`?
    These are the statements of a guarded program (the output of the WP phase). -/
@[expose] def Statement.isTreeForm (s : Statement) : Bool :=
  match s with
  | .cmd (.cmd (.assert ..)) | .cmd (.cmd (.assume ..)) | .cmd (.cmd (.cover ..))
  | .cmd (.cmd (.init ..)) | .cmd (.cmd (.set ..)) => true
  | .ite .nondet _ _ _ => true
  | _ => false

/-- Is `ss` in tree form: only `init`, `set`, `assume`, `assert` and `cover`, nested under
    `ite *` to any depth, every `ite *` the last statement of its list? -/
@[expose] def Statements.treeForm (ss : Statements) : Bool :=
  Imperative.Block.allSubstmts Statement.isTreeForm ss && Imperative.Block.nondetIteLast ss

---------------------------------------------------------------------

/-! ## Expressions of statements

`Statements.allExprs` collects every expression appearing in a list of
statements. It is a named entry point used by the whole-program expression
facts. -/

/-- Every expression in `ss`. -/
@[expose] def Statements.allExprs (ss : Statements) : List Expression.Expr :=
  Statements.collectExprs ss

/-- The variable names `ss` reads (its expressions' free variables) or declares. -/
def Statements.varNames (ss : Statements) : List String :=
  (Statements.allExprs ss).flatMap (fun e => (HasFvars.getFvars e).map (·.name)) ++
    (Imperative.Block.definedVars (P := Expression) (C := Command) ss false).map (·.name)

/-- `ss` with variable `x` renamed to `x'`, which has type `ty`, in its reads and
    its writes. -/
def Statements.renameVar (ss : Statements) (x x' : Expression.Ident)
    (ty : Option Lambda.LMonoTy) : Statements :=
  Block.renameLhs (Block.substFvar ss x (.fvar default x' ty)) x x'

---------------------------------------------------------------------

/-! ## The calls of statements -/

/-- A call: the callee's name, its type arguments, the arguments and the call's
    metadata. -/
structure CallSite where
  procName : String
  tyArgs : Option (List Expression.Ty)
  args : List (CallArg Expression)
  md : MetaData Expression

/-- The call that a command is, if it is one. -/
def Command.callSites : Command → List CallSite
  | .call procName tyArgs args md => [{ procName, tyArgs, args, md }]
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
