/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Axiom
public import Strata.DL.Lambda.LExprWF
public import Strata.DL.Lambda.LExprType

/-! # Collectors and type-parameter renaming for Core declarations

Collectors of the expressions and written types of commands and statements, the
type variables a procedure or lemma mentions, and `Lemma.renameTypeArgs`. -/

public section

namespace Core

open Lambda Imperative

/-! ## Collectors over commands and statements

Each collector lists, in syntax order, what `fe` gives for the expressions of a command or
statement and what `ft` gives for the declared types of its `init`s. -/

namespace Statement

/-- The guard, measure and invariants of a loop. -/
def loopExprs (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
    (invariant : List (String × Expression.Expr)) : List Expression.Expr :=
  guard.toList ++ measure.toList ++ invariant.map (·.2)

/-- The expressions a command reads. -/
def cmdExprs (c : Command) : List Expression.Expr :=
  match c with
  | .cmd c => c.readExprs
  | .call _ args _ => CallArg.getInputExprs args

end Statement

section Collect

variable {β : Type} (fe : Expression.Expr → List β) (ft : LMonoTy → List β)

/-- What `fe` and `ft` collect from a command: `ft` of a declared variable type, then `fe` of
    each expression the command reads. -/
def cmdCollect (c : Command) : List β :=
  (CmdExt.initTypes c).flatMap (fun ty => ft ty.toMonoTypeUnsafe) ++
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

/-- The type annotations of a command: the declared type of a variable and the annotations of
    its expressions. -/
def cmdAnnotTys (c : Command) : List LMonoTy :=
  cmdCollect exprAnnotTys ([·]) c

/-- The type annotations of a statement. -/
def stmtAnnotTys (s : Statement) : List LMonoTy :=
  stmtCollect exprAnnotTys ([·]) s

/-- The type annotations of a list of statements. -/
def stmtsAnnotTys (ss : List Statement) : List LMonoTy :=
  stmtsCollect exprAnnotTys ([·]) ss

/-- The types a procedure writes: its parameter types and the type annotations of its conditions
    and body. -/
def procAnnotTys (proc : Procedure) : List LMonoTy :=
  proc.header.inputs.values ++ proc.header.outputs.values ++
    proc.spec.preconditions.values.flatMap (fun chk => exprAnnotTys chk.expr) ++
    proc.spec.postconditions.values.flatMap (fun chk => exprAnnotTys chk.expr) ++
    match proc.body with
    | .structured ss => stmtsAnnotTys ss
    | .cfg c => c.blocks.flatMap fun (_, blk) =>
        blk.cmds.flatMap cmdAnnotTys ++
          match blk.transfer with
          | .condGoto g _ _ _ => exprAnnotTys g
          | .finish _ => []

/-- The type variables a declaration with type parameters `typeArgs` mentions, given the types
    `annot` it writes: its type parameters and the type variables of `annot`. -/
def declMentionedTyVarsIn (typeArgs : List String) (annot : List LMonoTy) : List String :=
  typeArgs ++ annot.flatMap LMonoTy.freeVars

/-- The type variables a procedure mentions, given the types `annot` it writes. -/
def Procedure.mentionedTyVarsIn (proc : Procedure) (annot : List LMonoTy) :
    List String :=
  declMentionedTyVarsIn proc.header.typeArgs annot

/-- The type variables a procedure mentions in its type parameters and annotations. -/
def Procedure.mentionedTyVars (proc : Procedure) : List String :=
  proc.mentionedTyVarsIn (procAnnotTys proc)

/-- The type variables a lemma mentions, given the types `annot` it writes. -/
def Lemma.mentionedTyVarsIn (l : Lemma) (annot : List LMonoTy) : List String :=
  declMentionedTyVarsIn l.typeArgs annot

/-- The type variables a lemma mentions in its type parameters and annotations. -/
def Lemma.mentionedTyVars (l : Lemma) : List String :=
  l.mentionedTyVarsIn (exprAnnotTys l.e)

/-- `l` with its type parameters renamed by `ren` throughout, as
    `renameTyArgList` does to the parameter list. -/
def Lemma.renameTypeArgs (l : Lemma) (ren : List (String × String)) : Lemma :=
  { l with typeArgs := renameTyArgList ren l.typeArgs,
           e := mapExprTys (LMonoTy.subst (Subst.ofRenaming ren)) l.e }

end Core

end -- public section
