/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.Cmd

namespace Imperative
---------------------------------------------------------------------

/-! ## Statements

Imperative's Statements include commands and add constructs like structured and
unstructured control-flow.
-/

mutual
inductive Stmt (P : PureExpr) (Cmd : Type) : Type where
  | cmd      (cmd : Cmd)
  | block    (label : String) (b : Block P Cmd) (md : MetaData P := .empty)
  /-- `ite` (if-then-else) statement provides structured control flow. -/
  | ite      (cond : P.Expr)  (thenb : Block P Cmd) (elseb : Block P Cmd) (md : MetaData P := .empty)
  /-- `loop` Loop statement with optional measure (for termination) and invariant. -/
  | loop     (guard : P.Expr) (measure : Option P.Expr) (invariant : Option P.Expr) (body : Block P Cmd) (md : MetaData P := .empty)
  /-- `goto` provides unstructured control flow. -/
  | goto     (label : String) (md : MetaData P := .empty)
  deriving Inhabited

structure Block (P : PureExpr) (Cmd : Type) where
  ss : List (Stmt P Cmd)
end

abbrev Stmts (P : PureExpr) (Cmd : Type) := List (Stmt P Cmd)

def Stmt.isCmd {P : PureExpr} {Cmd : Type} (s : Stmt P Cmd) : Bool :=
  match s with
  | .cmd _ => true
  | _ => false

---------------------------------------------------------------------

/-! ### SizeOf -/

mutual
@[simp]
def Stmt.sizeOf (s : Imperative.Stmt P C) : Nat :=
  match s with
  | .cmd c => 1 + SizeOf.sizeOf c
  | .block l b _ => 1 + Stmts.sizeOf b.ss
  | .ite c t e _ => 3 + sizeOf c + Stmts.sizeOf t.ss + Stmts.sizeOf e.ss
  | .loop g _ _ b _ => 3 + sizeOf g + Stmts.sizeOf b.ss
  | .goto l _ => 1 + l.length
  termination_by (sizeOf s)
  decreasing_by
  all_goals simp_wf
  cases b; simp; omega
  cases t; simp; omega
  cases e; simp; omega
  cases b; simp; omega

@[simp]
def Stmts.sizeOf (ss : Imperative.Stmts P C) : Nat :=
  match ss with
  | [] => 1
  | s :: srest => 1 + Imperative.Stmt.sizeOf s + Stmts.sizeOf srest
  termination_by (sizeOf ss)
end

instance (P : PureExpr) : SizeOf (Imperative.Stmt P C) where
  sizeOf := Stmt.sizeOf

instance (P : PureExpr) : SizeOf (Imperative.Stmts P C) where
  sizeOf := Stmts.sizeOf

---------------------------------------------------------------------

/--
`Stmt.hasLabel label s` checks whether statement `s` is a block labeled
`label`. -/
def Stmt.hasLabel : String → Stmt P C → Bool
| label, Stmt.block label' _ _ => label = label'
| _, _ => False

mutual
/-- Does statement `s` contain any block labeled `label`? -/
def Stmt.hasLabelInside (label : String) (s : Stmt P C) : Bool :=
  match s with
  |  .block label' b _ => label = label' || Stmts.hasLabelInside label b.ss
  |  .ite _ t e _ => Stmts.hasLabelInside label t.ss || Stmts.hasLabelInside label e.ss
  |  _ => false
  termination_by (Stmt.sizeOf s)
  decreasing_by
  all_goals simp_wf <;> omega

/--
Do statements `ss` contain any block labeled `label`?
-/
def Stmts.hasLabelInside (label : String) (ss : List (Stmt P C)) : Bool :=
  match ss with
  | [] => false
  | s :: ss => Stmt.hasLabelInside label s || Stmts.hasLabelInside label ss
  termination_by (Stmts.sizeOf ss)
end

---------------------------------------------------------------------

/-! ### HasVars -/

mutual
/-- Get all variables accessed by `s`. -/
def Stmt.getVars [HasVarsPure P P.Expr] [HasVarsPure P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsPure.getVars cmd
  | .block _ b _ => Stmts.getVars b.ss
  | .ite _ tb eb _ => Stmts.getVars tb.ss ++ Stmts.getVars eb.ss
  | .loop _ _ _ b _ => Stmts.getVars b.ss
  | .goto _ _  => []
  termination_by (Stmt.sizeOf s)
  decreasing_by
  all_goals simp_wf <;> omega

def Stmts.getVars [HasVarsPure P P.Expr] [HasVarsPure P C] (ss : Stmts P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.getVars s ++ Stmts.getVars srest
  termination_by (Stmts.sizeOf ss)
end

instance (P : PureExpr) [HasVarsPure P P.Expr] [HasVarsPure P C]
  : HasVarsPure P (Stmt P C) where
  getVars := Stmt.getVars

instance (P : PureExpr) [HasVarsPure P P.Expr] [HasVarsPure P C]
  : HasVarsPure P (Stmts P C) where
  getVars := Stmts.getVars

mutual
/-- Get all variables defined by the statement `s`. -/
def Stmt.definedVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsImp.definedVars cmd
  | .block _ b _ => Stmts.definedVars b.ss
  | .ite _ tb eb _ => Stmts.definedVars tb.ss ++ Stmts.definedVars eb.ss
  | _ => []
  termination_by (Stmt.sizeOf s)
  decreasing_by
  all_goals simp_wf
  cases tb; omega
  cases eb; omega

def Stmts.definedVars [HasVarsImp P C] (ss : Stmts P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.definedVars s ++ Stmts.definedVars srest
  termination_by (Stmts.sizeOf ss)
end

mutual
/-- Get all variables modified by the statement `s`. -/
def Stmt.modifiedVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsImp.modifiedVars cmd
  | .goto _ _ => []
  | .block _ b _ => Stmts.modifiedVars b.ss
  | .ite _ tb eb _ => Stmts.modifiedVars tb.ss ++ Stmts.modifiedVars eb.ss
  | .loop _ _ _ b _ => Stmts.modifiedVars b.ss
  termination_by (Stmt.sizeOf s)
  decreasing_by
  all_goals simp_wf
  cases tb; omega
  cases eb; omega

def Stmts.modifiedVars [HasVarsImp P C] (ss : Stmts P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.modifiedVars s ++ Stmts.modifiedVars srest
  termination_by (Stmts.sizeOf ss)
end

mutual
/-- Get all variables modified/defined by the statement `s`.
    Note that we need a separate function because order matters here for sub-blocks
 -/
@[simp]
def Stmt.touchedVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .block _ b _ => Stmts.touchedVars b.ss
  | .ite _ tb eb _ => Stmts.touchedVars tb.ss ++ Stmts.touchedVars eb.ss
  | _ => Stmt.definedVars s ++ Stmt.modifiedVars s
  termination_by (Stmt.sizeOf s)
  decreasing_by
  all_goals simp_wf <;> omega

@[simp]
def Stmts.touchedVars [HasVarsImp P C] (ss : Stmts P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.touchedVars s ++ Stmts.touchedVars srest
  termination_by (Stmts.sizeOf ss)
end

instance (P : PureExpr) [HasVarsImp P C] : HasVarsImp P (Stmt P C) where
  definedVars := Stmt.definedVars
  modifiedVars := Stmt.modifiedVars
  -- order matters for Havoc, so needs to override the default
  touchedVars := Stmt.touchedVars

instance (P : PureExpr) [HasVarsImp P C] : HasVarsImp P (Stmts P C) where
  definedVars := Stmts.definedVars
  modifiedVars := Stmts.modifiedVars
  -- order matters for Havoc, so needs to override the default
  touchedVars := Stmts.touchedVars

---------------------------------------------------------------------

/-! ### Formatting -/

open Std (ToFormat Format format)

mutual
partial def formatStmt (P : PureExpr) (s : Stmt P C)
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C] : Format :=
  match s with
  | .cmd cmd => format cmd
  | .block label bl md => f!"{md}{label} : " ++ Format.bracket "{" f!"{formatStmts P bl.ss}" "}"
  | .ite cond th el md => f!"{md}if {cond} then " ++
                        Format.bracket "{" f!"{formatStmts P th.ss}" "}" ++
                        f!"{Format.line}else" ++
                        Format.bracket "{" f!"{formatStmts P el.ss}" "}"
  | .loop guard measure invariant body md => f!"{md}while ({guard}) ({measure}) ({invariant}) " ++
                        Format.bracket "{" f!"{formatStmts P body.ss}" "}"
  | .goto label md => f!"{md}goto {label}"

partial def formatStmts (P : PureExpr) (ss : List (Stmt P C))
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C] : Format :=
    match ss with
    | [] => f!""
    | s :: rest => formatStmt P s ++
                   if rest.isEmpty then f!""
                   else f!"\n{formatStmts P rest}"
end

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty]
        : ToFormat (Cmd P) where
  format c := formatCmd P c

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]
        : ToFormat (Stmt P C) where
  format s := formatStmt P s

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]
        : ToFormat (List (Stmt P C)) where
  format ss := formatStmts P ss

---------------------------------------------------------------------

end Imperative
