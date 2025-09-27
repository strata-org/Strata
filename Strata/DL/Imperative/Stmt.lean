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
  | .cmd c => 1 + sizeOf c
  | .block _ ⟨ bss ⟩ _ => 1 + Stmts.sizeOf bss
  | .ite c ⟨ tss ⟩ ⟨ ess ⟩ _ => 3 + sizeOf c + Stmts.sizeOf tss + Stmts.sizeOf ess
  | .loop g _ _ ⟨ bss ⟩ _ => 3 + sizeOf g + Stmts.sizeOf bss
  | .goto _ _ => 1

@[simp]
def Stmts.sizeOf (ss : Imperative.Stmts P C) : Nat :=
  match ss with
  | [] => 1
  | s :: srest => 1 + Stmt.sizeOf s + Stmts.sizeOf srest

@[simp]
def Block.sizeOf : Imperative.Block P C →  Nat
  | ⟨ bss ⟩ => 1 + Stmts.sizeOf bss

end

instance (P : PureExpr) : SizeOf (Imperative.Stmt P C) where
  sizeOf := Stmt.sizeOf

instance (P : PureExpr) : SizeOf (Imperative.Stmts P C) where
  sizeOf := Stmts.sizeOf

instance (P : PureExpr) : SizeOf (Imperative.Block P C) where
  sizeOf := Block.sizeOf

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
  |  .block label' ⟨ bss ⟩ _ => label = label' || Stmts.hasLabelInside label bss
  |  .ite _ ⟨ tss ⟩ ⟨ ess ⟩  _ => Stmts.hasLabelInside label tss || Stmts.hasLabelInside label ess
  |  _ => false
  termination_by (Stmt.sizeOf s)

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
  | .block _ ⟨ bss ⟩ _ => Stmts.getVars bss
  | .ite _ ⟨ tbss ⟩ ⟨ ebss ⟩ _ => Stmts.getVars tbss ++ Stmts.getVars ebss
  | .loop _ _ _ ⟨ bss ⟩ _ => Stmts.getVars bss
  | .goto _ _  => []
  termination_by (Stmt.sizeOf s)

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
  | .block _ ⟨ bss ⟩  _ => Stmts.definedVars bss
  | .ite _ ⟨ tbss ⟩ ⟨ ebss ⟩ _ => Stmts.definedVars tbss ++ Stmts.definedVars ebss
  | _ => []
  termination_by (Stmt.sizeOf s)

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
  | .block _ ⟨ bss ⟩ _ => Stmts.modifiedVars bss
  | .ite _ ⟨ tbss ⟩ ⟨ ebss ⟩ _ => Stmts.modifiedVars tbss ++ Stmts.modifiedVars ebss
  | .loop _ _ _ ⟨ bss ⟩ _ => Stmts.modifiedVars bss
  termination_by (Stmt.sizeOf s)

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
  | .block _ ⟨ bss ⟩ _ => Stmts.touchedVars bss
  | .ite _ ⟨ tbss ⟩ ⟨ ebss ⟩ _ => Stmts.touchedVars tbss ++ Stmts.touchedVars ebss
  | _ => Stmt.definedVars s ++ Stmt.modifiedVars s
  termination_by (Stmt.sizeOf s)

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
