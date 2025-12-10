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

inductive Stmt (P : PureExpr) (Cmd : Type) : Type where
  | cmd      (cmd : Cmd)
  | block    (label : String) (b : List (Stmt P Cmd)) (md : MetaData P := .empty)
  /-- `ite` (if-then-else) statement provides structured control flow. -/
  | ite      (cond : P.Expr)  (thenb : List (Stmt P Cmd)) (elseb : List (Stmt P Cmd)) (md : MetaData P := .empty)
  /-- `loop` Loop statement with optional measure (for termination) and invariant. -/
  | loop     (guard : P.Expr) (measure : Option P.Expr) (invariant : Option P.Expr) (body : List (Stmt P Cmd)) (md : MetaData P := .empty)
  /-- `goto` provides unstructured control flow. -/
  | goto     (label : String) (md : MetaData P := .empty)
  deriving Inhabited

abbrev Block (P : PureExpr) (Cmd : Type) := List (Stmt P Cmd)

def Stmt.isCmd {P : PureExpr} {Cmd : Type} (s : Stmt P Cmd) : Bool :=
  match s with
  | .cmd _ => true
  | _ => false


/--
Induction principle for `Stmt`
-/
@[elab_as_elim]
def Stmt.inductionOn {P : PureExpr} {Cmd : Type}
    {motive : Stmt P Cmd → Sort u}
    (cmd_case : ∀ (cmd : Cmd), motive (Stmt.cmd cmd))
    (block_case : ∀ (label : String) (b : List (Stmt P Cmd)) (md : MetaData P),
      (∀ s, s ∈ b → motive s) →
      motive (Stmt.block label b md))
    (ite_case : ∀ (cond : P.Expr) (thenb elseb : List (Stmt P Cmd)) (md : MetaData P),
      (∀ s, s ∈ thenb → motive s) →
      (∀ s, s ∈ elseb → motive s) →
      motive (Stmt.ite cond thenb elseb md))
    (loop_case : ∀ (guard : P.Expr) (measure invariant : Option P.Expr)
      (body : List (Stmt P Cmd)) (md : MetaData P),
      (∀ s, s ∈ body → motive s) →
      motive (Stmt.loop guard measure invariant body md))
    (goto_case : ∀ (label : String) (md : MetaData P),
      motive (Stmt.goto label md))
    (s : Stmt P Cmd) : motive s :=
  match s with
  | Stmt.cmd c => cmd_case c
  | Stmt.block label b md =>
    block_case label b md (fun s _ => inductionOn cmd_case block_case ite_case loop_case goto_case s)
  | Stmt.ite cond thenb elseb md =>
    ite_case cond thenb elseb md
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case goto_case s)
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case goto_case s)
  | Stmt.loop guard measure invariant body md =>
    loop_case guard measure invariant body md
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case goto_case s)
  | Stmt.goto label md => goto_case label md
  termination_by s

---------------------------------------------------------------------

/-! ### SizeOf -/

mutual
@[simp]
def Stmt.sizeOf (s : Imperative.Stmt P C) : Nat :=
  match s with
  | .cmd c => 1 + SizeOf.sizeOf c
  | .block _ bss _ => 1 + Block.sizeOf bss
  | .ite c tss ess _ => 3 + sizeOf c + Block.sizeOf tss + Block.sizeOf ess
  | .loop g _ _ bss _ => 3 + sizeOf g + Block.sizeOf bss
  | .goto _ _ => 1

@[simp]
def Block.sizeOf (ss : Imperative.Block P C) : Nat :=
  match ss with
  | [] => 1
  | s :: srest => 1 + Stmt.sizeOf s + Block.sizeOf srest

end

instance (P : PureExpr) : SizeOf (Imperative.Stmt P C) where
  sizeOf := Stmt.sizeOf

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
  |  .block label' bss _ => label = label' || Block.hasLabelInside label bss
  |  .ite _ tss ess _ => Block.hasLabelInside label tss || Block.hasLabelInside label ess
  |  _ => false
  termination_by (Stmt.sizeOf s)

/--
Do statements `ss` contain any block labeled `label`?
-/
def Block.hasLabelInside (label : String) (ss : List (Stmt P C)) : Bool :=
  match ss with
  | [] => false
  | s :: ss => Stmt.hasLabelInside label s || Block.hasLabelInside label ss
  termination_by (Block.sizeOf ss)
end

---------------------------------------------------------------------

/-! ### HasVars -/

mutual
/-- Get all variables accessed by `s`. -/
def Stmt.getVars [HasVarsPure P P.Expr] [HasVarsPure P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsPure.getVars cmd
  | .block _ bss _ => Block.getVars bss
  | .ite _ tbss ebss _ => Block.getVars tbss ++ Block.getVars ebss
  | .loop _ _ _ bss _ => Block.getVars bss
  | .goto _ _  => []
  termination_by (Stmt.sizeOf s)

def Block.getVars [HasVarsPure P P.Expr] [HasVarsPure P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.getVars s ++ Block.getVars srest
  termination_by (Block.sizeOf ss)
end

instance (P : PureExpr) [HasVarsPure P P.Expr] [HasVarsPure P C]
  : HasVarsPure P (Stmt P C) where
  getVars := Stmt.getVars

instance (P : PureExpr) [HasVarsPure P P.Expr] [HasVarsPure P C]
  : HasVarsPure P (Block P C) where
  getVars := Block.getVars

mutual
/-- Get all variables defined by the statement `s`. -/
def Stmt.definedVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsImp.definedVars cmd
  | .block _ bss _ => Block.definedVars bss
  | .ite _ tbss ebss _ => Block.definedVars tbss ++ Block.definedVars ebss
  | _ => []
  termination_by (Stmt.sizeOf s)

def Block.definedVars [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.definedVars s ++ Block.definedVars srest
  termination_by (Block.sizeOf ss)
end

mutual
/-- Get all variables modified by the statement `s`. -/
def Stmt.modifiedVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsImp.modifiedVars cmd
  | .goto _ _ => []
  | .block _ bss _ => Block.modifiedVars bss
  | .ite _ tbss ebss _ => Block.modifiedVars tbss ++ Block.modifiedVars ebss
  | .loop _ _ _ bss _ => Block.modifiedVars bss
  termination_by (Stmt.sizeOf s)

def Block.modifiedVars [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.modifiedVars s ++ Block.modifiedVars srest
  termination_by (Block.sizeOf ss)
end

mutual
/-- Get all variables modified/defined by the statement `s`.
    Note that we need a separate function because order matters here for sub-blocks
 -/
@[simp]
def Stmt.touchedVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .block _ bss _ => Block.touchedVars bss
  | .ite _ tbss ebss _ => Block.touchedVars tbss ++ Block.touchedVars ebss
  | _ => Stmt.definedVars s ++ Stmt.modifiedVars s
  termination_by (Stmt.sizeOf s)

@[simp]
def Block.touchedVars [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.touchedVars s ++ Block.touchedVars srest
  termination_by (Block.sizeOf ss)
end

instance (P : PureExpr) [HasVarsImp P C] : HasVarsImp P (Stmt P C) where
  definedVars := Stmt.definedVars
  modifiedVars := Stmt.modifiedVars
  -- order matters for Havoc, so needs to override the default
  touchedVars := Stmt.touchedVars

instance (P : PureExpr) [HasVarsImp P C] : HasVarsImp P (Block P C) where
  definedVars := Block.definedVars
  modifiedVars := Block.modifiedVars
  -- order matters for Havoc, so needs to override the default
  touchedVars := Block.touchedVars

---------------------------------------------------------------------

/-! ### Formatting -/

open Std (ToFormat Format format)

mutual
partial def formatStmt (P : PureExpr) (s : Stmt P C)
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C] : Format :=
  match s with
  | .cmd cmd => format cmd
  | .block label bl md => f!"{md}{label} : " ++ Format.bracket "{" f!"{formatBlock P bl}" "}"
  | .ite cond th el md => f!"{md}if {cond} then " ++
                        Format.bracket "{" f!"{formatBlock P th}" "}" ++
                        f!"{Format.line}else" ++
                        Format.bracket "{" f!"{formatBlock P el}" "}"
  | .loop guard measure invariant body md => f!"{md}while ({guard}) ({measure}) ({invariant}) " ++
                        Format.bracket "{" f!"{formatBlock P body}" "}"
  | .goto label md => f!"{md}goto {label}"

partial def formatBlock (P : PureExpr) (ss : List (Stmt P C))
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C] : Format :=
    match ss with
    | [] => f!""
    | s :: rest => formatStmt P s ++
                   if rest.isEmpty then f!""
                   else f!"\n{formatBlock P rest}"
end

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty]
        : ToFormat (Cmd P) where
  format c := formatCmd P c

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]
        : ToFormat (Stmt P C) where
  format s := formatStmt P s

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]
        : ToFormat (List (Stmt P C)) where
  format ss := formatBlock P ss

---------------------------------------------------------------------

end Imperative
