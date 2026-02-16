/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.Cmd

namespace Imperative

open Std.Format

---------------------------------------------------------------------

/-! ## Statements

Imperative's Statements include commands and add constructs like structured and
unstructured control-flow.
-/

/-- Imperative statements focused on control flow.

The `P` parameter specifies the type of expressions that appear in conditional
and loop guards.  The `Cmd` parameter specifies the type of atomic command
contained within the `.cmd` constructor.
-/
inductive Stmt (P : PureExpr) (Cmd : Type) : Type where
  /-- An atomic command. -/
  | cmd      (cmd : Cmd)
  /-- An block containing a `List` of `Stmt`. -/
  | block    (label : String) (b : List (Stmt P Cmd)) (md : MetaData P := .empty)
  /-- A conditional execution statement. -/
  | ite      (cond : P.Expr)  (thenb : List (Stmt P Cmd)) (elseb : List (Stmt P Cmd)) (md : MetaData P := .empty)
  /-- An iterated execution statement. Includes an optional measure (for
  termination) and invariant. -/
  | loop     (guard : P.Expr) (measure : Option P.Expr) (invariant : Option P.Expr) (body : List (Stmt P Cmd)) (md : MetaData P := .empty)
  /-- A semi-structured control flow statement transferring control to the given
  label. The control flow induced by `goto` must not create cycles. **NOTE:**
  This will likely be removed, in favor of an alternative view of imperative
  programs that is purely untructured. -/
  | goto     (label : String) (md : MetaData P := .empty)
  /-- A function declaration within a statement block. -/
  | funcDecl (decl : PureFunc P) (md : MetaData P := .empty)
  deriving Inhabited

/-- A block is simply an abbreviation for a list of commands. -/
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
    (funcDecl_case : ∀ (decl : PureFunc P) (md : MetaData P),
      motive (Stmt.funcDecl decl md))
    (s : Stmt P Cmd) : motive s :=
  match s with
  | Stmt.cmd c => cmd_case c
  | Stmt.block label b md =>
    block_case label b md (fun s _ => inductionOn cmd_case block_case ite_case loop_case goto_case funcDecl_case s)
  | Stmt.ite cond thenb elseb md =>
    ite_case cond thenb elseb md
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case goto_case funcDecl_case s)
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case goto_case funcDecl_case s)
  | Stmt.loop guard measure invariant body md =>
    loop_case guard measure invariant body md
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case goto_case funcDecl_case s)
  | Stmt.goto label md => goto_case label md
  | Stmt.funcDecl decl md => funcDecl_case decl md
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
  | .funcDecl _ _ => 1

@[simp]
def Block.sizeOf (ss : Imperative.Block P C) : Nat :=
  match ss with
  | [] => 1
  | s :: srest => 1 + Stmt.sizeOf s + Block.sizeOf srest

end

theorem sizeOf_stmt_in_block {s : Imperative.Stmt P C} {b: Imperative.Block P C} (s_in: s ∈ b) : s.sizeOf < b.sizeOf := by
  induction b with
  | nil => grind
  | cons hd tl IH =>
    rw[List.mem_cons] at s_in; simp only [Block.sizeOf]; grind

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

/-! ### NoFuncDecl

Predicate stating that a statement or block contains no function declarations.
This is useful when converting to non-deterministic statements which don't have function declarations.
-/

mutual
/-- Returns true if the statement contains no function declarations. -/
def Stmt.noFuncDecl (s : Stmt P C) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.noFuncDecl bss
  | .ite _ tss ess _ => Block.noFuncDecl tss && Block.noFuncDecl ess
  | .loop _ _ _ bss _ => Block.noFuncDecl bss
  | .goto _ _ => true
  | .funcDecl _ _ => false
  termination_by (Stmt.sizeOf s)

/-- Returns true if the block contains no function declarations. -/
def Block.noFuncDecl (ss : Block P C) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.noFuncDecl s && Block.noFuncDecl srest
  termination_by (Block.sizeOf ss)
end

---------------------------------------------------------------------

/-! ### StripMetaData

Functions to remove metadata from statements and blocks.
Useful for cleaner formatting output in tests.
-/

mutual
/-- Remove all metadata from a statement. -/
def Stmt.stripMetaData (s : Stmt P C) : Stmt P C :=
  match s with
  | .cmd c => .cmd c
  | .block label bss _ => .block label (Block.stripMetaData bss)
  | .ite cond tss ess _ => .ite cond (Block.stripMetaData tss) (Block.stripMetaData ess)
  | .loop guard measure invariant bss _ => .loop guard measure invariant (Block.stripMetaData bss)
  | .goto label _ => .goto label
  | .funcDecl decl _ => .funcDecl decl
  termination_by (Stmt.sizeOf s)

/-- Remove all metadata from a block. -/
def Block.stripMetaData (ss : Block P C) : Block P C :=
  match ss with
  | [] => []
  | s :: srest => Stmt.stripMetaData s :: Block.stripMetaData srest
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
  | .funcDecl decl _ =>
    -- Get free variables from function body, excluding formal parameters
    match decl.body with
    | none => []
    | some body =>
      let bodyVars := HasVarsPure.getVars body
      let formals := decl.inputs.map (·.1)
      bodyVars.filter (fun v => formals.all (fun f => ¬(P.EqIdent v f).decide))
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
  | .funcDecl decl _ => [decl.name]  -- Function declaration defines the function name
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
  | .funcDecl _ _ => []  -- Function declarations don't modify variables
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
def formatStmt (P : PureExpr) (s : Stmt P C)
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C] : Format :=
  match s with
  | .cmd cmd => format cmd
  | .block label bl md => f!"{md}{label} :" ++ line ++ formatBlock P bl
  | .ite cond th el md =>
      let thenPart := formatBlock P th
      let elsePart := formatBlock P el
      f!"{md}if " ++ group f!"{nestD $ format cond} {thenPart}" ++ line ++ f!"else {elsePart}"

  | .loop guard measure invariant body md =>
      let body := formatBlock P body
      let beforeBody := nestD f!"{line}{guard}{line}({measure}){line}({invariant})"
      let children := group f!"{beforeBody}{line}{body}"
      f!"{md}while{children}"
  | .goto label md => f!"{md}goto {label}"
  | .funcDecl _ md => f!"{md}funcDecl <function>"
  termination_by s.sizeOf

def formatBlock (P : PureExpr) (ss : List (Stmt P C))
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C] : Format :=
    match ss with
    | [] => "{}"
    | parts =>
      let inner := line ++ (group $ joinSep (parts.map (fun s => formatStmt P s)) (format "\n"))
      f!"\{{nestD inner}\n}"
  termination_by (Block.sizeOf ss)
  decreasing_by all_goals (simp_wf; apply sizeOf_stmt_in_block; simp_all)
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
