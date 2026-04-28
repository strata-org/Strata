/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd
public import Strata.DL.Lambda.TypeConstructor

namespace Imperative

public section

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
  | block    (label : String) (b : List (Stmt P Cmd)) (md : MetaData P)
  /-- A conditional execution statement. When `cond` is `.nondet`, the branch
  is chosen non-deterministically. -/
  | ite      (cond : ExprOrNondet P)  (thenb : List (Stmt P Cmd)) (elseb : List (Stmt P Cmd)) (md : MetaData P)
  /-- An iterated execution statement. Includes an optional measure (for
  termination) and labeled invariants. When `guard` is `.nondet`, the loop iterates
  a non-deterministic number of times. Each invariant carries a label string
  (expected to be distinct, like assert labels do). -/
  | loop     (guard : ExprOrNondet P) (measure : Option P.Expr)
             (invariants : List (String × P.Expr))
             (body : List (Stmt P Cmd)) (md : MetaData P)
  /-- An exit statement that transfers control out of the nearest enclosing
  block with the given label. If no label is provided, exits the nearest
  enclosing block. -/
  | exit     (label : Option String) (md : MetaData P)
  /-- A function declaration within a statement block. -/
  | funcDecl (decl : PureFunc P) (md : MetaData P)
  /-- A type declaration within a statement block. -/
  | typeDecl (tc : TypeConstructor) (md : MetaData P)
  deriving Inhabited

/-- A block is simply an abbreviation for a list of commands. -/
@[expose] abbrev Block (P : PureExpr) (Cmd : Type) := List (Stmt P Cmd)

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
    (ite_case : ∀ (cond : ExprOrNondet P) (thenb elseb : List (Stmt P Cmd)) (md : MetaData P),
      (∀ s, s ∈ thenb → motive s) →
      (∀ s, s ∈ elseb → motive s) →
      motive (Stmt.ite cond thenb elseb md))
    (loop_case : ∀ (guard : ExprOrNondet P) (measure : Option P.Expr) (invariant : List (String × P.Expr))
      (body : List (Stmt P Cmd)) (md : MetaData P),
      (∀ s, s ∈ body → motive s) →
      motive (Stmt.loop guard measure invariant body md))
    (exit_case : ∀ (label : Option String) (md : MetaData P),
      motive (Stmt.exit label md))
    (funcDecl_case : ∀ (decl : PureFunc P) (md : MetaData P),
      motive (Stmt.funcDecl decl md))
    (typeDecl_case : ∀ (tc : TypeConstructor) (md : MetaData P),
      motive (Stmt.typeDecl tc md))
    (s : Stmt P Cmd) : motive s :=
  match s with
  | Stmt.cmd c => cmd_case c
  | Stmt.block label b md =>
    block_case label b md (fun s _ => inductionOn cmd_case block_case ite_case loop_case exit_case funcDecl_case typeDecl_case s)
  | Stmt.ite cond thenb elseb md =>
    ite_case cond thenb elseb md
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case exit_case funcDecl_case typeDecl_case s)
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case exit_case funcDecl_case typeDecl_case s)
  | Stmt.loop guard measure invariant body md =>
    loop_case guard measure invariant body md
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case exit_case funcDecl_case typeDecl_case s)
  | Stmt.exit label md => exit_case label md
  | Stmt.funcDecl decl md => funcDecl_case decl md
  | Stmt.typeDecl tc md => typeDecl_case tc md
  termination_by s

---------------------------------------------------------------------

/-! ### sizeOf -/

mutual
@[simp]
def Stmt.sizeOf (s : Imperative.Stmt P C) : Nat :=
  match s with
  | .cmd c => 1 + SizeOf.sizeOf c
  | .block _ bss _ => 1 + Block.sizeOf bss
  | .ite _ tss ess _ => 3 + Block.sizeOf tss + Block.sizeOf ess
  | .loop _ _ _ bss _ => 3 + Block.sizeOf bss
  | .exit _ _ => 1
  | .funcDecl _ _ => 1
  | .typeDecl _ _ => 1

@[simp]
def Block.sizeOf (ss : Imperative.Block P C) : Nat :=
  match ss with
  | [] => 1
  | s :: srest => 1 + Stmt.sizeOf s + Block.sizeOf srest

end

---------------------------------------------------------------------

---------------------------------------------------------------------

/-! ### NoFuncDecl

Predicate stating that a statement or block contains no function declarations.
This is useful when converting to non-deterministic statements which don't have function declarations.
-/

mutual
/-- Returns true if the statement contains no function declarations. -/
@[expose] def Stmt.noFuncDecl (s : Stmt P C) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.noFuncDecl bss
  | .ite _ tss ess _ => Block.noFuncDecl tss && Block.noFuncDecl ess
  | .loop _ _ _ bss _ => Block.noFuncDecl bss
  | .exit _ _ => true
  | .funcDecl _ _ => false
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Returns true if the block contains no function declarations. -/
@[expose] def Block.noFuncDecl (ss : Block P C) : Bool :=
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
  | .block label bss _ => .block label (Block.stripMetaData bss) .empty
  | .ite cond tss ess _ => .ite cond (Block.stripMetaData tss) (Block.stripMetaData ess) .empty
  | .loop guard measure invariant bss _ => .loop guard measure invariant (Block.stripMetaData bss) .empty
  | .exit label _ => .exit label .empty
  | .funcDecl decl _ => .funcDecl decl .empty
  | .typeDecl tc _ => .typeDecl tc .empty
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
  | .ite cond tbss ebss _ => cond.getVars ++ Block.getVars tbss ++ Block.getVars ebss
  | .loop guard _ _ bss _ => guard.getVars ++ Block.getVars bss
  | .exit _ _  => []
  | .funcDecl decl _ =>
    -- Get free variables from function body, excluding formal parameters
    match decl.body with
    | none => []
    | some body =>
      let bodyVars := HasVarsPure.getVars body
      let formals := decl.inputs.map (·.1)
      bodyVars.filter (fun v => formals.all (fun f => ¬(P.EqIdent v f).decide))
  | .typeDecl _ _ => []  -- Type declarations don't reference variables

def Block.getVars [HasVarsPure P P.Expr] [HasVarsPure P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.getVars s ++ Block.getVars srest
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
  | .loop _ _ _ body _ => Block.definedVars body
  | .funcDecl decl _ => [decl.name]  -- Function declaration defines the function name
  | .typeDecl _ _ => []  -- Type declarations don't define variables
  | _ => []

def Block.definedVars [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.definedVars s ++ Block.definedVars srest
end

mutual
/-- Get all variables modified by the statement `s`. -/
def Stmt.modifiedVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsImp.modifiedVars cmd
  | .exit _ _ => []
  | .block _ bss _ => Block.modifiedVars bss
  | .ite _ tbss ebss _ => Block.modifiedVars tbss ++ Block.modifiedVars ebss
  | .loop _ _ _ bss _ => Block.modifiedVars bss
  | .funcDecl _ _ => []  -- Function declarations don't modify variables
  | .typeDecl _ _ => []  -- Type declarations don't modify variables

def Block.modifiedVars [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.modifiedVars s ++ Block.modifiedVars srest
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

@[simp]
def Block.touchedVars [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.touchedVars s ++ Block.touchedVars srest
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
      -- Format each labeled invariant as `[lbl]: expr` (unlabeled ones just as `expr`).
      let invParts : List Format := invariant.map fun (l, e) =>
        if l.isEmpty then f!"{e}" else f!"[{l}]: {e}"
      let invFmt : Format := f!"[{Format.joinSep invParts f!", "}]"
      let beforeBody := nestD f!"{line}{guard}{line}({measure}){line}{invFmt}"
      let children := group f!"{beforeBody}{line}{body}"
      f!"{md}while{children}"
  | .exit label md => match label with
    | some l => f!"{md}exit {l}"
    | none => f!"{md}exit"
  | .funcDecl _ md => f!"{md}funcDecl <function>"
  | .typeDecl tc md => f!"{md}type {tc.name} (arity {tc.numargs})"

def formatBlock (P : PureExpr) (ss : List (Stmt P C))
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C] : Format :=
    match ss with
    | [] => "{}"
    | parts =>
      let inner := line ++ (group $ joinSep (parts.map (fun s => formatStmt P s)) (format "\n"))
      f!"\{{nestD inner}\n}"
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

/-! ### exitsCoveredByBlocks

`exitsCoveredByBlocks labels s` holds when every `exit` statement in `s` is caught
by an enclosing `block` — either within `s` itself or with a label in
`labels` (representing blocks that enclose `s` externally).

When `s.exitsCoveredByBlocks []`, execution of `s` can never produce `.exiting`.

The labels have type `Option String` (not `String`) so that `exit` without
destination block label can be considered as covered even when it is surrounded
by unlabeled blocks (`[None]`). -/

@[expose] def Stmt.exitsCoveredByBlocks : List (Option String) → Stmt P CmdT → Prop
  | _, .cmd _ => True
  | labels, .block l ss _ => Block.exitsCoveredByBlocks (.some l :: labels) ss
  | labels, .ite _ tss ess _ => Block.exitsCoveredByBlocks labels tss ∧ Block.exitsCoveredByBlocks labels ess
  | labels, .loop _ _ _ body _ => Block.exitsCoveredByBlocks labels body
  | labels, .exit none _ => labels.length > 0
  | labels, .exit (some l) _ => .some l ∈ labels
  | _, .funcDecl _ _ => True
  | _, .typeDecl _ _ => True
where
  Block.exitsCoveredByBlocks : List (Option String) → List (Stmt P CmdT) → Prop
    | _, [] => True
    | labels, s :: ss => Stmt.exitsCoveredByBlocks labels s ∧ Block.exitsCoveredByBlocks labels ss

theorem block_exitsCoveredByBlocks_append
    {P : PureExpr} {CmdT : Type}
    (labels : List (Option String)) (ss₁ ss₂ : List (Stmt P CmdT))
    (h₁ : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss₁)
    (h₂ : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss₂) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels (ss₁ ++ ss₂) := by
  induction ss₁ with
  | nil => exact h₂
  | cons s ss ih => exact ⟨h₁.1, ih h₁.2⟩

/-- `exitsCoveredByBlocks` is monotone in the label list: more covering labels
    can only help. -/
theorem exitsCoveredByBlocks_weaken
    {P : PureExpr} {CmdT : Type}
    (labels₁ labels₂ : List (Option String))
    (hsub : ∀ l, l ∈ labels₁ → l ∈ labels₂) :
    (∀ (s : Stmt P CmdT),
      s.exitsCoveredByBlocks labels₁ → s.exitsCoveredByBlocks labels₂) ∧
    (∀ (ss : List (Stmt P CmdT)),
      Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels₁ ss →
      Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels₂ ss) := by
  suffices hstmt : ∀ (s : Stmt P CmdT),
      ∀ labels₁ labels₂, (∀ l, l ∈ labels₁ → l ∈ labels₂) →
        s.exitsCoveredByBlocks labels₁ → s.exitsCoveredByBlocks labels₂ by
    constructor
    · exact fun s => hstmt s labels₁ labels₂ hsub
    · intro ss
      induction ss with
      | nil => intros; trivial
      | cons s ss ih =>
        exact fun h => ⟨hstmt s _ _ hsub h.1, ih h.2⟩
  intro s
  induction s using Stmt.rec (motive_2 := fun ss =>
    ∀ labels₁ labels₂, (∀ l, l ∈ labels₁ → l ∈ labels₂) →
      Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels₁ ss →
      Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels₂ ss) with
  | cmd _ => intros; trivial
  | block l ss _ ih =>
    intro labels₁ labels₂ hsub h
    show Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (.some l :: labels₂) ss
    exact ih (.some l :: labels₁) (.some l :: labels₂)
      (fun x hx => by cases hx with
        | head => exact .head _
        | tail _ hm => exact .tail _ (hsub x hm))
      h
  | ite _ tss ess _ ih_t ih_e =>
    intro labels₁ labels₂ hsub h
    exact ⟨ih_t labels₁ labels₂ hsub h.1, ih_e labels₁ labels₂ hsub h.2⟩
  | loop _ _ _ body _ ih =>
    intro labels₁ labels₂ hsub h
    exact ih labels₁ labels₂ hsub h
  | exit label _ =>
    intro labels₁ labels₂ hsub h
    cases label with
    | none =>
      show labels₂.length > 0
      exact List.length_pos_iff_exists_mem.mpr
        (let ⟨x, hx⟩ := List.length_pos_iff_exists_mem.mp h; ⟨x, hsub x hx⟩)
    | some l => exact hsub (.some l) h
  | funcDecl _ _ => intros; trivial
  | typeDecl _ _ => intros; trivial
  | nil => intros; trivial
  | cons s ss ih_s ih_ss =>
    rename_i labels₁ labels₂ hsub h
    exact ⟨ih_s labels₁ labels₂ hsub h.1, ih_ss labels₁ labels₂ hsub h.2⟩

/-- If every statement in a list is a `.cmd`, then `exitsCoveredByBlocks` holds
    for any labels (since `.cmd` has no exit statements). -/
theorem all_cmd_exitsCoveredByBlocks
    {P : PureExpr} {CmdT : Type}
    (labels : List (Option String)) (ss : List (Stmt P CmdT))
    (h : ∀ s ∈ ss, ∃ c, s = Stmt.cmd c) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss := by
  induction ss with
  | nil => trivial
  | cons hd tl ih =>
    constructor
    · obtain ⟨c, hc⟩ := h hd (.head _)
      subst hc; exact True.intro
    · exact ih (fun s hs => h s (.tail _ hs))

---------------------------------------------------------------------

end -- public section
end Imperative
