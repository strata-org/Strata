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
  /-- An iterated execution statement. Includes an optional labeled measure
  (for termination) and labeled invariants. When `guard` is `.nondet`, the
  loop iterates a non-deterministic number of times and measure must be none.
  Each invariant and the optional measure carry a label string (expected to be
  distinct, like assert labels do). -/
  | loop     (guard : ExprOrNondet P) (measure : Option (String × P.Expr))
             (invariants : List (String × P.Expr))
             (body : List (Stmt P Cmd)) (md : MetaData P)
  /-- An exit statement that transfers control out of the enclosing block
  with the given label. -/
  | exit     (label : String) (md : MetaData P)
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
    (loop_case : ∀ (guard : ExprOrNondet P) (measure : Option (String × P.Expr)) (invariant : List (String × P.Expr))
      (body : List (Stmt P Cmd)) (md : MetaData P),
      (∀ s, s ∈ body → motive s) →
      motive (Stmt.loop guard measure invariant body md))
    (exit_case : ∀ (label : String) (md : MetaData P),
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
@[simp, expose]
def Stmt.sizeOf (s : Imperative.Stmt P C) : Nat :=
  match s with
  | .cmd c => 1 + SizeOf.sizeOf c
  | .block _ bss _ => 1 + Block.sizeOf bss
  | .ite _ tss ess _ => 3 + Block.sizeOf tss + Block.sizeOf ess
  | .loop _ _ _ bss _ => 3 + Block.sizeOf bss
  | .exit _ _ => 1
  | .funcDecl _ _ => 1
  | .typeDecl _ _ => 1

@[simp, expose]
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

/-! ### MapExpr

Apply a function to all expressions in a statement's structural positions
(guards, measures, invariants). Command-level expressions are mapped by
the caller-supplied `mapCmd` function.
-/

mutual
/-- Apply `fExpr` to structural expressions and `mapCmd` to commands. -/
def Stmt.mapExpr (fExpr : P.Expr → P.Expr) (mapCmd : C → C)
    (s : Stmt P C) : Stmt P C :=
  match s with
  | .cmd c => .cmd (mapCmd c)
  | .block l ss md => .block l (Block.mapExpr fExpr mapCmd ss) md
  | .ite (.det c) tss ess md =>
    .ite (.det (fExpr c)) (Block.mapExpr fExpr mapCmd tss) (Block.mapExpr fExpr mapCmd ess) md
  | .ite .nondet tss ess md =>
    .ite .nondet (Block.mapExpr fExpr mapCmd tss) (Block.mapExpr fExpr mapCmd ess) md
  | .loop (.det g) measure inv body md =>
    .loop (.det (fExpr g)) (measure.map fun (l, e) => (l, fExpr e))
      (inv.map fun (l, e) => (l, fExpr e))
      (Block.mapExpr fExpr mapCmd body) md
  | .loop .nondet measure inv body md =>
    .loop .nondet (measure.map fun (l, e) => (l, fExpr e))
      (inv.map fun (l, e) => (l, fExpr e))
      (Block.mapExpr fExpr mapCmd body) md
  | .exit l md => .exit l md
  | .funcDecl decl md => .funcDecl decl md
  | .typeDecl tc md => .typeDecl tc md
  termination_by (Stmt.sizeOf s)

/-- Apply `fExpr` and `mapCmd` to every statement in a block. -/
def Block.mapExpr (fExpr : P.Expr → P.Expr) (mapCmd : C → C)
    (ss : Block P C) : Block P C :=
  match ss with
  | [] => []
  | s :: rest => Stmt.mapExpr fExpr mapCmd s :: Block.mapExpr fExpr mapCmd rest
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
@[expose]
def Stmt.getVars [HasFvars P] [HasVarsPure P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsPure.getVars cmd
  | .block _ bss _ => Block.getVars bss
  | .ite cond tbss ebss _ => cond.getVars ++ Block.getVars tbss ++ Block.getVars ebss
  | .loop guard measure invariants bss _ =>
    guard.getVars ++
    (measure.map (fun lp => HasFvars.getFvars lp.2)).getD [] ++
    (invariants.flatMap fun lp => HasFvars.getFvars lp.2) ++
    Block.getVars bss
  | .exit _ _  => []
  | .funcDecl decl _ =>
    -- Get free variables from function body and axioms, excluding formal
    -- parameters. Axiom free variables are included because `closureCapture`
    -- (which is invoked by `step_funcDecl`) substitutes them using the
    -- current store at the funcDecl point — so they are read-dependencies
    -- on the surrounding scope, just like body free variables.
    (match decl.body with
      | some body => (HasFvars.getFvars body).filter
          (fun v => (decl.inputs.map (·.1)).all (fun f => !(P.EqIdent v f).decide))
      | none => []) ++
    decl.axioms.flatMap (fun ax => (HasFvars.getFvars ax).filter
      (fun v => (decl.inputs.map (·.1)).all (fun f => !(P.EqIdent v f).decide)))
  | .typeDecl _ _ => []  -- Type declarations don't reference variables

@[expose]
def Block.getVars [HasFvars P] [HasVarsPure P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.getVars s ++ Block.getVars srest
end

instance (P : PureExpr) [HasFvars P] [HasVarsPure P C]
  : HasVarsPure P (Stmt P C) where
  getVars := Stmt.getVars

instance (P : PureExpr) [HasFvars P] [HasVarsPure P C]
  : HasVarsPure P (Block P C) where
  getVars := Block.getVars

mutual
/-- Get all operator/function names referenced by `s`.  Mirrors
    `Stmt.getVars` but collects `.op`-style names (resolved via the evaluator)
    rather than free variables (resolved via the store). -/
@[expose]
def Stmt.getOps [HasOps P] [HasOpsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasOpsImp.getOps cmd
  | .block _ bss _ => Block.getOps bss
  | .ite cond tbss ebss _ =>
    cond.getOps ++ Block.getOps tbss ++ Block.getOps ebss
  | .loop guard measure invariants bss _ =>
    guard.getOps ++
    (measure.map (fun lp => HasOps.getOps (P := P) lp.2)).getD [] ++
    (invariants.flatMap fun lp => HasOps.getOps (P := P) lp.2) ++
    Block.getOps bss
  | .exit _ _  => []
  | .funcDecl decl _ =>
    -- Operator names referenced by the function body and axioms.
    -- (Operator names are global, so no formal-parameter filtering applies.)
    ((decl.body.map (HasOps.getOps (P := P))).getD []) ++
    decl.axioms.flatMap (HasOps.getOps (P := P))
  | .typeDecl _ _ => []

@[expose]
def Block.getOps [HasOps P] [HasOpsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.getOps s ++ Block.getOps srest
end

instance (P : PureExpr) [HasOps P] [HasOpsImp P C]
  : HasOpsImp P (Stmt P C) where
  getOps := Stmt.getOps

instance (P : PureExpr) [HasOps P] [HasOpsImp P C]
  : HasOpsImp P (Block P C) where
  getOps := Block.getOps

mutual
/-- Get all variables defined by the statement `s`. -/
@[simp, expose]
def Stmt.definedVars [HasVarsImp P C] (s : Stmt P C)
    (excludeScoped : Bool) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsImp.definedVars cmd excludeScoped -- excludeScoped doesn't matter
  | .block _ bss _ => if excludeScoped then [] else Block.definedVars bss excludeScoped
  | .ite _ tbss ebss _ =>
    if excludeScoped then [] else Block.definedVars tbss excludeScoped ++ Block.definedVars ebss excludeScoped
  | .loop _ _ _ body _ => if excludeScoped then [] else Block.definedVars body excludeScoped
  -- `step_funcDecl` extends `eval`, leaving `store` unchanged.  `definedVars`
  -- tracks store-level definitions, so funcDecl introduces nothing here; the
  -- name is tracked separately via `Stmt.funcDeclNames`.
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []
  | _ => []

@[simp, expose]
def Block.definedVars [HasVarsImp P C] (ss : Block P C)
    (excludeScoped : Bool) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.definedVars s excludeScoped ++ Block.definedVars srest excludeScoped
end

mutual
/-- Get all variables modified by the statement `s`. -/
@[simp, expose]
def Stmt.modifiedVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsImp.modifiedVars cmd
  | .exit _ _ => []
  | .block _ bss _ => Block.modifiedVars bss
  | .ite _ tbss ebss _ => Block.modifiedVars tbss ++ Block.modifiedVars ebss
  | .loop _ _ _ bss _ => Block.modifiedVars bss
  | .funcDecl _ _ => []  -- Function declarations don't modify variables
  | .typeDecl _ _ => []  -- Type declarations don't modify variables

@[simp, expose]
def Block.modifiedVars [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.modifiedVars s ++ Block.modifiedVars srest
end

/-- Get all variables modified/defined by the statement `s` (the write-set). -/
@[simp, expose]
def Stmt.modifiedOrDefinedVars [HasVarsImp P C] (s : Stmt P C)
    (excludeScoped : Bool): List P.Ident :=
  s.modifiedVars ++ s.definedVars excludeScoped

@[simp, expose]
def Block.modifiedOrDefinedVars [HasVarsImp P C] (ss : Block P C)
    (excludeScoped : Bool): List P.Ident :=
  ss.modifiedVars ++ ss.definedVars excludeScoped

mutual
/-- Get all variables touched (modified, defined, or read) by the statement `s`. -/
@[simp, expose]
def Stmt.touchedVars [HasVarsImp P C] [HasFvars P] [HasVarsPure P C]
    (s : Stmt P C) : List P.Ident :=
  Stmt.modifiedOrDefinedVars s true ++ Stmt.getVars s

@[simp, expose]
def Block.touchedVars [HasVarsImp P C] [HasFvars P] [HasVarsPure P C]
    (ss : Block P C) : List P.Ident :=
  Block.modifiedOrDefinedVars ss true ++ Block.getVars ss
end

mutual
/-- Collect all labeled `exit` targets occurring in a statement (recursive). -/
@[expose] def Stmt.labels (s : Stmt P C) : List String :=
  match s with
  | .exit l _        => [l]
  | .cmd _           => []
  | .block _ bss _   => Block.labels bss
  | .ite _ tss ess _ => Block.labels tss ++ Block.labels ess
  | .loop _ _ _ bss _ => Block.labels bss
  | .funcDecl _ _    => []
  | .typeDecl _ _    => []

/-- Collect all labeled `exit` targets in a list of statements. -/
@[expose] def Block.labels (ss : Block P C) : List String :=
  match ss with
  | []        => []
  | s :: rest => Stmt.labels s ++ Block.labels rest
end

mutual
/-- Collect `decl.name` from `funcDecl` AST nodes in a statement.

    `excludeScoped = false` (the recursive form): collect all `funcDecl`
    names syntactically inside `s`.
    `excludeScoped = true` (the scope-aware form): collect only `funcDecl`
    names introduced at the top level of `s`. Parallel to `Stmt.definedVars _ true`. -/
@[expose] def Stmt.funcDeclNames (s : Stmt P C) (excludeScoped : Bool) : List P.Ident :=
  match s with
  | .funcDecl decl _ => [decl.name]
  | .cmd _           => []
  | .exit _ _        => []
  | .typeDecl _ _    => []
  | .block _ bss _ => if excludeScoped then [] else Block.funcDeclNames bss excludeScoped
  | .ite _ tss ess _ =>
    if excludeScoped then [] else Block.funcDeclNames tss excludeScoped ++
                                  Block.funcDeclNames ess excludeScoped
  | .loop _ _ _ bss _ => if excludeScoped then [] else Block.funcDeclNames bss excludeScoped

/-- Collect `decl.name` from `funcDecl` AST nodes in a block.  See
    `Stmt.funcDeclNames` for the meaning of `excludeScoped`. -/
@[expose] def Block.funcDeclNames (ss : Block P C) (excludeScoped : Bool) : List P.Ident :=
  match ss with
  | []        => []
  | s :: rest => Stmt.funcDeclNames s excludeScoped ++
                 Block.funcDeclNames rest excludeScoped
end

mutual

/-- If a statement contains no function declarations, then `funcDeclNames` is
    empty (for either choice of `excludeScoped`). -/
theorem Stmt.funcDeclNames_eq_nil_of_noFuncDecl
    (s : Stmt P C) (excludeScoped : Bool) (h : Stmt.noFuncDecl s = true) :
    Stmt.funcDeclNames s excludeScoped = [] := by
  match s with
  | .cmd _ => simp [Stmt.funcDeclNames]
  | .exit _ _ => simp [Stmt.funcDeclNames]
  | .typeDecl _ _ => simp [Stmt.funcDeclNames]
  | .funcDecl _ _ => simp [Stmt.noFuncDecl] at h
  | .block _ bss _ =>
    simp [Stmt.noFuncDecl] at h
    cases excludeScoped <;> simp [Stmt.funcDeclNames]
    exact Block.funcDeclNames_eq_nil_of_noFuncDecl bss false h
  | .ite _ tss ess _ =>
    simp [Stmt.noFuncDecl, Bool.and_eq_true] at h
    cases excludeScoped <;> simp [Stmt.funcDeclNames]
    refine ⟨?_, ?_⟩
    · exact Block.funcDeclNames_eq_nil_of_noFuncDecl tss false h.1
    · exact Block.funcDeclNames_eq_nil_of_noFuncDecl ess false h.2
  | .loop _ _ _ body _ =>
    simp [Stmt.noFuncDecl] at h
    cases excludeScoped <;> simp [Stmt.funcDeclNames]
    exact Block.funcDeclNames_eq_nil_of_noFuncDecl body false h

/-- If a block contains no function declarations, then `funcDeclNames` is empty. -/
theorem Block.funcDeclNames_eq_nil_of_noFuncDecl
    (ss : Block P C) (excludeScoped : Bool) (h : Block.noFuncDecl ss = true) :
    Block.funcDeclNames ss excludeScoped = [] := by
  match ss with
  | [] => simp [Block.funcDeclNames]
  | s :: rest =>
    simp [Block.noFuncDecl, Bool.and_eq_true] at h
    simp [Block.funcDeclNames]
    refine ⟨?_, ?_⟩
    · exact Stmt.funcDeclNames_eq_nil_of_noFuncDecl s excludeScoped h.1
    · exact Block.funcDeclNames_eq_nil_of_noFuncDecl rest excludeScoped h.2

end

mutual
/-- Def-use well-formedness check for a statement. Any read/write of a variable
    must be followed by the definition of the var, and fresh var definition must
    not collide with previously defined vars.
    `declaredFuncs` tracks function names introduced by enclosing `funcDecl`s. -/
@[expose] def Stmt.defUseWellFormed [HasVarsImp P C] [HasFvars P] [HasOps P]
    [HasOpsImp P C] [HasVarsPure P C] [DecidableEq P.Ident]
    (definedVars : P.Ident → Bool) (declaredFuncs : P.Ident → Bool)
    (s : Stmt P C) : Bool :=
  match s with
  | .cmd c =>
    (HasVarsPure.getVars (P := P) c).all (fun n => definedVars n) &&
    (HasVarsImp.modifiedVars (P := P) c).all (fun n => definedVars n) &&
    -- All fresh variable names that are being initialized in command c must not
    -- have existed in the already defined vars 'definedVars'. Otherwise, var
    -- initialization in c will stuck due to duplicated name.
    (HasVarsImp.definedVars (P := P) c false).all (fun n => ¬definedVars n) &&
    -- All operator/function names referenced in c must have been declared.
    (HasOpsImp.getOps (P := P) c).all (fun n => declaredFuncs n)
  | .block _ bss _ => Block.defUseWellFormed definedVars declaredFuncs bss
  | .ite cond tbss ebss _ =>
    cond.getVars.all (fun n => definedVars n) &&
    cond.getOps.all (fun n => declaredFuncs n) &&
    Block.defUseWellFormed definedVars declaredFuncs tbss &&
    Block.defUseWellFormed definedVars declaredFuncs ebss
  | .loop guard measure invariants body _ =>
    guard.getVars.all (fun n => definedVars n) &&
    guard.getOps.all (fun n => declaredFuncs n) &&
    ((measure.map (fun lp => HasFvars.getFvars lp.2)).getD []).all (fun n => definedVars n) &&
    ((measure.map (fun lp => HasOps.getOps (P := P) lp.2)).getD []).all
      (fun n => declaredFuncs n) &&
    (invariants.flatMap fun lp => HasFvars.getFvars lp.2).all
      (fun n => definedVars n) &&
    (invariants.flatMap fun lp => HasOps.getOps (P := P) lp.2).all
      (fun n => declaredFuncs n) &&
    Block.defUseWellFormed definedVars declaredFuncs body
  | .exit _ _ => true
  | .funcDecl decl _ =>
    -- Free variables with formals excluded by `Stmt.getVars` must be in `definedVars`.
    (Stmt.getVars (P := P) (C := C) (.funcDecl decl .empty)).all
      (fun n => definedVars n) &&
    -- The function name itself must NOT be in `definedVars`: this is
    -- not a store-level conflict (`step_funcDecl` only updates `eval`),
    -- but the freshness invariant lets us derive that funcDecl-introduced
    -- names are disjoint from variables referenced by surrounding code.
    !definedVars decl.name &&
    -- Operator/function names referenced by the body and axioms must
    -- already be declared.
    (Stmt.getOps (P := P) (C := C) (.funcDecl decl .empty)).all
      (fun n => declaredFuncs n) &&
    -- The new name `decl.name` itself must be fresh against `declaredFuncs`.
    !declaredFuncs decl.name
  | .typeDecl _ _ => true

@[expose] def Block.defUseWellFormed [HasVarsImp P C] [HasFvars P] [HasOps P]
    [HasOpsImp P C] [HasVarsPure P C] [DecidableEq P.Ident]
    (definedVars : P.Ident → Bool) (declaredFuncs : P.Ident → Bool)
    (bss : Block P C) : Bool :=
  match bss with
  | [] => true
  | s :: rest =>
    Stmt.defUseWellFormed definedVars declaredFuncs s &&
      Block.defUseWellFormed
        (fun n => definedVars n || decide (n ∈ Stmt.definedVars s true))
        -- Only top-level `funcDecl` statements add to siblings' `declaredFuncs`;
        -- `funcDecl`s inside nested `.block`/`.ite`/`.loop` are scoped to those
        -- inner constructs (parallel to `Stmt.definedVars _ true`).
        (fun n => declaredFuncs n || decide (n ∈ Stmt.funcDeclNames s true)) rest
end

instance (P : PureExpr) [HasVarsImp P C] : HasVarsImp P (Stmt P C) where
  definedVars := Stmt.definedVars
  modifiedVars := Stmt.modifiedVars

instance (P : PureExpr) [HasVarsImp P C] : HasVarsImp P (Block P C) where
  definedVars := Block.definedVars
  modifiedVars := Block.modifiedVars

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
      let measureFmt : Format := match measure with
        | none => f!"none"
        | some (l, e) => if l.isEmpty then f!"{e}" else f!"[{l}]: {e}"
      let beforeBody := nestD f!"{line}{guard}{line}({measureFmt}){line}{invFmt}"
      let children := group f!"{beforeBody}{line}{body}"
      f!"{md}while{children}"
  | .exit label md => f!"{md}exit {label}"
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

When `s.exitsCoveredByBlocks []`, execution of `s` can never produce `.exiting`. -/

@[expose] def Stmt.exitsCoveredByBlocks : List String → Stmt P CmdT → Prop
  | _, .cmd _ => True
  | labels, .block l ss _ => Block.exitsCoveredByBlocks (l :: labels) ss
  | labels, .ite _ tss ess _ => Block.exitsCoveredByBlocks labels tss ∧ Block.exitsCoveredByBlocks labels ess
  | labels, .loop _ _ _ body _ => Block.exitsCoveredByBlocks labels body
  | labels, .exit l _ => l ∈ labels
  | _, .funcDecl _ _ => True
  | _, .typeDecl _ _ => True
where
  Block.exitsCoveredByBlocks : List String → List (Stmt P CmdT) → Prop
    | _, [] => True
    | labels, s :: ss => Stmt.exitsCoveredByBlocks labels s ∧ Block.exitsCoveredByBlocks labels ss

theorem block_exitsCoveredByBlocks_append
    {P : PureExpr} {CmdT : Type}
    (labels : List String) (ss₁ ss₂ : List (Stmt P CmdT))
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
    (labels₁ labels₂ : List String)
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
    show Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (l :: labels₂) ss
    exact ih (l :: labels₁) (l :: labels₂)
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
  | exit l _ =>
    intro labels₁ labels₂ hsub h
    exact hsub l h
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
    (labels : List String) (ss : List (Stmt P CmdT))
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
