/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd
public import Strata.DL.Lambda.TypeConstructor
public import Strata.Util.ListUtilsProps
public import Std.Data.HashMap
public import Strata.Util.OrderedSet

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
  (expected to be distinct, like assert labels do).
  TODO: invariants and measure will be moved to metadata md, since they don't
  contribute to the small-step semantics (StepStmtE).
  -/
  | loop     (guard : ExprOrNondet P) (measure : Option P.Expr)
             (invariants : List (String × P.Expr))
             (body : List (Stmt P Cmd)) (md : MetaData P)
  /-- An exit statement that transfers control out of the enclosing block
  with the given label. -/
  | exit     (label : String) (md : MetaData P)
  /-- A type declaration within a statement block. -/
  | typeDecl (tc : TypeConstructor) (md : MetaData P)
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
    (ite_case : ∀ (cond : ExprOrNondet P) (thenb elseb : List (Stmt P Cmd)) (md : MetaData P),
      (∀ s, s ∈ thenb → motive s) →
      (∀ s, s ∈ elseb → motive s) →
      motive (Stmt.ite cond thenb elseb md))
    (loop_case : ∀ (guard : ExprOrNondet P) (measure : Option P.Expr) (invariant : List (String × P.Expr))
      (body : List (Stmt P Cmd)) (md : MetaData P),
      (∀ s, s ∈ body → motive s) →
      motive (Stmt.loop guard measure invariant body md))
    (exit_case : ∀ (label : String) (md : MetaData P),
      motive (Stmt.exit label md))
    (typeDecl_case : ∀ (tc : TypeConstructor) (md : MetaData P),
      motive (Stmt.typeDecl tc md))
    (s : Stmt P Cmd) : motive s :=
  match s with
  | Stmt.cmd c => cmd_case c
  | Stmt.block label b md =>
    block_case label b md (fun s _ => inductionOn cmd_case block_case ite_case loop_case exit_case typeDecl_case s)
  | Stmt.ite cond thenb elseb md =>
    ite_case cond thenb elseb md
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case exit_case typeDecl_case s)
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case exit_case typeDecl_case s)
  | Stmt.loop guard measure invariant body md =>
    loop_case guard measure invariant body md
      (fun s _ => inductionOn cmd_case block_case ite_case loop_case exit_case typeDecl_case s)
  | Stmt.exit label md => exit_case label md
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
  | .typeDecl _ _ => 1

@[simp]
def Block.sizeOf (ss : Imperative.Block P C) : Nat :=
  match ss with
  | [] => 1
  | s :: srest => 1 + Stmt.sizeOf s + Block.sizeOf srest

end

---------------------------------------------------------------------

/-! ### DecidableEq -/

variable {P : PureExpr} {C : Type} [DecidableEq C] [DecidableEq P.Expr]
         [DecidableEq P.Ident]

mutual
def Stmt.beq (s1 s2 : Stmt P C) : Bool :=
  match s1, s2 with
  | .cmd c1, .cmd c2 => decide (c1 = c2)
  | .block l1 b1 md1, .block l2 b2 md2 =>
    decide (l1 = l2) && Block.beq b1 b2 && decide (md1 = md2)
  | .ite c1 t1 e1 md1, .ite c2 t2 e2 md2 =>
    decide (c1 = c2) && Block.beq t1 t2 && Block.beq e1 e2 && decide (md1 = md2)
  | .loop g1 m1 inv1 b1 md1, .loop g2 m2 inv2 b2 md2 =>
    decide (g1 = g2) && decide (m1 = m2) && decide (inv1 = inv2) &&
      Block.beq b1 b2 && decide (md1 = md2)
  | .exit l1 md1, .exit l2 md2 => decide (l1 = l2) && decide (md1 = md2)
  | .typeDecl t1 md1, .typeDecl t2 md2 => decide (t1 = t2) && decide (md1 = md2)
  | _, _ => false
  termination_by Stmt.sizeOf s1

def Block.beq (b1 b2 : List (Stmt P C)) : Bool :=
  match b1, b2 with
  | [], [] => true
  | s1 :: r1, s2 :: r2 => Stmt.beq s1 s2 && Block.beq r1 r2
  | _, _ => false
  termination_by Block.sizeOf b1
end

/-- Lift a per-element `beq_eq` (for the statements in `b1`) to the whole block. -/
private theorem Block.beq_eq_of_forall {b1 b2 : List (Stmt P C)}
    (h : ∀ s, s ∈ b1 → ∀ t, Stmt.beq s t = true ↔ s = t) :
    Block.beq b1 b2 = true ↔ b1 = b2 := by
  induction b1 generalizing b2 with
  | nil => cases b2 <;> simp [Block.beq]
  | cons s rest ih =>
    cases b2 with
    | nil => simp [Block.beq]
    | cons s2 rest2 =>
      simp only [Block.beq, Bool.and_eq_true, List.cons.injEq]
      rw [h s (.head _) s2, ih (fun s hs => h s (.tail _ hs))]

theorem Stmt.beq_eq (s t : Stmt P C) : Stmt.beq s t = true ↔ s = t := by
  induction s using Stmt.inductionOn generalizing t with
  | cmd_case c => cases t <;> simp [Stmt.beq]
  | block_case l b md ih =>
    cases t <;> simp only [Stmt.beq, Bool.and_eq_true, decide_eq_true_iff,
      Stmt.block.injEq, reduceCtorEq, Block.beq_eq_of_forall ih] <;> grind
  | ite_case c thn els md iht ihe =>
    cases t <;> simp only [Stmt.beq, Bool.and_eq_true, decide_eq_true_iff,
      Stmt.ite.injEq, reduceCtorEq, Block.beq_eq_of_forall iht,
      Block.beq_eq_of_forall ihe] <;> grind
  | loop_case g m inv b md ih =>
    cases t <;> simp only [Stmt.beq, Bool.and_eq_true, decide_eq_true_iff,
      Stmt.loop.injEq, reduceCtorEq, Block.beq_eq_of_forall ih] <;> grind
  | exit_case l md => cases t <;> simp [Stmt.beq]
  | typeDecl_case tc md => cases t <;> simp [Stmt.beq]

instance : DecidableEq (Stmt P C) :=
  beq_eq_DecidableEq Stmt.beq Stmt.beq_eq

---------------------------------------------------------------------

/-! ### LocalTypeDecls

Collect the type declarations (`typeDecl`) that appear inside a statement or
block, recursing into nested `block` / `ite` / `loop` bodies.
-/

mutual
/-- All type declarations appearing in a statement, including those nested in
    `block` / `ite` / `loop` bodies. -/
@[expose] def Stmt.localTypeDecls (s : Stmt P C) : List TypeConstructor :=
  match s with
  | .cmd _ => []
  | .block _ bss _ => Block.localTypeDecls bss
  | .ite _ tss ess _ => Block.localTypeDecls tss ++ Block.localTypeDecls ess
  | .loop _ _ _ bss _ => Block.localTypeDecls bss
  | .exit _ _ => []
  | .typeDecl tc _ => [tc]
  termination_by (Stmt.sizeOf s)

/-- All type declarations appearing in a block. -/
@[expose] def Block.localTypeDecls (ss : Block P C) : List TypeConstructor :=
  match ss with
  | [] => []
  | s :: srest => Stmt.localTypeDecls s ++ Block.localTypeDecls srest
  termination_by (Block.sizeOf ss)
end

mutual
/-- Does the statement contain any `typeDecl` (recursively through
    `block` / `ite` / `loop` bodies)?  Linear-time short-circuiting predicate;
    prefer this over `Stmt.localTypeDecls.isEmpty` for emptiness checks. -/
@[expose] def Stmt.hasLocalTypeDecl (s : Stmt P C) : Bool :=
  match s with
  | .typeDecl _ _ => true
  | .block _ b _ => Block.hasLocalTypeDecl b
  | .ite _ t e _ => Block.hasLocalTypeDecl t || Block.hasLocalTypeDecl e
  | .loop _ _ _ b _ => Block.hasLocalTypeDecl b
  | .cmd _ | .exit _ _ => false
  termination_by (Stmt.sizeOf s)

/-- Does the block contain any `typeDecl` (recursively)?  Linear-time
    short-circuiting predicate. -/
@[expose] def Block.hasLocalTypeDecl (ss : Block P C) : Bool :=
  match ss with
  | [] => false
  | s :: rest => Stmt.hasLocalTypeDecl s || Block.hasLocalTypeDecl rest
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
    .loop (.det (fExpr g)) (measure.map fExpr) (inv.map fun (l, e) => (l, fExpr e))
      (Block.mapExpr fExpr mapCmd body) md
  | .loop .nondet measure inv body md =>
    .loop .nondet (measure.map fExpr) (inv.map fun (l, e) => (l, fExpr e))
      (Block.mapExpr fExpr mapCmd body) md
  | .exit l md => .exit l md
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

mutual
/-- Monadic `Stmt.mapExpr`: apply `fExpr`/`mapCmd` threading a monad `M`. -/
def Stmt.mapExprM {M : Type → Type} [Monad M] (fExpr : P.Expr → M P.Expr) (mapCmd : C → M C)
    (s : Stmt P C) : M (Stmt P C) := do
  match s with
  | .cmd c => return .cmd (← mapCmd c)
  | .block l ss md => return .block l (← Block.mapExprM fExpr mapCmd ss) md
  | .ite (.det c) tss ess md =>
    return .ite (.det (← fExpr c)) (← Block.mapExprM fExpr mapCmd tss)
      (← Block.mapExprM fExpr mapCmd ess) md
  | .ite .nondet tss ess md =>
    return .ite .nondet (← Block.mapExprM fExpr mapCmd tss) (← Block.mapExprM fExpr mapCmd ess) md
  | .loop (.det g) measure inv body md =>
    return .loop (.det (← fExpr g)) (← measure.mapM fExpr)
      (← inv.mapM (fun (l, e) => return (l, ← fExpr e))) (← Block.mapExprM fExpr mapCmd body) md
  | .loop .nondet measure inv body md =>
    return .loop .nondet (← measure.mapM fExpr)
      (← inv.mapM (fun (l, e) => return (l, ← fExpr e))) (← Block.mapExprM fExpr mapCmd body) md
  | .exit l md => return .exit l md
  | .typeDecl tc md => return .typeDecl tc md
  termination_by (Stmt.sizeOf s)

/-- Monadic `Block.mapExpr`. -/
def Block.mapExprM {M : Type → Type} [Monad M] (fExpr : P.Expr → M P.Expr) (mapCmd : C → M C)
    (ss : Block P C) : M (Block P C) := do
  match ss with
  | [] => return []
  | s :: rest => return (← Stmt.mapExprM fExpr mapCmd s) :: (← Block.mapExprM fExpr mapCmd rest)
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
def Stmt.getVars [HasFvars P] [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsImp.readVars cmd
  | .block _ bss _ => Block.getVars bss
  | .ite cond tbss ebss _ => cond.getVars ++ Block.getVars tbss ++ Block.getVars ebss
  | .loop guard measure invariants bss _ =>
    guard.getVars ++
    (measure.map HasFvars.getFvars).getD [] ++
    (invariants.flatMap fun lp => HasFvars.getFvars lp.2) ++
    Block.getVars bss
  | .exit _ _  => []
  | .typeDecl _ _ => []  -- Type declarations don't reference variables

@[expose]
def Block.getVars [HasFvars P] [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.getVars s ++ Block.getVars srest
end

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
    (measure.map (HasOps.getOps (P := P))).getD [] ++
    (invariants.flatMap fun lp => HasOps.getOps (P := P) lp.2) ++
    Block.getOps bss
  | .exit _ _  => []
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
  | .typeDecl _ _ => []
  | _ => []

@[simp, expose]
def Block.definedVars [HasVarsImp P C] (ss : Block P C)
    (excludeScoped : Bool) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.definedVars s excludeScoped ++ Block.definedVars srest excludeScoped
end

/-- Deep init-variable list of a statement: the variables it defines at any
nesting level.  Definitionally `Stmt.definedVars s false`. -/
@[reducible, expose]
def Stmt.initVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  Stmt.definedVars s false

/-- Deep init-variable list of a block.  Definitionally `Block.definedVars ss false`. -/
@[reducible, expose]
def Block.initVars [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  Block.definedVars ss false

mutual
/-- Deep init-type list of a statement: the declared type of every `init`
    command at any nesting level.  Parallel to `Stmt.definedVars _ false`, but
    collecting the `init` types rather than the names. -/
@[expose]
def Stmt.initTypes [HasInitTypesImp P C] (s : Stmt P C) : List P.Ty :=
  match s with
  | .cmd cmd => HasInitTypesImp.initTypes cmd
  | .block _ bss _ => Block.initTypes bss
  | .ite _ tbss ebss _ => Block.initTypes tbss ++ Block.initTypes ebss
  | .loop _ _ _ body _ => Block.initTypes body
  | .exit _ _ => []
  | .typeDecl _ _ => []

/-- Deep init-type list of a block. -/
@[expose]
def Block.initTypes [HasInitTypesImp P C] (ss : Block P C) : List P.Ty :=
  match ss with
  | [] => []
  | s :: srest => Stmt.initTypes s ++ Block.initTypes srest
end

/-- Every init-type collected from the statement `s` has a `valueOfTy` witness in
    the factory `f`; types absent from `s` need no witness. -/
@[expose]
def Stmt.InitTypesInhabited [HasVal P] [HasInitTypesImp P C] (f : P.Factory) (s : Stmt P C) : Prop :=
  ∀ ty ∈ Stmt.initTypes s, ∃ v, HasVal.valueOfTy f v ty

/-- Every init-type collected from the block `ss` has a `valueOfTy` witness in
    the factory `f`.  See `Stmt.InitTypesInhabited`. -/
@[expose]
def Block.InitTypesInhabited [HasVal P] [HasInitTypesImp P C] (f : P.Factory) (ss : Block P C) : Prop :=
  ∀ ty ∈ Block.initTypes ss, ∃ v, HasVal.valueOfTy f v ty

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
def Stmt.touchedVars [HasVarsImp P C] [HasFvars P]
    (s : Stmt P C) : List P.Ident :=
  Stmt.modifiedOrDefinedVars s true ++ Stmt.getVars s

@[simp, expose]
def Block.touchedVars [HasVarsImp P C] [HasFvars P]
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
  | .typeDecl _ _    => []

/-- Collect all labeled `exit` targets in a list of statements. -/
@[expose] def Block.labels (ss : Block P C) : List String :=
  match ss with
  | []        => []
  | s :: rest => Stmt.labels s ++ Block.labels rest
end

mutual
/-- Def-use well-formedness check for a statement. Any read/write of a variable
    must be preceded by the definition of the var, and fresh var definition must
    not collide with previously defined vars.

    TODO: prove that `Statement.typeCheck` in
    `Strata/Languages/Core/StatementType.lean` guarantees this well-formedness. -/
@[expose] def Stmt.defUseWellFormed [HasVarsImp P C] [HasFvars P] [HasOps P]
    [HasOpsImp P C] [DecidableEq P.Ident]
    (definedVars : P.Ident → Bool) (declaredFuncs : P.Ident → Bool)
    (s : Stmt P C) : Bool :=
  match s with
  | .cmd c =>
    (HasVarsImp.readVars (P := P) c).all (fun n => definedVars n) &&
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
    ((measure.map HasFvars.getFvars).getD []).all (fun n => definedVars n) &&
    ((measure.map (HasOps.getOps (P := P))).getD []).all
      (fun n => declaredFuncs n) &&
    (invariants.flatMap fun lp => HasFvars.getFvars lp.2).all
      (fun n => definedVars n) &&
    (invariants.flatMap fun lp => HasOps.getOps (P := P) lp.2).all
      (fun n => declaredFuncs n) &&
    Block.defUseWellFormed definedVars declaredFuncs body
  | .exit _ _ => true
  | .typeDecl _ _ => true

@[expose] def Block.defUseWellFormed [HasVarsImp P C] [HasFvars P] [HasOps P]
    [HasOpsImp P C] [DecidableEq P.Ident]
    (definedVars : P.Ident → Bool) (declaredFuncs : P.Ident → Bool)
    (bss : Block P C) : Bool :=
  match bss with
  | [] => true
  | s :: rest =>
    Stmt.defUseWellFormed definedVars declaredFuncs s &&
      Block.defUseWellFormed
        (fun n => definedVars n || decide (n ∈ Stmt.definedVars s true))
        declaredFuncs rest
end


/-- Every annotated free-variable occurrence `(x, ty)` in `occs` carries the type `Γ`
    gives `x`. -/
@[expose] def VarTyping.annotates (Γ : VarTyping P)
    (occs : List (P.Ident × P.Ty)) : Prop :=
  ∀ x ty, (x, ty) ∈ occs → Γ x = some ty

/-- The variables the statement `s` defines in the enclosing scope, with their declared
    types: those of a command; a nested block's, branch's or loop body's definitions are
    scoped to it (as in `Stmt.definedVars s true`). -/
@[expose] def Stmt.typedDefinedVars [HasTypedVarsImp P C] : Stmt P C → List (P.Ident × P.Ty)
  | .cmd c => HasTypedVarsImp.typedDefinedVars (P := P) c
  | _ => []

mutual
/-- **Annotation check.**  Every type annotation on a free-variable occurrence in `s` agrees
    with the type of that variable: `Γ` types the variables in scope before `s`, and each
    definition adds its declared type for the statements after it in its scope.  It is a
    proposition about the syntax for a given `Γ`, with no decision procedure here (unlike the
    `Bool` checker `Stmt.defUseWellFormed`); with a typing of the entry store
    (`StoreHasTyping`) it says the annotations agree with the types of the stored values. -/
@[expose] def Stmt.fvarTypesWellAnnotated [HasTypedVarsImp P C] [HasFvars P]
    (Γ : VarTyping P) (s : Stmt P C) : Prop :=
  match s with
  | .cmd c => Γ.annotates (HasTypedVarsImp.typedReadVars (P := P) c)
  | .block _ bss _ => Block.fvarTypesWellAnnotated Γ bss
  | .ite cond tbss ebss _ =>
    Γ.annotates cond.getTypedVars ∧
    Block.fvarTypesWellAnnotated Γ tbss ∧
    Block.fvarTypesWellAnnotated Γ ebss
  | .loop guard measure invariants body _ =>
    Γ.annotates guard.getTypedVars ∧
    Γ.annotates ((measure.map HasFvars.getTypedFvars).getD []) ∧
    Γ.annotates (invariants.flatMap fun lp => HasFvars.getTypedFvars lp.2) ∧
    Block.fvarTypesWellAnnotated Γ body
  | .exit _ _ => True
  | .typeDecl _ _ => True

/-- `Stmt.fvarTypesWellAnnotated` over a list of statements, each checked with the
    definitions of the statements before it added to `Γ`. -/
@[expose] def Block.fvarTypesWellAnnotated [HasTypedVarsImp P C] [HasFvars P]
    (Γ : VarTyping P) (bss : Block P C) : Prop :=
  match bss with
  | [] => True
  | s :: rest =>
    Stmt.fvarTypesWellAnnotated Γ s ∧
      Block.fvarTypesWellAnnotated (Γ.extend (Stmt.typedDefinedVars s)) rest
end

instance (P : PureExpr) [HasFvars P] [HasVarsImp P C] : HasVarsImp P (Stmt P C) where
  definedVars := Stmt.definedVars
  modifiedVars := Stmt.modifiedVars
  readVars := Stmt.getVars

instance (P : PureExpr) [HasFvars P] [HasVarsImp P C] : HasVarsImp P (Block P C) where
  definedVars := Block.definedVars
  modifiedVars := Block.modifiedVars
  readVars := Block.getVars

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
        | some e => f!"some {e}"
      let beforeBody := nestD f!"{line}{guard}{line}({measureFmt}){line}{invFmt}"
      let children := group f!"{beforeBody}{line}{body}"
      f!"{md}while{children}"
  | .exit label md => f!"{md}exit {label}"
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

mutual
@[expose] def Stmt.exitsCoveredByBlocks : List String → Stmt P CmdT → Prop
  | _, .cmd _ => True
  | labels, .block l ss _ => Block.exitsCoveredByBlocks (l :: labels) ss
  | labels, .ite _ tss ess _ => Block.exitsCoveredByBlocks labels tss ∧ Block.exitsCoveredByBlocks labels ess
  | labels, .loop _ _ _ body _ => Block.exitsCoveredByBlocks labels body
  | labels, .exit l _ => l ∈ labels
  | _, .typeDecl _ _ => True

@[expose] def Block.exitsCoveredByBlocks : List String → List (Stmt P CmdT) → Prop
  | _, [] => True
  | labels, s :: ss => Stmt.exitsCoveredByBlocks labels s ∧ Block.exitsCoveredByBlocks labels ss

end

mutual
/-- Executable check for `Stmt.exitsCoveredByBlocks`; `Block.exitsCoveredByBlocks_of_check`
in `StmtProps` proves it sound. -/
@[expose] def Stmt.checkExitsCoveredByBlocks : List String → Stmt P CmdT → Bool
  | _, .cmd _ => true
  | labels, .block l ss _ => Block.checkExitsCoveredByBlocks (l :: labels) ss
  | labels, .ite _ tss ess _ =>
    Block.checkExitsCoveredByBlocks labels tss && Block.checkExitsCoveredByBlocks labels ess
  | labels, .loop _ _ _ body _ => Block.checkExitsCoveredByBlocks labels body
  | labels, .exit l _ => decide (l ∈ labels)
  | _, .typeDecl _ _ => true

/-- Executable check for `Block.exitsCoveredByBlocks`. -/
@[expose] def Block.checkExitsCoveredByBlocks : List String → List (Stmt P CmdT) → Bool
  | _, [] => true
  | labels, s :: ss =>
    Stmt.checkExitsCoveredByBlocks labels s && Block.checkExitsCoveredByBlocks labels ss

end
---------------------------------------------------------------------


---------------------------------------------------------------------
-- S2U pipeline syntactic helpers: pure functions on Stmt/Block/Cmd.
---------------------------------------------------------------------

/-! ### UniqueInits

Collect the names of every variable initialized by an `init` command anywhere
in a statement (across all nesting levels). The companion predicate
`Block.uniqueInits` asserts that the resulting list is `Nodup`, ruling out
the edge case where a name is projected away by `step_block_done` and then
reinitialized — a pattern the unstructured CFG cannot replicate because its
flat namespace has no projection.
-/

/-- Every `init` in the program (across all nesting levels) names a unique
variable. The flat-namespace CFG can simulate the structured semantics only
when this holds — without uniqueness, structured `step_block_done` can
project a name away that the structured semantics later reinitializes, a
pattern the CFG cannot replicate. This analysis is command-generic: it uses
only the command type's `HasVarsImp` instance. -/
@[expose] def Block.uniqueInits [HasVarsImp P C] (ss : List (Stmt P C)) : Prop :=
  (Block.initVars ss).Nodup

---------------------------------------------------------------------

/-! ### NoNondetGuards

Predicate stating that no `.ite` or `.loop` guard in a statement or block is
`.nondet`, at any nesting depth. Two consumers need it: the
structured-to-CFG soundness proof under axiom-free assumptions, and symbolic
evaluation, which rejects a nondeterministic guard outright. Nondet
elimination is what replaces such a guard with a fresh boolean and a
deterministic branch.

Only guards are read, so the predicate is stated for any command type, and
`.ite (.det _)`, `.block`, sequential `.cmd`s, `.exit`, and `.typeDecl` are all admitted. The auxiliary predicates `loopBodyNoInits`,
`loopHasNoInvariants` and `noMeasureLoops` defined below restrict loops
further for the proof's scope: no body-local variable inits, no labeled
invariants, no termination measure.
-/

mutual
/-- Returns true if no guard in `s` is nondeterministic, at any nesting depth. -/
@[expose] def Stmt.noNondetGuards (s : Stmt P C) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.noNondetGuards bss
  | .ite (.det _) tss ess _ => Block.noNondetGuards tss && Block.noNondetGuards ess
  | .ite .nondet _ _ _ => false
  | .loop guard _ _ bss _ =>
    (match guard with | .det _ => true | .nondet => false) && Block.noNondetGuards bss
  | .exit _ _ => true
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Is every guard in `ss` deterministic, at any nesting depth? -/
@[expose] def Block.noNondetGuards (ss : List (Stmt P C)) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.noNondetGuards s && Block.noNondetGuards srest
  termination_by (Block.sizeOf ss)
end

/-!
`transportShape` is a second walker, finer than `noNondetGuards`: it carves out
the fragment the loop-init hoist pass's body simulation can express (the same-name
`StoreAgreement` body simulation in `Strata.Transform.LoopInitHoistCorrect`).
Unlike `noNondetGuards`, which treats every `.cmd _` alike, `transportShape` inspects
the command — `init`/`set` are admitted with either a `.det` or `.nondet` rhs, and it admits a nested `.loop` only when it is
measure-free, invariant-free, and `.det`-guarded (`.loop (.det _) none [] _`).
-/
mutual
@[expose] def Stmt.transportShape (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd (.init _ _ (.det _) _) => true
  | .cmd (.init _ _ .nondet _) => true
  | .cmd (.set _ (.det _) _) => true
  | .cmd (.set _ .nondet _) => true
  | .cmd (.assert _ _ _) => true
  | .cmd (.assume _ _ _) => true
  | .cmd (.cover _ _ _) => true
  | .block _ bss _ => Block.transportShape bss
  | .ite (.det _) tss ess _ => Block.transportShape tss && Block.transportShape ess
  | .ite .nondet tss ess _ => Block.transportShape tss && Block.transportShape ess
  | .loop (.det _) none [] lbody _ => Block.transportShape lbody
  | .loop _ _ _ _ _ => false
  | .exit _ _ => true
  | .typeDecl _ _ => true
  termination_by sizeOf s

@[expose] def Block.transportShape (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: rest => Stmt.transportShape s && Block.transportShape rest
  termination_by sizeOf ss
end


---------------------------------------------------------------------

/-! ### LoopBodyNoInits

Predicate stating that every `.loop _ _ _ bss _` reachable inside a
statement (or block) has `Block.initVars bss = []`. Used by the
structured-to-CFG soundness proof: the CFG flat namespace cannot
re-execute body inits at iteration ≥ 2, so we restrict to loops whose
body declares no local variables.
-/

mutual
/-- Returns true if every reachable loop's body declares no local vars. -/
@[expose] def Stmt.loopBodyNoInits [HasVarsImp P C] (s : Stmt P C) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.loopBodyNoInits bss
  | .ite _ tss ess _ => Block.loopBodyNoInits tss && Block.loopBodyNoInits ess
  | .loop _ _ _ bss _ =>
      (Block.initVars bss).isEmpty && Block.loopBodyNoInits bss
  | .exit _ _ => true
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Block-level lifting of `Stmt.loopBodyNoInits`. -/
@[expose] def Block.loopBodyNoInits [HasVarsImp P C] (ss : List (Stmt P C)) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.loopBodyNoInits s && Block.loopBodyNoInits srest
  termination_by (Block.sizeOf ss)
end


---------------------------------------------------------------------

/-! ### AllSubstmts

Lifts a predicate on a single statement to "holds of this statement and of
every statement nested inside it", so a shape property that only inspects one
statement's own form needs no traversal of its own.
-/

mutual
/-- Does `f` hold of `s` and of every statement nested inside it? -/
@[expose] def Stmt.allSubstmts (f : Stmt P C → Bool) (s : Stmt P C) : Bool :=
  f s &&
  match s with
  | .block _ bss _ => Block.allSubstmts f bss
  | .ite _ tss ess _ => Block.allSubstmts f tss && Block.allSubstmts f ess
  | .loop _ _ _ bss _ => Block.allSubstmts f bss
  | .cmd _ | .exit _ _ | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Does `f` hold of every statement in `ss`, including nested ones? -/
@[expose] def Block.allSubstmts (f : Stmt P C → Bool) (ss : List (Stmt P C)) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.allSubstmts f s && Block.allSubstmts f srest
  termination_by (Block.sizeOf ss)
end

---------------------------------------------------------------------

/-! ### NoLoops

Predicate stating that no `.loop` occurs anywhere in a statement (or block).
Symbolic evaluation needs this: it rejects a `loop`, which is what loop
elimination removes.
-/

@[expose] def Stmt.isNotLoop (s : Stmt P C) : Bool :=
  match s with
  | .loop _ _ _ _ _ => false
  | _ => true

/-- Does `s` contain no loop, at any nesting depth? -/
@[expose] def Stmt.noLoops (s : Stmt P C) : Bool :=
  Stmt.allSubstmts Stmt.isNotLoop s

/-- Does `ss` contain no loop, at any nesting depth? -/
@[expose] def Block.noLoops (ss : List (Stmt P C)) : Bool :=
  Block.allSubstmts Stmt.isNotLoop ss

---------------------------------------------------------------------

/-! ### LoopHasNoInvariants

Predicate stating that every `.loop _ _ is _ _` reachable inside a
statement (or block) has `is = []` (no labeled invariants). Used by
the structured-to-CFG soundness proof to collapse the assert-chain
at the loop entry block to empty.
-/

mutual
/-- Returns true if every reachable loop has no invariants. -/
@[expose] def Stmt.loopHasNoInvariants (s : Stmt P C) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.loopHasNoInvariants bss
  | .ite _ tss ess _ => Block.loopHasNoInvariants tss && Block.loopHasNoInvariants ess
  | .loop _ _ is bss _ =>
      is.isEmpty && Block.loopHasNoInvariants bss
  | .exit _ _ => true
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Block-level lifting of `Stmt.loopHasNoInvariants`. -/
@[expose] def Block.loopHasNoInvariants (ss : List (Stmt P C)) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.loopHasNoInvariants s && Block.loopHasNoInvariants srest
  termination_by (Block.sizeOf ss)
end


---------------------------------------------------------------------

/-! ### NoMeasureLoops

Predicate stating that every `.loop _ m _ _ _` reachable inside a
statement (or block) has `m = .none` (no termination measure). Used
by the structured-to-CFG soundness proof to collapse the
`measure_lb` / `measure_decrease` blocks in the translator's loop
CFG layout.
-/

mutual
/-- Returns true if every reachable loop has no termination measure. -/
@[expose] def Stmt.noMeasureLoops (s : Stmt P C) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.noMeasureLoops bss
  | .ite _ tss ess _ => Block.noMeasureLoops tss && Block.noMeasureLoops ess
  | .loop _ m _ bss _ =>
      m.isNone && Block.noMeasureLoops bss
  | .exit _ _ => true
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Block-level lifting of `Stmt.noMeasureLoops`. -/
@[expose] def Block.noMeasureLoops (ss : List (Stmt P C)) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.noMeasureLoops s && Block.noMeasureLoops srest
  termination_by (Block.sizeOf ss)
end


---------------------------------------------------------------------

/-! ### NoBlocks

A boolean predicate asserting that a statement (or block) contains no
`.block` constructor anywhere in its tree. Used by the structured-to-CFG
correctness proof to identify subprograms whose CFG end-store is exactly
the structured end-store (no projection occurs).
-/

mutual
/-- Returns true if the statement contains no `.block` constructor. -/
@[expose] def Stmt.noBlocks (s : Stmt P C) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ _ _ => false
  | .ite _ tss ess _ => Block.noBlocks tss && Block.noBlocks ess
  | .loop _ _ _ bss _ => Block.noBlocks bss
  | .exit _ _ => true
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Returns true if the block contains no `.block` constructor. -/
@[expose] def Block.noBlocks (ss : Block P C) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.noBlocks s && Block.noBlocks srest
  termination_by (Block.sizeOf ss)
end


/-! ### NoInitsAnywhere -/

mutual
/-- Returns true if the statement contains no `.init` command anywhere. -/
@[expose] def Stmt.noInitsAnywhere (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd (.init _ _ _ _) => false
  | .cmd _ => true
  | .block _ bss _ => Block.noInitsAnywhere bss
  | .ite _ tss ess _ => Block.noInitsAnywhere tss && Block.noInitsAnywhere ess
  | .loop _ _ _ bss _ => Block.noInitsAnywhere bss
  | .exit _ _ => true
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Returns true if the block contains no `.init` command anywhere. -/
@[expose] def Block.noInitsAnywhere (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.noInitsAnywhere s && Block.noInitsAnywhere srest
  termination_by (Block.sizeOf ss)
end

/-! ### IsInitCmd helper -/

/-- Helper: a statement is `.cmd (.init ...)`. Useful for the hoisting
pass's per-statement classification (`liftInitsInLoopBody`). -/
@[expose] def Stmt.isInitCmd (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd (.init _ _ _ _) => true
  | _ => false

/-! ### ContainsNondetLoop

This predicate flags nondeterministic loops, which the deterministic
trace-inversion swap lemma cannot admit without additional `WFCongr` API.
-/

mutual
/-- Returns true if the statement contains a `.loop _ .nondet ...` somewhere. -/
@[expose] def Stmt.containsNondetLoop (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd _ => false
  | .block _ bss _ => Block.containsNondetLoop bss
  | .ite _ tss ess _ => Block.containsNondetLoop tss || Block.containsNondetLoop ess
  | .loop guard _ _ bss _ =>
      match guard with
      | .nondet => true
      | .det _ => Block.containsNondetLoop bss
  | .exit _ _ => false
  | .typeDecl _ _ => false
  termination_by (Stmt.sizeOf s)

/-- Returns true if any statement in `ss` contains a nondet loop. -/
@[expose] def Block.containsNondetLoop (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => false
  | s :: srest =>
      Stmt.containsNondetLoop s || Block.containsNondetLoop srest
  termination_by (Block.sizeOf ss)
end


/-! ## `getBlockLabels`

`getBlockLabels` collects all user-provided `Stmt.block` labels appearing in a
list of statements. The command type `C` is left abstract: `getBlockLabels`
never inspects a command, so this applies uniformly to the pipeline's
`Imperative.Cmd`-bodied statement lists and to extended command types. -/

@[expose] def Block.getBlockLabels {P : PureExpr} {C : Type} :
    List (Stmt P C) → List String
  | [] => []
  | s :: rest => stmtGetBlockLabels s ++ Block.getBlockLabels rest
where
  stmtGetBlockLabels : Stmt P C → List String
    | .block l ss _ => l :: Block.getBlockLabels ss
    | .ite _ tss ess _ => Block.getBlockLabels tss ++ Block.getBlockLabels ess
    | .loop _ _ _ ss _ => Block.getBlockLabels ss
    | _ => []


/-! ## Strengthened freshness predicate `namesFreshInExprs`

Parametric form: "every `names` element is fresh in every cmd
expression / loop guard / inv / measure at any depth in `s`".

The predicate is MONOTONE in `names`'s subset relation (smaller names
list = weaker requirement). It checks freshness at every expression
position — command RHS, loop/ite guard, invariant, and measure.

Each leaf freshness condition "`names` avoids `vars`" is expressed as
`List.Disj names vars` (i.e. `∀ z ∈ names, z ∉ vars`). -/

/-- "names is fresh in s": no name `z ∈ names` appears in any read position
(cmd expression, loop guard, invariant, or measure) at any depth in `s`.  This is
exactly disjointness from `s`'s read-var set `Stmt.getVars s`. -/
@[expose] def Stmt.namesFreshInExprs {P : PureExpr} [HasFvars P]
    (names : List P.Ident) (s : Stmt P (Cmd P)) : Prop :=
  List.Disj names (Stmt.getVars s)

/-- "names is fresh in ss": disjointness from the block's read-var set. -/
@[expose] def Block.namesFreshInExprs {P : PureExpr} [HasFvars P]
    (names : List P.Ident) (ss : List (Stmt P (Cmd P))) : Prop :=
  List.Disj names (Block.getVars ss)

/-! ## RHS-only freshness predicate `namesFreshInRhsExprs`

A relaxation of `namesFreshInExprs` that checks freshness only against
command *right-hand-side* expressions (`init`/`set` rhs, assertion / assume /
cover conditions) at every depth, but NOT against `.ite`/`.loop` *guard*,
invariant, or measure expressions.

The RHS-only form is load-bearing: `nondetElim` reads its own fresh guard
`$__ndelim_loop$_0` in a guard position, so a freshness-preservation result for
`nondetElim` requires the predicate to NOT check guards. -/

mutual

/-- "names is fresh in every command RHS of `s`": every `z ∈ names` is absent
from each `init`/`set` rhs and each `assert`/`assume`/`cover` condition at any
depth in `s`, with `.ite`/`.loop` recursing into branches/body only (the
guard/invariant/measure read positions are NOT checked). -/
@[expose] def Stmt.namesFreshInRhsExprs {P : PureExpr} [HasFvars P]
    (names : List P.Ident) (s : Stmt P (Cmd P)) : Prop :=
  match s with
  | .cmd (.init _ _ rhs _) => List.Disj names (ExprOrNondet.getVars rhs)
  | .cmd (.set _ rhs _) => List.Disj names (ExprOrNondet.getVars rhs)
  | .cmd (.assert _ e _) => List.Disj names (HasFvars.getFvars e)
  | .cmd (.assume _ e _) => List.Disj names (HasFvars.getFvars e)
  | .cmd (.cover _ e _) => List.Disj names (HasFvars.getFvars e)
  | .block _ bss _ => Block.namesFreshInRhsExprs names bss
  | .ite _ tss ess _ =>
    Block.namesFreshInRhsExprs names tss ∧ Block.namesFreshInRhsExprs names ess
  | .loop _ _ _ body _ =>
    Block.namesFreshInRhsExprs names body
  | .exit _ _ => True
  | .typeDecl _ _ => True
  termination_by sizeOf s

/-- Block-level RHS-only freshness, lifted pointwise across the block. -/
@[expose] def Block.namesFreshInRhsExprs {P : PureExpr} [HasFvars P]
    (names : List P.Ident) (ss : List (Stmt P (Cmd P))) : Prop :=
  match ss with
  | [] => True
  | s :: rest =>
    Stmt.namesFreshInRhsExprs names s ∧ Block.namesFreshInRhsExprs names rest
  termination_by sizeOf ss

end

/-- The freshness predicate the hoisting pass requires: RHS-only freshness
for the body's own init-vars. It uses `namesFreshInRhsExprs` (not the full
`namesFreshInExprs`): the hoisting preservation proof reads back only the
RHS / body-recursion parts of this conjunct. -/
@[expose] def Block.hoistedNamesFreshInRhsAndGuards {P : PureExpr} [HasFvars P]
    (ss : List (Stmt P (Cmd P))) : Prop :=
  Block.namesFreshInRhsExprs (Block.initVars ss) ss

/-! ## Expression shape-freedom predicate `exprsShapeFree`

A front-end well-formedness assumption on a source program: every variable
read by any expression occurring in the program — `init`/`set` rhs, `assert`
/`assume`/`cover` conditions, loop guards/measures/invariants, `.ite` guards
— is a "kind-free" name: it never satisfies the *kind predicate* `Q` on the
underlying label string (the kind of name a pass generates). -/

/-- "Every read-var occurring in `s` is kind-free": no variable read by `s`
is the identifier of a `Q`-kind label string.  Expressed directly over
`Stmt.getVars` (the read-var collector). -/
@[expose] def Stmt.exprsShapeFree {P : PureExpr} [HasIdent P] [HasFvars P]
    (Q : String → Prop)
    (s : Stmt P (Cmd P)) : Prop :=
  ∀ str : String, Q str → HasIdent.ident (P := P) str ∉ Stmt.getVars s

/-- "Every read-var occurring in `ss` is kind-free": expressed directly over
`Block.getVars` (the read-var collector). -/
@[expose] def Block.exprsShapeFree {P : PureExpr} [HasIdent P] [HasFvars P]
    (Q : String → Prop)
    (ss : List (Stmt P (Cmd P))) : Prop :=
  ∀ str : String, Q str → HasIdent.ident (P := P) str ∉ Block.getVars ss

/-! ## Identifiers, statement order and scoping

Over statements whose commands are `CmdExt P`: every identifier a statement list mentions
(`Stmt.idents`, `Block.idents`: binders and free variables); two conditions on the order of
statements: a nondeterministic `ite` is the last statement of its list
(`Block.nondetIteLast`) and only `assert`s and `cover`s follow an `assert`
(`Block.onlyChecksAfterAssert`); and the condition that every statement reads only names
defined before it, with no re-initialization (`Block.readsDefined`).

The order conditions restrict no statement kind; `Core.Statements.hasObligationForm`, which
restricts *which* statements occur, says nothing about their order or about scoping. -/

/-- A check: an `assert` or a `cover`. -/
@[expose] def Stmt.isCheck {P : PureExpr} : Stmt P (CmdExt P) → Bool
  | .cmd (.cmd (.assert _ _ _)) | .cmd (.cmd (.cover _ _ _)) => true
  | _ => false

mutual
/-- Every identifier occurring in a statement (binders and free variables). -/
@[expose] def Stmt.idents {P : PureExpr} [HasFvars P] : Stmt P (CmdExt P) → List P.Ident
  | .cmd (.cmd (.init x _ (.det e) _)) | .cmd (.cmd (.set x (.det e) _)) =>
    x :: HasFvars.getFvars e
  | .cmd (.cmd (.init x _ .nondet _)) | .cmd (.cmd (.set x .nondet _)) => [x]
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    HasFvars.getFvars e
  | .cmd (.call _ args _) =>
    (CallArg.getInArgs args).flatMap HasFvars.getFvars ++ CallArg.getLhs args
  | .block _ ss _ => Block.idents ss
  | .ite c tss ess _ => c.getVars ++ Block.idents tss ++ Block.idents ess
  | .loop g m inv body _ =>
    g.getVars ++ (m.map HasFvars.getFvars).getD [] ++ inv.flatMap (HasFvars.getFvars ·.2) ++
      Block.idents body
  | .exit _ _ | .typeDecl _ _ => []
/-- Every identifier occurring in a statement list (binders and free variables). -/
@[expose] def Block.idents {P : PureExpr} [HasFvars P] :
    List (Stmt P (CmdExt P)) → List P.Ident
  | [] => []
  | s :: rest => Stmt.idents s ++ Block.idents rest
end

/-- Every nondeterministic `.ite` is the last statement of its list, checked in the branches
    of nondeterministic `.ite`s too (not inside blocks, loops or deterministic `.ite`s).
    It allows every statement kind and constrains only where a nondeterministic `.ite` may
    stand. -/
@[expose] def Block.nondetIteLast {P : PureExpr} : Block P (CmdExt P) → Bool
  | [] => true
  | (.ite .nondet thenSs elseSs _) :: rest =>
      rest.isEmpty && Block.nondetIteLast thenSs && Block.nondetIteLast elseSs
  | _ :: rest => Block.nondetIteLast rest

/-- Every `.assert` is followed in its list only by `assert`s and `cover`s, checked in the
    branches of every `.ite` too (not inside blocks or loops). It allows every statement kind
    before an `assert` and constrains only what may follow one. -/
@[expose] def Block.onlyChecksAfterAssert {P : PureExpr} : Block P (CmdExt P) → Bool
  | [] => true
  | (.cmd (.cmd (.assert _ _ _))) :: rest => rest.all Stmt.isCheck
  | (.ite _ thenSs elseSs _) :: rest =>
      Block.onlyChecksAfterAssert thenSs && Block.onlyChecksAfterAssert elseSs &&
        Block.onlyChecksAfterAssert rest
  | _ :: rest => Block.onlyChecksAfterAssert rest

/-- Is the list in tree form: only `init`, `set`, `assume`, `assert`, `cover` and `ite *`, every
    `ite *` the last statement of its list? This is the shape of the guarded programs the WP phase
    produces, and the form `Core.Statements.treeForm` checks. -/
@[expose] def Block.treeForm {P : PureExpr} : Block P (CmdExt P) → Bool
  | [] => true
  | .cmd (.cmd (.init _ _ _ _)) :: rest | .cmd (.cmd (.set _ _ _)) :: rest
  | .cmd (.cmd (.assume _ _ _)) :: rest | .cmd (.cmd (.assert _ _ _)) :: rest
  | .cmd (.cmd (.cover _ _ _)) :: rest => Block.treeForm rest
  | .ite .nondet t e _ :: rest => rest.isEmpty && Block.treeForm t && Block.treeForm e
  | _ :: _ => false
  termination_by ss => sizeOf ss

/-- Is the list passive: only `init`, `assume`, `assert`, `cover` and `ite *`, no assignment? This
    is the shape of the obligation programs the SSA phase produces, and the form
    `Core.Statements.hasObligationForm` checks. -/
@[expose] def Block.passiveForm {P : PureExpr} : Block P (CmdExt P) → Bool
  | [] => true
  | .cmd (.cmd (.init _ _ _ _)) :: rest | .cmd (.cmd (.assume _ _ _)) :: rest
  | .cmd (.cmd (.assert _ _ _)) :: rest | .cmd (.cmd (.cover _ _ _)) :: rest =>
    Block.passiveForm rest
  | .ite .nondet t e _ :: rest =>
    Block.passiveForm t && Block.passiveForm e && Block.passiveForm rest
  | _ :: _ => false
  termination_by ss => sizeOf ss

/-- Store-independent well-scopedness: threading the set of names defined so far
    (`defined`), the free variables of every `init` value, `assume`, `assert` and `cover`
    are already defined, and each `.init` adds its binder and requires it not to be defined
    yet. Both branches of a nondeterministic `.ite` are checked from the pre-branch `defined`
    set, and the statements after it are not checked; other statements are skipped. -/
@[expose] def Block.readsDefined {P : PureExpr} [BEq P.Ident] [HasFvars P]
    (defined : List P.Ident) : Block P (CmdExt P) → Bool
  | [] => true
  | (.cmd (.cmd (.init name _ (.det e) _))) :: rest =>
      !defined.contains name &&
      (HasFvars.getFvars e).all (fun x => defined.contains x) &&
        Block.readsDefined (name :: defined) rest
  | (.cmd (.cmd (.init name _ .nondet _))) :: rest =>
      !defined.contains name &&
        Block.readsDefined (name :: defined) rest
  | (.cmd (.cmd (.assume _ e _))) :: rest =>
      (HasFvars.getFvars e).all (fun x => defined.contains x) &&
        Block.readsDefined defined rest
  | (.cmd (.cmd (.assert _ e _))) :: rest =>
      (HasFvars.getFvars e).all (fun x => defined.contains x) &&
        Block.readsDefined defined rest
  | (.cmd (.cmd (.cover _ e _))) :: rest =>
      (HasFvars.getFvars e).all (fun x => defined.contains x) &&
        Block.readsDefined defined rest
  | (.ite .nondet thenSs elseSs _) :: _ =>
      Block.readsDefined defined thenSs && Block.readsDefined defined elseSs
  | _ :: rest => Block.readsDefined defined rest

/-! ## Free, assigned and checked variables

Syntactic analyses of statement lists over `CmdExt P` commands: free variables respecting the
scope of `init` (`exprFV`, `Block.freeVars`), assigned variables (`Block.assignedVars`), whether
an `exit` or a check occurs (`Block.hasExit`, `Block.hasCheck`), and whether every arm of every
`ite` contains a check (`Block.armsHaveChecks`).

`Block.freeVars` and `Block.assignedVars` are specified by recursions that copy or filter lists;
`Block.freeVarsH` and `Block.assignedVarsH` compute them linearly, with an accumulator and, for
scopes, a hash map (proved equal in `StmtProps`). -/

section FreeVars

variable {P : PureExpr} [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [HasFvars P]

/-- Free variables of an expression, without duplicates (the first occurrence of each kept). -/
@[expose] def exprFV {P : PureExpr} [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident]
    [HasFvars P] (e : P.Expr) : List P.Ident :=
  Strata.Util.OrderedSet.eraseDups (HasFvars.getFvars e)

mutual
/-- Free (read) variables of a statement list, respecting `init` binding within a
    list (a block/branch scopes its inits). -/
@[expose] def Block.freeVars : Block P (CmdExt P) → List P.Ident
  | [] => []
  | s :: rest =>
    match s with
    | .cmd (.cmd (.init x _ e _)) =>
      (match e with | .det e => exprFV e | .nondet => []) ++ (Block.freeVars rest).filter (· != x)
    | _ => Stmt.freeVars s ++ Block.freeVars rest
/-- Free (read) variables of a statement. -/
@[expose] def Stmt.freeVars : Stmt P (CmdExt P) → List P.Ident
  | .cmd (.cmd (.init _ _ (.det e) _)) => exprFV e
  | .cmd (.cmd (.init _ _ .nondet _)) => []
  | .cmd (.cmd (.set x (.det e) _)) => x :: exprFV e
  | .cmd (.cmd (.set x .nondet _)) => [x]
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    exprFV e
  | .cmd (.call _ _ _) => []
  | .block _ ss _ => Block.freeVars ss
  | .ite c tss ess _ =>
    (match c with | .det c => exprFV c | .nondet => []) ++ Block.freeVars tss ++ Block.freeVars ess
  | .loop _ _ _ body _ => Block.freeVars body
  | .exit _ _ | .typeDecl _ _ => []
end

mutual
/-- Variables assigned (by `init` or `set`) anywhere in a statement list. -/
@[expose] def Block.assignedVars : Block P (CmdExt P) → List P.Ident
  | [] => []
  | s :: rest => Stmt.assignedVars s ++ Block.assignedVars rest
/-- Variables assigned (by `init` or `set`) anywhere in a statement. -/
@[expose] def Stmt.assignedVars : Stmt P (CmdExt P) → List P.Ident
  | .cmd (.cmd (.init x _ _ _)) | .cmd (.cmd (.set x _ _)) => [x]
  | .block _ ss _ => Block.assignedVars ss
  | .ite _ tss ess _ => Block.assignedVars tss ++ Block.assignedVars ess
  | .loop _ _ _ body _ => Block.assignedVars body
  | _ => []
end

mutual
/-- Does the statement list contain an `exit`, at any depth? -/
@[expose] def Block.hasExit : Block P (CmdExt P) → Bool
  | [] => false
  | s :: rest => Stmt.hasExit s || Block.hasExit rest
/-- Does the statement contain an `exit`, at any depth? -/
@[expose] def Stmt.hasExit : Stmt P (CmdExt P) → Bool
  | .exit _ _ => true
  | .block _ ss _ => Block.hasExit ss
  | .ite _ tss ess _ => Block.hasExit tss || Block.hasExit ess
  | .loop _ _ _ body _ => Block.hasExit body
  | _ => false
end

mutual
/-- Does the statement list contain an `assert` or a `cover`, at any depth? -/
@[expose] def Block.hasCheck : Block P (CmdExt P) → Bool
  | [] => false
  | s :: rest => Stmt.hasCheck s || Block.hasCheck rest
/-- Does the statement contain an `assert` or a `cover`, at any depth? -/
@[expose] def Stmt.hasCheck : Stmt P (CmdExt P) → Bool
  | .cmd (.cmd (.assert _ _ _)) | .cmd (.cmd (.cover _ _ _)) => true
  | .block _ ss _ => Block.hasCheck ss
  | .ite _ tss ess _ => Block.hasCheck tss || Block.hasCheck ess
  | .loop _ _ _ body _ => Block.hasCheck body
  | _ => false
end

mutual
/-- Does every arm of every `ite` of the list, at any depth, contain an `assert` or a `cover`
    (`Block.hasCheck`)? -/
@[expose] def Block.armsHaveChecks : Block P (CmdExt P) → Bool
  | [] => true
  | s :: rest => Stmt.armsHaveChecks s && Block.armsHaveChecks rest
/-- Does every arm of every `ite` of the statement, at any depth, contain an `assert` or a
    `cover`? -/
@[expose] def Stmt.armsHaveChecks : Stmt P (CmdExt P) → Bool
  | .ite _ tss ess _ =>
    Block.hasCheck tss && Block.hasCheck ess && Block.armsHaveChecks tss && Block.armsHaveChecks ess
  | .block _ ss _ => Block.armsHaveChecks ss
  | .loop _ _ _ body _ => Block.armsHaveChecks body
  | _ => true
end

mutual
/-- `Block.assignedVars ss ++ acc`, with an accumulator. -/
@[expose] def Block.assignedVarsAcc : Block P (CmdExt P) → List P.Ident → List P.Ident
  | [], acc => acc
  | s :: rest, acc => Stmt.assignedVarsAcc s (Block.assignedVarsAcc rest acc)
/-- `Stmt.assignedVars s ++ acc`, with an accumulator. -/
@[expose] def Stmt.assignedVarsAcc : Stmt P (CmdExt P) → List P.Ident → List P.Ident
  | .cmd (.cmd (.init x _ _ _)), acc | .cmd (.cmd (.set x _ _)), acc => x :: acc
  | .block _ ss _, acc => Block.assignedVarsAcc ss acc
  | .ite _ tss ess _, acc => Block.assignedVarsAcc tss (Block.assignedVarsAcc ess acc)
  | .loop _ _ _ body _, acc => Block.assignedVarsAcc body acc
  | _, acc => acc
end

/-- `Block.assignedVars` with an accumulator. -/
@[expose] def Block.assignedVarsH (ss : Block P (CmdExt P)) : List P.Ident :=
  Block.assignedVarsAcc ss []

/-- The names declared in scope, with multiplicities. -/
abbrev ScopeCount (P : PureExpr) [BEq P.Ident] [Hashable P.Ident] := Std.HashMap P.Ident Nat

/-- Declare `x`. -/
@[expose] def ScopeCount.inc (b : ScopeCount P) (x : P.Ident) : ScopeCount P :=
  b.insert x (b.getD x 0 + 1)

/-- Leave the scope of one declaration of `x`. -/
@[expose] def ScopeCount.dec (b : ScopeCount P) (x : P.Ident) : ScopeCount P :=
  match b[x]? with
  | some (n + 2) => b.insert x (n + 1)
  | _ => b.erase x

/-- Prepend (reversed) the variables of `xs` not declared in scope. -/
@[expose] def ScopeCount.emitFree (b : ScopeCount P) (xs : List P.Ident) (acc : List P.Ident) :
    List P.Ident :=
  xs.foldl (fun acc x => if b.contains x then acc else x :: acc) acc

mutual
/-- The free variables of a list prepended reversed to `acc`, the declarations of the list
    leaving scope at its end. -/
@[expose] def Block.freeVarsWalk (b : ScopeCount P) (acc : List P.Ident) (ss : Block P (CmdExt P)) :
    ScopeCount P × List P.Ident :=
  let (b, acc, added) := Block.freeVarsGo b acc [] ss
  (added.foldl ScopeCount.dec b, acc)
  termination_by (sizeOf ss, 1)
/-- `Block.freeVarsWalk` before the declarations of the list leave scope; `added` collects them. -/
@[expose] def Block.freeVarsGo (b : ScopeCount P) (acc added : List P.Ident) :
    Block P (CmdExt P) → ScopeCount P × List P.Ident × List P.Ident
  | [] => (b, acc, added)
  | .cmd (.cmd (.init x _ e _)) :: rest =>
    let acc := ScopeCount.emitFree b (match e with | .det e => exprFV e | .nondet => []) acc
    Block.freeVarsGo (b.inc x) acc (x :: added) rest
  | s :: rest =>
    let (b, acc) := Stmt.freeVarsWalk b acc s
    Block.freeVarsGo b acc added rest
  termination_by ss => (sizeOf ss, 0)
/-- The free variables of a statement prepended reversed to `acc`. -/
@[expose] def Stmt.freeVarsWalk (b : ScopeCount P) (acc : List P.Ident) :
    Stmt P (CmdExt P) → ScopeCount P × List P.Ident
  | .cmd (.cmd (.init _ _ (.det e) _)) => (b, ScopeCount.emitFree b (exprFV e) acc)
  | .cmd (.cmd (.init _ _ .nondet _)) => (b, acc)
  | .cmd (.cmd (.set x (.det e) _)) => (b, ScopeCount.emitFree b (x :: exprFV e) acc)
  | .cmd (.cmd (.set x .nondet _)) => (b, ScopeCount.emitFree b [x] acc)
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    (b, ScopeCount.emitFree b (exprFV e) acc)
  | .cmd (.call _ _ _) => (b, acc)
  | .block _ ss _ => Block.freeVarsWalk b acc ss
  | .ite c tss ess _ =>
    let acc := ScopeCount.emitFree b (match c with | .det c => exprFV c | .nondet => []) acc
    let (b, acc) := Block.freeVarsWalk b acc tss
    Block.freeVarsWalk b acc ess
  | .loop _ _ _ body _ => Block.freeVarsWalk b acc body
  | .exit _ _ | .typeDecl _ _ => (b, acc)
  termination_by s => (sizeOf s, 1)
end

/-- `Block.freeVars` in one forward pass with the declarations in scope in a hash map. -/
@[expose] def Block.freeVarsH (ss : Block P (CmdExt P)) : List P.Ident :=
  (Block.freeVarsWalk {} [] ss).2.reverse

/-- The scope hash map `b` holds each name of the scope list `T` with its multiplicity. -/
@[expose] def ScopeCountRep (b : ScopeCount P) (T : List P.Ident) : Prop :=
  ∀ x, b[x]? = if T.count x = 0 then none else some (T.count x)

end FreeVars

/-! ## Well-scopedness of loop-free statement lists

Well-scopedness of a loop-free statement list over `CmdExt P` commands from a scope
(`Block.WellScoped`, `Stmt.WellScoped`): reads are in scope, an `init` declares a local not in
scope, a `set` assigns a variable in scope, and there are no loops, calls or nondeterministic
guards; its Boolean check (`Block.wellScopedB`, `Stmt.wellScopedB`) and its one-pass version
with the scope in a hash map (`Block.wellScopedH`, proved equal in `StmtProps`). -/

section WellScoped

variable {P : PureExpr} [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [HasFvars P]

/-- The locals a statement puts in scope for the rest of its list. -/
@[expose] def Stmt.topInits : Stmt P (CmdExt P) → List P.Ident
  | .cmd (.cmd (.init x _ _ _)) => [x]
  | _ => []

mutual
/-- Well-scopedness of a loop-free statement list from scope `S` with local names `Lc`: reads
    are in scope, an `init` declares a local not in scope, a `set` assigns a variable in scope;
    no loops, calls or nondeterministic guards. -/
@[expose] def Block.WellScoped (Lc : List P.Ident) : List P.Ident → Block P (CmdExt P) → Prop
  | _, [] => True
  | S, s :: rest => Stmt.WellScoped Lc S s ∧ Block.WellScoped Lc (Stmt.topInits s ++ S) rest
@[expose] def Stmt.WellScoped (Lc : List P.Ident) (S : List P.Ident) : Stmt P (CmdExt P) → Prop
  | .cmd (.cmd (.init x _ (.det e) _)) => x ∉ S ∧ x ∈ Lc ∧ ∀ y ∈ exprFV e, y ∈ S
  | .cmd (.cmd (.init x _ .nondet _)) => x ∉ S ∧ x ∈ Lc
  | .cmd (.cmd (.set x (.det e) _)) => x ∈ S ∧ ∀ y ∈ exprFV e, y ∈ S
  | .cmd (.cmd (.set x .nondet _)) => x ∈ S
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    ∀ y ∈ exprFV e, y ∈ S
  | .ite (.det c) tss ess _ =>
    (∀ y ∈ exprFV c, y ∈ S) ∧ Block.WellScoped Lc S tss ∧ Block.WellScoped Lc S ess
  | .block _ ss _ => Block.WellScoped Lc S ss
  | .exit _ _ | .typeDecl _ _ => True
  | _ => False
end

mutual
/-- The Boolean check of well-scopedness (`Block.WellScoped`) of a loop-free statement list
    from scope `S` with local names `Lc`. -/
@[expose] def Block.wellScopedB (Lc : List P.Ident) : List P.Ident → Block P (CmdExt P) → Bool
  | _, [] => true
  | S, s :: rest => Stmt.wellScopedB Lc S s && Block.wellScopedB Lc (Stmt.topInits s ++ S) rest
/-- The Boolean check of well-scopedness (`Stmt.WellScoped`) of a loop-free statement from
    scope `S` with local names `Lc`. -/
@[expose] def Stmt.wellScopedB (Lc : List P.Ident) (S : List P.Ident) : Stmt P (CmdExt P) → Bool
  | .cmd (.cmd (.init x _ (.det e) _)) =>
    !S.contains x && Lc.contains x && (exprFV e).all S.contains
  | .cmd (.cmd (.init x _ .nondet _)) => !S.contains x && Lc.contains x
  | .cmd (.cmd (.set x (.det e) _)) => S.contains x && (exprFV e).all S.contains
  | .cmd (.cmd (.set x .nondet _)) => S.contains x
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    (exprFV e).all S.contains
  | .ite (.det c) tss ess _ =>
    (exprFV c).all S.contains && Block.wellScopedB Lc S tss && Block.wellScopedB Lc S ess
  | .block _ ss _ => Block.wellScopedB Lc S ss
  | .exit _ _ | .typeDecl _ _ => true
  | _ => false
end

mutual
/-- `Block.wellScopedB` with the scope in a hash map with multiplicities (`ScopeCount`) and the
    locals in a hash set: the scope additions of a list leave scope at its end; `none` at the
    first failure. -/
@[expose] def Block.wellScopedHWalk (lc : Std.HashSet P.Ident) (b : ScopeCount P)
    (ss : Block P (CmdExt P)) : Option (ScopeCount P) :=
  match Block.wellScopedHGo lc b [] ss with
  | some (b, added) => some (added.foldl ScopeCount.dec b)
  | none => none
  termination_by (sizeOf ss, 1)
/-- `Block.wellScopedHWalk` before the scope additions of the list leave scope; `added`
    collects them. -/
@[expose] def Block.wellScopedHGo (lc : Std.HashSet P.Ident) (b : ScopeCount P)
    (added : List P.Ident) : Block P (CmdExt P) → Option (ScopeCount P × List P.Ident)
  | [] => some (b, added)
  | .cmd (.cmd (.init x _ e _)) :: rest =>
    let ok := !b.contains x && lc.contains x &&
      (match e with | .det e => (exprFV e).all b.contains | .nondet => true)
    if ok then Block.wellScopedHGo lc (b.inc x) (x :: added) rest else none
  | s :: rest =>
    match Stmt.wellScopedHWalk lc b s with
    | some b => Block.wellScopedHGo lc b added rest
    | none => none
  termination_by ss => (sizeOf ss, 0)
/-- `Stmt.wellScopedB` of a statement that is not an `init` (see `Block.wellScopedHWalk`). -/
@[expose] def Stmt.wellScopedHWalk (lc : Std.HashSet P.Ident) (b : ScopeCount P) :
    Stmt P (CmdExt P) → Option (ScopeCount P)
  | .cmd (.cmd (.set x (.det e) _)) =>
    if b.contains x && (exprFV e).all b.contains then some b else none
  | .cmd (.cmd (.set x .nondet _)) => if b.contains x then some b else none
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    if (exprFV e).all b.contains then some b else none
  | .ite (.det c) tss ess _ =>
    if (exprFV c).all b.contains then
      match Block.wellScopedHWalk lc b tss with
      | some b => Block.wellScopedHWalk lc b ess
      | none => none
    else none
  | .block _ ss _ => Block.wellScopedHWalk lc b ss
  | .exit _ _ | .typeDecl _ _ => some b
  | _ => none
  termination_by s => (sizeOf s, 1)
end

/-- `Block.wellScopedB` in one pass with hash sets. -/
@[expose] def Block.wellScopedH (Lc : List P.Ident) (S : List P.Ident)
    (ss : Block P (CmdExt P)) : Bool :=
  (Block.wellScopedHWalk (Std.HashSet.ofList Lc) (S.foldl ScopeCount.inc {}) ss).isSome

end WellScoped

end -- public section
end Imperative
