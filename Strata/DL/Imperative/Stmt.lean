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
    (loop_case : ∀ (guard : ExprOrNondet P) (measure : Option P.Expr) (invariant : List (String × P.Expr))
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

/-! ### UniqueInits

Collect the names of every variable initialized by an `init` command anywhere
in a statement (across all nesting levels). The companion predicate
`Block.uniqueInits` asserts that the resulting list is `Nodup`, ruling out
the edge case where a name is projected away by `step_block_done` and then
reinitialized — a pattern the unstructured CFG cannot replicate because its
flat namespace has no projection.
-/

mutual
/-- Collect every variable initialized by an `init` command in a statement. -/
@[expose] def Stmt.initVars (s : Stmt P (Cmd P)) : List P.Ident :=
  match s with
  | .cmd (.init x _ _ _) => [x]
  | .cmd _ => []
  | .block _ bss _ => Block.initVars bss
  | .ite _ tss ess _ => Block.initVars tss ++ Block.initVars ess
  | .loop _ _ _ bss _ => Block.initVars bss
  | .exit _ _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []
  termination_by (Stmt.sizeOf s)

/-- Collect every variable initialized by an `init` command in a block. -/
@[expose] def Block.initVars (ss : List (Stmt P (Cmd P))) : List P.Ident :=
  match ss with
  | [] => []
  | s :: rest => Stmt.initVars s ++ Block.initVars rest
  termination_by (Block.sizeOf ss)
end

/-- Every `init` in the program (across all nesting levels) names a unique
variable. The flat-namespace CFG can simulate the structured semantics only
when this holds — without uniqueness, structured `step_block_done` can
project a name away that the structured semantics later reinitializes, a
pattern the CFG cannot replicate. -/
@[expose] def Block.uniqueInits (ss : List (Stmt P (Cmd P))) : Prop :=
  (Block.initVars ss).Nodup

---------------------------------------------------------------------

/-! ### SimpleShape

Predicate stating that a statement or block has a "simple" shape suitable
for the structured-to-CFG soundness proof under axiom-free assumptions:
- no nondeterministic `.ite`
- no nondeterministic `.loop` guards (only `.det _` loops are admitted)
- `.loop` is permitted **provided its body is itself simple-shape**.
  Auxiliary predicates `loopBodyNoInits`, `loopHasNoInvariants`, and
  `noMeasureLoops` further restrict which loops are admissible for the
  current proof scope (no body-local var inits, no labeled invariants,
  no termination measure). Those predicates are defined below.

`.ite (.det _)`, `.block`, sequential `.cmd`s, `.exit`, `.funcDecl`,
and `.typeDecl` are all allowed.
-/

mutual
/-- Returns true if the statement satisfies the simple-shape restriction. -/
@[expose] def Stmt.simpleShape (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.simpleShape bss
  | .ite (.det _) tss ess _ => Block.simpleShape tss && Block.simpleShape ess
  | .ite .nondet _ _ _ => false
  | .loop guard _ _ bss _ =>
    (match guard with | .det _ => true | .nondet => false) && Block.simpleShape bss
  | .exit _ _ => true
  | .funcDecl _ _ => true
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Returns true if the block satisfies the simple-shape restriction. -/
@[expose] def Block.simpleShape (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.simpleShape s && Block.simpleShape srest
  termination_by (Block.sizeOf ss)
end

/-- `Block.simpleShape` on `s :: rest` decomposes to the conjunction. -/
theorem Block.simpleShape_cons_iff
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} :
    Block.simpleShape (s :: rest) = true ↔
      Stmt.simpleShape s = true ∧ Block.simpleShape rest = true := by
  simp only [Block.simpleShape, Bool.and_eq_true]

/-- The then-branch of an `.ite (.det _)` is simple when the whole ite is. -/
theorem Stmt.simpleShape_branch_then
    {g : P.Expr} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.simpleShape (.ite (.det g) tss ess md) = true →
    Block.simpleShape tss = true := by
  simp only [Stmt.simpleShape, Bool.and_eq_true]
  intro h
  exact h.1

/-- The else-branch of an `.ite (.det _)` is simple when the whole ite is. -/
theorem Stmt.simpleShape_branch_else
    {g : P.Expr} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.simpleShape (.ite (.det g) tss ess md) = true →
    Block.simpleShape ess = true := by
  simp only [Stmt.simpleShape, Bool.and_eq_true]
  intro h
  exact h.2

/-- The body of a `.block` is simple when the whole block-statement is. -/
theorem Stmt.simpleShape_block_body
    {label : String} {body : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.simpleShape (.block label body md) = true →
    Block.simpleShape body = true := by
  simp only [Stmt.simpleShape]
  intro h; exact h

/-- The body of a `.loop` is simple when the whole loop-statement is. -/
theorem Stmt.simpleShape_loop_body
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.simpleShape (.loop g m is body md) = true →
    Block.simpleShape body = true := by
  intro h
  unfold Stmt.simpleShape at h
  cases g with
  | det ge => simpa using h
  | nondet => simp at h

/-- The guard of a simple-shape `.loop` is deterministic. -/
theorem Stmt.simpleShape_loop_guard_det
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.simpleShape (.loop g m is body md) = true →
    ∃ ge, g = .det ge := by
  intro h
  unfold Stmt.simpleShape at h
  cases g with
  | det ge => exact ⟨ge, rfl⟩
  | nondet => simp at h

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
@[expose] def Stmt.loopBodyNoInits (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.loopBodyNoInits bss
  | .ite _ tss ess _ => Block.loopBodyNoInits tss && Block.loopBodyNoInits ess
  | .loop _ _ _ bss _ =>
      (Block.initVars bss).isEmpty && Block.loopBodyNoInits bss
  | .exit _ _ => true
  | .funcDecl _ _ => true
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Block-level lifting of `Stmt.loopBodyNoInits`. -/
@[expose] def Block.loopBodyNoInits (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.loopBodyNoInits s && Block.loopBodyNoInits srest
  termination_by (Block.sizeOf ss)
end

theorem Block.loopBodyNoInits_cons_iff
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} :
    Block.loopBodyNoInits (s :: rest) = true ↔
      Stmt.loopBodyNoInits s = true ∧ Block.loopBodyNoInits rest = true := by
  simp only [Block.loopBodyNoInits, Bool.and_eq_true]

theorem Stmt.loopBodyNoInits_branch_then
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopBodyNoInits (.ite g tss ess md) = true →
    Block.loopBodyNoInits tss = true := by
  simp only [Stmt.loopBodyNoInits, Bool.and_eq_true]
  intro h; exact h.1

theorem Stmt.loopBodyNoInits_branch_else
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopBodyNoInits (.ite g tss ess md) = true →
    Block.loopBodyNoInits ess = true := by
  simp only [Stmt.loopBodyNoInits, Bool.and_eq_true]
  intro h; exact h.2

theorem Stmt.loopBodyNoInits_block_body
    {label : String} {body : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopBodyNoInits (.block label body md) = true →
    Block.loopBodyNoInits body = true := by
  simp only [Stmt.loopBodyNoInits]
  intro h; exact h

/-- A loop's body has no local variable initializations. -/
theorem Stmt.loopBodyNoInits_loop_body
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.loopBodyNoInits (.loop g m is body md) = true →
    Block.initVars body = [] := by
  simp only [Stmt.loopBodyNoInits, Bool.and_eq_true, List.isEmpty_iff]
  intro h; exact h.1

/-- The recursive `loopBodyNoInits` discharge for a loop's body. -/
theorem Stmt.loopBodyNoInits_loop_body_rec
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.loopBodyNoInits (.loop g m is body md) = true →
    Block.loopBodyNoInits body = true := by
  simp only [Stmt.loopBodyNoInits, Bool.and_eq_true]
  intro h; exact h.2

---------------------------------------------------------------------

/-! ### LoopHasNoInvariants

Predicate stating that every `.loop _ _ is _ _` reachable inside a
statement (or block) has `is = []` (no labeled invariants). Used by
the structured-to-CFG soundness proof to collapse the assert-chain
at the loop entry block to empty.
-/

mutual
/-- Returns true if every reachable loop has no invariants. -/
@[expose] def Stmt.loopHasNoInvariants (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.loopHasNoInvariants bss
  | .ite _ tss ess _ => Block.loopHasNoInvariants tss && Block.loopHasNoInvariants ess
  | .loop _ _ is bss _ =>
      is.isEmpty && Block.loopHasNoInvariants bss
  | .exit _ _ => true
  | .funcDecl _ _ => true
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Block-level lifting of `Stmt.loopHasNoInvariants`. -/
@[expose] def Block.loopHasNoInvariants (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.loopHasNoInvariants s && Block.loopHasNoInvariants srest
  termination_by (Block.sizeOf ss)
end

theorem Block.loopHasNoInvariants_cons_iff
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} :
    Block.loopHasNoInvariants (s :: rest) = true ↔
      Stmt.loopHasNoInvariants s = true ∧ Block.loopHasNoInvariants rest = true := by
  simp only [Block.loopHasNoInvariants, Bool.and_eq_true]

theorem Stmt.loopHasNoInvariants_branch_then
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopHasNoInvariants (.ite g tss ess md) = true →
    Block.loopHasNoInvariants tss = true := by
  simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true]
  intro h; exact h.1

theorem Stmt.loopHasNoInvariants_branch_else
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopHasNoInvariants (.ite g tss ess md) = true →
    Block.loopHasNoInvariants ess = true := by
  simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true]
  intro h; exact h.2

theorem Stmt.loopHasNoInvariants_block_body
    {label : String} {body : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopHasNoInvariants (.block label body md) = true →
    Block.loopHasNoInvariants body = true := by
  simp only [Stmt.loopHasNoInvariants]
  intro h; exact h

/-- A loop has no labeled invariants. -/
theorem Stmt.loopHasNoInvariants_loop_invs
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.loopHasNoInvariants (.loop g m is body md) = true →
    is = [] := by
  simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true, List.isEmpty_iff]
  intro h; exact h.1

/-- The recursive `loopHasNoInvariants` discharge for a loop's body. -/
theorem Stmt.loopHasNoInvariants_loop_body_rec
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.loopHasNoInvariants (.loop g m is body md) = true →
    Block.loopHasNoInvariants body = true := by
  simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true]
  intro h; exact h.2

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
@[expose] def Stmt.noMeasureLoops (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.noMeasureLoops bss
  | .ite _ tss ess _ => Block.noMeasureLoops tss && Block.noMeasureLoops ess
  | .loop _ m _ bss _ =>
      m.isNone && Block.noMeasureLoops bss
  | .exit _ _ => true
  | .funcDecl _ _ => true
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Block-level lifting of `Stmt.noMeasureLoops`. -/
@[expose] def Block.noMeasureLoops (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.noMeasureLoops s && Block.noMeasureLoops srest
  termination_by (Block.sizeOf ss)
end

theorem Block.noMeasureLoops_cons_iff
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} :
    Block.noMeasureLoops (s :: rest) = true ↔
      Stmt.noMeasureLoops s = true ∧ Block.noMeasureLoops rest = true := by
  simp only [Block.noMeasureLoops, Bool.and_eq_true]

theorem Stmt.noMeasureLoops_branch_then
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.noMeasureLoops (.ite g tss ess md) = true →
    Block.noMeasureLoops tss = true := by
  simp only [Stmt.noMeasureLoops, Bool.and_eq_true]
  intro h; exact h.1

theorem Stmt.noMeasureLoops_branch_else
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.noMeasureLoops (.ite g tss ess md) = true →
    Block.noMeasureLoops ess = true := by
  simp only [Stmt.noMeasureLoops, Bool.and_eq_true]
  intro h; exact h.2

theorem Stmt.noMeasureLoops_block_body
    {label : String} {body : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.noMeasureLoops (.block label body md) = true →
    Block.noMeasureLoops body = true := by
  simp only [Stmt.noMeasureLoops]
  intro h; exact h

/-- A loop has no termination measure. -/
theorem Stmt.noMeasureLoops_loop_measure
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.noMeasureLoops (.loop g m is body md) = true →
    m = .none := by
  simp only [Stmt.noMeasureLoops, Bool.and_eq_true, Option.isNone_iff_eq_none]
  intro h; exact h.1

/-- The recursive `noMeasureLoops` discharge for a loop's body. -/
theorem Stmt.noMeasureLoops_loop_body_rec
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.noMeasureLoops (.loop g m is body md) = true →
    Block.noMeasureLoops body = true := by
  simp only [Stmt.noMeasureLoops, Bool.and_eq_true]
  intro h; exact h.2

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
  | .funcDecl _ _ => true
  | .typeDecl _ _ => true
  termination_by (Stmt.sizeOf s)

/-- Returns true if the block contains no `.block` constructor. -/
@[expose] def Block.noBlocks (ss : Block P C) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.noBlocks s && Block.noBlocks srest
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
@[expose] def Stmt.getVars [HasVarsPure P P.Expr] [HasVarsPure P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsPure.getVars cmd
  | .block _ bss _ => Block.getVars bss
  | .ite cond tbss ebss _ => cond.getVars ++ Block.getVars tbss ++ Block.getVars ebss
  | .loop guard measure invariants bss _ =>
    guard.getVars ++
      (invariants.flatMap (fun p => HasVarsPure.getVars p.snd)) ++
      (match measure with | none => [] | some m => HasVarsPure.getVars m) ++
      Block.getVars bss
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

@[expose] def Block.getVars [HasVarsPure P P.Expr] [HasVarsPure P C] (ss : Block P C) : List P.Ident :=
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
@[expose] def Stmt.definedVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsImp.definedVars cmd
  | .block _ bss _ => Block.definedVars bss
  | .ite _ tbss ebss _ => Block.definedVars tbss ++ Block.definedVars ebss
  | .loop _ _ _ body _ => Block.definedVars body
  | .funcDecl decl _ => [decl.name]  -- Function declaration defines the function name
  | .typeDecl _ _ => []  -- Type declarations don't define variables
  | _ => []

@[expose] def Block.definedVars [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.definedVars s ++ Block.definedVars srest
end

mutual
/-- Get all variables modified by the statement `s`. -/
@[expose] def Stmt.modifiedVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .cmd cmd => HasVarsImp.modifiedVars cmd
  | .exit _ _ => []
  | .block _ bss _ => Block.modifiedVars bss
  | .ite _ tbss ebss _ => Block.modifiedVars tbss ++ Block.modifiedVars ebss
  | .loop _ _ _ bss _ => Block.modifiedVars bss
  | .funcDecl _ _ => []  -- Function declarations don't modify variables
  | .typeDecl _ _ => []  -- Type declarations don't modify variables

@[expose] def Block.modifiedVars [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.modifiedVars s ++ Block.modifiedVars srest
end

mutual
/-- Get all variables modified/defined by the statement `s`.
    Note that we need a separate function because order matters here for sub-blocks
 -/
@[expose] def Stmt.modifiedOrDefinedVars [HasVarsImp P C] (s : Stmt P C) : List P.Ident :=
  match s with
  | .block _ bss _ => Block.modifiedOrDefinedVars bss
  | .ite _ tbss ebss _ => Block.modifiedOrDefinedVars tbss ++ Block.modifiedOrDefinedVars ebss
  | _ => Stmt.definedVars s ++ Stmt.modifiedVars s

@[expose] def Block.modifiedOrDefinedVars [HasVarsImp P C] (ss : Block P C) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => Stmt.modifiedOrDefinedVars s ++ Block.modifiedOrDefinedVars srest
end

mutual
/-- Get all variables touched (modified, defined, or read) by the statement `s`. -/
@[expose] def Stmt.touchedVars [HasVarsImp P C] [HasVarsPure P P.Expr] [HasVarsPure P C]
    (s : Stmt P C) : List P.Ident :=
  Stmt.modifiedOrDefinedVars s ++ Stmt.getVars s

@[expose] def Block.touchedVars [HasVarsImp P C] [HasVarsPure P P.Expr] [HasVarsPure P C]
    (ss : Block P C) : List P.Ident :=
  Block.modifiedOrDefinedVars ss ++ Block.getVars ss
end

instance (P : PureExpr) [HasVarsImp P C] : HasVarsImp P (Stmt P C) where
  definedVars := Stmt.definedVars
  modifiedVars := Stmt.modifiedVars
  -- order matters for Havoc, so needs to override the default
  modifiedOrDefinedVars := Stmt.modifiedOrDefinedVars

instance (P : PureExpr) [HasVarsImp P C] : HasVarsImp P (Block P C) where
  definedVars := Block.definedVars
  modifiedVars := Block.modifiedVars
  -- order matters for Havoc, so needs to override the default
  modifiedOrDefinedVars := Block.modifiedOrDefinedVars

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

---------------------------------------------------------------------

end -- public section
end Imperative
