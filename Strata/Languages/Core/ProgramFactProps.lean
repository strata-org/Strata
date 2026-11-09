/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProgramFact
import Strata.DL.Util.Nodup

/-! # Properties of program facts

Key results:

* `ProgramFact.all_complete` — `ProgramFact.all` enumerates every constructor.
* `ProgramFact.all_nodup` — it lists each one once, which is what makes
  canonical lists duplicate-free.
* `ProgramFact.holds_iff_check` — a fact holds exactly when its own executable
  check accepts, for a fact that has one; `ProgramFact.holds_iff_check_get` is
  the form an asserting phase uses, which knows only that a check exists.
  These are the bridge from a fact's `Prop` to something a machine can
  evaluate.
* `Program.allStatements_of_proc` — a check accepted by
  `Program.allStatements` holds of every structured procedure body.
* `ProgramFact.noCalls_of_program`, `ProgramFact.uniqueInits_of_program`,
  `ProgramFact.loopBodyNoInits_of_program`,
  `ProgramFact.noNondetGuards_of_program`,
  `ProgramFact.noLoopInvariants_of_program`, and
  `ProgramFact.noLoopMeasures_of_program` — bridges from these facts to the
  matching `Statements` / `Block` condition on each structured procedure
  body.
* `Statements.treeForm_eq`, `Statements.hasObligationForm_eq` — the checks of the
  `treeForm` and `hasObligationForm` facts are the language-generic shapes
  `Imperative.Block.treeForm` and `Imperative.Block.passiveForm`. -/

namespace Core

public section

/-- Every `ProgramFact` constructor appears in `ProgramFact.all`. Adding a
    constructor without updating `all` breaks the build here. -/
theorem ProgramFact.all_complete : ∀ f : ProgramFact, f ∈ ProgramFact.all := by
  intro f; cases f <;> decide

/-- `ProgramFact.all` lists each fact once. Canonical form is a `filter` of
    `all`, so a canonical list is duplicate-free precisely because `all` is.
    Listing a constructor twice breaks the build here. -/
theorem ProgramFact.all_nodup : ProgramFact.all.Nodup := by decide

---------------------------------------------------------------------

/-- A fact that carries an executable check holds of a program exactly when that
    check accepts it. Not every fact carries one, and `h` names the check. -/
theorem ProgramFact.holds_iff_check {f : ProgramFact} {c : Program → Bool}
    (h : f.check? = some c) (p : Program) : f.holds p ↔ c p = true := by
  cases f <;>
    simp only [ProgramFact.check?, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;>
    simp [ProgramFact.holds]

/-- A fact that has a check holds of a program exactly when that check
    accepts it. The form an asserting phase uses: it knows only that the fact
    has a check, not which function it is. -/
theorem ProgramFact.holds_iff_check_get {f : ProgramFact} (hc : f.check?.isSome = true)
    (p : Program) : f.holds p ↔ (f.check?.get hc) p = true :=
  ProgramFact.holds_iff_check (Option.some_get hc).symm p

/-- A per-body check accepted by `Program.allStatements` holds of every
    structured procedure body of the program. The fact bridges below are
    instances of this lemma. -/
theorem Program.allStatements_of_proc
    {f : Statements → Bool} {program : Program} {q : Procedure}
    {md : Imperative.MetaData Expression} {ss : Statements}
    (h : Program.allStatements f program = true)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    f ss = true := by
  simp only [Program.allStatements, List.all_eq_true] at h
  simpa [Decl.allStatements, Imperative.Body.allStatements,
    Imperative.Body.statements, hb] using h (Decl.proc q md) hq

/-- Every structured procedure body in a program satisfying
    `ProgramFact.noCalls` is call-free. -/
theorem ProgramFact.noCalls_of_program
    {program : Program} {q : Procedure} {md : Imperative.MetaData Expression}
    {ss : Statements} (h : ProgramFact.noCalls.holds program)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    Statements.noCalls ss = Bool.true :=
  Program.allStatements_of_proc h hq hb

/-- Every structured procedure body in a program satisfying
    `ProgramFact.uniqueInits` has globally unique initializer names. -/
theorem ProgramFact.uniqueInits_of_program
    {program : Program} {q : Procedure} {md : Imperative.MetaData Expression}
    {ss : Statements} (h : ProgramFact.uniqueInits.holds program)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    Imperative.Block.uniqueInits (C := Command) ss := by
  have heq : (Imperative.Block.initVars (C := Command) ss).eraseDups =
      Imperative.Block.initVars (C := Command) ss := by
    simpa using Program.allStatements_of_proc h hq hb
  unfold Imperative.Block.uniqueInits
  rw [← heq]
  exact eraseDups_Nodup _

/-- Every structured procedure body in a program satisfying
    `ProgramFact.loopBodyNoInits` has no initializers in its loop bodies. -/
theorem ProgramFact.loopBodyNoInits_of_program
    {program : Program} {q : Procedure} {md : Imperative.MetaData Expression}
    {ss : Statements} (h : ProgramFact.loopBodyNoInits.holds program)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    Imperative.Block.loopBodyNoInits ss = Bool.true :=
  Program.allStatements_of_proc h hq hb

/-- Every structured procedure body in a program satisfying
    `ProgramFact.noNondetGuards` has only deterministic guards. -/
theorem ProgramFact.noNondetGuards_of_program
    {program : Program} {q : Procedure} {md : Imperative.MetaData Expression}
    {ss : Statements} (h : ProgramFact.noNondetGuards.holds program)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    Imperative.Block.noNondetGuards ss = Bool.true :=
  Program.allStatements_of_proc h hq hb

/-- Every structured procedure body in a program satisfying
    `ProgramFact.noLoopInvariants` has no loop invariants. -/
theorem ProgramFact.noLoopInvariants_of_program
    {program : Program} {q : Procedure} {md : Imperative.MetaData Expression}
    {ss : Statements} (h : ProgramFact.noLoopInvariants.holds program)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    Imperative.Block.loopHasNoInvariants ss = Bool.true :=
  Program.allStatements_of_proc h hq hb

/-- Every structured procedure body in a program satisfying
    `ProgramFact.noLoopMeasures` has no loop measures. -/
theorem ProgramFact.noLoopMeasures_of_program
    {program : Program} {q : Procedure} {md : Imperative.MetaData Expression}
    {ss : Statements} (h : ProgramFact.noLoopMeasures.holds program)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    Imperative.Block.noMeasureLoops ss = Bool.true :=
  Program.allStatements_of_proc h hq hb

/-- The check of the `treeForm` fact is the language-generic tree form `Block.treeForm`. -/
theorem Statements.treeForm_eq (ss : Statements) :
    Statements.treeForm ss = Imperative.Block.treeForm ss := by
  induction ss using Imperative.Block.treeForm.induct <;>
    simp_all [Statements.treeForm, Imperative.Block.treeForm, Imperative.Block.allSubstmts,
      Imperative.Stmt.allSubstmts, Imperative.Block.nondetIteLast, Statement.isTreeForm]
  case case7 rest ih2 ih1 =>
    rw [← ih1, ← ih2]
    cases rest <;>
      simp [Imperative.Block.allSubstmts, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
  case case8 s _ _ _ _ _ _ _ =>
    rcases s with ((_ | _ | _ | _ | _) | _) | _ | ⟨_ | _⟩ | _ | _ | _ <;>
      grind [Imperative.Stmt.allSubstmts, Statement.isTreeForm]

/-- The check of the `hasObligationForm` fact is the language-generic passive form
    `Block.passiveForm`. -/
theorem Statements.hasObligationForm_eq (ss : Statements) :
    Statements.hasObligationForm ss = Imperative.Block.passiveForm ss := by
  induction ss using Imperative.Block.passiveForm.induct <;>
    simp_all [Statements.hasObligationForm, Imperative.Block.passiveForm,
      Imperative.Block.allSubstmts, Imperative.Stmt.allSubstmts, Statement.isObligationForm]
  case case7 s _ _ _ _ _ _ =>
    rcases s with ((_ | _ | _ | _ | _) | _) | _ | ⟨_ | _⟩ | _ | _ | _ <;>
      grind [Imperative.Stmt.allSubstmts, Statement.isObligationForm]

end -- public section

end Core
