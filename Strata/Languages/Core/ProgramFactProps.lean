/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProgramFact
import Strata.DL.Util.Nodup
import Strata.Languages.Core.ProgramProps
import all Strata.Languages.Core.Program
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Stmt

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
  `Imperative.Block.treeForm` and `Imperative.Block.passiveForm`.
* `ProgramFact.holds_of_procs_eq` — a fact that reads only procedures
  (`ProgramFact.readsOnlyProcedures`) holds of every program with the same procedures in the
  same order, whatever its other declarations: the lemma a phase that leaves procedures alone
  proves its contract with.
* `ProgramFact.holds_iff_decls_all`, `ProgramFact.holds_of_decls_subset`,
  `ProgramFact.holds_of_procs_eq_of_subset` — every fact but `wellFormedCalls` and `noLambdas`
  checks each declaration on its own, so it holds of a program whose declarations are among
  those of one it holds of; with the same procedures, `wellFormedCalls` does too. -/

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
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss opq) :
    f ss = true := by
  simp only [Program.allStatements, List.all_eq_true] at h
  simpa [Decl.allStatements, Imperative.Body.allStatements,
    Imperative.Body.statements, hb] using h (Decl.proc q md) hq

/-- Every structured procedure body in a program satisfying
    `ProgramFact.noCalls` is call-free. -/
theorem ProgramFact.noCalls_of_program
    {program : Program} {q : Procedure} {md : Imperative.MetaData Expression}
    {ss : Statements} (h : ProgramFact.noCalls.holds program)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss opq) :
    Statements.noCalls ss = Bool.true :=
  Program.allStatements_of_proc h hq hb

/-- Every structured procedure body in a program satisfying
    `ProgramFact.uniqueInits` has globally unique initializer names. -/
theorem ProgramFact.uniqueInits_of_program
    {program : Program} {q : Procedure} {md : Imperative.MetaData Expression}
    {ss : Statements} (h : ProgramFact.uniqueInits.holds program)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss opq) :
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
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss opq) :
    Imperative.Block.loopBodyNoInits ss = Bool.true :=
  Program.allStatements_of_proc h hq hb

/-- Every structured procedure body in a program satisfying
    `ProgramFact.noNondetGuards` has only deterministic guards. -/
theorem ProgramFact.noNondetGuards_of_program
    {program : Program} {q : Procedure} {md : Imperative.MetaData Expression}
    {ss : Statements} (h : ProgramFact.noNondetGuards.holds program)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss opq) :
    Imperative.Block.noNondetGuards ss = Bool.true :=
  Program.allStatements_of_proc h hq hb

/-- Every structured procedure body in a program satisfying
    `ProgramFact.noLoopInvariants` has no loop invariants. -/
theorem ProgramFact.noLoopInvariants_of_program
    {program : Program} {q : Procedure} {md : Imperative.MetaData Expression}
    {ss : Statements} (h : ProgramFact.noLoopInvariants.holds program)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss opq) :
    Imperative.Block.loopHasNoInvariants ss = Bool.true :=
  Program.allStatements_of_proc h hq hb

/-- Every structured procedure body in a program satisfying
    `ProgramFact.noLoopMeasures` has no loop measures. -/
theorem ProgramFact.noLoopMeasures_of_program
    {program : Program} {q : Procedure} {md : Imperative.MetaData Expression}
    {ss : Statements} (h : ProgramFact.noLoopMeasures.holds program)
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss opq) :
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

/-! ### Facts and the declarations they read -/

/-- Every fact but `wellFormedCalls`, `noLambdas` and `varsNotFunctions` asks the same check of
    each declaration on its own. `wellFormedCalls` also reads, for each call, which procedure its
    callee names, `noLambdas` which functions the other declarations reach, and
    `varsNotFunctions` the program's function names. -/
theorem ProgramFact.holds_iff_decls_all {f : ProgramFact} (hf : f ≠ .wellFormedCalls)
    (hl : f ≠ .noLambdas) (hv : f ≠ .varsNotFunctions) :
    ∃ g : Decl → Bool, ∀ p : Program, f.holds p ↔ p.decls.all g = true := by
  cases f <;> first
    | exact absurd rfl hf
    | exact absurd rfl hl
    | exact absurd rfl hv
    | exact ⟨_, fun _ => Iff.rfl⟩

/-- A fact other than `wellFormedCalls`, `noLambdas` and `varsNotFunctions` that holds of a
    program holds of any program whose declarations are among its own. -/
theorem ProgramFact.holds_of_decls_subset {f : ProgramFact} (hf : f ≠ .wellFormedCalls)
    (hl : f ≠ .noLambdas) (hv : f ≠ .varsNotFunctions) {p p' : Program}
    (hsub : ∀ d ∈ p'.decls, d ∈ p.decls) (h : f.holds p) : f.holds p' := by
  obtain ⟨g, hg⟩ := ProgramFact.holds_iff_decls_all hf hl hv
  rw [hg] at h ⊢
  simp only [List.all_eq_true] at h ⊢
  exact fun d hd => h d (hsub d hd)

/-- A fact other than `wellFormedCalls` that reads only procedures asks of each declaration a
    check that every other declaration passes. -/
private theorem ProgramFact.decls_all_of_readsOnlyProcedures {f : ProgramFact}
    (hf : f.readsOnlyProcedures = true) (hw : f ≠ .wellFormedCalls) :
    ∃ g : Decl → Bool, (∀ p : Program, f.holds p ↔ p.decls.all g = true) ∧
      ∀ d, d.isProc = false → g d = true := by
  cases f <;> first
    | exact absurd rfl hw
    | exact absurd hf (by decide)
    | refine ⟨_, fun _ => Iff.rfl, fun d hd => ?_⟩
      cases d <;> first
        | (simp [Decl.isProc, Decl.kind] at hd; done)
        | rfl
        | decide
        | simp [Decl.allStatements, Imperative.Block.loopBodyNoInits,
            Imperative.Block.loopHasNoInvariants, Imperative.Block.noLoops,
            Imperative.Block.noMeasureLoops, Imperative.Block.noNondetGuards,
            Statements.hasObligationForm, Statements.noCalls, Statements.noInits,
            Statements.staticSingleAssignment, Statements.treeForm, Imperative.Block.allSubstmts,
            Imperative.Block.nondetIteLast]

/-- `ds.all g` reads only the procedures of `ds` when every other declaration passes `g`. -/
private theorem decls_all_eq_procs_all {g : Decl → Bool}
    (hg : ∀ d, d.isProc = false → g d = true) (ds : List Decl) :
    ds.all g = (ds.filter Decl.isProc).all g := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases hd : d.isProc = true
    · simp [List.filter_cons_of_pos hd, ih]
    · simp [List.filter_cons_of_neg hd, ih, hg d (by simpa using hd)]

/-- A fact that reads only procedures holds of a program whose procedures are those of a
    program it holds of, in the same order, whatever its other declarations. -/
theorem ProgramFact.holds_of_procs_eq {f : ProgramFact} (hf : f.readsOnlyProcedures = true)
    {p p' : Program} (hprocs : p'.decls.filter Decl.isProc = p.decls.filter Decl.isProc)
    (h : f.holds p) : f.holds p' := by
  by_cases hw : f = .wellFormedCalls
  · subst hw; exact Program.callsWellFormed_of_procs_eq hprocs h
  · obtain ⟨g, hg, hother⟩ := ProgramFact.decls_all_of_readsOnlyProcedures hf hw
    rw [hg] at h ⊢
    rw [decls_all_eq_procs_all hother] at h ⊢
    rwa [hprocs]

/-- Dropping declarations keeps `varsNotFunctions`: the declarations kept are among the
    program's, and the function names kept are among its function names. -/
private theorem Program.varsNotFunctions_of_subset {p p' : Program}
    (hsub : ∀ d ∈ p'.decls, d ∈ p.decls) (h : Program.varsNotFunctions p = true) :
    Program.varsNotFunctions p' = true := by
  have hnames : ∀ n, n ∈ Program.funcNames p' → n ∈ Program.funcNames p := by
    intro n hm
    simp only [Program.funcNames, List.mem_flatMap] at hm ⊢
    obtain ⟨e, he, hne⟩ := hm
    exact ⟨e, hsub e he, hne⟩
  have hclear : ∀ ns : List String,
      ns.all (!(Std.HashSet.ofList (Program.funcNames p)).contains ·) = true →
      ns.all (!(Std.HashSet.ofList (Program.funcNames p')).contains ·) = true := by
    intro ns hns
    simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      Std.HashSet.contains_ofList] at hns ⊢
    intro n hn
    cases hc : (Program.funcNames p').contains n with
    | false => rfl
    | true =>
      have hnot := hns n hn
      simp [hnames n (by simpa using hc)] at hnot
  unfold Program.varsNotFunctions at h ⊢
  simp only [List.all_eq_true] at h ⊢
  intro d hd
  have hdp := h d (hsub d hd)
  cases d with
  | proc r md => exact hclear _ hdp
  | func f md => exact hclear _ hdp
  | recFuncBlock fs md =>
    rw [List.all_eq_true] at hdp ⊢
    exact fun g hg => hclear _ (hdp g hg)
  | _ => trivial

/-- A program whose declarations are among those of a program a fact holds of, with the same
    procedures in the same order, has the fact too, unless it is `noLambdas`: what a phase that
    only deletes declarations other than procedures keeps. -/
theorem ProgramFact.holds_of_procs_eq_of_subset {f : ProgramFact} (hl : f ≠ .noLambdas)
    {p p' : Program} (hprocs : p'.decls.filter Decl.isProc = p.decls.filter Decl.isProc)
    (hsub : ∀ d ∈ p'.decls, d ∈ p.decls) (h : f.holds p) : f.holds p' := by
  by_cases hf : f = .wellFormedCalls
  · subst hf; exact Program.callsWellFormed_of_procs_eq hprocs h
  by_cases hv : f = .varsNotFunctions
  · subst hv; exact Program.varsNotFunctions_of_subset hsub h
  · exact ProgramFact.holds_of_decls_subset hf hl hv hsub h

end -- public section

end Core
