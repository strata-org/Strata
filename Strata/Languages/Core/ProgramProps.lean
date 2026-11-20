/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
import all Strata.Languages.Core.Program

/-! # Properties of Core programs

Facts about procedure lookup, declaration-order views of a `Program` and the expression
factories constructed from them.

Key results:
- `Program.Procedure.find?_eq_go` — procedure lookup is a scan of the declarations.
- `Program.Procedure.find?_of_mem_of_getNames_nodup`, `Program.Procedure.find?_of_mem_of_suffix`
  — with distinct declared names, a procedure in the program is found under its own name.
- `Program.factoryBeforeProcedure_eq_core_of_noFunctions` — when no user
  functions precede a procedure, its visible factory is `Core.Factory`.
- `Program.declsBeforeProcedure_eq` — the declarations before the first procedure
  of a name are `declsBeforeProcedure` of that name.
-/

public section

namespace Core

open Imperative

/-- Procedure lookup is declaration lookup followed by extracting a procedure. -/
private theorem Program.Procedure.find?_eq_bind (P : Program) (x : Expression.Ident) :
    Program.Procedure.find? P x = (P.find? .proc x).bind Decl.getProc? := by
  unfold Program.Procedure.find?
  split
  · rename_i hnone; simp [hnone]
  · rename_i d hsome
    have hk := Program.find?_kind hsome
    match d, hk with
    | .proc p md, _ => simp [hsome, Decl.getProc, Decl.getProc?]

/-- Program lookup is the declaration-list scan specialized to the program's declarations. -/
theorem Program.find?_eq_go (P : Program) (k : DeclKind) (x : Expression.Ident) :
    P.find? k x = Program.find?.go k x P.decls := rfl

/-- Scanning an empty declaration list finds no declaration. -/
theorem Program.find?_go_nil {k : DeclKind} {x : Expression.Ident} :
    Program.find?.go k x [] = none := by rw [Program.find?.go]

/-- A declaration-list scan returns a matching head and otherwise scans the tail. -/
theorem Program.find?_go_cons {k : DeclKind} {x : Expression.Ident} (d : Decl) (ds : Decls) :
    Program.find?.go k x (d :: ds)
      = if (d.kind == k && d.name == x) = true then some d else Program.find?.go k x ds := by
  rw [Program.find?.go]

/-- A hit of the scan is a declaration of the list, with the requested name and kind. -/
private theorem Program.find?_go_mem {k : DeclKind} {x : Expression.Ident} :
    ∀ (decls : Decls) (d : Decl), Program.find?.go k x decls = some d →
      d ∈ decls ∧ d.name = x ∧ d.kind = k := by
  intro decls
  induction decls with
  | nil => intro d hd; simp [Program.find?.go] at hd
  | cons hd tl ih =>
    intro d hres
    unfold Program.find?.go at hres
    split at hres
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      cases hres
      exact ⟨List.mem_cons_self, hcond.2, hcond.1⟩
    · obtain ⟨hmem, hname, hkind⟩ := ih d hres
      exact ⟨List.mem_cons_of_mem _ hmem, hname, hkind⟩

/-- A match found in a declaration-list prefix remains the result after appending a suffix. -/
private theorem Program.find?_go_append_of_some {k : DeclKind} {x : Expression.Ident} :
    ∀ (ds es : Decls) (d : Decl), Program.find?.go k x ds = some d →
      Program.find?.go k x (ds ++ es) = some d := by
  intro ds
  induction ds with
  | nil => intro es d h; simp [Program.find?.go] at h
  | cons hd tl ih =>
    intro es d h
    rw [List.cons_append, Program.find?_go_cons]
    rw [Program.find?_go_cons] at h
    split at h
    · rename_i hcond; rw [ite_eq_left hcond]; exact h
    · rename_i hcond; rw [ite_eq_right hcond]; exact ih es d h

/-- If a declaration-list prefix has no match, scanning the appended list scans the suffix. -/
private theorem Program.find?_go_append_of_none {k : DeclKind} {x : Expression.Ident} :
    ∀ (ds es : Decls), Program.find?.go k x ds = none →
      Program.find?.go k x (ds ++ es) = Program.find?.go k x es := by
  intro ds
  induction ds with
  | nil => intro es _; simp
  | cons hd tl ih =>
    intro es h
    rw [List.cons_append, Program.find?_go_cons]
    rw [Program.find?_go_cons] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hcond; rw [ite_eq_right hcond]; exact ih es h

/-- Procedure lookup is the declaration-list scan followed by extraction of a procedure. -/
theorem Program.Procedure.find?_eq_go (P : Program) (x : Expression.Ident) :
    Program.Procedure.find? P x
      = (Program.find?.go DeclKind.proc x P.decls).bind Decl.getProc? := by
  rw [Program.Procedure.find?_eq_bind, Program.find?_eq_go]

/-- A procedure that lookup returns is declared in the program under the looked-up name. -/
theorem Program.Procedure.find?_mem_decls (P : Program) (x : Expression.Ident) (q : Procedure)
    (h : Program.Procedure.find? P x = some q) :
    ∃ md, Decl.proc q md ∈ P.decls ∧ q.header.name = x := by
  rw [Program.Procedure.find?_eq_bind] at h
  revert h
  cases hgo : Program.find? P .proc x with
  | none => intro h; simp at h
  | some d =>
    intro h
    have hgo' : Program.find?.go DeclKind.proc x P.decls = some d := hgo
    obtain ⟨hmem, hname, hkind⟩ := Program.find?_go_mem P.decls d hgo'
    match d, hkind with
    | .proc p md, _ =>
      have h2 : Decl.getProc? (Decl.proc p md) = some q := by simpa using h
      have hg : Decl.getProc? (Decl.proc p md) = some p := rfl
      rw [hg] at h2
      have hpq : p = q := by simpa using h2
      subst hpq
      exact ⟨md, hmem, hname⟩

/-- A procedure found in a declaration-list prefix is found in the whole list. -/
theorem Program.Procedure.find?_append_of_some (ds es : Decls) (x : Expression.Ident)
    (q : Procedure) (h : Program.Procedure.find? { decls := ds } x = some q) :
    Program.Procedure.find? { decls := ds ++ es } x = some q := by
  rw [Program.Procedure.find?_eq_go] at h ⊢
  revert h
  cases hgo : Program.find?.go DeclKind.proc x ds with
  | none => intro h; simp at h
  | some d =>
    intro h
    rw [Program.find?_go_append_of_some ds es d hgo]
    exact h

/-- If a declaration-list prefix has no procedure of that name, lookup continues in the suffix. -/
theorem Program.Procedure.find?_append_of_none (ds es : Decls) (x : Expression.Ident)
    (h : Program.Procedure.find? { decls := ds } x = none) :
    Program.Procedure.find? { decls := ds ++ es } x
      = Program.Procedure.find? { decls := es } x := by
  rw [Program.Procedure.find?_eq_go] at h
  rw [Program.Procedure.find?_eq_go, Program.Procedure.find?_eq_go]
  have hgo : Program.find?.go DeclKind.proc x ds = none := by
    revert h
    cases hg : Program.find?.go DeclKind.proc x ds with
    | none => intro _; rfl
    | some d =>
      intro h
      have hk : d.kind = DeclKind.proc :=
        (Program.find?_go_mem ds d hg).2.2
      match d, hk with
      | .proc p md, _ => simp [Decl.getProc?] at h
  rw [Program.find?_go_append_of_none ds es hgo]

/-- An empty program contains no procedure. -/
theorem Program.Procedure.find?_nil (x : Expression.Ident) :
    Program.Procedure.find? { decls := [] } x = none := by
  rw [Program.Procedure.find?_eq_go]
  simp only [Program.find?_go_nil]
  rfl

/-- A procedure at the head of a program is found under its own name. -/
theorem Program.Procedure.find?_cons_proc_self (p : Procedure) (md : MetaData Expression)
    (L : Decls) :
    Program.Procedure.find? { decls := Decl.proc p md :: L } p.header.name = some p := by
  rw [Program.Procedure.find?_eq_go]
  rw [Program.find?_go_cons]
  rw [ite_eq_left (by simp [Decl.kind, Decl.name])]
  rfl

/-- A non-procedure declaration at the head does not affect procedure lookup. -/
private theorem Program.Procedure.find?_cons_not_proc (d : Decl) (L : Decls)
    (hkind : d.kind ≠ DeclKind.proc) (x : Expression.Ident) :
    Program.Procedure.find? { decls := d :: L } x
      = Program.Procedure.find? { decls := L } x := by
  rw [Program.Procedure.find?_eq_go, Program.Procedure.find?_eq_go]
  dsimp only
  rw [Program.find?_go_cons]
  rw [ite_eq_right (by simp [hkind])]

/-- Appending a non-procedure declaration cannot change procedure lookup. -/
theorem Program.Procedure.find?_append_singleton_not_proc (ds : Decls) (d : Decl)
    (hkind : d.kind ≠ DeclKind.proc) (x : Expression.Ident) :
    Program.Procedure.find? { decls := ds ++ [d] } x
      = Program.Procedure.find? { decls := ds } x := by
  cases hpre : Program.Procedure.find? { decls := ds } x with
  | some q => exact Program.Procedure.find?_append_of_some ds [d] x q hpre
  | none =>
    rw [Program.Procedure.find?_append_of_none ds [d] x hpre,
        Program.Procedure.find?_cons_not_proc d [] hkind x,
        Program.Procedure.find?_nil]

/-- Successful lookup in a singleton procedure program returns that procedure and its name. -/
theorem Program.Procedure.find?_singleton_proc (p : Procedure) (md : MetaData Expression)
    (x : Expression.Ident) (q : Procedure)
    (h : Program.Procedure.find? { decls := [Decl.proc p md] } x = some q) :
    x = p.header.name ∧ q = p := by
  rw [Program.Procedure.find?_eq_go] at h
  dsimp only at h
  rw [Program.find?_go_cons] at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    have hx : x = p.header.name := by
      have hname := hcond.2; simp only [Decl.name] at hname; exact hname.symm
    refine ⟨hx, ?_⟩
    have h2 : Decl.getProc? (Decl.proc p md) = some q := by simpa using h
    have hg : Decl.getProc? (Decl.proc p md) = some p := rfl
    rw [hg] at h2
    exact (by simpa using h2 : p = q).symm
  · rw [Program.find?_go_nil] at h; simp at h

/-! ### Locating a procedure from a membership fact -/

/-- A procedure that occurs in a declaration list is what `Program.Procedure.find?` returns
    for its own name, provided the list's declared names are distinct. -/
theorem Program.Procedure.find?_of_mem_of_getNames_nodup
    (L : Decls) (q : Procedure) (mdq : MetaData Expression)
    (hnodup : (Program.getNames.go L).Nodup)
    (hmem : Decl.proc q mdq ∈ L) :
    Program.Procedure.find? { decls := L } q.header.name = some q := by
  have key : ∀ (M : Decls), (Program.getNames.go M).Nodup → Decl.proc q mdq ∈ M →
      Program.find?.go DeclKind.proc q.header.name M = some (Decl.proc q mdq) := by
    intro M
    induction M with
    | nil => intro _ hm; simp at hm
    | cons d rest ih =>
      intro hnd hm
      have hndFlat : (List.flatMap Decl.names (d :: rest)).Nodup := by
        simpa only [Program.getNames.go] using hnd
      rw [List.flatMap_cons] at hndFlat
      obtain ⟨-, hrestNodup, hdisj⟩ := List.nodup_append.mp hndFlat
      rw [Program.find?_go_cons]
      rcases List.mem_cons.mp hm with heq | htl
      · rw [← heq]
        simp [Decl.kind, Decl.name]
      · have hcond : ¬ ((d.kind == DeclKind.proc && d.name == q.header.name) = true) := by
          intro hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨hk, hn⟩ := hc
          have hdn : Decl.names d = [d.name] := by
            cases d <;> simp_all [Decl.kind, Decl.names]
          have hmemSelf : d.name ∈ Decl.names d := by rw [hdn]; simp
          have hmemRest : q.header.name ∈ List.flatMap Decl.names rest :=
            List.mem_flatMap.mpr ⟨Decl.proc q mdq, htl, by simp [Decl.names, Decl.name]⟩
          exact hdisj d.name hmemSelf q.header.name hmemRest hn
        rw [ite_eq_right hcond]
        exact ih (by simpa only [Program.getNames.go] using hrestNodup) htl
  rw [Program.Procedure.find?_eq_go]
  show (Program.find?.go DeclKind.proc q.header.name L).bind Decl.getProc? = some q
  rw [key L hnodup hmem]
  rfl

/-- In a program with distinct declared names, a procedure in a suffix of its declarations is
    found under its own name. -/
theorem Program.Procedure.find?_of_mem_of_suffix
    (program : Program) (ds : Decls) (q : Procedure) (mdq : MetaData Expression)
    (hnodup : (Program.getNames.go program.decls).Nodup)
    (hsuffix : ds <:+ program.decls) (hmem : Decl.proc q mdq ∈ ds) :
    Program.Procedure.find? program q.header.name = some q := by
  obtain ⟨pre, hpre⟩ := hsuffix
  have hmemDecls : Decl.proc q mdq ∈ program.decls := by
    rw [← hpre]; exact List.mem_append_right _ hmem
  simpa using
    Program.Procedure.find?_of_mem_of_getNames_nodup program.decls q mdq hnodup hmemDecls

/-- If no user functions precede `procName`, its visible factory is exactly
    `Core.Factory`. -/
theorem Program.factoryBeforeProcedure_eq_core_of_noFunctions
    {p : Program} {procName : String}
    (h : (p.declsBeforeProcedure procName).all fun d =>
      match d with
      | .func _ _ | .recFuncBlock _ _ => false
      | _ => true) :
    p.factoryBeforeProcedure procName = Core.Factory := by
  simp only [List.all_eq_true] at h
  unfold Program.factoryBeforeProcedure
  have go : ∀ decls : List Decl,
      (∀ d ∈ decls,
        (match d with
         | .func _ _ | .recFuncBlock _ _ => false
         | _ => true) = true) →
      decls.foldl Decl.addFunctionsToFactory Core.Factory = Core.Factory := by
    intro decls hdecls
    induction decls with
    | nil => rfl
    | cons d ds ih =>
        rw [List.foldl_cons]
        have hd := hdecls d (List.mem_cons_self)
        have hds : ∀ d ∈ ds,
            (match d with
             | .func _ _ | .recFuncBlock _ _ => false
             | _ => true) = true :=
          fun d hdmem => hdecls d (List.mem_cons_of_mem _ hdmem)
        cases d <;> simp at hd
        all_goals simpa [Decl.addFunctionsToFactory] using ih hds
  exact go (p.declsBeforeProcedure procName) h

/-- **The declarations before `q` are those the verifier gives it.** If `q` is the first
    procedure of `p` with its name, the declarations before it are
    `p.declsBeforeProcedure`, the prefix the entry semantics uses for `q`. -/
theorem Program.declsBeforeProcedure_eq {p : Program} {pre post : List Decl} {q : Procedure}
    {md : Imperative.MetaData Expression} (hd : p.decls = pre ++ Decl.proc q md :: post)
    (hfirst : ∀ q' md', Decl.proc q' md' ∈ pre → q'.header.name.name ≠ q.header.name.name) :
    p.declsBeforeProcedure q.header.name.name = pre := by
  unfold Program.declsBeforeProcedure
  rw [hd, List.takeWhile_append_of_pos]
  · simp
  · intro d hdm
    cases d with
    | proc q' md' => simpa using hfirst q' md' hdm
    | _ => rfl

/-- A declaration `Program.find?` returns is one of the program's declarations. -/
theorem Program.find?_mem {p : Program} {k : DeclKind} {x : Expression.Ident} {d : Decl}
    (h : p.find? k x = some d) : d ∈ p.decls := by
  simp only [find?] at h
  generalize p.decls = decls at h
  induction decls with
  | nil => simp [Program.find?.go] at h
  | cons e rest ih =>
    unfold Program.find?.go at h
    split at h
    · cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

end Core

end -- public section
