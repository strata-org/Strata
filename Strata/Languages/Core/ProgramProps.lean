/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
import Strata.Util.ListUtilsProps
import all Strata.Languages.Core.Program

/-! # Properties of Core programs

Facts about procedure lookup, declaration-order views of a `Program` and the expression
factories constructed from them.

Key results:
- `Program.Procedure.find?_eq_go` — procedure lookup is a scan of the declarations.
- `Program.Procedure.find?_of_procs_eq`, `Program.callSites_of_procs_eq` — procedure lookup
  and the calls of a program depend only on its procedures, in order.
- `Program.funcsAll_of_funcs` — a check on functions carries to a program whose functions agree
  with the original's on it; `noFuncPreconditions` and `noPolymorphicFunctions` are such checks.
- `Program.Procedure.find?_of_mem_of_getNames_nodup`, `Program.Procedure.find?_of_mem_of_suffix`
  — with distinct declared names, a procedure in the program is found under its own name.
- `Program.Procedure.find?_of_mem_of_procNames_nodup` — the same with only the procedure names
  distinct.
- `Program.factoryBeforeProcedure_eq_core_of_noFunctions` — when no user
  function and no datatype precedes a procedure, its visible factory is `Core.Factory`.
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
    for its own name, provided the names that the list's procedure declarations introduce are
    distinct. -/
theorem Program.Procedure.find?_of_mem_of_procNames_nodup
    (L : Decls) (q : Procedure) (mdq : MetaData Expression)
    (hnodup : ((L.filter (fun d => d.kind == DeclKind.proc)).flatMap Decl.names).Nodup)
    (hmem : Decl.proc q mdq ∈ L) :
    Program.Procedure.find? { decls := L } q.header.name = some q := by
  have key : ∀ (M : Decls),
      ((M.filter (fun d => d.kind == DeclKind.proc)).flatMap Decl.names).Nodup →
      Decl.proc q mdq ∈ M →
      Program.find?.go DeclKind.proc q.header.name M = some (Decl.proc q mdq) := by
    intro M
    induction M with
    | nil => intro _ hm; simp at hm
    | cons d rest ih =>
      intro hnd hm
      rw [Program.find?_go_cons]
      rcases List.mem_cons.mp hm with heq | htl
      · rw [← heq]
        simp [Decl.kind, Decl.name]
      · obtain ⟨hndRest, hcond⟩ : ((rest.filter (fun d => d.kind == DeclKind.proc)).flatMap
            Decl.names).Nodup ∧
            ¬ ((d.kind == DeclKind.proc && d.name == q.header.name) = true) := by
          by_cases hk : d.kind = DeclKind.proc
          · have hkb : (d.kind == DeclKind.proc) = true := beq_iff_eq.2 hk
            rw [List.filter_cons_of_pos (p := fun (d : Decl) => d.kind == DeclKind.proc) hkb,
              List.flatMap_cons] at hnd
            obtain ⟨-, hndRest, hdisj⟩ := List.nodup_append.mp hnd
            refine ⟨hndRest, fun hc => ?_⟩
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            have hdn : Decl.names d = [d.name] := by
              cases d <;> simp_all [Decl.kind, Decl.names]
            have hmemSelf : d.name ∈ Decl.names d := by rw [hdn]; simp
            have hqk : ((Decl.proc q mdq).kind == DeclKind.proc) = true := by simp [Decl.kind]
            have hqn : q.header.name ∈ Decl.names (Decl.proc q mdq) := by
              simp [Decl.names, Decl.name]
            have hmemRest : q.header.name ∈
                (rest.filter (fun d => d.kind == DeclKind.proc)).flatMap Decl.names :=
              List.mem_flatMap.mpr ⟨Decl.proc q mdq, List.mem_filter.2 ⟨htl, hqk⟩, hqn⟩
            exact hdisj d.name hmemSelf q.header.name hmemRest hc.2
          · have hkb : ¬ (d.kind == DeclKind.proc) = true := fun h => hk (beq_iff_eq.1 h)
            rw [List.filter_cons_of_neg (p := fun (d : Decl) => d.kind == DeclKind.proc)
              hkb] at hnd
            refine ⟨hnd, fun hc => hk ?_⟩
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            exact hc.1
        rw [ite_eq_right hcond]
        exact ih hndRest htl
  rw [Program.Procedure.find?_eq_go]
  show (Program.find?.go DeclKind.proc q.header.name L).bind Decl.getProc? = some q
  rw [key L hnodup hmem]
  rfl

/-- A procedure that occurs in a declaration list is what `Program.Procedure.find?` returns
    for its own name, provided the list's declared names are distinct. -/
theorem Program.Procedure.find?_of_mem_of_getNames_nodup
    (L : Decls) (q : Procedure) (mdq : MetaData Expression)
    (hnodup : (Program.getNames.go L).Nodup)
    (hmem : Decl.proc q mdq ∈ L) :
    Program.Procedure.find? { decls := L } q.header.name = some q := by
  have hsub : List.Sublist ((L.filter (fun d => d.kind == DeclKind.proc)).flatMap Decl.names)
      (List.flatMap Decl.names L) :=
    List.Sublist.flatMap_of_sublist Decl.names List.filter_sublist
  have hnodupFlat : (List.flatMap Decl.names L).Nodup := by
    simpa only [Program.getNames.go] using hnodup
  exact Program.Procedure.find?_of_mem_of_procNames_nodup L q mdq (hnodupFlat.sublist hsub) hmem

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
  exact Program.Procedure.find?_of_mem_of_getNames_nodup program.decls q mdq hnodup hmemDecls

/-- If no function and no datatype is declared before `procName`, its visible factory is
    exactly `Core.Factory`. -/
theorem Program.factoryBeforeProcedure_eq_core_of_noFunctions
    {p : Program} {procName : String}
    (h : (p.declsBeforeProcedure procName).all fun d =>
      match d with
      | .func _ _ | .recFuncBlock _ _ | .type (.data _) _ => false
      | _ => true) :
    p.factoryBeforeProcedure procName = Core.Factory := by
  simp only [List.all_eq_true] at h
  unfold Program.factoryBeforeProcedure
  have go : ∀ decls : List Decl,
      (∀ d ∈ decls,
        (match d with
         | .func _ _ | .recFuncBlock _ _ | .type (.data _) _ => false
         | _ => true) = true) →
      decls.foldl Decl.addToRuntimeFactory Core.Factory = Core.Factory := by
    intro decls hdecls
    induction decls with
    | nil => rfl
    | cons d ds ih =>
        rw [List.foldl_cons]
        have hd := hdecls d (List.mem_cons_self)
        have hds : ∀ d ∈ ds,
            (match d with
             | .func _ _ | .recFuncBlock _ _ | .type (.data _) _ => false
             | _ => true) = true :=
          fun d hdmem => hdecls d (List.mem_cons_of_mem _ hdmem)
        cases d <;> (try cases ‹TypeDecl›) <;> simp at hd <;>
          simpa [Decl.addToRuntimeFactory, Decl.addFunctionsToFactory] using ih hds
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

/-- Dropping declarations of other kinds than `k` does not change a scan for kind `k`. -/
private theorem Program.find?_go_filter {k : DeclKind} {x : Expression.Ident} {q : Decl → Bool}
    (decls : Decls) (hq : ∀ d ∈ decls, d.kind = k → q d = true) :
    Program.find?.go k x (decls.filter q) = Program.find?.go k x decls := by
  induction decls with
  | nil => rfl
  | cons d ds ih =>
    have ih := ih fun e he => hq e (List.mem_cons_of_mem _ he)
    rw [Program.find?_go_cons]
    by_cases hd : q d = true
    · rw [List.filter_cons_of_pos hd, Program.find?_go_cons, ih]
    · have hk : d.kind ≠ k := fun hk => hd (hq d List.mem_cons_self hk)
      rw [List.filter_cons_of_neg hd, ih, ite_eq_right (by simp [hk])]

/-- Procedure lookup reads only the procedures of a program. -/
private theorem Program.Procedure.find?_eq_procs (P : Program) (x : Expression.Ident) :
    Program.Procedure.find? P x =
      Program.Procedure.find? { decls := P.decls.filter Decl.isProc } x := by
  have hq : ∀ d ∈ P.decls, d.kind = .proc → Decl.isProc d = true := fun d _ hk => by
    unfold Decl.isProc; rw [hk]; rfl
  rw [Program.Procedure.find?_eq_go, Program.Procedure.find?_eq_go]
  exact (congrArg (·.bind Decl.getProc?) (Program.find?_go_filter P.decls hq)).symm

/-- Two programs with the same procedures, in the same order, look procedures up alike. -/
theorem Program.Procedure.find?_of_procs_eq {P P' : Program}
    (h : P'.decls.filter Decl.isProc = P.decls.filter Decl.isProc) (x : Expression.Ident) :
    Program.Procedure.find? P' x = Program.Procedure.find? P x := by
  rw [Program.Procedure.find?_eq_procs P', Program.Procedure.find?_eq_procs P, h]

/-- Two programs with the same procedures, in the same order, have the same calls. -/
theorem Program.callSites_of_procs_eq {P P' : Program}
    (h : P'.decls.filter Decl.isProc = P.decls.filter Decl.isProc) :
    P'.callSites = P.callSites := by
  have hprocs : ∀ ds : List Decl, ds.flatMap Decl.callSites =
      (ds.filter Decl.isProc).flatMap Decl.callSites := by
    intro ds
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      by_cases hd : d.isProc = true
      · simp [List.filter_cons_of_pos hd, ih]
      · rw [List.filter_cons_of_neg hd, List.flatMap_cons, ← ih]
        cases d <;> simp_all [Decl.isProc, Decl.kind, Decl.callSites]
  simp only [Program.callSites]
  rw [hprocs P'.decls, hprocs P.decls, h]

/-- Dropping declarations that are not procedures keeps the procedures, in order. -/
theorem Decl.filter_isProc_filter {q : Decl → Bool} {ds : List Decl}
    (hq : ∀ d ∈ ds, d.kind = .proc → q d = true) :
    (ds.filter q).filter Decl.isProc = ds.filter Decl.isProc := by
  rw [List.filter_filter]
  exact List.filter_congr fun d hd => by
    by_cases hk : d.kind = .proc
    · simp [Decl.isProc, hk, hq d hd hk]
    · simp [Decl.isProc, hk]

/-- A list of declarations none of which is a procedure has no procedures. -/
theorem Decl.filter_isProc_eq_nil {ds : List Decl} (h : ∀ d ∈ ds, d.isProc = false) :
    ds.filter Decl.isProc = [] :=
  List.filter_eq_nil_iff.mpr fun d hd => by simp [h d hd]

/-! ### Checks on the functions a program declares -/

/-- `noPrecondsFromFuncs` asks of each declared function that it has no precondition. -/
theorem Program.noFuncPreconditions_eq_funcsAll (p : Program) :
    p.noFuncPreconditions = p.funcsAll (·.preconditions.isEmpty) := by
  unfold Program.noFuncPreconditions Program.funcsAll
  congr 1; funext d; cases d <;> simp [Decl.funcs]

/-- `noPolymorphicFunctions` asks of each declared function that it has no type parameter. -/
theorem Program.noPolymorphicFunctions_eq_funcsAll (p : Program) :
    p.noPolymorphicFunctions = p.funcsAll (·.typeArgs.isEmpty) := by
  unfold Program.noPolymorphicFunctions Program.funcsAll
  congr 1; funext d; cases d <;> simp [Decl.funcs]

/-- A check every function of `p` passes holds of every function of `p'` that passes it itself
    or agrees with some function of `p` on it. -/
theorem Program.funcsAll_of_funcs {c : Function → Bool} {p p' : Program}
    (h : ∀ d' ∈ p'.decls, ∀ f' ∈ d'.funcs,
      c f' = true ∨ ∃ d ∈ p.decls, ∃ f ∈ d.funcs, c f' = c f)
    (hp : p.funcsAll c = true) : p'.funcsAll c = true := by
  simp only [Program.funcsAll, List.all_eq_true] at hp ⊢
  intro d' hd' f' hf'
  rcases h d' hd' f' hf' with h | ⟨d, hd, f, hf, hc⟩
  · exact h
  · exact hc.trans (hp d hd f hf)

end Core

end -- public section
