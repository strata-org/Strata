/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
import all Strata.Languages.Core.Program

/-! # Properties of Core programs

Facts about declaration-order views of a `Program` and the expression factories
constructed from them.

Key results:
- `Program.factoryBeforeProcedure_eq_core_of_noFunctions` — when no user
  functions precede a procedure, its visible factory is `Core.Factory`.
- `Program.declsBeforeProcedure_eq` — the declarations before the first procedure
  of a name are `declsBeforeProcedure` of that name.
-/

public section

namespace Core

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
