/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProgramFact

/-! # Properties of program facts

Key results:

* `ProgramFact.all_complete` — `ProgramFact.all` enumerates every constructor.
* `ProgramFact.all_nodup` — it lists each one once, which is what makes
  canonical lists duplicate-free.
* `ProgramFact.holds_iff_check` — a fact holds exactly when its own executable
  check accepts, for a fact that has one; `ProgramFact.holds_iff_check_get` is
  the form an asserting phase uses, which knows only that a check exists.
  These are the bridge from a fact's `Prop` to something a machine can
  evaluate. -/

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
    simp only [ProgramFact.check?, Option.some.injEq] at h <;>
    subst h <;>
    simp [ProgramFact.holds]

/-- A fact that has a check holds of a program exactly when that check
    accepts it. The form an asserting phase uses: it knows only that the fact
    has a check, not which function it is. -/
theorem ProgramFact.holds_iff_check_get {f : ProgramFact} (hc : f.check?.isSome = true)
    (p : Program) : f.holds p ↔ (f.check?.get hc) p = true :=
  ProgramFact.holds_iff_check (Option.some_get hc).symm p

end -- public section

end Core
