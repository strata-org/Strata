# Implementation plan: remove polymorphic var-init (command-only)

**Branch:** `josh/remove-poly-init` — a command-only branch (no `Function` typing info; only
`Cmd`/`Statement`/`Procedure`). All commands run inside a statement inside a procedure, so
`C.rigidTypeVars` IS populated (by `ProcedureType`) — Part B's in-scope check is meaningful here.

**Design source:** [`REMOVE_POLY_VAR_INIT.md`](./REMOVE_POLY_VAR_INIT.md) (the *what* and *why*).
This doc is the ordered *how*, scoped to command code + command proofs. The function-side payoff
(replacing the false `h_ambient_rigid`) lands on the function branch later.

## Scope

**IN:** `Core/CmdType.lean`, `Core/CmdTypeProps.lean`, `Core/CmdTypeSpec.lean`,
`Core/CmdTypeSpecProps.lean`, command test files.

**OUT (do NOT touch on this branch):** `FunctionType.lean`, `FunctionTypeSpec*.lean`,
`ProcedureType.lean`, `Factory.lean`, function-soundness proofs.

## The fix in one line

Two checks guard `var` bindings:
- **`preprocess` (pre-unification):** the annotation must be **monomorphic** — reject `ty.boundVars != []`
  (`var x : ∀a. …`). A polymorphic annotation would be instantiated to a fresh tyvar and leak a
  non-rigid free var into the ambient context. This is the genuine #1399 fix.
- **`postprocess` (post-unification):** the **final stored** monotype's free vars must all be rigid
  (`(LMonoTy.freeVars ty).filter (· ∉ C.rigidTypeVars) = []`). This is the actual capture guard: a
  free var that *survived* unification (`var x : a := *`, no `proc<a>`) would be stored as
  `forall [] a` and generalized by a nested `funcDecl` — the bug. A free var that unification
  *solved away* (CallElim's `var f : a := b`, `a` solved against `b`) is already gone here.

The `init` spec rules keep the HEAD `RigidAnnotCompat`/`tys`/`openFull` form (the plain-`AliasEquiv`
simplification was reverted — see "Course correction" below).

---

## Phase 0 — baseline ✅ DONE
1. ✅ `lake build Strata.Languages.Core.CmdTypeSpecProps` — green (122 jobs), zero sorries in
   all four command files. Baseline recorded.

## Course correction (why the design changed mid-implementation)

The first attempt put **both** checks in `preprocess` (monomorphic + free-vars-rigid) and
**simplified the spec** from `RigidAnnotCompat`/`tys`/`openFull` to a plain `AliasEquiv`. Phase-5
testing exposed two fatal problems:

1. **The free-vars-rigid check at `preprocess` (pre-unification) is wrong in both directions.**
   - It rejected legitimate code: inside `proc P<t>(x:t)`, `var z : t` was rejected because the
     **raw** annotation names `t`, while `rigidTypeVars` holds the *fresh renamed* var `$__ty0`
     (the `t → $__ty0` body substitution only applies *during* instantiation, after the check).
   - When "fixed" to subst-first, it broke **CallElim**: `Core.verify` rewrites `call Id(b,out i)`
     (for `Id<a>(x:a,out y:a)`) into generated `var f : a := b` and re-typechecks at the *caller's*
     scope, where `a` is free and meant to be unified — `preprocess` can't tell this benign case
     from the bug, because both look like a free var *before* unification.
   - **Dropping the check entirely reopened #1399** (the whole point): `var x : a := *` stores
     `forall [] a`, capturable by a nested `funcDecl`.

   **Resolution:** move the free-vars-rigid check to **`postprocess`**, which both `init` paths hit
   *after* `unifyTypes`. There the bug case still has a free `a` (reject); CallElim's case has `a`
   already solved to `bool` (accept). This is the single correct checkpoint.

2. **The plain-`AliasEquiv` spec couldn't express `var z : t`** (annotation `t` ≠ stored `$__ty0`
   under alias-equivalence). **Resolution:** revert spec + proofs to HEAD's `RigidAnnotCompat` form,
   which relates them via an existential σ (the rename) — exactly what's needed.

## Phase 1 — typechecker code (`Core/CmdType.lean`) ✅ DONE
2. ✅ **`preprocess`**: reject `ty.boundVars != []` only ("Variable annotation must be monomorphic …").
   This is the sole pre-unification check.
3. ✅ **`postprocess`**: now takes `C`, and on the mono branch rejects when
   `(LMonoTy.freeVars ty).filter (· ∉ C.rigidTypeVars) != []` ("… references type variables … that
   are not procedure type parameters"). Runs after unification → distinguishes the bug from CallElim.
4. ✅ `Cmd.init` AST field kept as `LTy`. `Core.CmdType` builds.

## Phase 2 — spec rules (`Core/CmdTypeSpec.lean`) ✅ DONE (reverted to HEAD)
5. ✅ `init_det`/`init_nondet` keep HEAD's form: `tys` existential, `boundVars`-length premise, and
   `RigidAnnotCompat Γ.aliases C.rigidTypeVars (openFull xty tys) mty`. No spec change on this branch.

## Phase 3 — soundness proof (`Core/CmdTypeSpecProps.lean`) ✅ DONE (reverted to HEAD)
7. ✅ Init cases use HEAD's `preprocess_isInstance_rigidAnnotCompat` (no rewrite needed). The
   `postprocess` change is absorbed by `postprocess_result` (Phase 4).

## Phase 4 — typechecker-property lemmas (`Core/CmdTypeProps.lean`) 🔧 IN PROGRESS
10. ✅ **`preprocess_decompose`** added — peels the single monomorphic guard + `instantiateWithCheck`;
    the single decomposition point for `preprocess_mono`,
    `preprocess_preserves_stateSubstInfo`/`_context`/`_TEnvWF` and
    `preprocess_isInstance`/`_rigidAnnotCompat` (the latter two restored from HEAD, delegating to it).
11. 🔧 **`postprocess_result`** — needs to peel the new `postprocess` stray-var guard (the `else`
    success branch gives the same `ty' = forAll [] (subst …)` conclusion). *Currently failing on the
    isTrue-branch simp — in progress.*
12. ⏳ Re-confirm full `Core.CmdTypeSpecProps` builds green, zero sorries.

## Phase 5 — tests ⏳ behavior VERIFIED, expectations to lock
14. **`MonoLocalBindingTest.lean`** rewritten (3 cases): polymorphic `∀a.a→a` rejected (Part A);
    bare `var z : a` rejected (postprocess); `var z : t` under `proc<t>` accepted. Outputs to lock.
15. **`StatementTypeTests.lean`** (4 sites) and **`RigidTypeVarsTests.lean`** (Q1, 2 sites) use
    polymorphic `var : ∀a.…` annotations now rejected — update expectations. **CallElim regressions
    (RigidTypeVarsTests lines 101, 147) are FIXED** by the postprocess approach; A1–A7, Q2a–c pass.
16. Lock outputs with `#guard_msgs`.

### Behavior verified empirically (before proof completion)
- `var x : a := *` (free, unsolved) → **REJECTED** (#1399 closed).
- `var f : a := b` with `b:bool` (CallElim-like, `a` solved) → **ACCEPTED** (no regression).
- `var z : t` under `proc P<t>(x:t)` → **ACCEPTED** (rigid var, mirrors function bodies).
- `var x : ∀a.a→a` → **REJECTED** (Part A).

---

## Status: code DONE + behavior verified. Phase 4 proof (`postprocess_result`) in progress; Phase 5
## expectations to lock once proofs are green.

## Build checkpoints
After each phase: `lake build` the affected module + `lean_goal`/`lean_diagnostic_messages`
between edits. **Always verify test behavior before fixing proofs** (a proof can be made to pass on
a spec that doesn't match real typechecker behavior).
