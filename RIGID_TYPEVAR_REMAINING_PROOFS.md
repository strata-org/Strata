# Remaining Proof Obligations for Rigid Type Variable Fix

Two sorry'd lemmas in `Strata/Languages/Core/CmdTypeProps.lean` remain.

## 1. `inferType_absorbs`

**Statement:**
```lean
theorem inferType_absorbs (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst
```

**What it says:** The substitution produced by `inferType` absorbs the input substitution.

**Proof sketch:**

`CmdType.inferType` (in `CmdType.lean:60-66`) does:
1. `Env.freeVarCheck e` — doesn't change the env (returns Unit).
2. `LExpr.resolve C Env e` — this is the only step that modifies the env.

So the obligation reduces to: `LExpr.resolve` produces a substitution that absorbs the input.

`LExpr.resolve` (in `LExprResolve.lean`) internally calls `Constraints.unify` to solve
type constraints from the expression. Each `Constraints.unify` call produces a result
that absorbs its input (`Constraints.unify_absorbs` in `LTyUnifyProps.lean`). The resolve
function chains these — each intermediate result absorbs the previous.

The existing `resolveAux_HasTypeA_aux` proof in `LExprResolveProps.lean` already takes
an `h_absorbs` parameter and threads it through resolve's structure (lines 575-660),
confirming that the absorption chain is maintained. The proof should follow the same
structural induction as `resolveAux_HasTypeA_aux`, extracting the absorption conclusion
instead of the HasTypeA conclusion.

**Key existing lemma:**
- `resolveAux_properties` (in `LExprTypeSpec.lean:3645`) — returns a
  `ResolveAuxProperties` structure whose `.absorbs` field is exactly
  `Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst`.

**Difficulty: LOW.** The proof is just unfolding `inferType` (= `freeVarCheck` then
`resolve`), noting `freeVarCheck` doesn't change env, then extracting `.absorbs` from
`resolveAux_properties`. The main work is providing the preconditions (`h_ne`, `h_aw`,
`h_fwf`, `h_sf`, `h_cf`, `h_bvf`) — all of which come from `TEnvWF`.

## 2. `checkAnnotCompat_rigid`

**Statement:**
```lean
theorem checkAnnotCompat_rigid (C : LContext CoreLParams) (Env : TEnv Unit) (xty : LTy)
    (h : CmdType.checkAnnotCompat C Env xty = .ok ()) :
    ∀ v, v ∈ C.rigidTypeVars → LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v
```

**What it says:** If `checkAnnotCompat` passes, no rigid type variable was refined.

**Proof sketch:**

`checkAnnotCompat` (in `CmdType.lean:99-113`) does:
1. If `C.rigidTypeVars.isEmpty` → returns `.ok ()`. In this case the conclusion is
   vacuously true (no `v ∈ []`).
2. Otherwise, iterates `C.rigidTypeVars.find? (fun v => subst S (ftvar v) != ftvar v)`:
   - If `some v` → returns error (contradicts `h`).
   - If `none` → returns `.ok ()`.

When `find? ... = none`, by definition of `List.find?`, for ALL elements `v` in the list,
the predicate `subst S (ftvar v) != ftvar v` is `false`, i.e.,
`subst S (ftvar v) = ftvar v`. This is exactly the conclusion.

**Key proof steps:**
1. Unfold `CmdType.checkAnnotCompat` in `h`.
2. Case-split on `C.rigidTypeVars.isEmpty`:
   - If true: intro `v hv`; `List.mem_nil_iff` gives contradiction.
   - If false: the `find? ... = none` branch gives `List.find?_eq_none` which states
     the predicate is false for all elements. Use `Bool.not_eq_true` / `decide` to
     convert `(subst S (ftvar v) != ftvar v) = false` to the equality.

**Difficulty: LOW.** Pure definitional unfolding + standard list lemma. No induction,
no dependent types, no mutual recursion.

## 3. Invariant Preservation (`Cmd.typeCheck` preserves `h_rigid_inv`)

The `Cmd.typeCheck_sound` theorem takes `h_rigid_inv` as a hypothesis. The caller
must know the invariant is preserved — i.e., if it holds for `Env`, it also holds
for `Env'` after `Cmd.typeCheck`. This is a theorem about commands:

**Statement:**
```lean
theorem Cmd.typeCheck_preserves_rigid_inv (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) :
    ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env'.stateSubstInfo.subst (.ftvar v) = .ftvar v
```

**Proof sketch:**

Case-split on the command:

- **`init` det:** The env pipeline is `preprocess → inferType → unifyTypes →
  checkAnnotCompat → postprocess → update`. The output `Env'` has
  `Env'.stateSubstInfo = (update (postprocess Env_unified)).stateSubstInfo`.
  Both `postprocess` and `update` preserve `stateSubstInfo` (existing lemmas).
  So `Env'.stateSubstInfo = Env_unified.stateSubstInfo`.
  `checkAnnotCompat_rigid` on `Env_unified` gives the conclusion.

- **`init` nondet:** No unification happens. `Env'` = `update (postprocess (preprocess Env))`.
  All three preserve `stateSubstInfo`, so `Env'.subst = Env.subst` and the
  invariant is inherited directly from `h_rigid_inv`.

- **`set` det:** Same structure as `init` det: `inferType → unifyTypes →
  checkAnnotCompat`. Output `Env' = Env_unified`. `checkAnnotCompat_rigid` applies.

- **`set` nondet:** `Env' = Env`, trivial.

- **`assert`/`assume`/`cover`:** These now call `inferType → checkAnnotCompat →
  isBoolType`. The output env is from `inferType` (the `isBoolType` check doesn't
  change it). `checkAnnotCompat_rigid` on the post-inferType env gives the conclusion
  directly, same as the `init det` / `set det` cases.

**Difficulty: LOW.** Every case reduces to `checkAnnotCompat_rigid` applied to the
env that `checkAnnotCompat` was called on, plus showing `Env'` has the same
`stateSubstInfo` as that env (via preservation lemmas for `postprocess`/`update`).

**Key lemmas needed:** `checkAnnotCompat_rigid`, `update_preserves_subst`,
`preprocess_preserves_stateSubstInfo`, `postprocess` preserves subst (from
`postprocess_result`'s `Env' = Env` conclusion).

## Summary

| Lemma | Difficulty | Roadblocks |
|-------|-----------|------------|
| `checkAnnotCompat_rigid` | Low | None — pure unfolding |
| `inferType_absorbs` | Low | None — `resolveAux_properties.absorbs` already proves it |
| `typeCheck_preserves_rigid_inv` | Low | None — each case uses `checkAnnotCompat_rigid` |

No conceptual roadblocks remain. All three are mechanical proofs that apply existing
lemmas. The main effort is providing the preconditions for `resolveAux_properties`
(all derivable from `TEnvWF`) and unfolding `checkAnnotCompat`'s definition.
