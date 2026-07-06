# Simplifying the `Function` soundness proofs

**Scope.** This doc is about *how* we prove the two deliverables, and one checker
implementation detail. **Neither top-level theorem statement changes.** Both stay,
with their current meaning:

- `Function.typeCheck_sound : … → FuncHasType C Env.context func`
  — success ⟹ the **original** `func` is well-typed under the **polymorphic** `HasType`.
- `Function.typeCheck_annotated_sound : … → ∀ Γ, FuncHasTypeA C Γ func'`
  — success ⟹ the **resolved** `func'` is well-typed under the **annotated** `HasTypeA`.

There *will* be consumers (Procedure/Program-level soundness). The goal is to make
these provable in a few hundred lines, like the `Cmd` analog — not to remove them.

---

## 1. The problem, stated plainly

| | `Cmd.typeCheck_sound` | `Function.typeCheck_sound` |
|---|---|---|
| Proof size | ~250 readable lines | 3322 lines + a 1500-line plan, still has `sorry`s |
| Bridge to `resolve_HasType_core` | **direct** | via a lemma that is **false** (`HasType_TContext_subst`), now routed around with composite-subst machinery |
| Type-renaming/inverse infrastructure | none | ~1100 lines (`alphaEquivMap_renameSubst_inverse`, `go_bwd_mono/keys_subset/vals_subset/inverts`, `substWF_renameMap`, …) |

Both theorems sit on the **same** engine, `resolve_HasType_core.1` (LExprTypeSpec.lean:7607):

```
∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
     Subst.polyKeysFresh S Env.context →
  HasType C (TContext.subst Env.context S) e (.forAll [] (LMonoTy.subst S e_typed.toLMonoTy))
```

`Cmd` is short because **its spec concludes exactly this shape** — context `Γ.subst S`,
type `.forAll [] (subst S ty)`, for the chosen `S = Env'.subst`. Nothing to invert.

`Function` is long because its spec concludes about the **original user-named**
`func.output` and **original `funcContext`**, while the checker
(`FunctionType.lean:35–172`) runs this pipeline:

```
func.type
  → instantiate (fresh vars, decl order)        -- LTy.instantiateWithCheck
  → resolveAliases                              -- alias-free monotypes
  → push formals, resolve body                  -- LExpr.resolve  (the HasType engine)
  → unify (retty, bodyty) → S                   -- Constraints.unify
  → alphaEquivMap monoty (subst S monoty)       -- REJECT check + recover bwdMap
  → renameSubst from bwdMap.toList              -- fresh-unify-vars ↦ instantiation vars
  → rigid / #1399 generalization guards
  → userSubst: instantiation vars ↦ user names
```

So the proof must climb **back up** that entire pipeline to reach `func.output`. That
climb is the 3000 lines. Two facts confirm this is the wrong execution, not just hard:

1. **`HasType_TContext_subst` (LExprTypeSpec.lean:804) is false** — `LTy.subst` captures a
   range variable under a `.forAll` binder (machine-checked counterexample in
   `ALPHAEQUIV_RENAMESUBST_PLAN.md` §10c). The "obvious" bridge does not exist, which is
   why the plan grew a composite-substitution workaround ("ROUTE B").
2. The spec was **wrong twice** mid-proof (`funcContext` missing the ambient `Γ`; the D2
   lemma false as stated) and **three soundness bugs** (#1395, #1399, the measure one)
   surfaced. A target you keep getting wrong is a target whose proof is fighting the design.

The statements are fine. The **proof strategy** (invert the pipeline) and **one checker
choice** (recover the renaming by alpha-matching instead of remembering it) are the cost.

---

## 2. Two levers — both keep the theorem statements intact

### Lever 1 (checker): build the fresh→user renaming from the instantiation, not from `alphaEquivMap`'s `bwdMap`

**Today.** After unifying, the checker calls `alphaEquivMap monoty (subst S monoty)` and,
on success, reads a `bwdMap : HashMap`, then builds
`renameSubst = bwdMap.toList.filterMap (…)` to map surviving fresh-unify vars back to the
instantiation vars. **Recovering** this map by alpha-matching is what forces the proof to
reason about `go`/`goList` accumulators, monotonicity, key/value domains, inversion, and
`SubstWF` of the resulting map — the `go_bwd_*` + `alphaEquivMap_renameSubst_inverse` +
`substWF_renameMap` family (~1100 lines).

**Change.** The bijection already exists explicitly: `LTy.instantiate` (LExprTypeEnv.lean)
generated the fresh vars in **declaration order**, one per `func.type`'s bound vars
(= `func.typeArgs`, via `LFunc.type_boundVars_eq_typeArgs`). So:

- **Keep** `alphaEquivMap monoty inferredTy` as the **boolean reject check** — it is the
  "body may not over-constrain the polymorphic signature" guard, and that role is genuinely
  needed and correct. Nothing about the accept/reject behavior changes.
- **Stop** deriving `renameSubst` from `bwdMap`. Build the fresh→user renaming directly from
  the instantiation's fresh-var list (the `tys`/`freshtvs` already available from
  `LTy_instantiateWithCheck_isInstance`), so its inverse is **definitional**, not recovered.

**Effect on proofs.** The entire `go_bwd_*` / `alphaEquivMap_renameSubst_inverse` /
`substWF_renameMap` block (FunctionTypeSpecProps.lean:240–909, plus the `_ftvar`/`_inverse`
wrappers 911–1006) **deletes**. The renaming's `SubstWF`/inverse facts come from
`genTyVars` freshness + distinctness, which are short and already partly proved.

**Behavioral footprint.** Accept/reject set is **identical** (the alpha check still runs).
The final user-named `func'` is **identical** (same user names, same monotypes). Only the
*intermediate source* of the renaming changes. The plan already discovered the right
witness for this in §10g ("ρ is NOT userSubst; use the declaration-order instantiation
inverse") — but kept `bwdMap` for the body anyway. This lever commits to it uniformly.

> Note: §10g's counterexample (`f[a,b](x:b,y:a):a`) shows the *appearance-order* `userSubst`
> is the wrong witness; the *declaration-order* instantiation inverse is correct. Lever 1 is
> exactly "use the object the checker already built in declaration order."

### Lever 2 (proof): fold the renaming into `resolve_HasType_core`'s universal `S` — never bridge a finished judgment

**Today (broken).** `typeCheck_bodyTyped` wants to take the resolved judgment and *then*
substitute the context+type to reach `funcContext`/`func.output` — that is exactly
`HasType_TContext_subst`, **which is false**.

**Change.** Don't bridge after the fact. `resolve_HasType_core.1` is **universally
quantified over every absorbing WF `S`**, and it performs the context+type substitution
*inside* its own (sound) induction. So instantiate it **once** at

```
S := compose (fresh→user renaming) (unifier S_unify)
```

and the produced judgment is already `HasType C (Γ_internal.subst S) body (.forAll [] (subst S bodyty))`
with the renaming applied — no separate, false, post-hoc bridge. With Lever 1, this `S` is a
plain **var→var renaming** composed with the unifier, so:

- `absorbs S Env'.subst` — `absorbs_trans` through the unifier (`Constraints.unify_absorbs`),
- it **acts as** `rename ∘ S_unify` on the body type and formal context — which is what makes
  `subst S bodyty = func.output` (up to alias) and `Γ_internal.subst S` line up with
  `funcContext`.

> **CORRECTION (verified against the code, 2026-06).** An earlier draft of this doc claimed
> `SubstWF S` would be *short* — "an injective var→var map disjoint from the unifier's range,
> no composite-`SubstWF` saga, no 2-cycle." **That was wrong.** The composite
> `S = compose ρ₀ (compose rename v_unify)` has a genuine self-identity 2-cycle: `v_unify`
> sends `x ↦ y` and the inverse `rename` sends `y ↦ x`, so `compose rename v_unify` carries the
> entry `x ↦ ftvar x`, which is **not** `SubstWF`. The outer renaming `ρ₀` *scrubs* that entry
> (because `x ∈ keys ρ₀`), and the WF proof must go through `SubstWF_compose_of_cover` plus the
> provenance fact "user `typeArgs` never enter `v_unify`" (`vunify_avoids_typeArgs`, bottoming
> out at `resolve_freeVars_pred`). This composite machinery (`bodyComposite_wf_hyps`/`wf`/`pack`)
> is **forced** by the fixed spec + black-box core; it is NOT deletable. What Lever 1 *did*
> simplify is the renaming's own `SubstWF`/inverse (`substWF_renameMap_new` from idempotence
> alone) and the deletion of the ~485-line `bwdMap`/`alphaEquivMap`-inversion family. The
> composite stays.

`subst S bodyty = subst S output_mty` is the unify result (`retty`/`bodyty` unify), so the
type side closes the same way `Cmd` closes its `init` case.

**Effect on proofs.** The "ROUTE B" composite-substitution apparatus shrinks to one
composition law + one short WF fact; `HasType_TContext_subst` is **deleted** (no uses);
`bodyTyped`/`measureTyped` collapse toward the `Cmd` shape.

### What legitimately remains (not deletable, but small)

- **Alias bridges.** Because the body is resolved against alias-*resolved* types but the spec
  uses the raw (possibly aliased) signature, you still need `HasType.talias` (exists) for the
  result type and `HasType_context_aliasEquiv` (LExprTypeSpec.lean:832, one induction on
  `HasType`) for the context. These are real and should stay — but they are ~one lemma each,
  not 3000 lines.
- **The three soundness guards** (#1395 rigid, #1399 generalization, measure rigidity) are
  correct checker fixes and stay. Their proof obligations are small post-hoc extractions from
  `h` (the "fixes every rigid var" facts), mirroring `CmdType.checkAnnotCompat`.

---

## 3. The annotated theorem (`typeCheck_annotated_sound`) is already the cheap one

`FuncHasTypeA`'s `exprTyped` is `HasTypeA []` — it **ignores the context `Γ`**. So the
annotated proof types the body in the empty context via `resolve_HasTypeA` and never crosses
the context gap. This is why `typeCheck_bodyTyped_annotated`/`typeCheck_measureTyped_annotated`
are already done and short(ish). Lever 1 still helps it (the `bodyTyped_chain` uses the same
`renameSubst`), but the annotated side is not the swamp. **Leave its structure; just inherit
the smaller `renameSubst` facts.**

---

## 4. Concrete plan of record

> Layer 0 = `Function.typeCheck_sound`, `Function.typeCheck_annotated_sound` (UNCHANGED statements);
> layer 1 = `typeCheck_bodyTyped`, `typeCheck_measureTyped`, `typeCheck_*_annotated`, the three nodup/undeclared field lemmas.

1. **Checker (Lever 1).** In `FunctionType.lean`, keep `alphaEquivMap` as the boolean reject
   guard; derive the fresh→user renaming from the instantiation fresh-var list. Re-bless any
   affected `#eval`/golden tests (accept/reject + final `func'` unchanged; only renaming
   provenance changes).
2. **Delete** the inversion family in FunctionTypeSpecProps.lean once nothing references it:
   `go_bwd_mono`, `goList_bwd_mono`, `go_bwd_keys_subset`, `goList_bwd_keys_subset`,
   `go_bwd_vals_subset`, `goList_bwd_vals_subset`, `go_bwd_inverts`, `goList_bwd_inverts`,
   `alphaEquivMap_bwd_keys_subset`, `alphaEquivMap_self_subst_bwd(_inverts)`,
   `renameMap_key_imp_bwd`, `substWF_renameMap`, `find?_renameMap_of_mem`,
   `mem_keys_renameMap_imp`, `alphaEquivMap_renameSubst_inverse(_ftvar)`,
   `typeCheck_body_type_eq` (the bwd-based half).
3. **`bodyTyped` (Lever 2).** State the field as the `S`-instantiation of
   `resolve_HasType_core.1` at `S = compose rename S_unify`, with: `absorbs` via
   `absorbs_trans`; `SubstWF` via the short var-rename WF fact; type side via the unify
   equality; then the two alias bridges (`talias` + `HasType_context_aliasEquiv`). Target:
   tens of lines, mirroring `Cmd.typeCheck_sound`'s `init_det`.
4. **`measureTyped`.** Same shape against `measureBaseEnv` (already independent of the body
   per the §10l redesign), output `.int`, only the context alias bridge.
5. **Delete `HasType_TContext_subst`** (LExprTypeSpec.lean:804) and its call sites.
6. **Keep** `HasType_context_aliasEquiv` (prove the induction), the three guard extractions,
   and the annotated proof (inherits the smaller renaming facts).

**Net.** Both top-level theorems stand, unchanged. Expected proof size drops from ~3300+1500
to a few hundred lines on the `Cmd` template, with the one false lemma removed.

---

## 5. The one decision that needs sign-off

Lever 1 edits `FunctionType.lean` (a real, if behavior-preserving, change to the checker).
Lever 2 is proof-only. If the checker edit is undesirable, Lever 2 alone still removes the
false bridge and most of the composite-substitution apparatus, but the `alphaEquivMap`
inversion family survives — a smaller win. Recommendation: **do both**; Lever 1 is where the
~1100 lines actually live.
