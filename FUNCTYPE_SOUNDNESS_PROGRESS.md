# Function soundness simplification — progress & remaining work

Companion to `FUNCTYPE_SOUNDNESS_SIMPLIFICATION.md` (the why/plan). This file tracks the
**execution state**. Both top-level theorems stand UNCHANGED in statement:
- `Function.typeCheck_sound : … → FuncHasType C Env.context func`
- `Function.typeCheck_annotated_sound : … → ∀ Γ, FuncHasTypeA C Γ func'`

## Current state (checkpoint)

`lake build Strata.Languages.Core.FunctionTypeSpecProps` → **exit 0** (green; builds with `sorry`s).
Full `lake test` passed earlier with the checker change (only the untracked scratch probe
`AmbientTyvarGenProbe.lean` fails, and it fails on a clean checkout too — unrelated).

### Decision in force
**Keep the checker change (Lever 1) + re-prove the composite-`S` for the new shape (Lever 2).**
The checker (`FunctionType.lean`) now builds the fresh→instantiation renaming directly from
`monoty.freeVars.eraseDups` as the inverse of the unifier on those vars — `alphaEquivMap` is
kept ONLY as the boolean reject guard. The new renaming shape is:
```
renameMap S vs := vs.filterMap (fun x => match subst S (ftvar x) with
  | .ftvar y => if x == y then none else some (y, .ftvar x) | _ => none)
-- at the call site: vs = v_inst.fst.freeVars.eraseDups, S = v_unify.subst
```

## DONE (sorry-free, building)

### Checker (`Strata/Languages/Core/FunctionType.lean`)
- `alphaEquivMap monoty inferredTy` is now `match … | some _ => pure () | none => .error …`
  (boolean guard only; no `bwdMap` bound).
- `renameSubst` built as `[monoty.freeVars.eraseDups.filterMap (fun x => match subst S.subst (ftvar x) …)]`.

### New foundational lemmas (`FunctionTypeSpecProps.lean`, Task #1 — all sorry-free)
- `renameMap` (def) — the new single-scope renaming map.
- `alphaEquivMap_sigma_inj` — σ injectivity on `freeVars monoty` (from the irreducible
  `alphaEquivMap_self_subst_bwd` core).
- `mem_renameMap_iff`, `mem_keys_renameMap` — membership / key characterization.
- `freeVars_renameMap` — value-freeVars characterization.
- `substWF_renameMap_new` — **`SubstWF [renameMap S vs]` from idempotence of `S` ALONE**
  (genuinely simpler than the old `bwdMap` `substWF_renameMap`; no inverse-pairing needed).
- `Map.find?_of_mem_nodup` — generic find?-of-mem with nodup keys.
- `renameMap_keys_nodup` — keys nodup from σ-injectivity + `Nodup vs`.
- `renameMap_inverse_ftvar`, `renameMap_inverse` — **the inverse property**
  `subst [renameMap S vs] (subst S t) = t` for `freeVars t ⊆ freeVars monoty`, `vs` = nodup
  enumeration of `freeVars monoty`.
- `LMonoTy.mem_freeVars_subst_of_mem` — forward freeVars monotonicity through subst.

### Re-threaded to new shape (Task #1/#2 — sorry-free)
- `typeCheck_body_type_eq`, `bodyTyped_chain` — now use `[renameMap S monoty.freeVars.eraseDups]`.
- `Function.typeCheck_bodyTyped_annotated` — `bodyTyped_chain` call repaired; all 3 measure
  branches close. (`bwdMap` → `alphaMap` as the inverse witness.)
- `Function.contextAliasEquiv_facts` — `renameSubst` `let` switched to new shape; Region A uses
  `renameMap_inverse`; Region B uses `mem_keys_renameMap` + `mem_freeVars_subst_of_mem`
  (replacing `mem_keys_renameMap_imp` / `alphaEquivMap_bwd_keys_subset`).
- `Function.typeCheck_bodyTyped_instantiated` — `renameSubst`/`h_wf_rename`/`h_out_eq` re-threaded
  to new shape (`substWF_renameMap_new`, `renameMap_inverse`); `contextAliasEquiv_facts` call uses
  `alphaMap`.

### Annotated theorem chain (Task #2 — COMPLETE)
The entire `typeCheck_annotated_sound` dependency closure is sorry-free in the proof file.

## REMAINING WORK

### `sorry` inventory (FunctionTypeSpecProps.lean, authoritative line numbers from last build)
| line | theorem | difficulty | notes |
|---|---|---|---|
| 2263 | `Function.typeCheck_inverse_components` | layer-3 leaf | per-component alias adapter; pre-existing |
| 2576 | `Function.internalContext_values_mono` | layer-3 leaf | NOT trivial: `h_ambient_mono` is `find?`-quantified but goal is over `Maps.values` (includes shadowed entries) → needs a no-shadow/nodup ambient invariant (§10k) |
| 2848 | `Function.measureComposite_pack` | layer-2 | measure mirror of `bodyComposite_pack`; pre-existing |
| 3206 | `Function.typeCheck_bodyTyped_instantiated` | **NEW (Task #3 boundary)** | the composite-`S` `h_ht_post` body; temporarily `sorry`d with the exact 4-line discharge in a comment. Blocked only on re-targeting the composite helpers (below). |

Upstream pre-existing sorries (NOT in scope of this simplification, independent leaves):
`LExprTypeSpec.lean:804` (`HasType_TContext_subst` — the FALSE bridge, DELETE once Task #3 done;
verified no real uses, only comments), `:832` (`HasType_context_aliasEquiv`), `:5376`
(`LTy_instantiateWithCheck_inverse`), `LExprResolveProps.lean:771` (`resolve_freeVars_pred`).

### Task #3 — re-target the composite-`S` helpers to the new shape (the crux, NEXT)
These three helpers are still written against the OLD `bwdMap.toList.filterMap` shape and a
`(bwdMap : Std.HashMap …)` parameter. They must be re-targeted to
`renameMap v_unify.subst v_inst.fst.freeVars.eraseDups`:
- `Function.bodyComposite_wf_hyps` (~line 2600) — provenance bundle (C1/C2/hVU/hUT).
- `Function.bodyComposite_wf` (~line 2640) — `SubstWF` of `compose ρ₀ (compose rs₀ v_unify)`
  via `SubstWF_compose_of_cover`. Internally uses `renameMap_key_imp_bwd`,
  `alphaEquivMap_bwd_keys_subset`, `renameMap_val_imp_bwd`, `alphaEquivMap_bwd_vals_subset`,
  `substWF_renameMap` — ALL on the old shape. New-shape replacements:
  - key membership → `mem_keys_renameMap`
  - key ∈ freeVars(subst v_unify v_inst.fst) → `mem_keys_renameMap` + `mem_freeVars_subst_of_mem`
  - `SubstWF [rs₀]` → `substWF_renameMap_new`
  - value side → `mem_renameMap_iff` (value is `ftvar x`, `x ∈ vs = freeVars v_inst.fst.eraseDups`)
- `Function.bodyComposite_pack` (~line 2700) — produces `S`, `h_ctx`/`h_ty` (acts-as),
  `absorbs`, `SubstWF`, `polyKeysFresh`. The `rs₀`/`renameSubst` let-bindings must become the
  new shape so `h_ctx`/`h_ty` match `typeCheck_bodyTyped_instantiated`'s `renameSubst`.

Once re-targeted, restore the `h_ht_post` body at 3206 (the discharge is spelled out in the
`-- TODO(Task #3 …)` comment there): obtain `hyps`, `h_wf_S`, then
`bodyComposite_pack … alphaMap … h_wf_S`, `rw [h_ctx, h_ty]; exact h_core.1 S h_abs h_wf h_poly`.

### Task #4 — the genuine leaves + cleanup
- `internalContext_values_mono` (2576) — needs the ambient no-shadow/nodup invariant.
- `measureComposite_pack` (2848) — mirror of `bodyComposite_pack` for the measure (output `.int`).
- The three upstream leaves (`HasType_context_aliasEquiv`, `LTy_instantiateWithCheck_inverse`,
  `resolve_freeVars_pred`) — these are independent of this simplification and were never close to
  done; they are the real remaining research content.
- DELETE the dead `HasType_TContext_subst` (LExprTypeSpec:804) and the now-dead OLD-shape
  plumbing once nothing references it: `find?_renameMap_of_mem`, `mem_keys_renameMap_imp`,
  `renameMap_key_imp_bwd`, `renameMap_val_imp_bwd`, old `substWF_renameMap`,
  `alphaEquivMap_bwd_keys_subset`, `alphaEquivMap_bwd_vals_subset`,
  `alphaEquivMap_self_subst_bwd_inverts` (if unused after Task #3).
  **Keep** the irreducible core: `go_bwd_mono/inverts/keys_subset/vals_subset` + `goList_*`,
  `alphaEquivMap_self_subst_bwd` (these prove the body didn't over-constrain the signature and
  are shape-independent — needed by `alphaEquivMap_sigma_inj`).

### Measure side (mirror of body, after Task #3)
`typeCheck_measureTyped_instantiated` / `typeCheck_measureTyped` follow the body pattern with
output `.int` (alias-free); reuse `contextAliasEquiv_facts`. `measureComposite_pack` is the
measure analogue of the body composite.

## Dependency-pruning note (per user instruction)
Only repair lemmas in the reachable closure of the two top-level theorems. Reachability was
computed (62 reachable, 8 dead at the time). The new-shape lemmas become reachable as they are
wired in; the old `bwdMap` plumbing becomes dead as helpers move to the new shape — delete it
rather than maintaining it.
