# Function soundness simplification — progress & remaining work

Companion to `FUNCTYPE_SOUNDNESS_SIMPLIFICATION.md` (the why/plan). This file tracks the
**execution state**. Both top-level theorems stand with their conclusions UNCHANGED:
- `Function.typeCheck_sound : … → FuncHasType C Env.context func`
- `Function.typeCheck_annotated_sound : … → ∀ Γ, FuncHasTypeA C Γ func'`

> **Statement note.** `typeCheck_sound` (and its `bodyTyped`/`_instantiated` helpers) now carries
> one added hypothesis `h_resolved : AliasesResolved Env.context` — a genuine truth-need (the
> annotated theorem already carried it; it is the standard precondition the resolve pipeline
> assumes). Conclusion unchanged. This was explicitly approved.

## Current state (checkpoint)

`lake build Strata.Languages.Core.FunctionTypeSpecProps` → **exit 0** (green; builds with `sorry`s).
Branch `josh/func-type-spec`. Session commits:
- `Re-target composite-S helpers to renameMap; delete ~485 lines dead bwdMap machinery`
- `Wire h_ht_post via composite helpers`
- `Thread h_resolved through typeCheck_sound chain; discharge h_resolved_int`
- `Add typeArgs gen-prefix guard to typeCheck; repair proof unwrap sites`

**Uncommitted (this session) — FuncWF-bridge prep (changes 1–3 of 4):** `concreteEval = none`
guard + `isConstr = false` guard added to `Function.typeCheck` (both behavior-preserving;
proof unwrap sites repaired); `precond_freevars` field removed from `FuncWF` (+ all providers
and callers). All affected files + test suites build green. See the FunctionType section below.
Not yet committed (awaiting user direction). Change 4 (the `LFuncWF func'` bridge) not started.

## Decisions in force

1. **Composite-`S` is FORCED, not garbage.** The fixed spec (`bodyTyped` concludes in the
   user-frame `funcContext`/`func.output`) + the black-box `resolve_HasType_core` (concludes only
   in the `Γ.subst S` frame) mean the fresh→user renaming must be crossed *inside* `HasType`.
   The only sound way is to fold it into core's universal `S = compose ρ₀ (compose rename v_unify)`.
   That composite has a genuine self-identity 2-cycle (`v_unify : x↦y`, `rename : y↦x` ⟹ `x↦x`),
   so it is NOT `SubstWF`; the outer `ρ₀` scrubs it via `SubstWF_compose_of_cover`. **The doc's
   earlier "SubstWF is short, no composite saga" claim was wrong** — corrected in
   `FUNCTYPE_SOUNDNESS_SIMPLIFICATION.md` (CORRECTION block).
2. **What Lever 1 (the renameMap shape) actually bought:** `SubstWF [renameMap …]` from
   idempotence alone (`substWF_renameMap_new`), the inverse property definitionally, and deletion
   of the ~485-line `bwdMap`/`alphaEquivMap`-inversion family. The composite stays.
3. **Checker now enforces `typeArgs_no_gen_prefix`** (user directive). So the proof EXTRACTS that
   fact from `h` (the `h_genprefix` hypothesis) — it is NOT assumed as `LFuncWF func`.

## DONE (sorry-free, building)

### Checker (`Strata/Languages/Core/FunctionType.lean`)
- `alphaEquivMap monoty inferredTy` is the boolean reject guard only (no `bwdMap` bound).
- `renameSubst` built directly from `monoty.freeVars.eraseDups` as the inverse of the unifier.
- **NEW: gen-prefix guard.** After `func.type`, rejects any `typeArg` whose name starts with
  `$__ty` (`TState.tyPrefix`). Closes the `LFuncWF.typeArgs_no_gen_prefix` gap. Found via the
  counterexample `f<$__ty0>(x:$__ty0):$__ty0 {x}` (which the old checker accepted: the fresh var
  generated at `tyGen=0` is literally `$__ty0`, so `checkNoFutureGenVars` at `tyGen=1` does not
  flag it — and `h_inst_avoids` is then false).

### Proof file (`FunctionTypeSpecProps.lean`)
- New-shape foundation (Task #1): `renameMap`, `mem_renameMap_iff`, `mem_keys_renameMap`,
  `freeVars_renameMap`, `freeVars_renameMap_mem_vs`, `alphaEquivMap_sigma_inj`,
  `substWF_renameMap_new`, `renameMap_keys_nodup`, `renameMap_inverse(_ftvar)`,
  `LMonoTy.mem_freeVars_subst_of_mem`. **~485 lines of old bwd machinery deleted** (kept the
  irreducible core `go_bwd_mono/inverts` + `alphaEquivMap_self_subst_bwd` that the new lemmas use).
- Annotated theorem chain (Task #2): COMPLETE, sorry-free.
- Composite helpers (Task #3): `bodyComposite_wf_hyps`/`wf`/`pack` re-targeted to `renameMap`
  (dropped the `bwdMap`/`h_alphaMap` params). `bodyComposite_wf` now uses `mem_keys_renameMap` +
  `mem_freeVars_subst_of_mem` (key side) and `freeVars_renameMap_mem_vs` (value/self-ref side);
  `SubstWF [rs₀]` from `substWF_renameMap_new`.
- Body judgment wired: `typeCheck_bodyTyped_instantiated.h_ht_post` assembled through
  `bodyComposite_wf_hyps → bodyComposite_wf → bodyComposite_pack → h_core.1`. No longer a sorry.
- `h_resolved` threaded through `typeCheck_sound`/`typeCheck_bodyTyped`/`_instantiated`;
  `h_resolved_int` discharged via `typeCheck_internalEnv_wf`.
- All 8 `typeCheck`-unwrap sites repaired for the new gen-prefix guard: the guard desugars to TWO
  splittable nodes (the `if` + its trailing `pure`), so each site gains `elim_err h with
  h_genprefix` + one extra `elim_err h`.

## REMAINING `sorry`s

### In `FunctionTypeSpecProps.lean` (5; line numbers approximate)
| ~line | decl | status |
|---|---|---|
| — | `typeCheck_bodyTyped_instantiated` `h_inst_avoids` | ✅ **DONE** (sorry-free) via `instantiateWithCheck_freeVars_gen_prefixed` + `h_gen_avoids`. |
| 2855 | `typeCheck_bodyTyped_instantiated` `h_ctx_avoids` | **NEXT** — ambient-collision guard now in place; needs the extraction lemma + FORMALS/ambient split (NEXT STEPS 3–4). |
| 2865 | `typeCheck_bodyTyped_instantiated` `h_subin_avoids` | **NEXT** — same, over the internal subst (= ambient subst); new extraction lemma (NEXT STEP 5). |
| 1927 | `typeCheck_inverse_components` | pre-existing per-component alias leaf. |
| 2232 | `internalContext_values_mono` | pre-existing; `find?`-vs-`Maps.values` (needs no-shadow/nodup ambient invariant). |
| 2945 | `measureComposite_pack` | measure mirror of `bodyComposite_pack` (output `.int`). |

### Upstream (4, pre-existing, NOT introduced here)
- `LExprResolveProps:785` `resolve_freeVars_pred` — feeds `vunify_avoids_typeArgs` (composite WF).
- `LExprTypeSpec:809` `HasType_TContext_subst` — the FALSE bridge; **now unused by the body path**
  (Route B routes around it). **DELETE** once a grep confirms no remaining references.
- `LExprTypeSpec:838` `HasType_context_aliasEquiv` — context alias bridge (one induction).
- `LExprTypeSpec:5391` `LTy_instantiateWithCheck_inverse` — instantiation inverse (ρ₀-contract).

## NEXT STEP — provenance stubs: gen-name chain DONE; `vunify` rework IN PROGRESS

### DONE — the reusable gen-name chain (unblocked stub 1 of 3)
`instantiateWithCheck_freeVars_gen_prefixed` (FunctionTypeSpecProps.lean, sorry-free): freeVars of
an `instantiateWithCheck` output of a **closed** scheme are all `$__ty<k>`. Threads
`TGenEnv.genTyVars_is_genName` through `LTy.instantiate` and `LMonoTy_resolveAliases_freeVars_subset`
(both `private` upstream but reachable via `import all`). Reuses the cover skeleton from
`instantiateWithCheck_freeVars_eraseDups_length_le`.
- Also added: `Function.typeCheck_input_typeArgs_no_gen_prefix` (relocated *before*
  `typeCheck_bodyTyped_instantiated`), used by the bridge too.
- **`h_inst_avoids` DONE (sorry-free):** `v ∈ freeVars v_inst.fst → v = $__ty<k>` (chain lemma)
  `→ v ∉ func.typeArgs` (local `h_gen_avoids`, from the in-scope `h_genprefix` — NOT the original
  `h`, which is consumed by the unwrap at the stub site).

### THE PROBLEM — `h_ctx_avoids` / `h_subin_avoids` are FALSE as stated (NOT a truth-need)
Counterexample (to the *stub*, not the theorem): ambient `Env.context` has `y : a`,
`C.rigidTypeVars = ["a"]` (so `h_ambient_rigid` holds). User writes `function f<a>(x:a):a { x }`.
`typeCheck` ACCEPTS it (instantiates `a ↦ $__ty0`; body `x:$__ty0`; rigid `a` untouched; #1399 sees
generalized `$__ty0 ∉ {a}`). But then `a ∈ ambient knownTypeVars` **and** `a ∈ func.typeArgs`, so
`h_ctx_avoids` ("ambient knownTypeVars ∉ typeArgs") is FALSE. Yet `FuncHasType` HOLDS (in
`funcContext Γ f = Γ + x:a`, body `x : a = f.output`). So this is a **proof-strategy artifact**, not
a theorem truth-need — adding it as an assumption is forbidden by the rules.

The **real guarantor** that `v_unify` avoids `func.typeArgs` is the **#1399 generalization guard**
(`h_gen_none` in scope: no generalized var — free in `subst v_unify v_inst.fst` — is free in the
substituted ambient context). The dangerous function `f<a>(x:a):a { y }` (body drags ambient `y:a`
into the type, so `v_unify` touches `a`) is REJECTED by #1399. `h_ctx_avoids` was the wrong tool.

### DECISION (user directive) — REJECT typeArg/ambient-type-var collision in the checker
Rather than rework `vunify_avoids_typeArgs` around #1399, **add a `Function.typeCheck` guard that
rejects a function whose `typeArgs` collide with an ambient type variable.** This makes
`h_ctx_avoids`/`h_subin_avoids` genuinely TRUE and extractable from `h` — the same pattern as the
gen-prefix guard (`typeArgs_no_gen_prefix`), not an assumption. The counterexample
`function f<a>(x:a):a { x }` over ambient `y:a` becomes a (correct) type error.

**Investigation findings that fix the guard's exact shape:**
- **Entry point = `inferFVar`** (LExprT.lean:153): a body fvar `x` bound to ambient type `ty` runs
  `instantiateWithCheck ty`, so ambient type vars in `ty` DO flow into the resolved body type. This
  is the only context→result-type path (confirmed vs. §10m (i)-(iii)).
- **`h_subin_avoids` is about the AMBIENT subst:** `instantiateWithCheck` of a plain signature type
  performs no unification, so `v_inst.snd.stateSubstInfo.subst = Env.stateSubstInfo.subst`. Hence the
  guard must ensure `func.typeArgs` avoids ambient type vars *in both* `knownTypeVars` AND the ambient
  substitution's keys/range — i.e. all "ambient type variables".
- **Non-vacuous, and true post-guard:** ProcedureType freshens procedure type params to `$__ty` before
  the body (`instantiateWithSubst`, `tyArgSubst=[a→$__ty0]`; fresh vars enter `rigidTypeVars` + stored
  formal types via `LMonoTySignature.instantiateWithSubst`). So in practice ambient type vars are
  already `$__ty`-prefixed and a user `typeArg` (guaranteed non-`$__ty` by the gen-prefix guard) can
  never collide — the new guard is thus expected to never fire on ProcedureType-produced envs, but it
  is the clean local fact the proof extracts (no cross-file ambient invariant needed).

### TRACE RESULT (done) — the full consumption chain
- `bodyComposite_wf` (FunctionTypeSpecProps:2330) needs exactly `hVU` (`v_unify` keys ∉ typeArgs) and
  `hUT` (freeVars `subst v_unify v_inst.fst` ∉ typeArgs). `hUT` is *derived* in `bodyComposite_wf_hyps`
  (:2291) from `hA` (=`h_inst_avoids`, DONE) + `hVUr` (`v_unify` range ∉ typeArgs). So the ONLY thing
  still resting on the ambient-avoids stubs is `hVU`/`hVUr`, both produced by `vunify_avoids_typeArgs`.
- `vunify_avoids_typeArgs` (:2246) builds `hVU`/`hVUr` via: `resolve_freeVars_pred` (→ `hB` body-type
  freeVars ∉ typeArgs, `hC` output-subst range ∉ typeArgs) → `unify_pred` over the constraint
  `(reconstructedOutput, bodyType)` (output side via `hA` + `freeVars_reconstructedOutput_subset`).
  Both `hB` and `hC` are genuinely used.
- **Key insight from the counterexample:** in `f<a>(x:a):a {x}` over ambient `y:a`, the resolved body
  type is `$__ty0` (the body is just the formal `x`), so `hB`/`hC` (the *conclusions*) HOLD even though
  the *hypothesis* `h_ctx_avoids` (ambient knownTypeVars ∉ typeArgs) is FALSE. The over-strong
  hypothesis is `resolve_freeVars_pred`'s `h_ctx`/`h_sub`, which demand `P` on ALL ambient
  knownTypeVars/subst — more than the conclusion needs.

### NEXT STEPS (in order) — implement the ambient-collision guard, then discharge the 2 stubs
1. ✅ **DONE — checker guard added** in `Function.typeCheck` (`FunctionType.lean`), after the isConstr
   guard. `if Function.collidesWithAmbient Env func then .error …`, where `collidesWithAmbient`/
   `ambientTyVars` are standalone defs (`ambientTyVars Env = TContext.knownTypeVars Env.context ++
   Maps.keys Env.stateSubstInfo.subst ++ Subst.freeVars Env.stateSubstInfo.subst`). Factoring the
   condition into a named `def` (rather than an inline `List.filter … != []`) keeps it atomic so
   the proof-side split sees one guard, not a giant expression.
2. ✅ **DONE — proof unwrap sites repaired.** This uncovered a real blocker: the built-in `split`
   tactic (which `elim_err` used via `split at h`) case-splits ALL `if`/`match` in `h` at once and
   normalizes with an internal `simp` whose cost scales with the whole `do`-chain. `func`-stuck guard
   conditions can't be pruned, so past ~14 guards it overflows simp's 100000-step budget — adding the
   4th guard crossed that threshold. Minimal self-contained repro: `SplitRepro.lean` (12 guards OK, 14
   overflow). FIX: **`split_ns`** — a new simp-free `split` in `Strata/Util/Tactics.lean` that reduces
   ONLY the `if`/`match` it splits (via `if_pos`/`if_neg`/`dif_*` rewrites for `ite`, `reduceRecMatcher?`
   for `match`), leaving nested stuck subterms untouched (cost independent of chain length). `elim_err`/
   `elim_err with`/`elim_errs` now use `split_ns`. All unwrap sites rebuilt green; `typeCheck_inputsNodup`
   tail re-aligned to the `typeArgsNodup` template; `h_ce`/`h_ic` peel offsets in
   `typeCheck_input_concreteEval_none_isConstr_false` corrected for the extra guard.
3. **Add an extraction lemma** `Function.typeCheck_input_typeArgs_avoid_ambient` (sibling of
   `typeCheck_input_typeArgs_no_gen_prefix`): from `h`, `∀ ta ∈ func.typeArgs, ta ∉ ambientTyVars`.
4. **Discharge `h_ctx_avoids`** (FunctionTypeSpecProps ~2834): split `knownTypeVars` of
   `Env_int = v_inst.snd.pushEmptyContext.addInNewestContext FORMALS` into FORMALS ∪ ambient
   (`knownTypeVars_addInNewestContext_cases` / the `contextAliasEquiv` region-split template at :2147).
   FORMALS side → gen-names via `instantiateWithCheck_freeVars_gen_prefixed` + `mem_destructArrow_
   freeVars_subset` → `h_gen_avoids`. Ambient side → the new extraction lemma (via
   `h_ctx_eq : v_inst.snd.context = Env.context`, already in scope).
5. **Discharge `h_subin_avoids`** (~2840): `v_inst.snd`'s subst = `Env`'s subst (from
   `instantiateWithCheck` doing no unification; find/att the context-eq lemma), then the new extraction
   lemma directly.

Then: delete `HasType_TContext_subst`; tackle the pre-existing leaves
(`HasType_context_aliasEquiv`, `LTy_instantiateWithCheck_inverse`, `internalContext_values_mono`,
`typeCheck_inverse_components`) and the measure mirror `measureComposite_pack`.

## FunctionType: changes still needed

### For the soundness proof (`typeCheck_sound`): TWO guards.
1. **Gen-prefix guard** (`typeArgs_no_gen_prefix`) — DONE. Extracted as `h_genprefix`.
2. **Ambient-collision guard** (`collidesWithAmbient`) — DONE (checker + all unwrap sites, via
   `split_ns`). Extraction lemma + discharge of `h_ctx_avoids`/`h_subin_avoids` still pending (NEXT
   STEPS 3–5).
Both are checker changes that the proof EXTRACTS from `h` (not assumptions). No other checker edits.

> **Direction note (important).** Mid-proof, an `LFuncWF func` *hypothesis* on `typeCheck_sound`
> was considered and **rejected**: it's a proof-strategy need (the theorem is true without it),
> and the call-site trace FAILS (`ProgramType.lean` calls `Function.typeCheck` on the raw parsed
> `func`, no `LFuncWF func` in scope). So `typeCheck_sound`'s statement is UNCHANGED (only the
> earlier-approved `h_resolved` was added). The bridge below goes the **opposite** direction — it
> *produces* `LFuncWF func'` *from* a successful check (sound; usable by `addFactoryFunction func'`).

### `typeCheck succeeds ⟹ LFuncWF func'` bridge — DONE (sorry-free)
Audit of every `FuncWF`/`LFuncWF` field vs. what `typeCheck` enforces on success:

| field | enforced? |
|---|---|
| `arg_nodup`, `typeArgs_nodup` | ✅ `LFunc.type` |
| `inputs/output_typevars_in_typeArgs` | ✅ `undeclaredVars` check |
| `typeArgs_no_gen_prefix` | ✅ gen-prefix guard |
| 3× `concreteEval_*` (`_argmatch`, `body_or_concreteEval`, `_eraseMetadata`) | ✅ **vacuous** — `concreteEval = none` guard (change 1, DONE) |
| `constr_no_eval` (`isConstr → body=none ∧ concreteEval=none`) | ✅ **vacuous** — `isConstr = false` guard (change 2, DONE) |
| ~~`body_freevars`~~ | ❌ **REMOVED from `FuncWF`** (change 4, DONE) — **false** for nested functions (a `function foo(y){x+y}` inside a procedure with ambient local `x` resolves fine, since `pushEmptyContext` does NOT hide outer scopes and `Maps.find?` spans them). Never consumed by any proof, so removed rather than weakening the bridge with a no-ambient-vars hypothesis. |
| ~~`precond_freevars`~~ | ❌ **REMOVED from `FuncWF`** (change 3, DONE) — nothing consumed it; same nested-function reason |

**DONE — checker guards added (`FunctionType.lean`), all behavior-preserving for parsed funcs:**
1. ✅ `concreteEval = none` guard (`if func.concreteEval.isSome then .error …`). `ofPureFunc`
   always sets `concreteEval := none`, so no source function is rejected. Discharges the three
   `concreteEval_*` fields **vacuously**. Proof unwrap sites in `FunctionTypeSpecProps.lean`
   repaired (2 extra `elim_err h` per site; 2 body=none `simp_all` → targeted `reduceCtorEq`).
2. ✅ `isConstr = false` guard (`if func.isConstr then .error …`). Constructors are built only by
   the datatype factory (never via `Function.typeCheck`). Discharges `constr_no_eval` **entirely
   vacuously**. Proof unwrap sites repaired (2 more `elim_err h` per site).
3. ✅ **Removed** the unused `precond_freevars` field from `FuncWF` (`Func.lean`) + its
   decidability instance; dropped `h_precond` from `IntBoolFactory.polyUneval`/`unaryOp`/`binaryOp`
   and the three `Factory.lean` callers; removed 4 `precond_freevars := by decide` in
   `LExprEvalTests.lean`. Chosen over a behavior-changing precondition rejection because the field
   was never consumed by any proof. (A `function foo(y) requires (y > x)` referencing an outer
   local `x` is now still accepted by `typeCheck`, as before.)

Constructors and concrete-eval functions only ever arise from the built-in factory (e.g.
`IntBoolFactory`) / datatype declarations, which construct their `LFuncWF` directly and never go
through `Function.typeCheck` — so nothing is lost.

All three changes build green; `FunctionType`/`ProgramType`/`ProcedureType`/`ProgramEval`/
`FunctionType`/`LExprEval` test suites pass.

**DONE — change 4: the bridge `Function.typeCheck_LFuncWF`** (`FunctionTypeSpecProps.lean`, end of
the `TypeSpec` namespace; sorry-free). Assembled field-by-field:
- `arg_nodup`: from `typeCheck_inputsNodup` (key-nodup) → name-nodup via `List.Pairwise.map`
  (`Identifier.name` is injective for `IDMeta = Unit`).
- `typeArgs_nodup`: `typeCheck_typeArgsNodup`.
- `inputs/output_typevars_in_typeArgs`: from `typeCheck_noUndeclaredVars` + `freeVars_mkArrow'`.
- 3× `concreteEval_*` + `constr_no_eval`: **vacuous** via the helper
  `typeCheck_concreteEval_none_isConstr_false` (= preservation lemma
  `typeCheck_concreteEval_isConstr_preserved` ∘ guard-extraction
  `typeCheck_input_concreteEval_none_isConstr_false`, the split you suggested).
- `typeArgs_no_gen_prefix`: `typeCheck_typeArgs_subset` (func'.typeArgs ⊆ func.typeArgs — a
  prefix, since the zip truncates to used vars) + `typeCheck_input_typeArgs_no_gen_prefix`
  (the gen-prefix guard says no `func.typeArg` has the prefix).

Helper lemmas added alongside (all sorry-free): `typeCheck_concreteEval_isConstr_preserved`,
`typeCheck_input_concreteEval_none_isConstr_false`, `typeCheck_concreteEval_none_isConstr_false`,
`typeCheck_input_typeArgs_no_gen_prefix`, `typeCheck_typeArgs_subset`.

All build green; full `FunctionType`/`ProgramType`/`ProcedureType`/`ProgramEval`/`LExprEval` +
denote (`LExprDenoteConstrs`) suites pass. **Uncommitted.** The bridge is for program/procedure-level
consumers (`ProgramType.addFactoryFunction func'` needs `LFuncWF func'` to keep `FactoryWF`); it is
NOT on the critical path for `typeCheck_sound`/`typeCheck_annotated_sound` (still their own layers).
