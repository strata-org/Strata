# Plan: `alphaEquivMap_renameSubst_inverse`

**Goal (FunctionTypeSpecProps.lean:64):**
```lean
theorem alphaEquivMap_renameSubst_inverse (monoty t : LMonoTy) (S : Subst)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap)
    (h_sub : ∀ v, v ∈ LMonoTy.freeVars t → v ∈ LMonoTy.freeVars monoty) :
    let renameSubst : Subst :=
      [bwdMap.toList.filterMap (fun (k, v) => if k == v then none else some (k, .ftvar v))]
    LMonoTy.subst renameSubst (LMonoTy.subst S t) = t
```

## 0. Where this lemma lives / where helpers go

`alphaEquivMap` is defined in `LTy.lean`. `LMonoTy.subst`, `Subst`, `Maps.find?` are in
`LTyUnify.lean` / `Maps.lean`. The target theorem is in `FunctionTypeSpecProps.lean`, which
does `import all` of LExprTypeSpec (transitively LTy, LTyUnify). So **`alphaEquivMap.go` is
transparent** in FunctionTypeSpecProps via `import all`. Decision:

- **Structural helpers about `alphaEquivMap.go`/`goList`** → prove in **`LTy.lean`** (where
  `go` is defined and transparent natively; avoids fighting `import all` opacity and keeps
  the HashMap-invariant reasoning next to the definition). These are reusable.
- **The `subst`-composition glue** (`renameSubst ∘ S = id` on `t`) → prove in
  **FunctionTypeSpecProps.lean** (or LTyUnify if `subst` needs to be transparent — it is
  `@[expose]`, so either works; prefer FunctionTypeSpecProps to keep the new surface local).

Confirm `LTy.lean` imports suffice: it defines `alphaEquivMap` but NOT `subst` (that's
LTyUnify, which imports LTy). So the `subst`-level glue **cannot** go in LTy.lean. Split:
  - LTy.lean: everything about `alphaEquivMap.go` and the resulting `bwdMap` (pure HashMap facts).
  - FunctionTypeSpecProps.lean: combine with `subst`.

## 1. The mathematical content (why it's true)

Write `m := monoty`, `m' := subst S m`. `alphaEquivMap m m'` runs `go m m' {} {}` and returns
`bwd` on success. Reading `go`:

- `go (ftvar x) (ftvar y) fwd bwd`: if `fwd[x]?` set, require it `== y`; else if `bwd[y]?`
  set, require it `== x`; else insert `fwd[x]:=y`, `bwd[y]:=x`.
- `go (bitvec n) (bitvec m)`: require `n==m`.
- `go (tcons n1 a1) (tcons n2 a2)`: require `n1==n2`, recurse `goList a1 a2`.
- else `none`.

Since `m' = subst S m`, the second argument is *structurally identical* to `m` except each
`ftvar x` becomes `subst S (ftvar x)` = `S.find? x` (or `ftvar x` if unmapped / S has empty
scopes). For `go` to succeed at every `ftvar` leaf, **`subst S (ftvar x)` must itself be an
`ftvar`** (a `tcons`/`bitvec` would force the `_,_ => none` branch since the first arg is
`ftvar`). So define `σ x := the y with subst S (ftvar x) = ftvar y`. Success of `go` proves:

  **(A) For every `x ∈ freeVars m`, `subst S (ftvar x) = ftvar (σ x)` for some `σ x`.**
  (S maps each relevant var to a *variable*, not a compound type.)

  **(B) `σ` is injective on `freeVars m`** — the `bwd[y]?` consistency check rejects two
  distinct `x1, x2` mapping to the same `y` (it would find `bwd[y] = x1 ≠ x2`). The `fwd[x]?`
  check rejects one `x` mapping to two different `y`s, but that can't happen anyway (S is a
  function); the meaningful constraint is injectivity via `bwd`.

  **(C) `bwd` (= bwdMap) contains exactly `{ (σ x, x) | x ∈ freeVars m }`** (the inverse of σ).
  i.e. `bwdMap[σ x]? = some x` for each free `x`, and every key of bwdMap is some `σ x`.

Then `renameSubst` = `[ filterMap (fun (k,v) => if k==v then none else (k, ftvar v)) bwdMap.toList ]`
is the single-scope substitution sending `σ x ↦ ftvar x` (dropping fixed points `σ x = x`).

**Inverse property on a leaf** `ftvar x` with `x ∈ freeVars m` (hence `x ∈ freeVars t` allowed
by h_sub ⊆): `subst renameSubst (subst S (ftvar x)) = subst renameSubst (ftvar (σ x))`.
  - If `σ x ≠ x`: renameSubst has key `σ x ↦ ftvar x`, so result = `ftvar x`. ✓
  - If `σ x = x`: entry filtered out, but then `subst S (ftvar x) = ftvar x` and renameSubst
    doesn't contain key `x` (could it contain key `x` from a *different* `x'` with σ x' = x?
    No — injectivity (B): σ x' = x = σ x ⟹ x' = x, and that entry is the filtered fixed point).
    So result = `ftvar x`. ✓

Lift from leaves to all of `t` by structural induction on `t` (subst distributes over tcons;
bitvec inert), using h_sub to know every `ftvar` leaf of `t` is in `freeVars m`.

## 2. Helper lemmas (LTy.lean) — about `alphaEquivMap.go`

All quantify over the accumulators and prove an **invariant maintained by the recursion**.
The cleanest formulation threads a relation between `(fwd, bwd)` and S.

### H1 (accumulator monotonicity / inverse-pairing invariant)
```lean
theorem alphaEquivMap.go_bwd_inverts (S : Subst) :
  ∀ (t1 fwd bwd fwd' bwd'),
    -- t2 is forced to be subst S t1
    go t1 (subst S t1) fwd bwd = some (fwd', bwd') →
    -- precondition: incoming bwd already inverts S on its keys
    (∀ y x, bwd[y]? = some x → subst S (ftvar x) = ftvar y) →
    -- conclusion: outgoing bwd' still inverts S, AND covers freeVars t1
    (∀ y x, bwd'[y]? = some x → subst S (ftvar x) = ftvar y) ∧
    (∀ x ∈ LMonoTy.freeVars t1, ∃ y, subst S (ftvar x) = ftvar y ∧ bwd'[y]? = some x)
```
Proof: mutual induction on `t1` (with a `goList` companion over `List LMonoTy` covering
`LMonoTys.freeVars`). The `ftvar` case does the HashMap reasoning:
  - subst S (ftvar x) must be `ftvar y` (else `go` returns none on the `ftvar, tcons`/`bitvec`
    mismatch — **needs a case-split lemma** `subst S (ftvar x) = ftvar _ ∨ ... ` then the
    non-ftvar branches contradict `= some`).
  - three sub-branches (fwd hit / bwd hit / fresh insert) each re-establish the invariant.
    Insert case uses `Std.HashMap.getElem?_insert` to read back `bwd'[y] = x`.
  - `tcons`: `n1 == n2` forced true, then chain through `goList` companion (the IH).
  - `bitvec`: `freeVars = []`, conclusion's ∃ part vacuous; invariant unchanged.

**Std API needed** (all confirmed to exist):
- `Std.HashMap.getElem?_insert` (read-back after insert; may be `getElem?_insertIfNew`-style — verify exact name)
- `Std.HashMap.mem_toList_iff_getElem?_eq_some : (k,v) ∈ m.toList ↔ m[k]? = some v` ✓ confirmed
- `Std.HashMap.distinct_keys_toList : Pairwise (·.fst == ·.fst = false) m.toList` ✓ confirmed
- decidable `==` on `TyIdentifier` (String) — `LawfulBEq` instance present (used by API above).

### H2 (top-level specialization)
```lean
theorem alphaEquivMap_self_subst_bwd (S : Subst) (m : LMonoTy)
    (bwdMap) (h : alphaEquivMap m (subst S m) = some bwdMap) :
    (∀ y x, bwdMap[y]? = some x → subst S (ftvar x) = ftvar y) ∧
    (∀ x ∈ LMonoTy.freeVars m, ∃ y, subst S (ftvar x) = ftvar y ∧ bwdMap[y]? = some x)
```
Proof: unfold `alphaEquivMap` (`(go m (subst S m) {} {}).map (·.2) = some bwdMap`), so
`go ... {} {} = some (fwd0, bwdMap)`. Apply H1 with empty accumulators; the precondition
"`{}[y]? = some x → ...`" is vacuous (`Std.HashMap.getElem?_empty`).

### H3 (injectivity of σ from H2)
From H2: if `subst S (ftvar x1) = ftvar y` and `subst S (ftvar x2) = ftvar y` with both
`x1,x2 ∈ freeVars m`, then `bwdMap[y]? = some x1` and `= some x2` (second conjunct of H2),
so `x1 = x2`. (Direct, no induction.)

## 3. Glue lemma (FunctionTypeSpecProps.lean) — `subst renameSubst` inverts on a leaf

### G1 (renameSubst lookup)
```lean
-- renameSubst = [ filterMap (fun (k,v)=> if k==v then none else some (k, ftvar v)) bwdMap.toList ]
-- For y with bwdMap[y]? = some x:
--   if y ≠ x: Maps.find? renameSubst y = some (ftvar x)
--   if y = x: y ∉ keys renameSubst
```
Proof: `Maps.find?` on a single-scope `[map]` reduces to `Map.find? map y`. `map` is the
`filterMap`; relate `Map.find?` of a filterMap-of-toList to `bwdMap[y]?` using
`mem_toList_iff_getElem?_eq_some` + `distinct_keys_toList` (distinct keys ⟹ `Map.find?`
returns the unique matching entry). The fixed-point filter removes exactly `y = x`.

**Risk point:** `Map.find?` is a left-to-right list scan; need that the filterMapped toList
has the key `y` at a findable position and no earlier shadowing entry. Distinctness of
toList keys (H: `distinct_keys_toList`) gives uniqueness. May need a small bridge lemma
`Map.find?_filterMap_of_mem` or prove via `List.find?`/`List.mem` + nodup-keys. Budget a
helper here.

### G2 (leaf inverse) — combine H2/H3 + G1
```lean
∀ x ∈ freeVars m, subst renameSubst (subst S (ftvar x)) = ftvar x
```
Case `subst S (ftvar x) = ftvar y` (from H2 (A)):
  - `subst renameSubst (ftvar y)`: by G1,
    - `y ≠ x`: `= ftvar x`. ✓  (Note y = σ x; the stored value is x.)
    - `y = x`: renameSubst lacks key y, so `subst renameSubst (ftvar y) = ftvar y = ftvar x`. ✓
  Wait: G1 keys on `y` with value `x`. Need `y=x ⟺ σx = x`. When `y = x`, leaf already `ftvar x`. ✓
  Injectivity (H3) ensures no *other* var x' contributes a key `y` with a different value.

**Subst guard caveat:** `LMonoTy.subst` first checks `Subst.hasEmptyScopes S`. If S has empty
scopes, `subst S t = t`, and we need `subst renameSubst t = t`. Then `alphaEquivMap m m` (t2=t1)
yields `bwdMap` = identity-ish (every var maps to itself) ⟹ renameSubst filters everything ⟹
`hasEmptyScopes renameSubst` ⟹ `subst renameSubst t = t`. **Check this degenerate branch
explicitly** — H2's conclusion still holds (`subst S (ftvar x) = ftvar x`, `bwdMap[x] = x`),
and G1 says all entries filtered, so renameSubst = `[[]]`, `hasEmptyScopes` true. ✓ Covered
uniformly by G2 (the `y = x` sub-case), no separate branch needed — but verify `[ [] ]`
(empty filterMap) has `hasEmptyScopes = true` so `subst renameSubst` is identity.

## 4. Final assembly (the target theorem)

Structural induction on `t` (NOT on m):
- `t = ftvar x`: `x ∈ freeVars t` so `h_sub` ⟹ `x ∈ freeVars m`. Apply G2. ✓
- `t = bitvec n`: `subst _ (bitvec n) = bitvec n` (both substs inert). ✓
- `t = tcons name args`: `subst` distributes (`LMonoTy.subst_tcons`); apply IH to each arg.
  Need `freeVars (tcons ..) = LMonoTys.freeVars args` to pass h_sub down to each arg
  (every arg's freeVars ⊆ t's freeVars ⊆ m's freeVars). Use `LMonoTys.freeVars_mem_subset`.
  Companion induction over the `args` list (mirror `subst`/`freeVars` mutual structure).

Handle the `hasEmptyScopes S` / `hasEmptyScopes renameSubst` guards: `simp [LMonoTy.subst]`
unfolding is gated on `hasEmptyScopes`. Cleanest: prove the leaf lemma G2 *without*
unfolding the guard (treat `subst` abstractly via `subst_tcons`, `subst_emptyS`,
and a `subst` of `ftvar` lemma). Add if missing:
  - `LMonoTy.subst_ftvar : ¬hasEmptyScopes S → subst S (ftvar x) = (S.find? x).getD (ftvar x)`
    (or find existing). Verify name.

## 5. Concrete lemma list & order — PROGRESS (all in FunctionTypeSpecProps.lean)

**Location decision (REVISED):** `go`/`goList` are private `where`-defs but are accessible
AND unfoldable here via `import all Strata.DL.Lambda.LExprTypeSpec` (transitively LTy). There
are NO public `.eq_def`/`.induct` lemmas for them, but `unfold LMonoTy.alphaEquivMap.go`
works in tactic mode. So EVERYTHING lives in FunctionTypeSpecProps.lean — no split to LTy.lean.

**H3 (injectivity) DROPPED** — not needed. G2 needs only H1's existential + paired invariant.

### Done & building (sorry-free):
- ✅ **Target** `alphaEquivMap_renameSubst_inverse` — assembled (§4); reduces to the leaf stub
  `alphaEquivMap_renameSubst_inverse_ftvar` via `LMonoTy.induct`. tcons case uses
  `subst_unfold` + `List.map_congr_left`/`map_id_fun'`.
- ✅ **G1** `find?_renameMap_of_mem` + helper `mem_keys_renameMap_imp` — the
  `Map.find?`-of-filterMap-of-toList lookup, over a key-distinct `List`. Built via
  `List.filterMap_cons` + `simp only [beq_iff_eq]` + `Map.findNone_eq_notmem_mapfst`.
- ✅ **Monotonicity** (NEW foundation lemma, not in original plan) — `go_bwd_mono` +
  companion `goList_bwd_mono`: existing `bwd` entries are never overwritten across the
  recursion. Needed by H1's fwd/bwd-hit cases to carry an already-inserted entry to `bwd'`.
  Proved by `LMonoTy.induct` on t1 (companion: list induction with per-element hypothesis),
  HashMap `getElem?_insert` in the fresh-insert case, mismatched-constructor cases discharged
  by `exact absurd hgo (by unfold ...go; simp)`.

### ✅ COMPLETE — `alphaEquivMap_renameSubst_inverse` is fully proved (sorry-free).
1. ✅ **H1** `go_bwd_inverts` + companion `goList_bwd_inverts` — proved with a *strengthened*
   invariant carrying BOTH (P1) `bwd` inverts `S` and (P2) `fwd`/`bwd` are mutual inverses.
   P2 was the missing piece (not in the original §2 sketch): the `ftvar` fwd-hit branch needs
   it to recover `bwd[y]? = some x` from `fwd[x]? = some y`. fresh-insert case re-establishes
   both via `getElem?_insert`; tcons threads through `goList_bwd_inverts`; bitvec vacuous.
2. ✅ **H2** `alphaEquivMap_self_subst_bwd` — unfolded `alphaEquivMap`, ran H1 at `{}` with
   both preconditions discharged via `getElem?_empty`.
3. ✅ **G2 = leaf stub** `alphaEquivMap_renameSubst_inverse_ftvar` — H2 gives `(y, x)` with
   `bwdMap[y]? = some x`; `mem_toList_iff_getElem?_eq_some` lifts to `(y,x) ∈ toList`;
   `distinct_keys_toList` (→ `List.pairwise_map`) gives key-nodup; G1 (`find?_renameMap_of_mem`)
   does the lookup; `Maps.find?`/`subst_unfold` finish both `y=x` and `y≠x` cases.

### Remaining sorrys in FunctionTypeSpecProps.lean (separate tracks, not part of this lemma):
Status as of this session (signature-helper track):
- ✅ `LTy.freeVars_nil_imp_mem` — DONE. `removeAll xs = []` ⟹ every free var ∈ `xs`.
  Proof: unfold `LTy.freeVars`/`List.removeAll` to a `filter`, `Decidable.em` on `v ∈ xs`,
  contradiction via `List.mem_filter` + `List.not_mem_nil`. (No Mathlib `by_contra` in this repo.)
- ✅ `Function.typeCheck_inputsNodup` — DONE. Peel `typeCheck` to all `.ok` branches via
  `elim_err`; in every branch `func'.inputs = map (fun x => (x.fst, _)) (func.inputs.keys.zip _)`,
  so its keys are a `Sublist` of `func.inputs.keys` (Nodup via existing
  `Function.typeCheck_inputs_nodup`). New helper `List.map_fst_zip_sublist`.
- ✅ `Function.typeCheck_typeArgsNodup` — DONE. Same peel; `func'.typeArgs =
  map Prod.snd (_ .zip func.typeArgs)`, a `Sublist` of `func.typeArgs` (Nodup via
  `LFunc.type_typeArgs_nodup`). New helper `List.map_snd_zip_sublist`.
- ✅ `Function.typeCheck_noUndeclaredVars` — **DONE, fully sorry-free.** Top-level reduces to
  D1 + D2 (both now proved). **NOT an "easy helper"** as originally labeled. Added
  `h_wf : TEnvWF Env` to the signature (needed for `AliasesWF`); call site in
  `typeCheck_annotated_sound` updated. See §9 for the proof shape.
- ✅ **D2** `instantiateWithCheck_freeVars_eraseDups_length_le` — **DONE.** ⚠️ The original
  statement was FALSE (counterexample: `type = .forAll [] (.ftvar "a")` gives
  `boundVars=[]` but `monoty.freeVars.eraseDups=["a"]`, so `1 ≤ 0`). Fixed by adding
  hypothesis `h_closed : LTy.freeVars type = []` (the undeclared-vars guard, always true at
  the call site via `h_undecl`; threaded in there FIRST). Proof: `rcases type`, `h_closed`
  ⟹ body freeVars ⊆ `xs`; decompose `instantiateWithCheck` (`elim_err`) into `instantiate`
  + `resolveAliases`; `LMonoTy_resolveAliases_freeVars_subset` (de-alias ⊆) + case on `xs`
  (`[]`: freshtvs=[]; `cons`: `genTyVars_length` + `LMonoTy.freeVars_subst_closed`); then
  `eraseDups_Nodup` (needs `import all Strata.DL.Util.Nodup`) + `List.subset_nodup_length`.
- ✅ **D1** `freeVars_rename_subset` — **DONE.** Two standalone zip/take equalities
  (`(I.zip T).map snd = T.take I.length`; subst-map = `zip I (map ftvar (T.take I.length))`)
  reduce to `LMonoTy.freeVars_subst_closed` with `freshtvs := tgts.take ids.length`
  (`h_len` from `List.length_take` + `h_cov`). `ids=[]` case is vacuous via `h_closed` +
  `subst_emptyS`; `cons` case discharges `hasEmptyScopes = false` by casing on the take.
- ✅ `typeCheck_bodyTyped_annotated` (1026), `typeCheck_measureTyped_annotated` (1137) —
  DONE (sorry-free); both consumed by `typeCheck_annotated_sound` (1329), also done.
- ⏳ `typeCheck_sound` (Thm 2, polymorphic soundness → `FuncHasType`). Now decomposed into
  five `func`-side field helpers (assembled in `typeCheck_sound` via `exact { ... }`, building):
  - ✅ `typeCheck_inputsNodup_orig`, `typeCheck_typeArgsNodup_orig` — DONE (cheap, route through
    `func.type` succeeding).
  - ✅ `typeCheck_noUndeclaredVars_orig` — **DONE.** New reusable helper
    `LMonoTy.freeVars_subset_destructArrow` (reverse of `freeVars_destructArrow_subset`); then
    decompose `LFunc.type`, both `inputs.values` cases, close via the undeclared-vars guard
    `sigBody.freeVars.removeAll typeArgs = []`.
  - ✅ `typeCheck_bodyTyped`, `typeCheck_measureTyped` — **top-down skeleton DONE (build green).**
    Each delegates to a pipeline-extractor helper (`typeCheck_bodyTyped_instantiated` /
    `typeCheck_measureTyped_instantiated`) and then bridges to the user-facing context/output. The
    renaming bridge was originally `HasType_TContext_subst` (now FALSE — see §10c; ROUTE B replaces it
    by folding the renames into `resolve_HasType_core`'s universal `S`). The deliverable structure
    (instantiated extractor + alias bridges) is unchanged.
    Two design issues surfaced and were resolved while wiring this:
    - **Ambient-context bug → `funcContext Γ` fix (§10d, DONE).** Old `funcContext func` (single
      formals scope) is false for statement-level `funcDecl`s checked in a non-empty ambient context;
      `funcContext` now takes the ambient `Γ`. `typeCheck_sound` concludes `FuncHasType C Env.context func`.
    - **Type-alias gap → original-func + alias bridges (§10e, planned).** Body is checked against
      alias-RESOLVED types but the spec uses the raw (possibly aliased) `func` signature; the
      `_instantiated` equalities relax to `AliasEquiv`, bridged at the top level via `talias` (output)
      + a NEW `HasType_context_aliasEquiv` lemma (context).
  - ⏳ **Remaining `sorry`s & ORDERED next steps** — strict top-down: finish each PARENT body against
    sorried stubs (validates the stub statements) BEFORE proving the stubs; among independent leaves,
    hardest-first. (`_instantiated` witness scaffold built green; see §10f/§10g/§10h/§10i.)

    ### ⚠️ EXACT REMAINING WORK (authoritative — 6 `sorry`s as of this session)
    `lake build` is EXIT 0 with **6 `sorry` warnings**. Nothing in the `typeCheck_sound` chain is fully
    proved until all are discharged (each parent transitively depends on `sorryAx`). Current state:

    **CURRENT SORRY INVENTORY (7; build GREEN, verified `lake build`).** `bodyComposite_pack`
    (FunctionTypeSpecProps:2235) and the 4 composition helpers (`LTy.subst_compose_forAll_nil`:33,
    `TContext.{types_subst_go,types_subst,subst}_compose_forAll_nil`:…/80) are PROVEN, sorry-free.
    Both `_instantiated` proof BODIES are sorry-free.

    | # | `sorry` location | what it is | status |
    |---|---|---|---|
    | C | FunctionTypeSpecProps:1869 | `typeCheck_inverse_components` (per-component alias adapter) | ⏳ layer 3 (genuine leaf) |
    | G | FunctionTypeSpecProps:2183 | `internalContext_values_mono` (internal ctx all `forAll []`) | ⏳ layer 3 leaf, LOW (§10m pt 1) |
    | H | FunctionTypeSpecProps:2257 | `bodyComposite_wf` (concludes `SubstWF S`; replaced `bodyComposite_disjointness`) | ⏳ **NEXT** layer 2, sorry'd-with-plan. WIRED top-down: `bodyComposite_pack` now takes a single `h_wf_S` (sorry-free), call site passes `bodyComposite_wf`. Discharge via `SubstWF_compose_of_cover` (PROVEN) + `vunify_avoids_typeArgs` (PROVEN) + E ρ₀-contract. |
    | H-engine | LTyUnifyProps `SubstWF_compose_of_cover`, `freeVars_compose_subset_scrub` | composite WF without inner-factor WF | ✅ PROVEN |
    | H-prov | FunctionTypeSpecProps `vunify_avoids_typeArgs` | `v_unify` keys+range ∩ `func.typeArgs` = ∅ | ✅ PROVEN (from `resolve_freeVars_pred` leaf + `unify_pred`) |
    | H-unify | LExprTypeSpec `Constraints.unify_pred` | predicate transfer through unify | ✅ PROVEN |
    | H-resolve | LExprResolveProps:771 `resolve_freeVars_pred` | body type + resolve subst avoid typeArgs (predicate-closure of resolve) | ⏳ deep leaf, sorry'd-with-plan (resolveAux induction) |
    | B | FunctionTypeSpecProps:2697 | `measureComposite_pack` (ROUTE B measure composite `∃ S`; fold `ρ∘Sm`, context-only) | ⏳ layer 2, mirror of body (§10m pt 3) |
    | D | LExprTypeSpec:832 | `HasType_context_aliasEquiv` (context alias transfer) | ⏳ layer 3 (genuine leaf) |
    | E | LExprTypeSpec:5346 | `LTy_instantiateWithCheck_inverse` (STRENGTHENED to single-scope `[ρ₀]`; FEEDS G/H/B) | ⏳ layer 3 (genuine leaf, §10m pt 4) |
    | F | LExprTypeSpec:804 | ⛔ `HasType_TContext_subst` — FALSE (§10c). **No uses remain.** | ⏳ DELETE once H/B proved |

    **ROUTE B step 1 DONE (build green):** composition law `LMonoTy.subst_compose` + WF companion
    `SubstWF.compose` (general, inner multi-scope) in LTyUnifyProps.lean; see §10c STATUS box. All
    false-bridge CALL SITES already rewired (body+measure `_instantiated` STATE the post-ρ judgment;
    consumers `typeCheck_bodyTyped`/`measureTyped` drop the bridge).

    **ROUTE B step 2 DONE (build green):** producer stubs EXTRACTED into named layer-2 helpers
    `bodyComposite_pack` (now PROVEN) / `measureComposite_pack` (sorry, mirror), so the
    `_instantiated` proof BODIES contain no sorry (they `obtain` the composite from the helper and feed
    `resolve_HasType_core.1`, with the measure also bridging `Cm→C` via `HasType.of_rigidTypeVars_irrel`
    and collapsing `subst S .int = .int`). `bodyComposite_pack` is now FULLY PROVEN (acts-as via the
    composition helpers, absorbs via the two-layer subst argument, SubstWF via `SubstWF.compose`,
    polyKeysFresh vacuous) — it consumes its disjointness/WF/mono facts as HYPOTHESES, supplied at the
    body call site by the leaves G (`internalContext_values_mono`) and H (`bodyComposite_disjointness`).
    The remaining genuinely-new content is H (the SubstWF-of-composite crux, §10m pt 2) and B
    (`measureComposite_pack`, the measure mirror).

    **Done this session (parent gluing — NOT a full proof, just sorry-free bodies):** body
    `_instantiated` (all 4 sub-goals: `h_wf_rename`, `h_ws_internal`, `polyKeysFresh`, Region A — Region B
    was done earlier) + the factored shared `contextAliasEquiv_facts`. These make the parent bodies
    `sorry`-tactic-free, which validates the 5 stub STATEMENTS, but the theorems remain UNPROVED until
    A–E above are closed.

    **STRUCTURE DECIDED (this session): general stub + shared adapter (§10i).** The instantiation
    inverse is split into a reusable LExprTypeSpec stub (`Function`-agnostic, equality form) and a
    shared FunctionTypeSpecProps adapter (`Function`-shape, per-component facts) consumed by BOTH
    `_instantiated` lemmas — no duplication across body/measure.

    **✅ `typeCheck_bodyTyped_instantiated` — its PROOF BODY now contains no `sorry` tactic (this session,
    build green).** ⚠️ This does NOT mean it is fully proved: it still transitively depends on `sorryAx`
    through sorried LEAF lemmas it calls — `HasType_TContext_subst` (LExprTypeSpec:804, **FALSE — being
    DELETED via ROUTE B**), `LTy_instantiateWithCheck_inverse` (LExprTypeSpec:5346),
    `typeCheck_inverse_components` (FunctionTypeSpecProps:1811), and (via `typeCheck_bodyTyped`)
    `HasType_context_aliasEquiv` (LExprTypeSpec:832). What IS established: the parent gluing logic is real, validating the stub
    STATEMENTS are the right ones. (See the authoritative 6-`sorry` table above for current exact state.)

    **🔧 SHARED LEMMA FACTORED (this session): `Function.contextAliasEquiv_facts`.** The two context-alias
    conjuncts (`.aliases`-eq + `TContextAliasEquiv`) are IDENTICAL for body and measure — both resolve their
    subject in the SAME internal context `Γ_inst = ((FORMALS :: ambient).subst v_unify.subst).subst renameSubst`
    (the measure resolves in the post-unify env, whose `.context` = body-resolution context via
    `resolve_preserves_context`; `updateSubst` doesn't touch `.context`). Factored into one lemma taking the
    extracted facts (`h_alphaMap`, `h_gen_none`, `h_rigid_fixed`, `h_ρ_keys`, `h_ae_ins`, `h_ambient_rigid`,
    `h_ambient_mono`) as explicit hypotheses; the body now calls `(contextAliasEquiv_facts …).1/.2`. Avoids
    duplicating ~220 lines into the measure.

    1. **`typeCheck_bodyTyped_instantiated` BODY** (FunctionTypeSpecProps) — ✅ DONE, sorry-free.
       a. 3 alias conjuncts:
          - ✅ `.aliases`-eq — DONE (`subst_aliases` ×3 + `context'` + `funcContext` rfl via `import all`).
          - ✅ output `AliasEquiv` — DONE (`rw [h_out_eq]` then the adapter's `h_ae_out`).
          - ✅ `TContextAliasEquiv` — DONE (now via shared `contextAliasEquiv_facts`). `find?`-quantifier
            over the context stack `formals :: Env.context.types` (newest-first). The decomposition:
            `intro x ty h_find`; reduce internal `.types` to `FORMALS :: Env.context.types` (`h_int_types`
            via `pushEmptyContext`/`addInNewest`/`List.nil_append`); walk the triple subst back to a raw `ty0` via
            **3× `TContext_types_subst_find_reverse`** (de-privatized from LExprTypeSpec, with its two `go` helpers);
            `cases Map.find? FORMALS x` → Region A (`some`) / Region B (`none`).
            - **Region A (formals, newest scope):** ✅ DONE this session (build green). `h_formals : FORMALS.find?
              x = some tyF` ⟹ `tyF = forAll [] s` with `s ∈ slice` (`Map.find?_mem` + `List.mem_map`); the triple
              subst collapses `s` via the input round-trip `alphaEquivMap_renameSubst_inverse` (input analog of
              `h_out_eq`, free vars of slice elt ⊆ `v_inst.fst` via `mem_destructArrow_freeVars_subset`); NEW
              parallel-walk helper `region_a_input_lookup` extracts the funcContext-scope lookup + pointwise
              `AliasEquiv` from `h_ae_ins`. Closed with `AliasEquiv.symm`.
            - **Region B (ambient `Env.context.types`):** 🔧 top-level DONE, sub-haves in progress. Γ applies
              `ρ∘rename∘unify` to ambient types while Γ' leaves them raw, so equality needs those substs to be
              IDENTITY on ambient free tyvars. Structure built this session (build green):
                · **`h_ambient_mono` ADDED** (alongside `h_ambient_rigid`) to all 5 lemmas + threaded through
                  call sites: `∀ x ty, find? x = some ty → boundVars ty = []`. **CORRECTION to old plan:**
                  monomorphism IS needed (the `find?`-quantifier form does NOT sidestep it). A closed-but-poly
                  ambient entry `forAll [a] (a→a)` satisfies `h_ambient_rigid` (freeVars=[]) yet breaks the
                  `forAll []` shape `TContextAliasEquiv` requires. Established by setupInputEnv + the poly-init
                  removal in CmdType (local `var` decls now store only `forAll [] _`). TODO(preservation).
                · **`h_rigid_fixed` extracted** from `h` before `clear h` (the §10j rigid check ⟹ `v_unify.subst`
                  fixes every rigid var).
                · ✅ **B1a (`h_unify_id`)**: `subst v_unify.subst mty0 = mty0` via `agree_on_freeVars_implies_subst_eq`
                  (LTyUnify.lean:375) against the empty subst + `h_rigid_fixed` + `h_fv_rigid` (free vars of mty0
                  are rigid, from `h_ambient_rigid` + `removeAll_nil`).
                · ✅ **B1b (`h_rename_id`) — DONE this session (build green).** `subst renameSubst mty0 = mty0`
                  via `LMonoTy.subst_no_relevant_keys`. Disjointness chain: a `renameSubst` key is a `bwdMap`
                  key (`mem_keys_renameMap_imp`), hence a free var of `subst v_unify.subst v_inst.fst` (NEW
                  lemma `alphaEquivMap_bwd_keys_subset`, built on NEW structural `go_bwd_keys_subset` /
                  `goList_bwd_keys_subset`); meanwhile `freeVars mty0 ⊆ knownTypeVars(subst Env.context.types
                  v_unify.subst)` (`types_knownTypeVars_of_find` on `h_unify_id`-substituted ambient entry).
                  The **#1399 guard fact `h_gen_none`** (extracted from `h` before `clear h`, alongside
                  `h_rigid_fixed`, via `h_rigid_none` then `pure ()` reduction) says those two sets are disjoint.
                  This uses NEITHER `h_ambient_rigid` NOR `h_ambient_mono` for the key fact.
                · ✅ **B1c (`h_rho_id`) — DONE this session (build green).** `subst ρ mty0 = mty0` via
                  `subst_no_relevant_keys`. ρ's keys are `isFresh` for `Env.context` (so absent from every
                  ambient binding incl. `mty0` via `h0`). **Required strengthening the inverse stub**
                  `LTy_instantiateWithCheck_inverse` (LExprTypeSpec:5346) with a 4th conjunct
                  `∀ x ∈ Maps.keys ρ, TContext.isFresh x Env.context` (the honest contract; provable from
                  `instantiateEnv_freeVars_fresh` when that stub is discharged in step 5). Call site destructures
                  `h_ρ_keys`. **This is the CORRECT route for B1c** — the #1399 guard covers `renameSubst`'s keys
                  (post-unification generalized vars) but NOT ρ's keys (pre-unification fresh instantiation vars);
                  freshness is the right argument for ρ. Counterexample if freshness failed: if instantiation
                  reused ambient `t` as the "fresh" var, ρ = {t↦a} and `subst ρ t = a ≠ t`.
                · ✅ **B2 (`h_rhs_lookup`) — DONE this session (build green).** `funcContext.types.find? x =
                  some (forAll [] mty0)`. `funcContext` pushes the input scope (keys = `func.inputs.keys`) onto
                  `Env.context.types`; `x ∉ FORMALS` (`h_formals`) + formals/input scopes share keys ⟹ `x ∉
                  func.inputs.keys` ⟹ RHS input scope misses `x` ⟹ falls through to ambient `h0`. Length match
                  `(take n da).length = func.inputs.keys.length` from `h_ae_ins` (NEW `AliasEquivList.length_eq`)
                  + `List.map_fst_zip`; `Map`/`ListMap.findNone_eq_notmem_mapfst` for the lookups.
                · Final assembly (DONE): `rw [h_ty_eq, LTy.subst_forAll_nil ×3, h_subst_id]` + `AliasEquiv.refl`.
       **REGION B IS COMPLETELY SORRY-FREE** (proven earlier; now lives in `contextAliasEquiv_facts`).
       b. ✅ 3 mechanical haves — all DONE this session (build green):
          - ✅ `SubstWF renameSubst` — NOT mechanical as labeled; needs the bwd-inverts-S invariant +
            idempotence of the WF `v_unify.subst` (a swap-substitution would violate `SubstWF`). NEW helpers:
            `alphaEquivMap_self_subst_bwd_inverts` (exposes P1 from `go_bwd_inverts`) + `substWF_renameMap`
            (key-can't-be-a-value via `LMonoTy.subst_idempotent`).
          - ✅ `WellScoped body` internal env — knownVars monotonicity: internal `.types` = `FSIG :: ambient`,
            so `h_ws`'s ambient membership lifts via `List.mem_append`.
          - ✅ `polyKeysFresh v_unify.subst` — vacuous: every internal binding is monomorphic (FORMALS are
            `forAll []` by construction; ambient via `h_ambient_mono`), so the `boundVars ≠ []` guard never fires.
    2. **`typeCheck_measureTyped_instantiated` BODY** — ✅ DONE (sorry-free body, build green). Sibling of
       step 1 (output `.int`, alias-free, no output bridge). Reuses the SHARED `contextAliasEquiv_facts` for
       both context conjuncts (same `Γ_inst`). The measure peel extracts
       `v_measure`/`h_measure_resolve`/`h_measure_int` (+ `h_gen_none`/`h_rigid_fixed`/`h_ρ_keys`/`h_ae_ins`);
       `resolve_HasType_core` is applied via the layer-2 helper `measureComposite_pack` (B) at the composite
       `S = compose ρ₀ Sm`, then bridged `Cm→C` by `HasType.of_rigidTypeVars_irrel` and collapsed
       `subst S .int = .int`. The remaining sorry is INSIDE B (the composite helper), not the body.

    **Dependencies (leaf lemmas) — ordered top-level-first then hardest→easiest, respecting the
    topological constraint that the adapter (step 6) uses `resolveAliases`-over-`mkArrow'` (step 7).**
    3. **⛔ `HasType_TContext_subst` is FALSE → ROUTE B** (see the §10c correction box for the
       machine-checked capture counterexample). Do NOT prove it by induction — the `tgen` case is
       genuinely false. Instead: construct a composite substitution `R` (rename folded into
       `v_unify`), instantiate the already-proved `resolve_HasType_core.1` (:7582, universal over
       absorbing `S`) at `R`, collapse via `LMonoTy.subst_absorbs` (LTyUnifyProps:107), rewire both
       `_instantiated` lemmas, then DELETE `HasType_TContext_subst` + its `LTy.subst_forAll_nil` call
       sites. `typeCheck_sound` remains true (resolve never emits `tgen`).
    4. **`HasType_context_aliasEquiv`** (LExprTypeSpec:804, §10e) — context alias transfer, induction
       on `HasType`. Second hardest (sibling induction to step 3).
    5. **`LTy_instantiateWithCheck_inverse`** (LExprTypeSpec:5346, stub) — REFORMULATED to equality
       form `resolveAliases (toMonoTypeUnsafe ty) Env = .ok (subst ρ mty, Env_r)` (§10i; the old
       `AliasEquiv`/whole-`destructArrow` `AliasEquivList` form was ill-typed — output region expands
       under resolution, see §10h EMPIRICAL CHECK). Build `ρ` from `genTyVars` freshness/distinctness;
       core fact = ρ inverts the fresh instantiation + commutes through `resolveAliases`. **STRENGTHENED
       this session with a 4th conjunct `∀ x ∈ Maps.keys ρ, TContext.isFresh x Env.context`** (needed by
       Region B B1c, already threaded to that call site). Discharge via `instantiateEnv_freeVars_fresh`
       (LExprTypeSpec:959): ρ's keys are the fresh instantiation vars, each fresh-for-`Env.context`.
    6. **`typeCheck_inverse_components`** (FunctionTypeSpecProps adapter, sorried) — peel `n` leading
       arrows of `SIG` (`resolveAliases` distributes over the arrow spine since no alias is named
       `"arrow"`), then `resolveAliases_aliasEquiv` per raw component → output `AliasEquiv` + input
       `AliasEquivList`. Parent of step 7 (so proven against a sorried step 7 first).
    7. **`resolveAliases` distributes over `mkArrow'`** given `∀ a ∈ aliases, a.name ≠ "arrow"` (§10h,
       Option 2). Concrete/structural over the arrow spine. New helper in LExprTypeSpec. Leaf of step 6;
       easiest, proven last.
    - **TODO(preservation), separate track:** discharge `h_aliases_not_known` (∀ context alias name ≠
      "arrow") as an invariant preserved by the type-decl/function typechecker (enforced by
      `TEnv.addTypeAlias` LExprTypeEnv:1348 + `"arrow" ∈ knownTypes`), threaded to call sites.
    - **NEW invariant track (rigidity), for Region B above — ✅ VERIFIED + threaded:** `h_ambient_rigid`
      (`freeVars of every ambient binding ⊆ C.rigidTypeVars`) added to all 5 lemmas, build green.
      Established by ProcedureType.setupInputEnv, preserved by checkAnnotCompat + goBlock, vacuous at
      top level. TODO(preservation): discharge it as an invariant at the call site (like
      `h_aliases_not_known`). Identity-on-ambient confirmed via §10j rigid check + gen-counter
      disjointness (see §5 step 1a Region B).
  See §10/§10c/§10d/§10e/§10f/§10g/§10h/§10i/§10j for the proof shapes & reuse map.

## 10. `typeCheck_sound` — investigation result (this session)

**Goal:** `FuncHasType C func` = `FuncHasType' LTy instHasType C func` — same 5-field structure
as the DONE `typeCheck_annotated_sound`, but differs on TWO axes simultaneously:
- **Subject**: original `func` (not output `func'`).
- **Relation**: polymorphic `HasType C (funcContext func)` with output `.forAll [] func.output`
  (not monomorphic `HasTypeA []` on `func'.output`).

**There is NO `HasTypeA → HasType` bridge lemma** (confirmed by exhaustive grep). So we cannot
convert the annotated result; we must re-derive polymorphically.

**Field-by-field:**
- `inputsNodup`, `typeArgsNodup` — cheap. Existing `func'` versions already route through the
  original `func`'s nodup (`LFunc.type_inputs_nodup`/`type_typeArgs_nodup`); `func.type = .ok type`
  recoverable from `h`. Keys of `func'.inputs` = keys of `func.inputs`, so mechanical.
- `noUndeclaredVars` — `func`-side analog of the proved `func'` one (about `func.output`/
  `func.inputs.values` instead). Follows from `LFunc.type` well-formedness; modest.
- `bodyTyped` — **hard core.** Need `HasType C (funcContext func) body (.forAll [] func.output)`
  on the ORIGINAL (unresolved) body. Path: re-run the body through the POLYMORPHIC
  `resolve_HasType` (LExprTypeSpec:7562) — NOT `resolve_HasTypeA`. This is exactly why the three
  extra hypotheses exist: they ARE `resolve_HasType`'s preconditions (annotated twin needs none):
  - `h_ws : WellScoped body Env.context` (LExprTypeSpec:6339, every free var ∈ knownVars)
  - `h_fresh : Subst.allKeysFresh Env.stateSubstInfo.subst Env.context` (:432)
  - `h_closed : LExpr.checkContextTypesClosed Env` (LExprT:313, all context types freeVars=[])
- `measureTyped` — mirrors `bodyTyped`.

**Reuse map:**
- **Template**: `Cmd.typeCheck_sound` (CmdTypeSpecProps:277, ~250 lines) is the EXACT analog —
  same poly-vs-annotated split, same three extra hypotheses. Follow its skeleton.
- **Generalization machinery (reusable):** `HasType_subst_fresh` (:306), `HasType_subst_fresh_all`
  (:706), `HasType_tinst_all` (:3987), `HasType_LTy_instantiate` — handle the `.forAll []`
  generalization and the `userSubst`/`renameSubst` round-trip on TYPES.
- **Must build fresh:** `HasType_tyvar_rename` (referenced in `FuncHasType'` docstring at
  FunctionTypeSpec:51 but DOES NOT EXIST) — `HasType` preserved under renaming instantiated fresh
  vars back to user names. Plus relating `funcContext func` to typeCheck's internal env
  (`pushEmptyContext` + `LFunc.inputMonoSignature`, Factory:127). This renaming lemma is the
  main research risk.

**Effort:** large (~200+ lines by analogy with `Cmd.typeCheck_sound`).

### 10b. UPDATE — `bodyTyped`/`measureTyped` blocker analysis (this session, post-decomposition)

Three of five fields now proved (`inputsNodup_orig`, `typeArgsNodup_orig`, `noUndeclaredVars_orig`).
`bodyTyped`/`measureTyped` remain. Two candidate paths investigated; **both blocked on a missing
lemma**:

1. **Bridge the annotated result** (`typeCheck_bodyTyped_annotated` → polymorphic): the annotated
   proof types the body in the EMPTY context `[]` (via `bodyTyped_chain`/`resolve_HasTypeA`), so it
   never crosses the context gap. The polymorphic goal carries `funcContext func`. There is NO
   `HasTypeA [] e mty → HasType C Γ e (.forAll [] mty)` bridge, and NO context-renaming lemma.

2. **Direct polymorphic resolve in `funcContext func`** (mirror `Cmd.typeCheck_sound`, which resolves
   in the USER context `Env.context`): blocked because `Function.typeCheck` resolves the body in the
   INTERNAL INSTANTIATED env (inputs bound to FRESH monotypes from `monoty.destructArrow`), NOT in
   `funcContext func` (inputs bound to USER monotypes). The provided `h_ws`/`h_fresh`/`h_closed` are
   wrt `Env.context`, not `funcContext func` or the internal env. So `h` gives a resolve fact about
   the instantiated env only; relating it to a `funcContext`-resolve is the same renaming gap.

**Definitional facts confirmed:** `funcContext func = { types := [LFunc.inputMonoSignature func] }`
(both = `func.inputs.map (id,mty)↦(id,.forAll [] mty)`). But `funcContext` uses the ORIGINAL func
(user monotypes) while typeCheck's internal env uses `inputMonoSignature` of the INSTANTIATED func
(fresh monotypes). The instantiation is a bijective tyvar renaming (sigBody.freeVars ⊆ typeArgs,
each typeArg ↦ distinct fresh var).

**The missing lemma (research risk, must author):** a `HasType` preservation lemma under a bijective
tyvar renaming applied SIMULTANEOUSLY to context and type — i.e.
`HasType C (Γ.substTyVars ρ) e (ty.substTyVars ρ) ↔ HasType C Γ e ty` for a tyvar bijection `ρ`.
`HasType_subst_fresh`/`HasType_subst_fresh_all` (:306/:706) only substitute the TYPE for vars FRESH
in Γ — unusable here since user tyvars are BOUND in `funcContext`'s input types. Also need to relate
`Env_inst.pushEmptyContext.addInNewestContext (inputMonoSignature func_inst)` (a scope ON TOP of
`Env_inst.context.types`) to the single-scope `funcContext` — no packaged lemma; nontrivial unless
`Env_inst.context.types` is handled.

**Recommendation:** confirm with user before authoring the simultaneous context+type tyvar-renaming
preservation lemma (substantial, new infrastructure in LExprTypeSpec). This is the crux for both
remaining fields.

### 10c. The renaming step — `HasType_TContext_subst` is FALSE; use ROUTE B

> **⛔ `HasType_TContext_subst` IS FALSE — DELETE it, do NOT prove it.**
> The originally-planned lemma `HasType C Γ e ty → SubstWF S → HasType C (Γ.subst S) e (LTy.subst S ty)`
> (and its "injective renaming" fallback) is **not a theorem**. The bug is the capturing behaviour of
> `LTy.subst`: on `.forAll xs body` it only removes `xs` (the scheme's *own* bound vars) from `S`, then
> substitutes the body — so a *range* variable of `S` is captured by the binder. The `tgen` case of any
> `induction h` is therefore unprovable in general.
>
> **CONCRETE COUNTEREXAMPLE (machine-checked: each fact below closed by `native_decide`/`rfl`).**
> Context `Γ = { z : forAll [] (ftvar "b") }` (mono — `boundVars = []`), and the **injective renaming**
> `S = [[("b", ftvar "a")]]` (`SubstWF S = true`). Derivation of the hypothesis:
> 1. `tvar`: `HasType C Γ (fvar z) (forAll [] (ftvar "b"))`.
> 2. `"a"` is fresh in `Γ` (Γ mentions only `"b"`), so `tgen` gives
>    `HasType C Γ (fvar z) (close "a" (forAll [] (ftvar "b"))) = HasType C Γ (fvar z) (forAll ["a"] (ftvar "b"))`.
>
> The lemma's conclusion would be `HasType C (Γ.subst S) (fvar z) (subst S (forAll ["a"] (ftvar "b")))`.
> But `subst S (forAll ["a"] (ftvar "b")) = forAll ["a"] (ftvar "a")` (**capture**: `"a"` is bound, `S`
> removes only `"a"` from its scope, leaving `"b" ↦ "a"` active), while `Γ.subst S = { z : forAll [] (ftvar "a") }`.
> Typing `fvar z` at `∀a. a` is underivable: `tvar` only yields the recorded `forAll [] (ftvar "a")`, and
> re-`tgen` needs `isFresh "a" (Γ.subst S)`, now FALSE since `z`'s type contains `"a"`. **All hypotheses
> hold, conclusion is false.** ∎ The "injective renaming" fallback (lines below) dies on this same example
> (`S` IS injective). A mono *context* does not help (the counterexample's context is already mono);
> mono *output* alone does not help either (the `tgen`/`tinst` premises in the induction are polymorphic).
>
> **The exact repairing side-condition (for the record):** `Subst.freeVars S ⊆ TContext.knownTypeVars Γ`
> (every *range* var of `S` is already known in `Γ`). Then any `tgen`-var `a` (`isFresh a Γ` ⟹
> `a ∉ knownTypeVars Γ` ⟹ `a ∉ freeVars S`) avoids both capture and the freshness-transfer failure.
> **BUT this is FALSE at the call site:** `S = ρ` is a fresh→user renaming and `Γ_inst` binds formals at
> the *instantiated fresh* monotypes, so ρ's range (user names) is renamed OUT of `Γ_inst` —
> `freeVars ρ ⊄ knownTypeVars Γ_inst`, exactly the counterexample's shape. So we cannot discharge it.
>
> **`typeCheck_sound` IS STILL TRUE (the bug is only the over-general bridge, not the deliverable).**
> `resolve` NEVER emits the `tgen` rule (verified: no `HasType.tgen`/`LTy.close` is constructed anywhere
> in `resolve_HasType_core` :7575–7950 or the resolve pipeline). Every resolve-produced judgment lives in
> the **monomorphic, `tgen`-free fragment** (only `tvar`/`tapp`/`tif`/`teq`/`tabs`/`tquant`/`talias`/`top`/
> mono-`tinst`), so the capturing case never arises on the judgments we actually substitute.
>
> **DECISION — ROUTE B (delete the bridge; reuse the already-proved `resolve_HasType_core`).**
> `resolve_HasType_core.1` (:7582) is UNIVERSALLY quantified over every `S` that absorbs `Env'.subst`,
> already yielding `HasType C (Γ.subst S) e (.forAll [] (subst S ety))` — i.e. context-substitution
> preservation *for the resolved body* is ALREADY PROVED, for free, for any absorbing `S`. Combined with
> the collapse law **`LMonoTy.subst_absorbs`** (LTyUnifyProps:107) — `absorbs S_outer S_inner →
> subst S_outer (subst S_inner mty) = subst S_outer mty` — plus `absorbs_refl`/`absorbs_trans`
> (LTyUnifyProps:181/192) and the `subst_compose_*` family (LExprTypeSpec:4429+), we instantiate
> `h_core.1` ONCE at a single substitution `R` that already folds in the fresh→user renaming, instead of
> the current two-step (`h_core.1 v_unify.subst` THEN the false bridge). No induction, no `tgen`, no capture.
>
> **WHY `SubstWF` is the crux (refined this session).** `resolve_HasType_core.1` has signature
> `∀ S, absorbs S Env'.subst → SubstWF S → polyKeysFresh S Env.context → HasType C (Γ.subst S) e
> (.forAll [] (subst S ety))`. So `SubstWF S` is REQUIRED just to obtain the context-substituted
> judgment (it is also an existential conjunct of the goal — the witness rename must be WF). The
> `absorbs` family (`subst_absorbs` :107, `absorbs_trans` :192, `absorbs_refl` :181) discharges the
> *absorbing* side-condition and the *type collapse* for free, but does NOT give `SubstWF` of a
> composite — **that is the only genuinely new content replacing the false bridge.**
>
> **⚠️ A FLAT MERGE OF THE TWO RENAMINGS IS NOT `SubstWF`.** `renameSubst : unifyVar ↦ instVar`
> (keys = surviving unify-fresh vars, values = instantiation vars); `ρ : instVar ↦ userVar` (keys =
> instantiation vars). The instantiation vars are simultaneously `renameSubst`'s *values* and `ρ`'s
> *keys*, so `[renameSubst-scope ++ ρ-scope]` has a key inside a value (a 2-cycle
> `unifyVar→instVar→userVar`) → violates `SubstWF`. The composite MUST be built **sequentially** via
> `Subst.apply` (pre-apply the later rename to the earlier one's values), yielding `unifyVar ↦ userVar`
> directly. `Subst.find?_apply` (LTyUnify:586) gives the per-key action; `SubstWF` of the result needs
> `ρ`'s RANGE disjoint from {unify-vars, inst-vars}.
>
> **All three substitutions are single-scope** (`renameSubst` = `[..]` literal; `v_unify.subst` and
> `ρ` are single-scope by the unify/instantiate invariants), which keeps the composite single-scope
> and its WF proof tractable.
>
> **NEW DEPENDENCY — general composition law (does not yet exist).** Only `subst_compose_ftvar_*`
> (LExprTypeSpec:4429/4654, single-scope ftvar-only, closed types) exist. Route B needs a general
> `subst (compose S₂ S₁) x = subst S₂ (subst S₁ x)` for single-scope `S₁ S₂` (via `Subst.apply`).
> Author it in LTyUnifyProps near `subst_absorbs`.
>
> **Obligations for Route B (the real remaining work, replacing the bridge):**
> - Author the general single-scope composition law + its `SubstWF`-of-composite companion (needs
>   `ρ`'s range disjointness — STRENGTHEN the still-`sorry` `LTy_instantiateWithCheck_inverse`
>   (step 5) to also expose `ρ`'s range facts; it's already being strengthened, so this is in-scope).
> - Construct the composite `S` (rename(s) folded into `v_unify` via `Subst.apply`).
> - Prove `S` absorbs `v_resolve.snd.subst` (via `absorbs_trans` through `v_unify`, which already absorbs it).
> - Prove `SubstWF S` (composite law companion) and `polyKeysFresh S Env.context` (vacuous: internal context is mono).
> - Prove `S` ACTS AS rename∘`v_unify` on the body type + formal-context types (so output / `funcContext`
>   come out right) — dovetails with the round-trip identity `alphaEquivMap_renameSubst_inverse` already proved.
> - Rewire `typeCheck_bodyTyped_instantiated` to call `h_core.1 S` once; mirror in `typeCheck_measureTyped_instantiated`.
> - Then **delete** `HasType_TContext_subst` (LExprTypeSpec:804) and its call sites' `LTy.subst_forAll_nil` rewrites
>   (used twice in `typeCheck_bodyTyped_instantiated`/`typeCheck_bodyTyped` + once in the measure).
>
> Route A (a `tgen`-free induction) was REJECTED: `HasType` is a `Prop`, so "this derivation used no `tgen`"
> can't be inspected without a custom auxiliary predicate threaded through `resolve_HasType_core` — more
> invasive than Route B.
>
> **STATUS:** Step (1) DONE (build green). Step order within Route B:
> - ✅ **(1) composition law + WF companion (GENERAL, inner multi-scope)** — `LMonoTy.subst_compose`
>   (`subst [s] (subst S mty) = subst (Subst.compose s S) mty`, unconditional, inner `S` ARBITRARY
>   multi-scope — so no dependence on `v_unify.subst` being single-scope) and `SubstWF.compose`
>   (composite WF from `SubstWF [s]`, `SubstWF S`, + two cross-disjointness conds: S-keys ∉ s-range,
>   s-keys ∉ S-range). `Subst.compose s S := Subst.apply s S ++ [s]`. Helpers `Maps.find?_compose`,
>   `Subst.freeVars_compose_subset`, `Maps.values_single` (LTyUnifyProps) + `Maps.keys_append` /
>   `Maps.values_append` / `Maps.find?_append` (Maps.lean) + `Map.values_append` (Map.lean). All green.
> - ✅ **(3/4 interface) ALL call sites of the false bridge rewired (build green).** Both
>   `_instantiated` lemmas now STATE the post-ρ judgment `HasType C (Γ_inst.subst ρ) e
>   (.forAll [] (subst ρ output_inst))` (measure: output `.int`, `subst ρ .int = .int`). Consumers
>   `typeCheck_bodyTyped`/`typeCheck_measureTyped` drop the `HasType_TContext_subst` call entirely
>   (just `talias` for the body output + `HasType_context_aliasEquiv` for the context). The post-ρ
>   judgments `h_ht_post`/`h_sm_post` are now CLOSED inside the `_instantiated` bodies (sorry-free)
>   by `obtain`ing the composite from the layer-2 helpers `bodyComposite_pack` (PROVEN) /
>   `measureComposite_pack` (sorry) and feeding `resolve_HasType_core.1 S`. See §5 table + §10m for
>   the current sorry inventory.
> - ⏳ Remaining: H = `bodyComposite_disjointness` (SubstWF-of-composite crux, §10m pt 2), B =
>   `measureComposite_pack`, G = `internalContext_values_mono`, E (strengthened inverse), then
>   delete the bridge `HasType_TContext_subst` (LExprTypeSpec:804) — no uses remain.
>

### 10d. Ambient-context bug in the spec + the `funcContext Γ` fix (DECIDED: reformulate)

**The bug (found while proving `typeCheck_bodyTyped_instantiated`).** The old spec used
`funcContext func = { types := [formals] }` — a *single* scope holding only the formals — and
`typeCheck_sound` concluded `FuncHasType C func`. This is **false** for statement-level
`funcDecl`s, which run with a **non-empty ambient context**.

- `Maps.find?` (Maps.lean:97) searches the *entire* scope stack newest→oldest. Body resolution runs
  in `Env_inst.pushEmptyContext.addInNewestContext (inputMonoSignature func_inst)`, whose stack is
  `[formals_inst] ++ Env.context_inst`. So a body can resolve a reference to an **enclosing local**.
- `funcContext func` (single formals scope) omits that enclosing scope, so the resulting `HasType`
  judgment is underivable there.

**Concrete counterexample** (statement-level function capturing an enclosing local):
```
procedure P() {
  var z : int := 0;        // inserts z : int into Env.context.types (under a goBlock pushEmptyContext)
  func g(x : int) : int { body := z }   // funcDecl: body references z, which is NOT a formal of g
}
```
`Function.typeCheck C Env g` succeeds: `z` resolves against the enclosing `z : int` scope, unify
`g.output = int` with `bodyty = int` holds. But `FuncHasType C g`'s `bodyTyped` field demands
`HasType C (funcContext g) z (.forAll [] .int)` with `funcContext g = { types := [[(x, int)]] }`,
which lacks `z` — `tvar` cannot fire. **So `typeCheck_sound : FuncHasType C g` is false.** (The
*annotated* soundness escapes this only because `instHasTypeA.exprTyped` ignores `Γ` and asserts
`HasTypeA []`; the polymorphic spec actually uses `Γ`, so it cannot dodge it.)

Top-level program functions are unaffected: there `Env.context.types = []` (from `TEnv.default`,
preserved across `Program.typeCheck.go` because `LExpr.resolve` preserves `context` and
`Function.typeCheck` does `pushEmptyContext … popContext`).

**The fix — parameterize `funcContext` and the spec by the ambient context `Γ`:**
```lean
def funcContext (Γ : TContext Unit) (func : Function) : TContext Unit :=
  { Γ with types := Γ.types.addInNewest (func.inputs.map (fun (id, mty) => (id, .forAll [] mty))) }
```
i.e. push the formals as the *newest* scope **on top of** the ambient `Γ` (instead of discarding
`Γ`). `FuncHasType' … C Γ func` now carries `Γ`; the fields become
`S.exprTyped C (funcContext Γ func) body (S.embed func.output)` (and the `.int` measure analog).
`typeCheck_sound` concludes `FuncHasType C Env.context func` — the context it was actually checked
in.

**Why this makes `_instantiated` provable.** The bridge equality becomes
`TContext.subst Γ_inst ρ = funcContext Env.context func`, which holds scope-for-scope: `Γ_inst` =
`[formals_inst] ++ Env.context_inst`, and renaming by `ρ` restores the formals scope (fresh→user
names) AND the ambient scope — no scope-erasure needed. Faithful (the spec now says "body has the
output type in the context it was checked in"); covers BOTH paths (top-level: `Env.context.types =
[]` recovers the old single-scope meaning; nested funcDecl: ambient preserved); needs NO
`h_emptyCtx` hypothesis.

**Cost / threading.** `funcContext` gains a `Γ` argument; `FuncHasType`/`FuncHasTypeA` and the five
field call sites in the annotated proof (`typeCheck_annotated_sound`) take the extra argument. The
annotated side stays trivially true (its `exprTyped` ignores `Γ`). No current consumers of
`typeCheck_sound` exist, so no downstream breakage. **Status: DONE** — both files build green;
`funcContext Γ` threaded; `typeCheck_annotated_sound` strengthened to `∀ Γ, FuncHasTypeA C Γ func'`;
`typeCheck_sound` now concludes `FuncHasType C Env.context func`.

### 10e. Type-alias gap in `_instantiated` + the bridge plan (DECIDED: original func + alias bridges)

**The gap (found while drafting `typeCheck_bodyTyped_instantiated`).** `Function.typeCheck` resolves
`func.type` through `LTy.instantiateWithCheck`, whose **first step is `resolveAliases`**
(`LExprTypeEnv.lean:1218`). So the body is type-checked against **alias-resolved** (alias-free)
types: the instantiated context binds formals to resolved monotypes and `output_inst` is resolved.
But the spec's goal `HasType C (funcContext Env.context func) body (.forAll [] func.output)` uses the
**raw** `func.output` and **raw** `func.inputs`, which may still contain type aliases. The exact
equalities I first wrote into `_instantiated` are therefore **false** on any function whose signature
uses an alias.

**Concrete counterexample:**
```
type MyInt := int
func f(x : MyInt) : MyInt { body := x }
```
Pipeline: `instantiateWithCheck` expands `MyInt → int`, so `monoty = int → int`, `output_inst = int`,
`Γ_inst.types = [[(x, .forAll [] int)]]`, `ρ = []` (no tyvars). `typeCheck` succeeds. But the spec
wants `HasType C {x : MyInt} x (.forAll [] MyInt)` with raw `f.output = MyInt`. The two exact
equalities fail:

| helper claim | LHS (resolved, pipeline) | RHS (raw, spec) | holds? |
|---|---|---|---|
| `LMonoTy.subst ρ output_inst = func.output` | `int` | `MyInt` | ❌ only `AliasEquiv` |
| `TContext.subst Γ_inst ρ = funcContext Env.context func` | `{x : int}` | `{x : MyInt}` | ❌ only `AliasEquiv` |

`int` and `MyInt` are **alias-equivalent** (`AliasEquiv aliases int MyInt` via `collapse`), not equal.

**Why the theorem is still TRUE.** `HasType` has the `talias` rule (`LExprTypeSpec.lean:258`) for
exactly this. From the resolved judgment `HasType C {x : int} x (.forAll [] int)` we move BOTH the
result type and the context bindings from `int` to `MyInt`:
- **result type:** directly `HasType.talias` with `AliasEquiv aliases output_inst func.output`
  (`talias` bridges the result type up to alias-equivalence — already exists).
- **context bindings:** needs a NEW lemma `HasType_context_aliasEquiv`: if `body` types in `Γ` and
  `Γ'` has the same aliases and bindings that are pointwise `AliasEquiv` to `Γ`'s, then `body` types
  in `Γ'`. `talias` does NOT cover this (it only touches the result type). Provable by induction on
  `HasType`, dual in spirit to `HasType_resolveAliases` (`:5442`); the `tvar` case re-derives the
  variable at the alias-equivalent type via `talias` after the lookup, the binder cases (`tabs`,
  `tquant`) extend `Γ'` with the alias-equivalent formal type. `AliasEquiv.symm` (`:5039`) is
  available for direction-flipping.

**DECISION (this session):** conclude soundness about the **original `func`** (not the resolved
`func'`), and bridge the alias gap. Faithful to the input function; the cost is the one new
`HasType_context_aliasEquiv` lemma.

**Relaxed `_instantiated` statement.** Replace the two exact equalities with their true forms:
```lean
theorem Function.typeCheck_bodyTyped_instantiated … :
    ∀ body, func.body = some body →
      ∃ (Γ_inst : TContext Unit) (output_inst : LMonoTy) (ρ : Subst),
        HasType C Γ_inst body (.forAll [] output_inst) ∧
        SubstWF ρ ∧
        -- after renaming, the context is alias-equivalent to the spec context:
        (TContext.subst Γ_inst ρ).aliases = (funcContext Env.context func).aliases ∧
        TContextAliasEquiv (funcContext Env.context func).aliases
          (TContext.subst Γ_inst ρ) (funcContext Env.context func) ∧
        -- after renaming, the output is alias-equivalent to the declared output:
        AliasEquiv (funcContext Env.context func).aliases
          (LMonoTy.subst ρ output_inst) func.output
```
(`TContextAliasEquiv aliases Γ₁ Γ₂` := same shape + pointwise `AliasEquiv` on every binding type;
define alongside the lemma. The aliases field of `Γ_inst.subst ρ` equals `Env.context.aliases`
because `TContext.subst` preserves aliases (`subst_aliases`) and the internal env's aliases come from
`Env` unchanged.)

**Top-level chain for `typeCheck_bodyTyped`** (black-box steps):
1. ~~`HasType_TContext_subst` (tyvar renaming)~~ — ELIMINATED under ROUTE B. The `_instantiated`
   helper already produces the judgment under the renamed context `Γ_inst.subst ρ` at `subst ρ
   output_inst` (ρ is folded into the composite `S` fed to `resolve_HasType_core.1`), so no separate
   renaming step is needed here.
2. `HasType.talias` — bridge the result type `subst ρ output_inst ↝ func.output` via the supplied
   `AliasEquiv`.
3. `HasType_context_aliasEquiv` (NEW) — bridge the context `Γ_inst.subst ρ ↝ funcContext Env.context
   func` via the supplied `TContextAliasEquiv` + equal aliases.

**Measure analog.** `output_inst = .int` is already alias-free (`.int` is a known type, not an alias),
so the output bridge (step 2) is trivial (`AliasEquiv.refl`); only the context bridge (step 3) is
needed. The `measure`-instantiated helper carries just the `TContextAliasEquiv` + aliases-eq fields.

**Net NEW obligations from §10e (on top of §10c's ROUTE B composite-substitution machinery):**
- `TContextAliasEquiv` definition (pointwise `AliasEquiv` over context bindings, same shape).
- `HasType_context_aliasEquiv` lemma (induction on `HasType`; dual to `HasType_resolveAliases`).
- The relaxed `_instantiated` helpers now must *produce* the `AliasEquiv`/`TContextAliasEquiv` facts:
  the output `AliasEquiv` comes from `resolveAliases_aliasEquiv` (the same lemma `HasType_resolveAliases`
  uses) applied to `func.output`'s instantiation; the context `TContextAliasEquiv` comes from the same
  fact applied pointwise to each formal's monotype (each formal type is alias-resolved from the raw
  `func.inputs` monotype during `instantiateWithCheck`).

### 10f. Proving `_instantiated` — structure, the closed-context obstacle, the 3-subst split

**Status correction (this session).** `funcContext` was using `Γ.types.addInNewest formals`, which
*merges* the formals into the existing newest scope `(s0 ++ formals) :: rest` and gives formals
LOWER lookup priority than outer locals — wrong (and not what the typechecker does). Fixed to
`Γ.types.push formals` = `formals :: Γ.types`, matching `pushEmptyContext + addInNewestContext` on a
fresh scope. (For empty `Γ` the two coincide, which is why the build stayed green; the bug only bites
nested funcDecls.) **DONE.**

**Obstacle: the internal body-resolution context is NOT `checkContextTypesClosed`.** The polymorphic
`resolve_HasType` (`:7575`) requires `checkContextTypesClosed Env_internal` and `allKeysFresh`, but
`checkContextTypesClosed` (`LExprT.lean:313`) demands EVERY binding have `freeVars == []`. The
internal env binds formals to *instantiated* monotypes that contain FRESH tyvars (`%t0 → %t1`), so it
is NOT closed. ⟹ We must use **`resolve_HasType_core`** (`:7428`) instead, whose conclusion is the
"∀ absorbing S" form
```
∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S → Subst.polyKeysFresh S Env_internal.context →
  HasType C (TContext.subst Env_internal.context S) body (.forAll [] (LMonoTy.subst S body_ty))
```
and needs NO closed/allKeysFresh precondition — only `polyKeysFresh` (which holds: the internal
formals are MONOmorphic, `boundVars = []`, so `polyKeysFresh` is vacuous — discharge via
`allKeysFresh_implies_polyKeysFresh` or directly). `WellScoped body Env_internal.context` follows
from `h_ws` (`WellScoped body Env.context`) by knownVars-monotonicity (internal context ⊇ ambient).

**The substitution layers under ROUTE B.** The pipeline applies S(unify) → renameSubst → userSubst.
Route B never renames a `HasType` judgment after the fact (the renaming lemma is FALSE, §10c).
Instead, fold the layers into ONE composite `S` fed to `resolve_HasType_core.1` a single time:
- **unify `S`**: already the universally-quantified `S` of `resolve_HasType_core.1`. `Subst.absorbs
  (v_unify.subst) (resolve-env subst)` from `Constraints.unify_absorbs`; `SubstWF` from `v_unify.isWF`.
- **renameSubst / userSubst**: composed onto `v_unify.subst` SEQUENTIALLY via `Subst.apply` (NOT a flat
  scope-merge — that breaks `SubstWF`, see §10c box). The composite `S` then satisfies
  `subst S x = subst (rename∘user) (subst v_unify.subst x)` by the general composition law (to be
  authored), absorbs the resolve-env subst by `absorbs_trans`, and is `SubstWF` by the composite-WF
  companion (needs `ρ`'s range disjointness from the strengthened `LTy_instantiateWithCheck_inverse`).

**Witnesses for `_instantiated` (Route B):** choose `Γ_inst`/`output_inst`/`ρ` so the single
`h_core.1 S` judgment IS the body field directly; the alias conjuncts consume `ρ` as today via
`contextAliasEquiv_facts`/`_base`. No `HasType_TContext_subst` anywhere.

**The alias facts (the genuinely new content).** After the renames, the formals scope of
`TContext.subst Γ_inst ρ` holds `subst userSubst (subst renameSubst (subst S input_mty_inst))` for
each formal, which `typeCheck_body_type_eq`-style round-trip lemmas (`:518`, already proved for the
output) reduce to the INSTANTIATED user input monotype = `resolveAliases` of the RAW `func.inputs`
monotype. `resolveAliases_aliasEquiv` (`:5086`) then gives the per-binding `AliasEquiv` (raw ↝
resolved; flip with `AliasEquiv.symm` to the resolved↝raw direction `TContextAliasEquiv` wants). The
ambient scopes of `Γ_inst.subst ρ` map back to `Env.context` unchanged (renames touch only fresh
tyvars, which don't occur in the closed ambient context), giving `AliasEquiv.refl` there. The
`.aliases` equality is `TContext.subst_aliases` + the internal env inheriting `Env`'s aliases. The
output `AliasEquiv` is exactly `typeCheck_body_type_eq` (round-trip = `output_mty`) composed with
`resolveAliases_aliasEquiv` on `func.output`.

**Plan to prove it (top-down within `_instantiated`):** fix the three witnesses; state the body
`HasType` via `resolve_HasType_core.1` at the ROUTE B composite `S` (no `HasType_TContext_subst`);
then state the `.aliases`-eq,
`TContextAliasEquiv`, and output-`AliasEquiv` as named `have`s. Prove the mechanical scaffold
(witness plumbing, `SubstWF`s, `WellScoped`/`polyKeysFresh` discharge) immediately; the three alias
`have`s reduce to the round-trip lemmas + `resolveAliases_aliasEquiv` and are the only nontrivial
remainder. Reuse the annotated proof's decomposition (`typeCheck_bodyTyped_annotated`, `:1026`) for
the pipeline `elim_err`/`split` skeleton — it already extracts `v_inst`, `v_resolve`, `v_unify`,
`bwdMap`, `h_alpha`, and the internal-env WF facts in exactly the shape needed.

### 10g. CRITICAL — the `ρ` witness is NOT `userSubst` (wrong-witness bug, caught by hard-first)

Proving the output `AliasEquiv` conjunct FIRST (hardest-first) immediately surfaced that
`ρ := userSubst` is the **wrong witness**. `userSubst = v_inst.fst.freeVars.eraseDups.zip
func.typeArgs` pairs fresh instantiation vars to declared type args by **appearance order**.
`LTy.instantiate` (`LExprTypeEnv:918`) assigns fresh vars in **declaration order**. When a
function's type args appear out of declaration order, these diverge.

**Counterexample (spec is TRUE, only the witness is wrong):** `func f[a,b](x:b, y:a):a` with body
`y`. Signature monotype `b→a→a`; instantiate (decl order) `a↦t0,b↦t1` ⟹ `t1→t0→t0`.
`freeVars.eraseDups = [t1,t0]` (appearance) ≠ `[t0,t1]` (declaration). Internal env `x:t1,y:t0`,
body `y:t0`, `RO=t0`, unify trivial, alphaEquivMap ok ⟹ **typeCheck succeeds**. Then
`userSubst={t1↦a,t0↦b}`, so `subst userSubst RO = b ≠ a = func.output`: goal `AliasEquiv b a` is
FALSE. (The context conjunct fails the same way: `userSubst` maps `x:t1,y:t0 ↦ x:a,y:b`, not the
declared `x:b,y:a`.) But in `funcContext func` body `y` genuinely has type `a = func.output` ✓ — the
spec holds; only my chosen `ρ` was wrong.

**Fix (DECIDED, no spec change):** `ρ` is an existential WE supply. Use the **declaration-order
instantiation inverse** `ρ' = {freshtvs[j] ↦ ftvar typeArgs[j]}`, where `freshtvs` are the fresh
vars `LTy.instantiate` generated for `func.type`'s bound vars (= `func.typeArgs`, via
`LFunc.type_boundVars_eq_typeArgs`). Source: `LTy_instantiateWithCheck_isInstance` (`:5276`) gives
`tys` (fresh monotypes, one per bound var, in declaration order) with
`AliasEquiv (openFull type tys) v_inst.fst`. With `ρ'`: `subst ρ' RO = func.output` (up to alias) ✓
and the internal context maps back to `funcContext func` ✓✓.

**`Γ_inst` and `output_inst` are already CORRECT** (in fresh decl-order instantiation vars): the
`renameSubst`/`alphaEquivMap_renameSubst_inverse` round-trip cleans unify's renaming back to those
fresh vars, independent of `ρ`. Only `ρ := userSubst` changes to `ρ := ρ'`. The `userSubst` machinery
(`typeCheck_body_type_eq`, `freeVars_reconstructedOutput_subset`) was for the *annotated* proof which
concludes about `func'.output`; here we conclude about the raw `func.output`, so the bridge is the
instantiation inverse, not the appearance-order rename.

### 10h. arrow-not-alias condition + per-component decomposition route (Option 2, DECIDED)

After fixing `ρ`, the output/context conjuncts reduce (output shown):
```
have : AliasEquiv aliases (subst ρ v_inst.fst) (mkArrow' func.output func.inputs.values)   -- whole signature
goal : AliasEquiv aliases (subst ρ RO) func.output                                          -- output component
```
Two ways to get the per-component facts:
- **Abstract inversion (REJECTED):** invert `AliasEquiv (arrow ..) (arrow ..)` to componentwise. This
  needs "no alias restructures an arrow", and `a.name ≠ "arrow"` is INSUFFICIENT: an alias *body* can
  be an arrow (`type Endo a := a→a` collapses `arrow X X ↝ Endo X`), so a `trans` derivation can detour
  through it. Would need the stronger "no alias body is arrow-headed" + a hard inversion lemma.
- **Concrete resolveAliases (CHOSEN):** don't invert abstract `AliasEquiv`. Reformulate
  `LTy_instantiateWithCheck_inverse` to return the per-component facts directly. `resolveAliases` is a
  concrete recursive function: at a `tcons name args` it recurses into `args` then calls
  `tconsAliasSimple name args' aliases`, which matches an alias by name+arity. With
  `h_aliases_not_known : ∀ a ∈ aliases, a.name ≠ "arrow"`, the `"arrow"` head never matches ⟹
  `resolveAliases (arrow a b) = arrow (resolveAliases a) (resolveAliases b)` — it provably distributes
  over `mkArrow'`. So I produce `AliasEquiv (subst ρ RO) func.output` and each input fact componentwise
  from `resolveAliases_aliasEquiv`, with NO abstract arrow inversion and NO Endo problem. The
  `a.name ≠ "arrow"` hypothesis (already threaded, with TODO(preservation)) suffices.

**Lemmas (hardest-first):**
1. `LTy_instantiateWithCheck_inverse` (`LExprTypeSpec:5311`, stub) — reformulate to expose per-component
   `AliasEquiv` (or return the inverse `ρ` + a `resolveAliases`-distributes-over-arrow fact, applied at
   the call site). The decl-order inverse comes from `genTyVars` freshness/distinctness.
2. `resolveAliases`-distributes-over-`mkArrow'` given `a.name ≠ "arrow"` for all aliases (concrete,
   structural over the arrow spine).

**EMPIRICAL CHECK (this session) — the slicing is SOUND; the "arrow-bodied alias" fear was WRONG.**
Concern raised: an arrow-*bodied* alias (`type Endo a := a -> a`) used as an INPUT might make the
typechecker's `take n`/`drop n` split of `v_inst.fst.destructArrow` slice at the wrong boundary
(input `Endo Int` resolves to `Int->Int`, seemingly adding spine slots). VERIFIED FALSE by `#eval`
on the resolved signature `(Int->Int) -> Int` of `f(g : Endo Int) : Int`:
  - `destructArrow = [(Int->Int), Int]` — **2 slots, NOT 3**;  `take 1 = [(Int->Int)]` (= input `g`);
    `drop 1 = [Int]` (= output). Correct split.
Reason: `LMonoTy.destructArrow` recurses ONLY into the last argument (the right spine), never into
`t1`. In `LFunc.type = mkArrow ity (irest ++ outs)` every input sits in a `t1` position, so an
arrow-bodied input occupies EXACTLY ONE slot regardless of internal structure. `take n` always
recovers exactly the `n` resolved inputs. Arrow-bodied OUTPUT is also fine: the raw output is
destructured BEFORE resolution (atomic), so the n-boundary is unchanged and the reconstructed output
is alias-equiv to the raw output via `collapse`. ⟹ Per-component decomposition is valid; the
`a.name ≠ "arrow"` hypothesis is needed ONLY for the `resolveAliases`-distributes-over-arrow-spine
step (lemma 2), not for the slicing. (Lesson: `destructArrow` structural traces are unreliable by
hand — `#eval` these claims, do not narrate them.)

### 10i. General stub + shared adapter (DECIDED + partly DONE this session)

**Structure (user-chosen): general stub in LExprTypeSpec + one shared adapter in FunctionTypeSpecProps**,
because there are TWO call sites (`typeCheck_bodyTyped_instantiated`, `typeCheck_measureTyped_instantiated`)
needing the same per-component facts. Keeps the stub reusable and writes the `Function`-shape reassembly
ONCE.

**General stub — REFORMULATED to equality form (DONE, statement only).** `LTy_instantiateWithCheck_inverse`
(LExprTypeSpec:5311) now returns:
```lean
∃ (ρ : Subst) (Env_r : TEnv T.IDMeta), SubstWF ρ ∧
  LMonoTy.resolveAliases (LTy.toMonoTypeUnsafe ty) Env = .ok (LMonoTy.subst ρ mty, Env_r)
```
i.e. resolving aliases on the raw scheme body recovers EXACTLY `subst ρ mty` (ρ = decl-order inverse of
the fresh instantiation, commuted through `resolveAliases`). **Why equality, not the earlier `AliasEquiv`
or whole-`destructArrow` `AliasEquivList`:** `#eval` (§10h) showed the OUTPUT region EXPANDS under
resolution (`f(x:Int):Endo Int`: raw `destructArrow` len 2, resolved len 3), so an `AliasEquivList` over
the full `destructArrow` of raw-vs-resolved is ILL-TYPED (length mismatch). The equality form sidesteps
this: it's a single structural fact, decomposed per-component at the adapter via `mkArrow'`-injectivity —
NO abstract `AliasEquiv` arrow inversion (avoids the Endo problem entirely).

**Shared adapter `Function.typeCheck_inverse_components` (FunctionTypeSpecProps, DONE statement only).**
Consumes the stub's equality + `h_type : LFunc.type func = .ok type` + `h_aliases_not_known`, returns:
- output: `AliasEquiv aliases (subst ρ RO) func.output` (RO = `mkArrow'` of the `drop n` slice);
- inputs: `AliasEquivList aliases (subst ρ <$> take n da) func.inputs.values`.
Proof plan (sorried): rewrite `SIG = mkArrow ity (irest ++ destructArrow output)`; peel the `n` leading
arrows (`resolveAliases` distributes over the spine — step-5 lemma, needs `a.name ≠ "arrow"`); apply
`resolveAliases_aliasEquiv` to each raw component. Both `_instantiated` lemmas call this; measure ignores
the output fact.

**Wiring status (DONE, build green with sorries):** call site `obtain`s `⟨ρ, Env_r, h_wf_ρ, h_ra⟩` from
the stub, then `⟨h_ae_out, h_ae_ins⟩` from the adapter. Conjunct-3 (output) closes via `rw [h_out_eq]` +
`h_ae_out`. Conjunct-2 (`TContextAliasEquiv`) still needs its plumbing helper — Region A from `h_ae_ins`
(plumbing) and Region B from the rigidity invariant (§10j), NOT ambient-refl (corrected; see §5 step 1a).

### 10j. Rigid-typevar soundness bug + fix (DISCOVERED + FIXED this session)

**Bug (GitHub #1395).** `Function.typeCheck` accepted a nested funcDecl that refines an ambient
procedure type variable, e.g. `procedure proc<t>(y : t) { function f() : int { y } }` — `f`'s body
`y : t` was unified against declared output `int`, silently solving `t := int`. Procedure type-params
ARE rigid (`ProcedureType.lean:137` sets `C.rigidTypeVars`), and the var-initializer path enforces this
via `CmdType.checkAnnotCompat` (`CmdType.lean:95-108`) — but `Function.typeCheck` ran its own unification
(`FunctionType.lean:82`) and never ran that check. Its only post-unify guard, `alphaEquivMap monoty
inferredTy`, compares the function's OWN signature against itself, so refining an ambient `t` (absent
from `monoty`) was invisible.

**Fix.** After `Function.typeCheck` updates `Env` with the unify subst `S`, reject if `S` refines any
`v ∈ C.rigidTypeVars` (the funcDecl analog of `checkAnnotCompat`). Top-level functions unaffected
(`C.rigidTypeVars = []`). Test: `StrataTest/Languages/Core/Examples/NestedFuncDeclTyvarBug.lean` (green:
nested-refines-rigid → rejected; var-init → rejected; monomorphic nested fn → accepted).

**Spec impact: NONE.** `FuncHasType` unchanged. The fix only rejects programs the spec already deems
ill-typed (those were exactly the soundness counterexamples), so `typeCheck_sound` gets STRICTLY easier.

**Proof impact:** (1) 5 proof sites that peel `Function.typeCheck` needed mechanical repair — two
`elim_err h` to peel the new rigid-check `match` + its `pure ()` (DONE; build green). (2) The new rigid
check is the missing justification for Region B of conjunct-2 (§5 step 1a): ambient tyvars provably
unrefined ⟹ `subst` identity on ambient entries. This REPLACES the discredited "ambient-refl" claim.
The `h_ambient_rigid` hypothesis (freeVars of ambient bindings ⊆ rigidTypeVars) is NOW THREADED through
all 5 lemmas (build green); it is justified/preserved by the outer checks (see §5 step 1a Region B),
TODO to discharge as a call-site invariant like `h_aliases_not_known`.

### 10k. Generalization-over-ambient-tyvar soundness bug + fix (GitHub #1399, FIXED this session)

**Bug (GitHub #1399 — the DUAL of #1395).** Where #1395 *refines* an ambient rigid var, #1399
*generalizes over* an ambient (non-rigid) var. `Function.typeCheck` generalizes over EVERY free tyvar
of the solved signature (`typeArgs := monoty.freeVars.eraseDups`, `FunctionType.lean:48`), omitting the
standard HM side condition `gen(Γ,τ) = ∀ᾱ. τ` with `ᾱ = ftv(τ) \ ftv(Γ)`. So a nested
`function f<a>() : a { y }` over ambient `y : t` is recorded as `∀a. a` even though its body is the
single fixed value `y : t` — callable at any type.

**Why this was THE blocker for Region B (not just a wrong proof route).** Verified empirically by calling
`Function.typeCheck` directly (DDM blocks the surface syntax at elaboration; the `var x:∀a.a` route is
closed by the poly-var-init removal, so the witness must be built abstractly): unify produces
`{$__ty_a ↦ t}`, and `alphaEquivMap $__ty_a t` SUCCEEDS as an ordinary var↦var α-renaming, giving
`bwdMap = [("t", "$__ty_a")]`. So **`renameSubst`'s KEY is the ambient var `t`** — directly falsifying the
B1b assumption "renameSubst keys are gen-fresh, disjoint from ambient vars." This held even with `t`
RIGID, confirming the §1395 rigid check is orthogonal (it catches refinement of `t`, not `f`'s param
being unified ONTO `t`). ⟹ `typeCheck_bodyTyped_instantiated` was FALSE as stated until #1399 is fixed.

**Fix (`FunctionType.lean`, separate guard block after the §10j rigid check).** After unifying the body
against the return type (subst `Sb = Env.stateSubstInfo.subst`), reject if any free var of the solved
signature coincides with a free var of the solved ambient context:
```
ambientFreeVars := TContext.types.knownTypeVars (TContext.types.subst ambientTypes Sb)
genVars := (LMonoTy.subst Sb monoty).freeVars
match genVars.find? (· ∈ ambientFreeVars) with | some v => .error … | none => pure ()
```
`ambientTypes := Env.context.types` captured at entry (`instantiateWithCheck` preserves `.context`).
Comparing UNDER `Sb` is orientation-independent (catches both directions by comparing representatives).
Top-level unaffected (`ambientTypes = []`). NOT caught by `alphaEquivMap` (both `monoty` and `subst S
monoty` are bare vars when a param unifies with an ambient var).

**This is "Tier 1" of `LOCAL_FUNCTION_TYPEVAR_LEVELS.md`** — the local explicit `\ ftv(Γ)`. "Tier 2"
(OCaml-style levels) is the same side condition computed incrementally in O(1), a larger unifier-wide
change deferred unless nested functions become permanent. Levels and rigidity are orthogonal; both are
needed regardless of tier.

**Tests (`FunctionTypeTests.lean`, established `#eval do … #guard_msgs` method — NO IO, NO probe file).**
`generalizeAmbientFunc` (`f<a>():a{y}` over ambient rigid `y:t`) → REJECTED with the #1399 message;
`genuinePolyInAmbientFunc` (`id<a>(x:a):a{x}` in same ambient) → ACCEPTED. #1395 tests still green.

**Proof impact.** (1) The 5 peel sites each get ONE more `elim_err h` for the new guard's `match` (DONE;
build green). (2) **This is what makes Region B B1b/B1c PROVABLE** (and DISCREDITS the
`h_ambient_rigid`/`h_ambient_mono` hypotheses as the justification): extract the guard's `none` result
from `h` (like `h_rigid_fixed` extracts the rigid check) to get `∀ v ∈ (subst Sb monoty).freeVars,
v ∉ ftv(subst Sb ambientTypes)`. Since `renameSubst`/`ρ` keys live inside `(subst Sb monoty).freeVars`'s
gen-fresh world and ambient `mty0`'s free vars are in `ftv(subst Sb ambientTypes)`, they are DISJOINT ⟹
`LMonoTy.subst_no_relevant_keys` closes B1b/B1c. NEXT STEP (§5 step 1a Region B): replace the
`h_ambient_rigid`/`h_ambient_mono` assumption-route with this extracted-from-`h` fact.

### 10l. Measure-refines-signature soundness bug + fix + fresh-context redesign (DISCOVERED + FIXED this session)

**Bug (third in the family, after #1395/#1399).** `Function.typeCheck` accepted a polymorphic recursive
function whose *measure* refines a signature type parameter, e.g. `f<a>(x:a):a { x } decreases (x+0)`.
The body `x` stays polymorphic (passes the §10j/§10k gates), but the measure `Int.Add x 0` unifies the
formal's fresh instantiation var `t0 := int`. The original code resolved the measure in the **post-body,
post-unify env** (`FunctionType.lean:136`, output env DISCARDED) and only checked `measurety == .int` —
none of the body's three anti-refinement gates (alphaEquivMap / rigid / #1399-gen). So `measureTyped`
claimed `HasType (funcContext func) (x+0) int` with `x : ∀[].a` — FALSE for an accepted function.
Verified empirically by calling `Function.typeCheck` directly (Factory-equipped `C`): ACCEPTED before fix.

**Fix — fresh-context redesign (NOT a post-hoc scan).** First attempt was a post-hoc scan of the
discarded measure env's subst for refinement of `genVars ++ rigidTypeVars`; this worked but forced an
awkward soundness crux (★): `internal.subst Sm = internal.subst v_unify.subst`, reconciling the measure's
leaked subst `Sm` against the body's `v_unify.subst`. (★) is *false in general* (it is exactly the bug)
and only holds under the scan — i.e. the proof had to argue backwards that the leak didn't matter.
**Redesign (the morally-correct one):** type-check the measure INDEPENDENTLY of the body, against the
SAME initial context the body starts from. Concretely (`FunctionType.lean`):
- Save `measureBaseEnv := Env` right after the formals are pushed (`addInNewestContext
  (LFunc.inputMonoSignature func)`), before the body's `resolve`/`unify` touch it.
- In the measure branch, set `measureRigid := func.typeArgs ++ C.rigidTypeVars` (signature type params,
  now fresh instantiation vars, are rigid here just as in the body), `Cm := {C with rigidTypeVars :=
  measureRigid}`, then `resolve Cm measureBaseEnv measure`; check `measurety == .int`; reject if `Sm`
  (the measure env's subst) refines any `v ∈ measureRigid` — same post-hoc rigid check the body and
  `CmdType.checkAnnotCompat` use (rigidity is ALWAYS enforced post-hoc in this codebase; `unify` never
  consults `rigidTypeVars`).

The accept/reject set is identical to the scan, but the rejection is now a clean rigid-var check against
the measure's OWN resolution, and the measure resolves in `Γ_base := measureBaseEnv.context = FORMALS ::
ambient` — independent of `v_unify.subst`. **The (★) crux disappears entirely.**

**Spec impact: NONE.** `FuncHasType` unchanged; the fix only rejects programs the spec already deems
ill-typed. **Tests (`FunctionTypeTests.lean`):** `measureRefinesSigFunc` (`f<a>(x:a):a{x}
decreases(x+0)`) → REJECTED; `measureLegitFunc` (`g(n:int):int{n} decreases(n+0)`) → ACCEPTED. All
recursion suites (Int/Recursive/Termination/Mutual) still green.

**Proof plan for `typeCheck_measureTyped_instantiated` (this is the active deliverable).**
Layer 0 = `Function.typeCheck_measureTyped_instantiated`; layer 1 = its `sorry`'d helpers below.
- **(L1a) NEW helper `HasType_rigidTypeVars_irrel`** (in LExprTypeSpec, where `HasType` is defined):
  `HasType {C with rigidTypeVars := rv} Γ e t → HasType C Γ e t`. Induction on `HasType`; every
  constructor reads only `functions`/`knownTypes`/`aliases`, never `rigidTypeVars`, so each case
  transfers. NEEDED because `resolve_HasType_core` yields `HasType Cm`, and `Cm` differs from `C` only in
  the rigid field — verified this is NOT definitional (`exact`/`convert using 2` leave a residual goal).
- **(L1b)** context-subst-identity `Γ_base.subst Sm = Γ_base`: from the extracted refine-guard
  (`Sm` fixes every var in `func.typeArgs ++ C.rigidTypeVars`, ⊇ all free vars of the formals/ambient
  context). Local `have`, per-entry agreement via `agree_on_freeVars_implies_subst_eq`.
- **(L1b)** context-subst-identity `Γ_base.subst Sm = Γ_base`: from `h_measure_norefine`
  (`Sm` fixes every var in `v_inst.fst.freeVars.eraseDups ++ C.rigidTypeVars` ⊇ all free vars of the
  FORMALS/ambient context). Per-entry agreement via `agree_on_freeVars_implies_subst_eq`.

- **DESIGN DECISION (user, this session): "same theorem, only the different parts per-expression."**
  Body and measure are PARALLEL: each concludes `HasType C (funcContext Env.context func) <e> (.forAll []
  <target>)`, both resolved from the SAME base context `Γ_base = FORMALS :: ambient` (= `measureBaseEnv`),
  bridged to `funcContext` by the SAME `ρ_inv` (`LTy_instantiateWithCheck_inverse`) via the SAME Region-A
  (formals: `subst ρ_inv instantiated ≈ original`) + Region-B (ambient: `ρ_inv` keys fresh ⟹ identity).
  ⟹ **factor the shared parts into helper lemmas; only the genuinely-different parts are done per-expr.**
  - **DIFFERENT per-expression:** (i) target type (`func.output` for body, `.int` for measure); (ii) the
    body carries `v_unify.subst`+`renameSubst` layers between `Γ_base` and its judgment, the measure
    carries `Sm`-collapsed-to-identity (L1b). (iii) output-alias conjunct exists for body (`subst ρ_inv
    output_inst ≈ func.output`), is trivial for measure (`.int` alias-free, fixed by `ρ_inv`).
  - **SHARED (factor into helper):** the two context-alias conjuncts (`.aliases`-eq + `TContextAliasEquiv
    (funcContext).aliases (Γ_base.subst ρ_inv) (funcContext)`). Today `contextAliasEquiv_facts` bakes in
    the body's `v_unify.subst`/`renameSubst`. **Refactor it** to take the inter-layer substitution as a
    parameter `S_inner` (body: `v_unify.subst` then `renameSubst`; measure: identity), OR split off a
    `Γ_base`-vs-`funcContext` core (`region_a_input_lookup` + Region-B-freshness) that both call. Prefer
    the split: a `contextAliasEquiv_base` lemma stating the two conjuncts for `Γ_base.subst ρ_inv`, reused
    verbatim by body (after it shows its `Γ_inst.subst ρ = Γ_base.subst ρ_inv`) and measure (after L1b).

**STATUS — DONE (this session).** All four steps below are COMPLETE; `Function.typeCheck_measureTyped_instantiated`
is fully proved (no `sorry`), the body/measure share `contextAliasEquiv_base`, and `lake build` is green
(502 jobs). The remaining `sorry`s are deeper-layer leaves only (see §END). Detail of what was done:
1. ✅ **Factored `Function.contextAliasEquiv_base`** (FunctionTypeSpecProps.lean ~1841): the genuinely-shared
   ρ-walk + funcContext-matching, parameterized over the resolution context `Γ0` by a single `find?`-agreement
   hypothesis `h_find_eq` against `FORMALS :: ambient`. Drops ALL inner-subst machinery (`v_unify`/`renameSubst`/
   `bwdMap`/`alphaMap`/gen/rigid/`ambient_rigid`). `contextAliasEquiv_facts` (the body wrapper) now proves its own
   `h_find_eq` (inner `v_unify`+`renameSubst` identity via roundtrip + §10j/#1399 guards) and delegates to base;
   body proof re-pointed and still green. ⚠️ EXCEPTION to top-down ordering taken with user sign-off (the two
   context-alias conjuncts were identical, so factoring before the second consumer avoided duplicating ~200 lines).
2. ✅ **(L1b)** `h_find_eq` for the measure: `Sm` is the identity on every visible binding (Region A via formals'
   freeVars ⊆ `v_inst.fst.freeVars.eraseDups`, Region B via `h_ambient_rigid ⊆ C.rigidTypeVars`), both discharged
   from `h_measure_norefine` + `agree_on_freeVars_implies_subst_eq`. Done inline in the measure lemma.
3. ✅ **HasType arm:** `resolve_HasType_core m … Cm measureBaseEnv` at `S := Sm` (`absorbs_refl`, `polyKeysFresh`
   from monomorphic formals/ambient) → `subst Sm int = int` via `h_core.2.1` idempotence + `h_measure_int`; **(L1a)**
   `HasType.of_rigidTypeVars_irrel` for `Cm → C`; context conjuncts from `contextAliasEquiv_base` at `Γ0 :=
   measureBaseEnv.context.subst Sm`; `ρ`/`h_ρ_keys`/`h_ae_ins` from `LTy_instantiateWithCheck_inverse` +
   `typeCheck_inverse_components`. Witnesses: `Γ_inst := measureBaseEnv.context.subst Sm`, `ρ`.
4. ✅ Measure `WellScoped`-lift (`h_ws_measure_internal`): mirror of the body's `h_ws_internal` (knownVars
   monotonicity over ambient via `List.mem_append`), sourced from the `h_ws_measure` hypothesis.
- ✅ **Annotated route repaired too** (`typeCheck_measureTyped_annotated`, ~1462): its measure peel now resolves
  under the rigidified `Cm` + the internal env (`h_envwf_internal`/`h_resolved_internal`), not the post-body env.

**END — remaining `sorry`s (deeper layers, NOT measure-related):** `HasType_context_aliasEquiv`
(LExprTypeSpec:832), `LTy_instantiateWithCheck_inverse` (:5346), `typeCheck_inverse_components`
(FunctionTypeSpecProps.lean:1811). These are shared by BOTH the body and measure soundness chains.
`HasType_TContext_subst` (:804) is NOT in this list — it is FALSE and being DELETED (ROUTE B, §10c);
Route B adds a small composition-law + WF-companion in LTyUnifyProps instead.

## 9. `typeCheck_noUndeclaredVars` — investigation result (this session)

**Goal:** `∀ v ∈ freeVars (mkArrow' func'.output func'.inputs.values) → v ∈ func'.typeArgs`.

In every `.ok` branch:
- `func'.output = subst userSubst (reconstructedOutput monoty n)`,
- `func'.inputs.values = (func.inputs.keys.zip input_mtys).map (·.2)` each under `subst userSubst`,
- `func'.typeArgs = (monoty.freeVars.eraseDups.zip func.typeArgs).map Prod.snd`,
- `userSubst = [ (monoty.freeVars.eraseDups.zip func.typeArgs).map (fun (fresh,orig) => (fresh, .ftvar orig)) ]`,

where `monoty = (LTy.instantiateWithCheck type C Env).1` and `type = func.type` with
`LTy.freeVars type = []` (the undeclared-vars guard, captured by `h_undecl`).

**Why it's true (coverage chain — all lemmas already exist):**
1. `instantiateWithCheck` = `instantiateEnv` then `resolveAliases` (LExprTypeEnv:1157).
   `instantiate` (LExprTypeEnv:857) builds `S = zip func.typeArgs (map ftvar freshtvs)` with
   `freshtvs.length = func.typeArgs.length` (`genTyVars`), then `subst [S] [sig]`.
2. `LTy.freeVars type = []` ⟹ (via **`LTy.freeVars_nil_imp_mem`**, just proved) the
   signature monotype's freeVars ⊆ `func.typeArgs` = keys of `S`.
3. **`LMonoTys.freeVars_subst_closed`** (LExprTypeSpec:1018): instantiate-output freeVars ⊆ `freshtvs`.
4. **`LMonoTy_resolveAliases_freeVars_subset`** (LExprTypeSpec:3431): resolveAliases does not grow
   freeVars (needs `AliasesWF`, available from `TEnvWF`/`h_resolved`). So `monoty.freeVars ⊆ freshtvs`.
5. `freshtvs` nodup + `monoty.freeVars.eraseDups` nodup ⊆ `freshtvs` ⟹
   **`monoty.freeVars.eraseDups.length ≤ func.typeArgs.length`** (coverage).
6. Coverage ⟹ `userSubst` keys = full `monoty.freeVars.eraseDups` (zip's fst-projection is the
   whole first list when `k ≤ n`), each mapped to `ftvar orig` with
   `orig ∈ func'.typeArgs` (= the zip's snd-projection).
7. For each signature component `X`: `freeVars X ⊆ freeVars monoty` (reconstructed parts are
   `monoty.destructArrow` slices — `LMonoTy.freeVars_reconstructedOutput_subset` LExprTypeSpec:3343,
   `mem_destructArrow_freeVars_subset`), all keys of `userSubst`, so each free var of
   `subst userSubst X` is one of the `orig` names ∈ `func'.typeArgs`.

**Top-level proof (DONE, building):** peel `typeCheck` to `.ok`; establish shared facts before
the branch split — `h_cov` (coverage, from D2), `h_in_ids` (`mem_eraseDups`), and `h_close`
(the closing fact, from D1). Then a `h_finish` that turns `mkArrow' func'.output
func'.inputs.values` into `subst userSubst (mkArrow' RO ins)` via `subst_mkArrow'` +
`ListMap.values_eq_map_snd` + `List.map_map`. All four `.ok` branches discharge with
`rw [ListMap.values_eq_map_snd, List.map_map] at hv; exact h_finish v hv`.
- `h_close` keys on the WHOLE `mkArrow' RO ins`: its free vars split (`freeVars_mkArrow'`) into
  inputs (destructArrow slices → `mem_destructArrow_freeVars_subset`) and RO
  (`freeVars_reconstructedOutput_subset`), all ⊆ `monoty.freeVars` ⊆ `eraseDups` = D1 keys.

**Two remaining stub helpers (in FunctionTypeSpecProps.lean, above `noUndeclaredVars`):**
- **D1** `freeVars_rename_subset (ids tgts W) (h_cov : ids.length ≤ tgts.length)
  (h_closed : ∀ v ∈ freeVars W, v ∈ ids) : ∀ v ∈ freeVars (subst [(ids.zip tgts).map (fun x =>
  (x.1, ftvar x.2))] W), v ∈ (ids.zip tgts).map Prod.snd`. **Plan:** reduce to existing
  `LMonoTy.freeVars_subst_closed` by instantiating its `freshtvs := tgts.take ids.length` (so
  `ids.zip tgts = ids.zip (tgts.take ids.length)` by coverage, and `(ids.zip tgts).map snd =
  tgts.take ids.length`). `freeVars_subst_closed` gives `∈ freshtvs = tgts.take ids.length`,
  which is `(ids.zip tgts).map Prod.snd` (via `zip_map_snd_eq`-style + coverage). Hardest of
  the two — does the actual rename-image reasoning.
- **D2** `instantiateWithCheck_freeVars_eraseDups_length_le (h) (h_aw) :
  monoty.freeVars.eraseDups.length ≤ type.boundVars.length`. **Plan:** `monoty.freeVars ⊆
  freshtvs` (steps 1–4: `instantiateWithCheck_decompose`/`LTy.resolveAliases`-decompose →
  `freeVars_subst_closed` for the instantiate step + `LMonoTy_resolveAliases_freeVars_subset`
  for de-alias), with `freshtvs` nodup (`genTyVars` is gen-fresh ⇒ distinct) and
  `freshtvs.length = boundVars.length`. Then `eraseDups.Nodup` (`eraseDups_Nodup`, DL/Util/
  Nodup.lean:219 — may need import) + `List.subset_nodup_length` (DL/Util/List.lean:445).

**Useful existing list lemmas (DL/Util/List.lean):** `subset_nodup_length` (445),
`zip_map_fst_eq`/`zip_map_snd_eq` (679/684); `eraseDups_Nodup` (DL/Util/Nodup.lean:219).
`List.mem_eraseDups` (core) for membership.

**Build status:** the three earlier proofs + the `noUndeclaredVars` top-level all build clean.
`lake build Strata.Languages.Core.FunctionTypeSpecProps` passes with only D1, D2 stubs and the
separate `typeCheck_sound` still `sorry`.

## 6. API to verify exists before starting (verify, don't assume)

- `Std.HashMap.getElem?_empty` (or `_emptyc`) — `({} : HashMap)[k]? = none`.
- `Std.HashMap.getElem?_insert` — read-back: `(m.insert k v)[k']? = if k'==k then some v else m[k']?`.
- `Std.HashMap.mem_toList_iff_getElem?_eq_some` ✓ (confirmed).
- `Std.HashMap.distinct_keys_toList` ✓ (confirmed).
- `LMonoTy.subst_tcons` ✓ (exists, LTyUnify:233), `LMonoTy.subst_emptyS` ✓ (LTyUnify:226).
- `subst` of a single `ftvar` lemma — find or add.
- `Maps.find?` on `[m]` reduces to `Map.find? m` then `none`-fallthrough — trivial by `rfl`/unfold.
- `LMonoTys.freeVars_mem_subset` ✓ (LTy:354), `LMonoTys.freeVars_exists` ✓ (LTy:365).

## 7. Risk register

- **R1 (highest): H1 invariant shape.** The exact pre/post-condition coupling `bwd` ↔ S may
  need a stronger statement (e.g. also tracking `fwd` inverts σ, or that `bwd` keys = image of
  freeVars seen so far). Mitigation: prove H2/G2 against the stub first to pin the *needed*
  shape, then prove H1 to exactly that shape.
- **R2: `Map.find?`-of-filterMap (G1).** Left-scan find? + filterMap + nodup. Could be fiddly.
  Mitigation: isolate as its own `private` lemma over a generic nodup-keyed list.
- **R3: subst guards (`hasEmptyScopes`).** Keep `subst` abstract (use `subst_tcons`/`_emptyS`/
  ftvar lemma) instead of `simp [subst]` to avoid guard-driven case explosion.
- **R4: `==` vs `=` on TyIdentifier (String).** filterMap uses `k == v`; bwd checks use `==`.
  Need `LawfulBEq String` (present) to convert. Keep `beq_iff_eq` handy.

## 8. Build checkpoints

After each of steps 1–6: `lake build Strata.DL.Lambda.LTy` (for H1/H2/H3) and
`lake build Strata.Languages.Core.FunctionTypeSpecProps` (for G1/G2/target). Use
`lean_goal`/`lean_multi_attempt` between edits.

## 10m. ROUTE B composite — extracted layer-2/3 lemmas + proof plans (this session)

**State (build GREEN, verified).** The false bridge's producer stubs `h_ht_post`/`h_sm_post` are
closed via named helpers; both `_instantiated` proof BODIES are sorry-free (both call sites wired
to the strengthened single-scope E). The genuinely-new Route B content lives in named lemmas, each
with a sorry body + the proof plan below. BFS order recap:
`Layer 0 = Function.typeCheck_sound`; layer 1 = `bodyComposite_pack` (PROVEN) /
`measureComposite_pack` (sorry, mirror) + the pre-existing leaves; layer 2/3 = the extracted
provenance leaves below + D/E/F.

**DONE this session (sorry-free, green):**
- `LTy.subst_compose_forAll_nil`, `TContext.types_subst_go_compose_forAll_nil`,
  `TContext.types_subst_compose_forAll_nil`, `TContext.subst_compose_forAll_nil` — lift the
  monotype composition law `LMonoTy.subst_compose` through `LTy.subst`/`TContext.subst` for a
  monomorphic context (all entries `forAll []`). Membership hypothesis is `∀ ty ∈ Maps.values …`.
- `Function.bodyComposite_pack` — builds `S = compose ρ₀ (compose rs₀ v_unify.subst)` and proves
  all 5 conjuncts (context acts-as via the `TContext.subst_compose_forAll_nil`; type acts-as via
  two `LMonoTy.subst_compose`; absorbs by the two-layer outer-subst argument; SubstWF by two
  `SubstWF.compose`; polyKeysFresh vacuous by `Maps.find?_mem_values` + mono). Takes its
  disjointness + WF + mono facts as hypotheses (supplied at the call site).

**TODO leaves (sorry body + plan):**

1. **`Function.internalContext_values_mono`** (layer 3, LOW difficulty). Goal:
   `∀ ty ∈ Maps.values (Γ_internal).types, ty.boundVars = []` where
   `Γ_internal = v_inst.snd.pushEmptyContext.addInNewestContext FORMALS`.
   - PLAN: `Γ_internal.types = FORMALS :: Env.context.types` (the `h_int_types` reduction already
     used in `h_poly_fresh`, via `LTy_instantiateWithCheck_context'`). Then
     `Maps.values (FORMALS :: amb) = Map.values FORMALS ++ Maps.values amb` (`Maps.values` def).
     `List.mem_append` splits: (a) FORMALS values are `List.map (fun p => forAll [] p.snd) …` so
     every value is `forAll [] _` ⟹ `boundVars = []` by `rfl` after `List.mem_map`;
     (b) ambient values — needs `ty ∈ Maps.values Env.context.types ⟹ boundVars ty = []`. The
     main-theorem hyp `h_ambient_mono` is `find?`-based; under key-shadowing `mem_values` is
     wider than `find?`-reachable. RESOLUTION: ambient `Env.context.types` keys are nodup in a
     well-formed `TEnv` (`h_wf : TEnvWF Env`), so `mem_values ⟹ ∃ x, find? = some ty` holds. Need
     a Maps lemma `Maps.mem_values_nodup_imp_find` (or reuse an existing nodup→find? fact). If no
     such lemma exists, add it in Maps.lean (induction on scopes, using key-nodup). Then apply
     `h_ambient_mono`. ALTERNATIVE if nodup is awkward: strengthen the *helper's* hypothesis to a
     `mem_values`-based ambient-mono (pass it from the call site, where `h_ambient_mono` +
     TEnvWF-nodup discharge it once).

2. **`Function.bodyComposite_disjointness` → `Function.bodyComposite_wf`** (layer 3, the genuine
   crux). Goal: `SubstWF` of `S = compose ρ₀ (compose rs₀ v_unify)`.

   **⚠️ TWO PRIOR PLANS WERE WRONG. Both falsified empirically (2026-06-29) by `#eval`-ing the
   actual defs — NOT inferred from statement shape.**

   * **Draft 1 (d1–d4 via two `SubstWF.compose`):** asserted "rs₀ keys ⊆ keys v_unify" from
     `Constraints.unify` domain provenance. Unsupported: `Constraints.unify_*` (LTyUnifyProps:932/943)
     expose ONLY `absorbs`/`sound`; and from `alphaEquivMap` (LTy.lean:382) **bwdMap keys =
     freeVars(subst v_unify v_inst.fst)**, **values ⊆ freeVars v_inst.fst**.
   * **Draft 2 (direct `SubstWF (compose rs₀ v_unify)`):** **PROVABLY FALSE.** Verified:
     with `v_unify = [[(x, ftvar y)]]`, `rs₀ = [(y, ftvar x)]` (the inverse rename forced by
     inverse-pairing), `compose rs₀ v_unify = [[(x, ftvar x)], [(y, ftvar x)]]`. The `apply rs₀
     v_unify` step scrubs the range var `y` but **creates a self-identity entry `(x, ftvar x)`** —
     so key `x ∈ freeVars`, hence `SubstWF (compose rs₀ v_unify) = false`. The inner composite is
     **not** WF; therefore `SubstWF.compose` (which REQUIRES `SubstWF S` of its inner factor via
     `hS`) is the wrong tool entirely, in BOTH layers.

   **VERIFIED foundation (the correct handle).** `alphaEquivMap_self_subst_bwd_inverts`
   (FunctionTypeSpecProps:684): `bwdMap[y]? = some x → subst v_unify (ftvar x) = ftvar y` — the
   inverse-pairing invariant `substWF_renameMap` (712) already uses. From it: `rs₀` entries are
   `(y, ftvar x)` for kept `bwdMap[y]?=some x`, `y≠x`; so **keys rs₀ = {y}**, **freeVars[rs₀] = {x}**,
   each `y` a v_unify range var.

   **RESOLVED: composite is RIGHT; the WF must be proven on the FULL `S`, not factor-by-factor.**
   The full triple composite IS WF (verified `SubstWF S = true` on the toy) — because `ρ₀` on top
   maps the offending inst var `x` to a fresh user name, **scrubbing `ftvar x` out of the whole
   range**. Crucially this is a property of `S` *as a whole*: verified that if `ρ₀`'s keys do NOT
   cover that inst var, `SubstWF S` flips to `false`. acts-as + absorbs are unaffected (still by two
   `LMonoTy.subst_compose` + `h_out_eq`:2573 for the type; inner-pair cancel for the context;
   v_unify-absorbs + two outer layers for absorbs — all already proven in `bodyComposite_pack`).

   **PLAN — replace `bodyComposite_disjointness` with `bodyComposite_wf` returning `SubstWF S`
   directly, via a NEW general WF lemma that does NOT require the inner factor WF.**

   * **NEW general lemma `SubstWF_compose_of_cover`** (add in LTyUnifyProps next to `SubstWF.compose`):
     ```
     theorem SubstWF_compose_of_cover (s : SubstOne) (S : Subst)
       (hs    : SubstWF [s])
       (hkeys : ∀ k ∈ Maps.keys S, k ∉ Subst.freeVars [s])
       (hcover: ∀ k ∈ Maps.keys S, k ∈ Subst.freeVars S → k ∈ Map.keys s) :
       SubstWF (Subst.compose s S)
     ```
     **Keystone, soundness `#eval`-checked across self-ref / uncovered / multi-entry cases (all
     pass, correctly vacuous on the false ones).** Proof sketch: keys(compose s S) = keys S ++ keys s
     (`Maps.keys_append` + `keys_of_apply_eq`, as in `SubstWF.compose`). For `k ∈ keys S` in
     `freeVars(compose s S)`: by `freeVars_compose_subset` it's in `freeVars[s]` (excluded by
     `hkeys`) or `freeVars S` — but then `hcover` puts `k ∈ keys s`, and a key of `s` that is also a
     key of `S` would, after `apply s`, have been substituted: tighten via a sharper range lemma
     `freeVars(compose s S) ⊆ freeVars[s] ∪ (freeVars S \ keys s)` (the `apply` scrubs s-keys from
     S's range) — prove THIS as the engine, then `SubstWF` is immediate. For `k ∈ keys s`: ∉
     freeVars[s] (`hs`); ∉ `freeVars S \ keys s` trivially. **The real lemma to prove is the sharper
     range bound `freeVars_compose_subset_scrub`; `SubstWF_compose_of_cover` is its corollary.**
   * **`bodyComposite_wf` (the restated H)** supplies, for `s := ρ₀`, `S := compose rs₀ v_unify`:
     - `hs = h_wf_ρ` (`SubstWF [ρ₀]`, from E).
     - `hkeys`: keys(compose rs₀ v_unify) = keys v_unify ++ keys rs₀ (= {x}∪{y} type vars) ∉
       freeVars[ρ₀] (= the FRESH USER names ρ₀ introduces). True because ρ₀'s **range** is fresh
       user names disjoint from all inst/unify type vars. SOURCE: needs a freshness fact on ρ₀'s
       range — CHECK what E exposes (E currently gives `keys ρ₀ isFresh`, i.e. about ρ₀'s KEYS, not
       its range). **May require strengthening E to also expose `freeVars[ρ₀]` fresh, OR derive it.**
     - `hcover`: every self-referential key of `compose rs₀ v_unify` (the `(x, ftvar x)` entries) is
       an inst var `x`, and `keys ρ₀` = the inst vars being renamed to user names ⟹ `x ∈ keys ρ₀`.
       SOURCE: ρ₀ is the fresh→user inverse of the instantiation, so its keys ARE exactly the inst
       vars `freeVars v_inst.fst`; and `compose rs₀ v_unify`'s self-ref range vars ⊆ inst vars (they
       are `x` with `bwdMap[y]?=some x`, `x ∈ freeVars v_inst.fst`). **CHECK against E's `keys ρ₀`
       characterization — this is the load-bearing fact; verify before coding.**
   * **Restate `bodyComposite_pack`**: drop the 4 disjointness hyps `h_rs_keys_unify`,
     `h_unifyKeys_rs`, `h_ρkeys_rsv`, `h_ρ0keys_rsv`; replace with single `h_wf_S : SubstWF S = true`
     (or inline-call `bodyComposite_wf`). The WF bullet becomes `exact h_wf_S`. acts-as/absorbs/poly
     bullets UNCHANGED. Also drop now-unused `h_wf_rs`/`h_wf_unify` if only used for the WF split
     (keep if absorbs/acts-as need them — CHECK; absorbs uses neither, acts-as uses neither).
   * **Call site** (`typeCheck_bodyTyped_instantiated`:2630): replace the `obtain ⟨d1..d4⟩` +
     pass-through with `have h_wf_S := bodyComposite_wf …` then pass `h_wf_S` to pack.
   * **VERIFY** the two SOURCE facts (`hkeys` ρ₀-range-fresh, `hcover` keys ρ₀ = inst vars) against
     E's actual output and `alphaEquivMap` defs BEFORE coding. If E doesn't expose them, the honest
     move is to strengthen E (layer-3 leaf, still ours to shape) — NOT to assume them.

   * **⚠️ A VERIFIED COUNTEREXAMPLE TO `hcover` AS AN ABSTRACT LEMMA (2026-06-29).** For ARBITRARY
     `v_unify`, `SubstWF S` is FALSE. Concretely (`#eval`, sorry-free): `v_inst.fst = $__ty0→$__ty0`,
     hand-set `v_unify : $__ty0 ↦ a` (a user typeArg) ⟹ unified `a→a` ⟹ `bwdMap={a↦$__ty0}` ⟹
     `rs₀={a↦ftvar $__ty0}` (KEY `a` is a user name!) ⟹ `S=[[$__ty0↦a],[a↦a],[$__ty0↦a]]`, the `a↦a`
     entry UN-scrubbable by ρ₀ (keys ρ₀ = gen-vars only) ⟹ **`SubstWF S = false`**. The
     mono-transport route (`R = compose ρ₀ renameSubst`, dropping v_unify) is ALSO non-WF on this
     example (`R=[[a↦a],[$__ty0↦a]]`) — and `HasType_subst_fresh_all` needs `SubstWF` too. So BOTH
     transport routes need the SAME reachability fact below.

   * **✅ THE FIX IS A REACHABILITY FACT — `v_unify`'s range never contains a user typeArg.** The
     counterexample's `v_unify : $__ty0↦a` is UNREACHABLE at the real call site. **Empirically
     verified (RhoProbe.lean, real `Function.typeCheck` unify path, 6 cases incl. higher-order +
     constant-return + abstraction):** every `v_unify` range/key var is `$__ty`-prefixed; `CLASH`
     with `func.typeArgs` is `[]` in ALL cases. **WHY (the proof structure, NOT a test):** the body is
     resolved in `Env2` whose context is `LFunc.inputMonoSignature func2`, where `func2`'s
     inputs/output are the INSTANTIATED `$__ty`-monotypes — the user typeArgs `a,b` are substituted
     AWAY before resolution. So `bodyty` and `func2.output` freeVars ⊆ scope(`Env2.context`) ⊆
     `$__ty`-world, and by `goodSubset` (LTyUnifyProps unify) `v_unify`-range ⊆ those ⟹ no user
     typeArg.
   * **⚠️ THE GAP (precise): gen-FRESHNESS does NOT prove this; it needs SCOPE-CONTAINMENT.** The
     codebase tracks only `SubstFreshForGen`/`resolve_properties` = "`v ≠ $__ty++toString k` for
     future `k`" (NEGATIVE: not a future gen-name). A user typeArg `a` ALSO satisfies that
     (vacuously), so freshness CANNOT separate `a` from `v_unify`'s range. The real obligation is a
     NEW **scope-containment** lemma (does NOT exist; `HasType.regularity` only gives `LExpr.WF`):
     ```
     -- body's resolved type freeVars ⊆ the internal context's known type vars
     bodyType_freeVars_in_scope :
       LExpr.resolve C Env2 body = .ok (bodya, Env3) →
       ∀ v ∈ LMonoTy.freeVars (LMonoTy.subst Env3.stateSubstInfo.subst bodya.toLMonoTy),
         v ∈ TContext.knownTypeVars Env2.context
     ```
     combined with `func.typeArgs ∩ knownTypeVars Env2.context = ∅` (typeArgs were instantiated out;
     `Env2.context` holds only the `$__ty`-monomorphized formals). Together these give
     `v_unify`-range ∩ typeArgs = ∅, discharging `hkeys`/`hcover`. **This scope lemma is the genuine
     remaining proof obligation — prove by induction on `resolve`/`HasType` (every var introduced is
     either from the context or freshly generated, both in scope). STATUS: stated, NOT yet proven;
     empirically true (6/6 probe cases). Do NOT claim H done until this is a green lemma.**

   * **✅ COMPLETE PROOF CHAIN FOUND (2026-06-29) — every link has a PROVEN lemma; no new induction
     needed for the ROOT, only assembly.** The disjointness `v_unify-range ∩ func.typeArgs = ∅`
     decomposes as:
     1. **Closed scheme** (`FuncWF.inputs_typevars_in_typeArgs` + `output_typevars_in_typeArgs`,
        Util/Func.lean:144-148): `freeVars(scheme body) ⊆ func.typeArgs`. ✅ exists.
     2. **Instantiation removes typeArgs** (`LMonoTy.freeVars_subst_closed`, LExprTypeSpec:1052,
        `private`): instantiating a type with `freeVars ⊆ ids` via `[zip ids (map ftvar freshtvs)]`
        yields freeVars ⊆ `freshtvs`. So `freeVars v_inst.fst ⊆ freshtvs` (the generated vars). ✅
        exists (may need de-`private` or a re-export).
     3. **Fresh vars are `$__ty`-prefixed** (`genTyVar_genFresh'`/`TGenEnv.genTyVar` form
        LExprTypeEnv:1627 — `tv = $__ty++toString tyGen`); **typeArgs are non-`$__ty`**
        (`LFuncWF.typeArgs_no_gen_prefix`, FactoryWF.lean:40). ⟹ `freshtvs ∩ func.typeArgs = ∅`,
        hence `freeVars v_inst.fst ∩ func.typeArgs = ∅`. ✅ both exist.
     4. **Body stays in `$__ty`-world**: `bodyty`/`func2.output` freeVars ⊆ (instantiated-formals
        vars ⊆ freshtvs) ∪ (newly generated `$__ty` vars). The output side is (2)+(3). The body side
        uses `resolveAux_properties.context` (context unchanged = instantiated formals) + the
        gen-freshness `preserves.2` for the freshly-generated part. ⟹ ∩ typeArgs = ∅.
     5. **Unify range bounded** (`goodSubset`, used at LExprTypeSpec:1861 inside
        `unify_preserves_SubstFreshForGen`): `freeVars v_unify.subst ⊆ Constraints.freeVars cs ++
        freeVars(resolve-subst)`, both ⊆ `$__ty`-world by (4). ⟹ `v_unify`-range ∩ typeArgs = ∅. ✅.
     **So the NEW work is an ASSEMBLY lemma `vunify_range_disjoint_typeArgs` chaining 1–5 (plus a
     keys-side variant), NOT a from-scratch induction.** The `private` on
     `freeVars_subst_closed` is the main packaging friction. THEN `hkeys`/`hcover` follow:
     - `hkeys` (`keys(compose rs₀ v_unify) = keys v_unify ++ keys rs₀ ∉ freeVars[ρ₀]=typeArgs`):
       keys v_unify ⊆ `$__ty` (same chain, keys-side); keys rs₀ = bwdMap-keys ⊆
       freeVars(subst v_unify v_inst.fst) ⊆ `$__ty` (closure under `$__ty`-subst). Both ∩ typeArgs=∅.
     - `hcover` (self-ref keys of `compose rs₀ v_unify` ∈ keys ρ₀): self-ref keys ∈ freeVars v_inst.fst
       (inverse-pairing), and keys ρ₀ ⊇ freeVars v_inst.fst (E's contract). ✅.
     **STATUS: chain verified to exist link-by-link (each lemma located + line-cited); assembly NOT
     yet written/green. This is the concrete proof plan for `hkeys`/`hcover`.**

   * **✅ IMPLEMENTED (2026-06-29) — top-down, build green, sorries only in named helpers.**
     Structure now in code (FunctionTypeSpecProps unless noted):
     - **`bodyComposite_pack`** — restated to take a single `h_wf_S : SubstWF S`; **sorry-free body**.
       (Dropped the 6 false WF/disjointness hyps + the broken two-level `SubstWF.compose` proof.)
     - **`bodyComposite_wf`** — **body sorry-free.** Proves `SubstWF S` via `SubstWF_compose_of_cover`
       (PROVEN engine, LTyUnifyProps) from `hkeys` + `hcover`:
       · `hkeys` proved: `keys(compose rs₀ v_unify) = keys v_unify ++ keys rs₀`; `keys v_unify`
         via `hVU`; `keys rs₀` are bwd keys ⊆ `freeVars(subst v_unify v_inst.fst)` via
         `renameMap_key_imp_bwd` + `alphaEquivMap_bwd_keys_subset`, then `hUT`; both ∌ `freeVars[ρ₀]`
         (= typeArgs via `hC1`).
       · `hcover` proved: via `hC2` + internal `hSelf`. **`hSelf` PROVEN** (task #23) by
         `freeVars_compose_subset_scrub` (case B impossible by `SubstWF v_unify`) + `renameMap_val_imp_bwd`
         + `alphaEquivMap_bwd_vals_subset` (case A: bwd value ⊆ `freeVars v_inst.fst`).
       Takes `hC1`/`hC2` (ρ₀-contract) + `hVU`/`hUT` (v_unify-provenance) as hypotheses.
     - **NEW sorry-free supporting lemmas:** `SubstWF_compose_of_cover`, `freeVars_compose_subset_scrub`
       (LTyUnifyProps); `Constraints.unify_pred` (LExprTypeSpec); `go_bwd_vals_subset`,
       `goList_bwd_vals_subset`, `alphaEquivMap_bwd_vals_subset`, `renameMap_key_imp_bwd`,
       `renameMap_val_imp_bwd`, `vunify_avoids_typeArgs`, `genTyVars_prefixed` (LExprTypeEnv).
     - **E (`LTy_instantiateWithCheck_inverse`) STRENGTHENED** (LExprTypeSpec): statement now also
       exposes C2 `(∀ v ∈ freeVars mty, v ∈ keys ρ₀)` and C1-raw `(∀ v ∈ freeVars[ρ₀], v ∈ boundVars ty)`.
       Body still `sorry` (deeper leaf E). Both `_instantiated` call sites updated to destructure them.
     - **`LFunc.type_boundVars_eq_typeArgs`** de-`private`d (bridges `boundVars type = func.typeArgs`).
     - **`bodyComposite_wf_hyps`** — bundles the 4 facts for `bodyComposite_wf`. C1 from C1-raw + the
       boundVars bridge (**proved**); C2 = E's cover (**proved**); `hVU` from `vunify_avoids_typeArgs.1`;
       `hUT` from `hA` + `vunify_avoids_typeArgs.2` via `LMonoTy.freeVars_of_subst_subset` (**verified**).
     - **REMAINING open sorries in the H-subtree:** `resolve_freeVars_pred` (LExprResolveProps, the
       resolveAux predicate-closure induction — feeds `vunify_avoids_typeArgs`'s body side); the
       instantiation-side closure leaves `hA`/`h_ctx`/`h_subin` for `vunify_avoids_typeArgs` (= #19 +
       internal-context-avoids-typeArgs); and E's body. NONE are in a main proof body.

   * **✅ THE HARD LEAF (b) — body type stays in `$__ty`-world — IS TRUE, with the MECHANISM now
     verified (2026-06-29, RhoProbe.lean).** Attacked head-on by trying to BREAK it: built the
     predicted counterexample `f<a>(d:a):(a→a)`, body `λz:a. z` (output instantiates to `$__ty`, body
     annotation `a` — hoped `a` survives so outer unify binds `$__ty↦a`). **It did NOT break**:
     `v_unify range=[$__ty1,$__ty1]`, `CLASH=[]`. ROOT CAUSE (verified directly):
     `LMonoTy.instantiateWithCheck (ftvar "a") = ftvar "$__ty0"` — **every body type ANNOTATION is run
     through `instantiateWithCheck` (`typeBoundVar`, LExprT.lean:139; `.fvar`/`.op` cases too), which
     renames ALL its free vars to fresh `$__ty` vars** (annotations are implicitly generalized —
     LExprTypeEnv.lean:824-827). So the THREE and only entry points for type vars during `resolveAux`
     are: (i) the context (instantiated formals = `$__ty`), (ii) `genTyVar` (fresh `$__ty`), (iii)
     annotations via `instantiateWithCheck` (renamed to `$__ty`). **ALL THREE produce only
     `$__ty`-vars — there is NO path for a user typeArg to enter `bodyty`.**
     **⟹ PROOF STRUCTURE for (b):** induction over `resolveAux` (use the existing
     `resolveAux_properties_aux` size-induction skeleton, LExprTypeSpec:3606), new invariant: every
     free var of `et.toLMonoTy` (and of every value in `Env.stateSubstInfo`) is `$__ty`-prefixed,
     given the context's known type vars are all `$__ty`-prefixed. Each case: const (no tyvars), op/
     fvar (instantiateWithCheck output — link 2/3 of the chain above), abs/quant (typeBoundVar via
     instantiateWithCheck + recursion + genTyVar), app/eq/ite (recursion + genTyVar + unify, unify
     range bounded by `goodSubset` over `$__ty` inputs). This is a NEW induction but every case's
     tyvar-source has a proven `$__ty` lemma. **This is the genuine hardest leaf — prove it FIRST.**

   * **✅ ALIAS CONCERN RESOLVED (2026-06-29).** Worry: could `resolveAliases` reintroduce a USER
     typeArg into the body type (breaking the invariant)? **NO.** `TypeAlias.WF.fvs_closed`
     (LExprTypeEnv:54): every free var of an alias body ∈ its `typeArgs`; `TypeAlias.expand`
     (LExprTypeEnv:86) substitutes ALL those `typeArgs` via `openVars`. So `freeVars(expand a args) ⊆
     freeVars(args)` — alias expansion introduces NO new var. `LMonoTy.resolveAliases_fvs_fresh`
     (LExprTypeSpec:1333) already proves this for the `isFresh` invariant.
   * **CHOSEN INVARIANT — `isFresh`/not-in-context, NOT the `$__ty` prefix.** Thread the EXISTING
     invariant "all relevant type vars ∉ `knownTypeVars`(body context)" (already preserved by
     `resolveAliases_fvs_fresh` + freshness machinery), then close disjointness via "`func.typeArgs`
     ∉ `knownTypeVars`(internal body context)" — formals were monomorphized to `$__ty` types, so the
     context's known vars are the instantiated `$__ty` vars, none a user typeArg. REUSES proven
     lemmas instead of new prefix lemmas. `genTyVars_prefixed` (#18, DONE) stays as backup.

   * **✅ VERIFIED ρ₀ CONTRACT (2026-06-29, clean `#eval` in `StrataTest/.../RhoProbe.lean`, NO
     `#eval!` — sorry-free).** Ran `instantiateWithCheck` + `resolveAliases` on concrete schemes:
     | scheme | `v_inst.fst` freeVars | ρ₀ (= fresh→user inverse) keys | ρ₀ range |
     |---|---|---|---|
     | `∀a b. a→b→a` (closed) | `{$__ty0,$__ty1}` all fresh | `{$__ty0,$__ty1}` | `{a,b}` |
     | `∀a b. a→a` (unused b) | `{$__ty0}` | `{$__ty0}` | `{a}` |
     | `∀a. a→c` (**OPEN**, free c) | `{$__ty0, c}` ← user var leaks in | `{$__ty0}` | `{a}` |
     The OPEN case would BREAK `hcover` (the leaked user var `c ∈ freeVars v_inst.fst` is NOT a key
     of ρ₀). **But OPEN schemes are excluded by `FuncWF`** (Util/Func.lean:144-148):
     `inputs_typevars_in_typeArgs` + `output_typevars_in_typeArgs` ⟹ body freeVars ⊆ `func.typeArgs`,
     i.e. the scheme `func.type = .forAll func.typeArgs body` is **CLOSED**. So for a WF function,
     `freeVars v_inst.fst` are ALL fresh `$__ty`-vars. Plus `LFuncWF.typeArgs_no_gen_prefix`
     (FactoryWF.lean:40): `func.typeArgs` never carry the `$__ty` prefix ⟹ ρ₀'s **range** (= typeArgs)
     is disjoint-by-prefix from any `$__ty`-var. **These two WF invariants are the real foundation
     for `hkeys`/`hcover` — NOT a guess about ρ₀'s shape.**
   * **⏳ STILL TO VERIFY before coding H:** the LAST link — that every key/var of
     `compose rs₀ v_unify` is a `$__ty`-var (so `hkeys`'s "composite keys ∉ ρ₀-range={non-$__ty}"
     holds). rs₀ vars are bwdMap vars (⊆ freeVars v_inst.fst = `$__ty` ✓); v_unify vars need a
     "unify introduces only gen-fresh vars" fact. CHECK whether `SubstFreshForGen`/`TEnvWF` gives
     `v_unify` keys/range all `$__ty`-prefixed. If yes, `hkeys`/`hcover` reduce to prefix-disjointness
     + the inverse-pairing key characterization. If no, reconsider.
   * **E's required new conclusion** (to feed H without guessing): expose
     `Map.keys ρ₀ = (freeVars v_inst.fst).dedup` (or ⊇) AND `∀ v ∈ Subst.freeVars [ρ₀], v ∈ func.typeArgs`
     (range = user typeArgs). Both are TRUE per the probe + WF; add to E's (sorried) statement.

3. **`measureComposite_pack`** (layer 2, mirror of body, MEDIUM). Same shape with only two
   factors (`compose ρ₀ Sm`, no renameSubst layer) and ground `.int` (no type conjunct). Reuses
   `TContext.subst_compose_forAll_nil` once, `SubstWF.compose` once, the same absorbs/polyKeysFresh
   arguments. Disjointness: `keys ρ₀ ∩ freeVars Sm` and `keys Sm ∩ freeVars [ρ₀]` — analogous to
   (d3)/(d4) with `Sm` (= `v_measure` resolve subst) in place of `compose rs₀ v_unify`.

4. **E = `LTy_instantiateWithCheck_inverse`** (layer 3, pre-existing). STRENGTHENED this session:
   now returns `ρ` as a single scope `[ρ₀]` (`∃ ρ₀ : SubstOne, … SubstWF [ρ₀] … keys ρ₀ isFresh`).
   Proof still sorry. The single-scope shape is true because the fresh→user inverse is built as
   one scope. PLAN unchanged from prior notes except the witness is now `ρ₀` (the scope) directly.

**Call-site wiring status (BOTH DONE — build green):** body site
(`typeCheck_bodyTyped_instantiated`) obtains `ρ₀` from strengthened E, packages `ρ := [ρ₀]`,
proves the easy hyps (h_absorbs via `Constraints.unify_absorbs`, WF via
`v_unify.isWF`/`substWF_renameMap`/E), delegates disjointness to `bodyComposite_disjointness` (H)
and mono to `internalContext_values_mono` (G). Measure site
(`typeCheck_measureTyped_instantiated`) also rewired to the strengthened E (obtains `ρ₀`, packages
`ρ := [ρ₀]`, derives `h_ρ_keys` over `Maps.keys`); it still calls `measureComposite_pack` (B) with
the OLD signature (`ρ : Subst`, no extra hyps), which `[ρ₀]` satisfies — B's hypotheses will be
added when B is restated to mirror the body composite.

**NEXT (BFS layer 3, hardest-first):** H = `bodyComposite_wf` per §10m pt 2 — BOTH prior routes
(`SubstWF.compose` two-level split; direct `SubstWF (compose rs₀ v_unify)`) are FALSE (the inner
composite is not WF — verified). Prove `SubstWF S` on the FULL composite via new general lemma
`SubstWF_compose_of_cover` (engine: sharper range bound `freeVars_compose_subset_scrub`), then
restate `bodyComposite_pack` to take a single `h_wf_S` and rewire the call site. VERIFY the two
SOURCE facts (ρ₀-range-fresh; keys ρ₀ = inst vars) against E before coding.
Then G (LOW), then B (measure mirror), then the pre-existing leaves C/D/E and finally delete F.
