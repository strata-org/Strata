# Function Typechecker Soundness — Proof Plan

Deliverables (statements moved to `Strata/Languages/Core/FunctionTypeSpecSound.lean`,
both currently `sorry`, file builds):

- **A. `Function.typeCheck_annotated_sound`** — `∀ Γ, FuncHasTypeA C Γ func'`
- **B. `Function.typeCheck_sound`** — `FuncHasType C Env.context func`

`FuncHasType'` (FunctionTypeSpec.lean:47) is a 5-field structure:
`inputsNodup, typeArgsNodup, noUndeclaredVars, bodyTyped, measureTyped`.

> Layer 0 = {typeCheck_annotated_sound, typeCheck_sound};
> layer 1 = their five `FuncHasType'` fields.

**Priority (user): polymorphic (B) first.** Behavior-preserving implementation
changes to `FunctionType.lean` are permitted if they make proofs easier.

> ⚠️ Treat the existing `FunctionTypeSpecProps.lean` as garbage (only the two
> theorem *statements* were reused). Do not assume any of its `sorry`s reflect a
> real obstruction.

---

## Verified reusable infrastructure (sorry-free, in core libs)

| Lemma | File:line | Gives |
|---|---|---|
| `resolve_HasTypeA` | LExprResolveProps.lean:1205 | `HasTypeA [] et.unresolved et.toLMonoTy` |
| `resolve_AbsWF` | LExprResolveProps.lean:1171 | `AbsWF et` |
| `resolve_HasType_core` | LExprTypeSpec.lean:7612 | poly `HasType` ∀ absorbing `S` |
| `applySubst_typeCheck` | LExprDenoteTySubst.lean:78 | `HasTypeA` under `applySubst S` |
| `applySubstT_toLMonoTy` | LExprTypeSpec.lean:352 | `(applySubstT et S).toLMonoTy = subst S et.toLMonoTy` |
| `applySubstT_AbsWF` | LExprResolveProps.lean:552 | `AbsWF` preserved |
| `applySubstT_unresolved_eq_applySubst` | LExprResolveProps.lean:502 | unresolve∘subst commute (needs AbsWF) |
| `Function.typeCheck_inputs_nodup` | FunctionType.lean:194 | `func.inputs.keys.Nodup` (proven) |
| `TContext_types_subst_find` | LExprTypeEnv.lean:248 | `find?` in substituted ctx |
| `TContext.subst_aliases` | LExprTypeEnv.lean:243 | subst preserves aliases |

`ExprTypingSpec` instances (CmdTypeSpec.lean:37–43):
- `instHasTypeA.exprTyped _C _Γ e mty := HasTypeA [] e mty` — **ignores Γ** ⇒ annotated `bodyTyped`/`measureTyped` are context-independent (`∀ Γ` trivially).
- `instHasType.exprTyped C Γ e (forAll [] mty) := HasType C Γ e (forAll [] mty)` — context-dependent ⇒ poly path must land judgment in `funcContext Env.context func`.

---

## Plan

### Phase 1 — the three "easy" fields (shared by A and B)
- `inputsNodup`: peel `typeCheck`, recover `func.type = ok`, apply `typeCheck_inputs_nodup`; `func'.inputs.keys` is a zip-sublist.
- `typeArgsNodup`: from the nodup guard inside `LFunc.type`; zip-sublist.
- `noUndeclaredVars`: from the `undeclaredVars != []` guard (`LTy.freeVars type = []`) + `mkArrow'`/`destructArrow` freevar lemmas (rebuild `freeVars_subset_destructArrow`).

### Phase 2 — polymorphic body/measure (Deliverable B, hard)
`resolve_HasType_core` yields `HasType` in the substituted *internal* context.
Reaching `funcContext Env.context func` requires the two context-transfer lemmas
below. **Route:** establish those (or leave as justified `sorry` per the
assessment), then assemble. Also: re-examine which of B's extra hypotheses
(`h_aliases_not_known`, `h_ambient_rigid`, `h_ambient_mono`, `h_ws`,
`h_ws_measure`) are actually needed — likely droppable.

### Phase 3 — annotated body/measure (Deliverable A)
Context-independent. Chain: `resolve_HasTypeA` + `resolve_AbsWF`, push the three
substitutions (`S`, `renameSubst`, `userSubst`) via `applySubst_typeCheck` /
`applySubstT_*`, then rewrite the type with unify-soundness + a
**renameSubst-inverts-S** lemma (the deep sub-layer: alphaEquivMap bijective-
renaming inversion, rebuilt from scratch).

---

## Upstream `sorry` lemmas in `LExprTypeSpec.lean` (assessment)

The polymorphic path's natural context-transfer tools are two `sorry`s in the
core library. Per instruction: detailed plan + evidence-based truth assessment;
if convinced TRUE, leave `sorry` and use them.

### (1) `HasType_TContext_subst` (LExprTypeSpec.lean:804)
`HasType C Γ e ty → SubstWF S → HasType C (TContext.subst Γ S) e (LTy.subst S ty)`

**Assessment: TRUE.** Proof by induction on `HasType`.
- **const cases**: `knownTypes` is in `C`, untouched by Γ-subst; `LTy.subst S (forAll [] base) = forAll [] base` (no ftvars). ✓
- **tvar**: `Γ.types.find? x = some ty` ⟹ `TContext_types_subst_find` gives
  `(subst Γ S).types.find? x = some (LTy.subst S ty)`. Close by `tvar`. ✓ (load-bearing lemma already proven)
- **tabs/tquant/tinst/tgen**: need standard commutation lemmas —
  `subst`∘`insert` distribute, `subst`∘`open`/`close`/`openFull` commute,
  `isMonoType`/`toMonoType` stable under subst, and **freshness preservation**
  (`isFresh a Γ → isFresh a (subst Γ S)` given `SubstWF S` / `a` fresh). These
  are the real work; all are standard subst-commutation facts.
- **tvar_annotated/top_annotated/talias**: `AliasEquiv`/`AnnotCompat` are over
  `.aliases`, preserved by `subst_aliases`; the monotype side substitutes uniformly.

**Risk**: medium — the binder/gen/inst commutation + freshness lemmas are
nontrivial but standard. No counterexample found. **Verdict: usable as sorry.**

### (2) `HasType_context_aliasEquiv` (LExprTypeSpec.lean:832)
`HasType C Γ e ty → Γ'.aliases = Γ.aliases → TContextAliasEquiv Γ.aliases Γ Γ'
→ HasType C Γ' e ty`

where `TContextAliasEquiv aliases Γ Γ'` (LExprTypeSpec.lean:819) says: for every
`Γ.types.find? x = some ty`, `ty = forAll [] mty`, `Γ'.types.find? x = some
(forAll [] mty')`, and `AliasEquiv aliases mty' mty`.

**Assessment: TRUE, but with one delicate case (tgen).** Induction on `HasType`.
- **tvar**: equiv gives `ty = forAll [] mty`, `Γ'` has `forAll [] mty'`,
  `AliasEquiv aliases mty' mty`. Derive `HasType C Γ' (.fvar..) (forAll [] mty')`
  by `tvar`, then `talias` (direction `mty' ↝ mty`) to reach `ty`. ✓ — this is
  exactly why the relation stores the `mty' ↝ mty` direction.
- **tabs/tquant**: insert the *same* `x_ty` into both contexts; `TContextAliasEquiv`
  is preserved at the new key via **AliasEquiv reflexivity** (`x_ty` mono), at old
  keys unchanged; aliases unchanged by insert. Need: `AliasEquiv.refl` (verify it
  exists / prove it) and `isMonoType x_ty ⇒ x_ty = forAll [] _`.
- **tgen (delicate)**: uses `TContext.isFresh a Γ`. We need `isFresh a Γ'`. Since
  `Γ'`'s stored types differ from `Γ`'s only up to `AliasEquiv`, and aliases can
  change freevars (e.g. alias `Foo = int` drops a var), `isFresh a Γ` need not
  imply `isFresh a Γ'` in general. **Open sub-question**: confirm whether `isFresh`
  depends on stored-type freevars or only on keys; if only keys, the case is
  trivial (same keys). NEED TO VERIFY `TContext.isFresh` definition before fully
  trusting this lemma.

**Risk**: medium-high pending the `isFresh` definition check. **Verdict: usable
as sorry for now, but flag tgen; verify `isFresh` shape early in Phase 2.**

### Action
- Use both as `sorry` initially to unblock Phase 2 assembly (top-down).
- Then prove them in `LExprTypeSpec.lean` (where `HasType` is transparent).
- If `HasType_context_aliasEquiv`/tgen proves false-as-stated, fall back to the
  *proven* instantiation lemmas (`HasType_tinst_all`:4087, `HasType_subst_fresh_all`:734,
  `HasType_LTy_instantiate`:4199) to build the context transfer directly.

### Other upstream sorries observed (build output)
LExprTypeSpec.lean:5376, LExprResolveProps.lean:771 — not yet on the critical
path; investigate only if reached.
