# R10b — Decompose-internalization (`_v7`)

**Tier:** 1 — full closure of both targeted hypotheses on the
user-facing signature.

## Result

A new theorem
`coreCFGToGotoTransform_forward_simulation_concrete_v7` lives in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean`. It has the
*same conclusion* as `_v6` but **drops** the two structural witnesses
that R8a left as parameters:

* `(st_final : Strata.CoreCFGTransLoopState)`
* `(h_blocks_run : cfg.blocks.foldlM ... = .ok st_final)`

Both are derived inside the proof from `h_run` via
`coreCFGToGotoTransform_decompose`
(`Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean:4044`). The
theorem then forwards every other hypothesis untouched into `_v6`.

## Approach

```lean
theorem coreCFGToGotoTransform_forward_simulation_concrete_v7
    ... -- same hypothesis bundle as _v6 except:
    -- (1) no `(st_final : ...)` parameter,
    -- (2) no `(h_blocks_run : ...)` parameter,
    -- (3) `h_labelMap_agree` is universally quantified
    --     over an arbitrary `st_final'` paired with its run-equation.
    (h_labelMap_agree :
      ∀ (st_final' : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final' →
      ∀ (wf : ...),
      ∀ l blk target, (l, blk) ∈ cfg.blocks →
        st_final'.labelMap[l]? = some target →
        wf.labelMap l = some target)
    ...
    : ∃ pc_entry σ_goto', ... := by
  obtain ⟨st_final, _resolved, _trans_post,
          h_blocks_run, _h_patches_run, _h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  exact coreCFGToGotoTransform_forward_simulation_concrete_v6
    ... callResult eval fenv h_eval_bool_corr h_inj
    st_final h_blocks_run (h_labelMap_agree st_final h_blocks_run)
    ...
```

The `h_labelMap_agree` shape is the "massaged" form recommended by the
task brief: it abstracts over `st_final'` and takes the run-equation
as a premise so the caller need not witness the post-blocks-fold
result. Inside `_v7`, after the `obtain`, we instantiate
`h_labelMap_agree` at the *actual* `st_final` and `h_blocks_run` and
pass it to `_v6` exactly where `_v6` expects an `st_final`-specialised
agreement.

R10a's labelMap-agreement work targets exactly this hypothesis. When
R10a lands, the supervisor can drop `h_labelMap_agree` from `_v7` (the
quantified body becomes provable internally from R10a's lemma).

## Verification

* `lake build` (full project): **green** (585/585).
* `lake build StrataTest.Backends.CBMC.GOTO.CoreCFGToGOTOConcreteAxioms`:
  **green**, with
  ```
  'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v7'
    depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
  matching the targeted axiom set.
* No `sorry` introduced.

## Files touched

* `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` — added `_v7`
  immediately after `_v6` (≈230 lines, mostly the parameter bundle
  copy; proof body is six logical lines).
* `StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean` —
  added `#print axioms` for `_v7`.
* `docs/_workers/R10b_decompose_internalization_report.md` — this
  report.

## Boundaries respected

* **R10a's territory (`WfLabelMapAgree.lean`)** — untouched.
  `h_labelMap_agree` is kept as a `_v7` parameter in the
  quantified-shape recommended by the task brief; the supervisor can
  drop it when R10a lands.
* **R10c's territory (`InstructionLookups.lean`,
  `TranslatorBridgeHypsDischarge.lean`)** — untouched.
* No edits under `docs/superpowers/specs/`.
* No `git push`.
