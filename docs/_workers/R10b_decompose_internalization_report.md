# R10b — Decompose-internalization (`_v7`)

**Status:** in progress (stub)

**Approach.** Add a new theorem `coreCFGToGotoTransform_forward_simulation_concrete_v7`
in `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` that has the
same conclusion as `_v6` but drops the two structural witnesses
`st_final` and `h_blocks_run` from its parameter list. The proof body
calls `coreCFGToGotoTransform_decompose` (from
`CoreCFGToGotoTransformWF.lean`) on `h_run` to obtain the
post-blocks-fold state and its run-equation, then forwards every other
hypothesis untouched into `_v6`. Because R10a's labelMap-agreement
work is parallel, `_v7` keeps a `h_labelMap_agree` parameter — but in
the universally-quantified shape: it abstracts over an `st_final'` and
takes its run-equation as a premise so the caller need not witness the
fold result. After `obtain ⟨st_final, …⟩ := …` we instantiate that
universal at the obtained `st_final` and forward to `_v6`. Tier
target: 1 (full closure of both hypotheses on the user-facing
signature).
