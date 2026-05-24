# Worker S2 — `inj_subst` macro for `CmdProvenance` boilerplate

## Summary

Introduced `inj_subst` tactic macro in a new file
`Strata/Backends/CBMC/GOTO/Tactics.lean`, and replaced 11 occurrences of the
`Option.some.inj (h_at.symm.trans h_X_at); subst` boilerplate inside
`Strata/Backends/CBMC/GOTO/CmdProvenance.lean`.

## Macro

```lean
macro "inj_subst" h1:ident h2:ident : tactic =>
  `(tactic| (
    have h_eq := Option.some.inj (Eq.trans (Eq.symm $h1) $h2)
    subst h_eq))
```

Given `h1 : f a = some x` and `h2 : f a = some y`, it derives `x = y` via
`Option.some.inj (h1.symm.trans h2)` and immediately `subst`s. The macro is
~5 LoC of definition (the rest of `Tactics.lean` is copyright/docstring).

## Representative before/after

Before (3 lines per call site, 11 sites):

```lean
| init_nondet v _ty _md i_decl h_decl_at _h_decl_ty gty h_decl_code =>
  have h_eq : instr = i_decl :=
    Option.some.inj (h_at.symm.trans h_decl_at)
  subst h_eq
  exact ⟨v, gty, h_decl_code⟩
```

After (1 line):

```lean
| init_nondet v _ty _md i_decl h_decl_at _h_decl_ty gty h_decl_code =>
  inj_subst h_at h_decl_at
  exact ⟨v, gty, h_decl_code⟩
```

## LoC accounting

* `CmdProvenance.lean`: 372 → 351  (−21 lines)
* `Tactics.lean`: new, 27 lines (most of which is module/copyright/docstring;
  the macro itself is 5 lines)
* Net file LoC: +6, but 11 boilerplate triples replaced by single-line tactic
  calls. The clarity win at each call site (3 → 1 line, plus a named
  intent-revealing tactic) is the primary motivation; the new file's
  copyright/docstring overhead is amortised against future re-use of the
  macro on similar idioms (e.g., other provenance lemmas, future bridge
  files).

## Verification

* `lake build Strata.Backends.CBMC.GOTO.CmdProvenance` — green.
* `lake build StrataTest.Backends.CBMC.GOTO.CoreCFGToGOTOConcreteAxioms` —
  green; axioms for `coreCFGToGotoTransform_forward_simulation_concrete_v4..v7`
  unchanged at `[propext, Classical.choice, Quot.sound]`.
