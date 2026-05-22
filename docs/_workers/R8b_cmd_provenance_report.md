# R8b — Cmd Provenance theorems (Round 8)

## Goal

Add three provenance theorems to a new file
`Strata/Backends/CBMC/GOTO/CmdProvenance.lean`:

1. `decl_provenance_of_translator` — every DECL instruction's code is
   `Code.decl (Expr.symbol (nameMap v_src) gty)` for some source ident `v_src`.
2. `assn_provenance_of_translator` — every ASSIGN instruction's code is
   `Code.assign (Expr.symbol (nameMap v_src) gty) rhs_emitted` for some `v_src`,
   `gty`, `rhs_emitted`.
3. `assn_nondet_provenance_of_translator` — like (2), with the rhs being a
   `Nondet` side-effect.

## Branch verification

Reset to `e2c552ab6` (round-7 supervisor report) — the HEAD of
`htd/unstructured-to-goto` at the start of round 8. Confirmed.

## Status

In progress — see commits.
