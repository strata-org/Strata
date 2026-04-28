# Boole Feature Request Inventory

This document tracks the selected Boole feature-request seeds kept under
[`StrataTest/Languages/Boole/FeatureRequests`](../StrataTest/Languages/Boole/FeatureRequests).

## Current priorities

- Prioritize Rust-facing language support over Verus-only proof-visibility features.
- Treat `opaque`, `reveal`, `hide`, `reveal_with_fuel`, `closed`, and `HasType`
  as lower-priority compatibility items unless they unblock a broader Rust path.
- Keep early return, extensional equality, and casts/coercions active because
  they affect the translated program shape more directly.
- For extensional equality, prefer lowering to an explicit quantified formula
  during translation; only add a dedicated Boole form if it makes the pipeline
  cleaner.
- For casts/coercions, prefer a centralized type-directed coercion story over
  ad hoc expression-local patching. Verus also tends to internalize `nat` and
  fixed-width arithmetic through integer encodings, so this likely overlaps with
  the broader `nat`/`int` boundary work.

## Implemented feature requests

1. Extensional equality
   - Extensional equality for direct `Map` types is now partially implemented.
   - Boole surface syntax: `a =~= b`
   - Lowering strategy: keep the Boole syntax for readability, but expand it
     during translation to a quantified formula over map indices:
     `∀ i : k . a[i] == b[i]`
   - Current limitation: this first implementation handles direct `Map k v` types.
     It does not yet normalize named type synonyms such as `type IntMap := Map int int`,
     and it does not yet extend to sequences or higher-order/function extensionality.
   - Problem: this hardcodes a quantified encoding too early in Boole lowering.
     We want to preserve extensional equality as a semantic notion and avoid
     making SMT-level encoding decisions before the Lean level.
2. Nested `for`-loop lowering
   - Direct nested `for ... to` loops now lower cleanly through Boole to Core.
   - Two fixes were needed:
     fresh Core block labels for lowered `for` loops, so nested loops do not
     shadow the enclosing `"for"` label;
     and loop elimination now havocs only loop-carried variables, not
     block-local indices introduced by inner loops.
   - The benchmark in
     [`square_matrix_multiply.lean`](../StrataTest/Languages/Boole/square_matrix_multiply.lean)
     now uses the textbook nested `for` structure directly, so it has been moved
     into the main working Boole examples.

## Semantic preservation requests

1. Generic `opaque` / `reveal`: Lower priority for now. If we revisit this family, preserve reveals for generic spec functions instead of dropping them.
2. `hide`: Lower priority for now. Emit a real hiding boundary so a revealed body does not stay globally visible.
3. `reveal_with_fuel`: Lower priority for now. Preserve the requested fuel amount instead of lowering it to an unrestricted reveal.
4. `closed` visibility: Lower priority for now. Keep closed spec-function bodies hidden across module boundaries.
5. Early return: Support `return expr` as a real statement instead of comment-only lowering. Current Core `exit` only exits blocks, so this needs function-level return semantics in Boole lowering.
6. Overflow guards: Lower priority for now. Preserve `HasType`-style arithmetic overflow checks in the translated program if we decide Verus-specific guards are worth modeling directly.
7. Extensional equality: Distinguish extensional equality from ordinary `==`, especially for maps/collections, preferably by translating it directly to quantifiers. Status: implemented for direct `Map` types via Boole `=~=` syntax lowered to `∀` over indices.
8. Widening casts outside call sites: Insert or preserve cast/coercion structure in comparisons, quantifiers, and other expressions with a centralized type-directed coercion pass.
9. `decreases` metadata: Keep loop/procedure/spec-function decreases information in a form the downstream pipeline can use. Status: loop-level `decreases` is supported in the CST/Core path; the remaining gap is function/procedure/spec-function `decreases`, especially for recursive definitions over builtins such as `int`.

## Type/model requests

10. Native `nat` support: Stop modeling `nat` as a purely abstract type with uninterpreted coercions.
11. Missing model types: Add or standardize support for model types such as `Cell`, `Atomic`, `Thread`, `Rwlock`, `Unit`, and `Arithmetic_overflow`.
12. On-demand stdlib/pervasive stubs: Re-evaluate how much Boole/Strata still needs here. Core has `Sequence` support, so older `Seq_len`/`Seq_get` style stubs are less compelling, but the Boole frontend does not yet lower Boole `Sequence` types end to end. Some pervasive stubs may also no longer be necessary after pruning translation output.
13. Generic/category typing cleanup: Reduce `nat`/`int`/bitvector width mismatches and generic type-shape mismatches in the type-checker.

## Expressiveness requests

14. Higher-order / lambda / closure support: Replace `Unsupported.lambda` placeholders with a real encoding for lambdas/closures.
15. `choose`: Translate Hilbert-epsilon-style `choose` without erasing the predicate.
16. Mutual recursion / forward references: Allow a function body to refer to a mutually recursive sibling before both are fully elaborated.
17. Trait-spec symbol resolution: Preserve trait-spec symbols across module boundaries.

## Robustness requests

18. Datatype constructor/selector verification robustness: Improve solver/type-checker handling for richer datatype VCs that are already emitted faithfully. The small selector/constructor seed passes today; the remaining issue is larger datatype examples whose generated VCs still fail.
19. Complex recursive type shapes: Support more nested recursive datatype shapes during type-checking.
20. Non-Boole SST artifacts: Decide whether `RevealString` / `Air`-style statements need first-class treatment or an explicit erase/lower policy.

## Boole seed examples

These are the curated one-gap Boole seeds.

| Definition | Primary request(s) | Source | Current status |
| --- | --- | --- | --- |
| [`datatypes_and_selectors.lean`](../StrataTest/Languages/Boole/FeatureRequests/datatypes_and_selectors.lean) | Datatype constructor/selector robustness | Verus `guide/datatypes`, `adts`; VLIR `rec_adt_structural` | Basic seed passes; richer cases still active |
| [`abstract_types_and_stubs.lean`](../StrataTest/Languages/Boole/FeatureRequests/abstract_types_and_stubs.lean) | Missing model types, stdlib/pervasive stubs | Verus `guide/quants`, `broadcast_proof`, `guide/higher_order_fns` | Active; Core has `Sequence`, but Boole lowering still lags |
| [`nat_int_boundary.lean`](../StrataTest/Languages/Boole/FeatureRequests/nat_int_boundary.lean) | Native `nat`, coercions | Verus `quantifiers`, `guide/integers`, `power_of_2`; VLIR `rec_adt_structural` | Active |
| [`map_extensionality.lean`](../StrataTest/Languages/Boole/FeatureRequests/map_extensionality.lean) | Extensional equality | Verus `guide/ext_equal` | Implemented for direct `Map` types |
| [`overflow_guard.lean`](../StrataTest/Languages/Boole/FeatureRequests/overflow_guard.lean) | Overflow guards | Verus `guide/overflow`, `overflow` | Lower priority |
| [`opaque_reveal_hide.lean`](../StrataTest/Languages/Boole/FeatureRequests/opaque_reveal_hide.lean) | `opaque`, `reveal`, `hide`, `closed` visibility | Verus `generics`, `test_expand_errors`, `debug_expand`, `modules` | Lower priority |
| [`reveal_with_fuel.lean`](../StrataTest/Languages/Boole/FeatureRequests/reveal_with_fuel.lean) | `reveal_with_fuel` | Verus `test_expand_errors`, `recursion` | Lower priority |
| [`early_return.lean`](../StrataTest/Languages/Boole/FeatureRequests/early_return.lean) | Early return | Verus SST `return` translation gap from `differential_status.md` | Active |
| [`widening_casts.lean`](../StrataTest/Languages/Boole/FeatureRequests/widening_casts.lean) | Widening casts in quantifiers/comparisons | Verus `guide/integers`, `quantifiers`, `statements` | Active |
| [`choose_operator.lean`](../StrataTest/Languages/Boole/FeatureRequests/choose_operator.lean) | `choose` | Verus `trigger_loops` (`choose_example`, `quantifier_example`) | Active |
| [`higher_order_encoding.lean`](../StrataTest/Languages/Boole/FeatureRequests/higher_order_encoding.lean) | Higher-order values via first-order `apply` encoding | Verus `fun_ext`, `trait_for_fn` | Active |
| [`lambda_closure.lean`](../StrataTest/Languages/Boole/FeatureRequests/lambda_closure.lean) | Direct lambda / closure syntax | Local reduced Rust/Verus-style lambda example | Active |
| [`mutual_recursion.lean`](../StrataTest/Languages/Boole/FeatureRequests/mutual_recursion.lean) | Mutual recursion / forward references | Verus `guide/recursion`; VLIR `mutual_recursion`, `recursion` | Active |
| [`decreases_metadata.lean`](../StrataTest/Languages/Boole/FeatureRequests/decreases_metadata.lean) | `decreases` preservation | Verus `proposal-rw2022`, `rw2022_script`, `recursion`; VLIR `LoopSimpleWithSpec` | Loop-level supported; function/procedure-level still active |
| [`horner_poly_eval.lean`](../StrataTest/Languages/Boole/FeatureRequests/horner_poly_eval.lean) | Reusable math/power/summation support for richer functional specs | CLRS Horner’s rule, Exercise 2.3 | Type-checks; full math spec still open |
| [`embedded_postcondition.lean`](../StrataTest/Languages/Boole/FeatureRequests/embedded_postcondition.lean) | Inline `let`-binding blocks in `ensures` clauses | dalek-lite `montgomery.rs` `mul_clamped`, `mul_bits_be` | Implemented: `let v := value in body` is now first-class Boole syntax, lowers by substitution in `toCoreExpr` |
| [`montgomery_loop_invariant.lean`](../StrataTest/Languages/Boole/FeatureRequests/montgomery_loop_invariant.lean) | Relational loop invariants over two co-evolving variables backed by elliptic curve group-law axioms | dalek-lite `montgomery.rs` `mul_bits_be` (Montgomery ladder) | Relational `while`-loop invariants over integer variables work today; remaining gap is cvc5 discharging non-linear group-law axioms for the elliptic curve case |
