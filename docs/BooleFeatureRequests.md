# Boole Feature Request Inventory

Source: `https://raw.githubusercontent.com/ChengZ3/verus-boogie/boogie/tests/differential_status.md`

This is a condensed Boole/Strata backlog derived from the `faithful but
different`, `not faithful translation`, `others`, and `Gaps` sections of the
upstream status file.

## Semantic fidelity requests

1. Generic `opaque` / `reveal`
   Preserve reveals for generic spec functions instead of dropping them.
2. `hide`
   Emit a real hiding boundary so a revealed body does not stay globally visible.
3. `reveal_with_fuel`
   Preserve the requested fuel amount instead of lowering it to an unrestricted reveal.
4. `closed` visibility
   Keep closed spec-function bodies hidden across module boundaries.
5. Early return
   Support `return expr` as a real statement instead of comment-only lowering.
6. Overflow guards
   Preserve `HasType`-style arithmetic overflow checks in the translated program.
7. Extensional equality
   Distinguish extensional equality from ordinary `==`, especially for maps/collections.
8. Widening casts outside call sites
   Insert or preserve cast/coercion structure in comparisons, quantifiers, and other expressions.
9. `decreases` metadata
   Keep loop/procedure/spec-function decreases information in a form the downstream pipeline can use.

## Type/model requests

10. Native `nat` support
    Stop modeling `nat` as a purely abstract type with uninterpreted coercions.
11. Missing model types
    Add or standardize support for model types such as `Cell`, `Atomic`, `Thread`, `Rwlock`, `Unit`, and `Arithmetic_overflow`.
12. On-demand stdlib/pervasive stubs
    Keep generating typed stubs for referenced library symbols, but make the model library more systematic.
13. Generic/category typing cleanup
    Reduce `nat`/`int`/bitvector width mismatches and generic type-shape mismatches in the type-checker.

## Expressiveness requests

14. Higher-order / lambda support
    Replace `Unsupported.lambda` placeholders with a real encoding for lambdas/closures.
15. `choose`
    Translate Hilbert-epsilon-style `choose` without erasing the predicate.
16. Mutual recursion / forward references
    Allow a function body to refer to a mutually recursive sibling before both are fully elaborated.
17. Trait-spec symbol resolution
    Preserve trait-spec symbols across module boundaries.

## Robustness requests

18. Datatype constructor/selector verification robustness
    Improve solver/type-checker handling for datatype VCs that are already emitted faithfully.
19. Complex recursive type shapes
    Support more nested recursive datatype shapes during type-checking.
20. Non-Boole SST artifacts
    Decide whether `RevealString` / `Air`-style statements need first-class treatment or an explicit erase/lower policy.

## Boole seed examples

These are now separate Lean examples under [`StrataTest/Languages/Boole/FeatureRequests`](../StrataTest/Languages/Boole/FeatureRequests).

| Definition | Primary request(s) |
| --- | --- |
| [`datatypes_and_selectors.lean`](../StrataTest/Languages/Boole/FeatureRequests/datatypes_and_selectors.lean) | Datatype constructor/selector robustness |
| [`abstract_types_and_stubs.lean`](../StrataTest/Languages/Boole/FeatureRequests/abstract_types_and_stubs.lean) | Missing model types, stdlib/pervasive stubs |
| [`nat_int_boundary.lean`](../StrataTest/Languages/Boole/FeatureRequests/nat_int_boundary.lean) | Native `nat`, coercions |
| [`map_extensionality.lean`](../StrataTest/Languages/Boole/FeatureRequests/map_extensionality.lean) | Extensional equality |
| [`overflow_guard.lean`](../StrataTest/Languages/Boole/FeatureRequests/overflow_guard.lean) | Overflow guards |
| [`opaque_reveal_hide.lean`](../StrataTest/Languages/Boole/FeatureRequests/opaque_reveal_hide.lean) | `opaque`, `reveal`, `hide`, `closed` visibility |
| [`reveal_with_fuel.lean`](../StrataTest/Languages/Boole/FeatureRequests/reveal_with_fuel.lean) | `reveal_with_fuel` |
| [`early_return.lean`](../StrataTest/Languages/Boole/FeatureRequests/early_return.lean) | Early return |
| [`widening_casts.lean`](../StrataTest/Languages/Boole/FeatureRequests/widening_casts.lean) | Widening casts in quantifiers/comparisons |
| [`choose_operator.lean`](../StrataTest/Languages/Boole/FeatureRequests/choose_operator.lean) | `choose` |
| [`higher_order_encoding.lean`](../StrataTest/Languages/Boole/FeatureRequests/higher_order_encoding.lean) | Higher-order / lambda |
| [`mutual_recursion.lean`](../StrataTest/Languages/Boole/FeatureRequests/mutual_recursion.lean) | Mutual recursion / forward references |
| [`decreases_metadata.lean`](../StrataTest/Languages/Boole/FeatureRequests/decreases_metadata.lean) | `decreases` preservation |

## Notes

- Trait-spec symbol resolution is above the current Boole layer, so it is listed here but does not have a direct Boole-only seed.
- `RevealString` / `Air` are also upstream-of-Boole artifacts; I kept them in the backlog but not as standalone Boole files.
- Several upstream failures collapse onto the same Boole seed. That is intentional: the goal here is to get minimal, reusable repro cases rather than mirror the full upstream test matrix.
