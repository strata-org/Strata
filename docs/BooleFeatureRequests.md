# Boole Feature Request Inventory

This document tracks the selected Boole feature-request seeds kept under
[`StrataTest/Languages/Boole/FeatureRequests`](../StrataTest/Languages/Boole/FeatureRequests).

## Current priorities

- Prioritize Rust-facing language support over Verus-only proof-visibility features.
- Treat `opaque`, `reveal`, `hide`, `reveal_with_fuel`, `closed`, and `HasType`
  as lower-priority compatibility items unless they unblock a broader Rust path.
- Keep widening casts/coercions active; prefer a centralized type-directed coercion
  pass. This likely overlaps with `nat`/`int` boundary work given how Verus
  internalizes fixed-width arithmetic.

## Implemented feature requests

- **Extensional equality** (#684, #795)
  - Syntax: `a =~= b`; lowers via `toCoreExtensionalEq` to `∀ i : k . a[i] == b[i]`.
  - `axiomatizeArrays` (PR #795) moves array-theory encoding to a post-encoding SMT-IR pass.
  - Regression test covers de Bruijn capture under outer quantifiers.
  - Remaining gaps: named map synonyms, sequences, higher-order extensionality.
- **Nested `for`-loop lowering**
  - Fresh Core block labels prevent inner loops from shadowing the enclosing `"for"` label.
  - Loop elimination havocs only loop-carried variables, not block-local indices.
  - Benchmark: [`square_matrix_multiply.lean`](../StrataTest/Languages/Boole/square_matrix_multiply.lean).
- **Early return** (#871)
  - Every procedure body is wrapped in a Core labeled block named after the procedure.
  - `exit functionName;` exits that block, acting as an early return; no grammar changes needed.
- **Bitwise operators on `bvN` types** (#970)
  - `&`, `|`, `^`, `>>` (UShr), `>>s` (SShr), `<<`, `~` lower to `Bv{N}.And/Or/Xor/UShr/SShr/Shl/Not` Core ops.
  - `bvWidth` helper extracts the bit-width from the Boole type and dispatches to the right-sized op.
  - Benchmark: [`bitvector_ops.lean`](../StrataTest/Languages/Boole/bitvector_ops.lean) (X25519 scalar clamping with `bv8` `&` and `|`).
- **Signed bitvector comparisons** (#1075) (`<s`, `<=s`, `>s`, `>=s`)
  - `a <s b` etc. lower via `toCoreBvBin` to `Bv{N}.SLt/SLe/SGt/SGe`; four `toCoreExpr` cases added to `Verify.lean`.
  - Benchmark: [`bitvector_ops.lean`](../StrataTest/Languages/Boole/bitvector_ops.lean) (`bv_signed_cmp`, 7 postconditions).
- **Mutual recursion over datatypes** (#599)
  - `rec function ... ;` blocks work end-to-end; two `Verify.lean` fixes: `lowerPureFuncDef` propagates `@[cases]` to `FuncAttr.inlineIfConstr`, and `toCoreDecls` injects preceding sibling op-exprs as De Bruijn bvars so cross-sibling calls resolve.
  - Remaining gap: mutual recursion over `int` still needs function-level `decreases` (not yet implemented).
  - Benchmark: [`mutual_recursion.lean`](../StrataTest/Languages/Boole/FeatureRequests/mutual_recursion.lean) (`even`/`odd` over `MyNat`).
- **`choose` syntax**
  - `w := choose z : T :: pred(z)` desugars to `havoc w; assume pred[z/w]` in `toCoreStmt`.
  - Grammar op `choose_assign` added to `Boole/Grammar.lean`; `" :: "` separator avoids dot-access ambiguity.
  - Benchmark: [`choose_operator.lean`](../StrataTest/Languages/Boole/choose_operator.lean).
- **`decreases` annotation on functions and procedures**
  - `decreases e;` is now a `SpecElt` in Core grammar; parses in function `preconds` and `spec {}` blocks. Silently dropped by `toCoreSpecElts`.
  - `boole_procedure` accepts an optional `Measure` (`decreases e`) before the spec block. Dropped by the lowering.
  - Termination is not separately verified in the SMT path; the annotation is preserved for readability and for future well-foundedness checking.
  - Remaining gap: recursive functions over `int` still require `@[cases]` in the Core type-checker; int-based termination proofs are not yet supported.
  - Benchmark: [`decreases_metadata.lean`](../StrataTest/Languages/Boole/FeatureRequests/decreases_metadata.lean).
- **`Sequence T` type and slicing ops**
  - `Sequence T` now translates: `toCoreMonoType` handles `.Sequence _ elem` → `.tcons "Sequence" [elem]`.
  - All 8 Core inherited ops have `toCoreExpr` cases routing to the corresponding `Core.*Op` constants. They are called in Boole via their canonical qualified-keyword syntax: `Sequence.length(s)`, `Sequence.select(s,i)`, `Sequence.take(s,n)`, `Sequence.drop(s,n)`, `Sequence.append(s1,s2)`, `Sequence.build(s,v)`, `Sequence.update(s,i,v)`, `Sequence.contains(s,v)`.
  - Three Boole-specific wrappers added to `Grammar.lean`: `Sequence.skip(s,n)` (lowers to `seq_drop`), `Sequence.dropFirst(s)` (lowers to `seq_drop(s,1)`), `Sequence.subrange(s,lo,hi)` (expands to `Sequence.take(Sequence.drop(s,lo), hi-lo)` in the lowering). The `"Sequence.xxx"` single-string-token pattern is used deliberately: it places the dot inside a string literal, preventing the DDM's `qualifiedIdentExplicit` rule from consuming `id.id` as a qualified identifier before Expr-level trailing rules can apply.
  - Remaining gap: recursive spec functions over sequences need int-based termination proofs (blocked on `@[cases]`-free recursion over `int`).
  - Benchmark: [`seq_slicing.lean`](../StrataTest/Languages/Boole/FeatureRequests/seq_slicing.lean).
- **Inline `let`-block postconditions**
  - `ensures ({ let x = e; ... })` — postconditions whose body is a `let`-binding block — now lower correctly. Each `let` binding is translated to a Core local definition before the postcondition expression is evaluated.
  - Enables encoding of dalek-lite's `mul_clamped` postcondition style directly.
  - Benchmark: [`embedded_postcondition.lean`](../StrataTest/Languages/Boole/embedded_postcondition.lean).
- **Lambda abstraction and application**
  - `fun x : T => body` (Core's `lambda` op) now lowers to a Core `.abs` node: `toCoreExpr` handles `.lambda _ _ decls body` by building nested `.abs` nodes via the same `declListToList` / `withBVarExprs` / `foldr` pattern used for quantifiers.
  - `(f)(x)` (Core's `apply_expr` op) lowers to `.app () f x`.
  - Arrow types `T -> U` were already handled by `toCoreMonoType`.
  - Remaining gap: first-class function values as procedure parameters / local variables still need abstract-type encoding for the SMT path; lambda works in spec expression positions.
  - Benchmark: [`lambda_closure.lean`](../StrataTest/Languages/Boole/FeatureRequests/lambda_closure.lean).

## Semantic preservation requests

1. **Generic `opaque` / `reveal`**: Lower priority. Preserve reveals for generic spec functions instead of dropping them.
2. **`hide`**: Lower priority. Emit a real hiding boundary so a revealed body does not stay globally visible.
3. **`reveal_with_fuel`**: Lower priority. Preserve the requested fuel amount instead of lowering it to an unrestricted reveal.
4. **`closed` visibility**: Lower priority. Keep closed spec-function bodies hidden across module boundaries.
5. **Overflow guards**: Lower priority. Preserve `HasType`-style arithmetic overflow checks if Verus-specific guards are worth modeling directly.
6. **Widening casts outside call sites**: Insert or preserve cast/coercion structure in comparisons, quantifiers, and other expressions with a centralized type-directed coercion pass.
7. **`decreases` metadata**: Implemented for parsing — loop-level, function-level (as `SpecElt`), and procedure-level (as optional `Measure`) `decreases` all parse and are silently dropped by the lowering. Loop measures are used for VC generation; function/procedure measures are not separately verified. Remaining gap: recursive functions over `int` still require `@[cases]`-based structural recursion; int-based termination checking is not yet supported.

## Type/model requests

8. **Native `nat` support**: Stop modeling `nat` as a purely abstract type with uninterpreted coercions.
9. **Missing model types**: Add or standardize support for model types such as `Cell`, `Atomic`, `Thread`, `Rwlock`, `Unit`, and `Arithmetic_overflow`.
10. **On-demand stdlib/pervasive stubs**: Some pervasive stubs may be droppable after pruning translation output.
11. **Sequence slicing**: Implemented — see implemented section above. Remaining gap: recursive spec functions over sequences (e.g. `bytes_seq_as_nat`) need int-based termination proofs.
12. **Generic/category typing cleanup**: Reduce `nat`/`int`/bitvector width mismatches and generic type-shape mismatches in the type-checker.
13. **Struct/record types with named field access**: `type T := { f1: A, f2: B }` declarations, `.field` accessor expressions, struct literal construction, and quantification over fixed-size field arrays (e.g. `∀ i < 5 . fe.limbs[i] < 2^51`). Used in every dalek spec function.
14. **`Option<T>` in spec functions**: Native `Option<T>` return type so fallible spec functions can be represented faithfully; currently encoded as `is_some` flag plus component functions. Every Vest parser returns `Option<(int, T)>`.

## Expressiveness requests

15. **Higher-order / lambda / closure support**: Implemented for spec expression positions — see implemented section above. Remaining gap: first-class function values as procedure parameters or local variables.
16. **`choose`**: Implemented — see implemented section above.
17. **Mutual recursion / forward references**: Implemented for functions over datatypes (structural recursion via `@[cases]`). Remaining gap: mutual recursion over `int` or other non-datatype types requiring an explicit `decreases` clause.
18. **Trait-spec symbol resolution**: Preserve trait-spec symbols across module boundaries.
19. **Trait / interface with spec and proof methods**: `interface` declarations bundling `spec function` and `lemma` members, with `matches` pattern syntax in `ensures` and `external_body`-style trusted bodies. Confirmed as the backbone of Vest combinators.
20. **Reusable math spec support**: `pow2`, summation, and modular arithmetic helpers for functional specs; avoids re-axiomatising arithmetic in each seed.

## Robustness requests

21. **Datatype constructor/selector verification robustness**: Improve solver/type-checker handling for richer datatype VCs that are already emitted faithfully. The small selector/constructor seed passes; the remaining issue is larger datatype examples whose generated VCs still fail.
22. **Complex recursive type shapes**: Support more nested recursive datatype shapes during type-checking.
23. **Non-Boole SST artifacts**: Decide whether `RevealString` / `Air`-style statements need first-class treatment or an explicit erase/lower policy.

## Bitvector requests

24. **`by (bit_vector)` proof mode**: Route pure bitvector sub-goals to a bitvector decision procedure automatically. Confirmed in Vest LEB128 (`assert(...) by (bit_vector)`).

## Boole seed examples

These are the curated one-gap Boole seeds.

| Definition | Primary request(s) | Source | Current status |
| --- | --- | --- | --- |
| [`datatypes_and_selectors.lean`](../StrataTest/Languages/Boole/FeatureRequests/datatypes_and_selectors.lean) | Datatype constructor/selector robustness | Verus `guide/datatypes`, `adts`; VLIR `rec_adt_structural` | Basic seed passes; richer cases still active |
| [`abstract_types_and_stubs.lean`](../StrataTest/Languages/Boole/FeatureRequests/abstract_types_and_stubs.lean) | Missing model types, stdlib/pervasive stubs | Verus `guide/quants`, `broadcast_proof`, `guide/higher_order_fns` | Active; `Sequence` lowering now implemented; primary gaps: Thread, Cell, Rwlock model types and pervasive stubs |
| [`nat_int_boundary.lean`](../StrataTest/Languages/Boole/FeatureRequests/nat_int_boundary.lean) | Native `nat`, coercions | Verus `quantifiers`, `guide/integers`, `power_of_2`; VLIR `rec_adt_structural` | Active |
| [`map_extensionality.lean`](../StrataTest/Languages/Boole/FeatureRequests/map_extensionality.lean) | Extensional equality | Verus `guide/ext_equal` | Implemented (#684, #795); named synonyms and non-map types still open |
| [`overflow_guard.lean`](../StrataTest/Languages/Boole/FeatureRequests/overflow_guard.lean) | Overflow guards | Verus `guide/overflow`, `overflow` | Lower priority |
| [`opaque_reveal_hide.lean`](../StrataTest/Languages/Boole/FeatureRequests/opaque_reveal_hide.lean) | `opaque`, `reveal`, `hide`, `closed` visibility | Verus `generics`, `test_expand_errors`, `debug_expand`, `modules` | Lower priority |
| [`reveal_with_fuel.lean`](../StrataTest/Languages/Boole/FeatureRequests/reveal_with_fuel.lean) | `reveal_with_fuel` | Verus `test_expand_errors`, `recursion` | Lower priority |
| [`early_return.lean`](../StrataTest/Languages/Boole/early_return.lean) | Early return | Verus SST `return` translation gap from `differential_status.md` | Implemented (#871) |
| [`widening_casts.lean`](../StrataTest/Languages/Boole/FeatureRequests/widening_casts.lean) | Widening casts in quantifiers/comparisons | Verus `guide/integers`, `quantifiers`, `statements` | Active |
| [`choose_operator.lean`](../StrataTest/Languages/Boole/choose_operator.lean) | `choose` | Verus `trigger_loops` (`choose_example`, `quantifier_example`) | Implemented (#1075) |
| [`higher_order_encoding.lean`](../StrataTest/Languages/Boole/FeatureRequests/higher_order_encoding.lean) | Higher-order values via first-order `apply` encoding | Verus `fun_ext`, `trait_for_fn` | Active |
| [`lambda_closure.lean`](../StrataTest/Languages/Boole/FeatureRequests/lambda_closure.lean) | Direct lambda / closure syntax | Local reduced Rust/Verus-style lambda example | Implemented (#1075); remaining gap: first-class function values as procedure parameters/variables |
| [`mutual_recursion.lean`](../StrataTest/Languages/Boole/FeatureRequests/mutual_recursion.lean) | Mutual recursion / forward references | Verus `guide/recursion`; VLIR `mutual_recursion`, `recursion` | Implemented for datatypes (#599); mutual recursion over `int` still open |
| [`decreases_metadata.lean`](../StrataTest/Languages/Boole/FeatureRequests/decreases_metadata.lean) | `decreases` preservation | Verus `proposal-rw2022`, `rw2022_script`, `recursion`; VLIR `LoopSimpleWithSpec` | Implemented (#1075); remaining gap: int-based termination for recursive functions |
| [`horner_poly_eval.lean`](../StrataTest/Languages/Boole/FeatureRequests/horner_poly_eval.lean) | Reusable math/power/summation support for richer functional specs | CLRS Horner’s rule, Exercise 2.3 | Type-checks; full math spec still open |
| [`embedded_postcondition.lean`](../StrataTest/Languages/Boole/embedded_postcondition.lean) | Inline `let`-binding blocks in `ensures` clauses | dalek-lite `montgomery.rs` `mul_clamped`, `mul_bits_be` | Implemented (#1075) |
| [`montgomery_loop_invariant.lean`](../StrataTest/Languages/Boole/FeatureRequests/montgomery_loop_invariant.lean) | Relational loop invariants over two co-evolving variables | dalek-lite `montgomery.rs` `mul_bits_be` (Montgomery ladder) | Linear arithmetic case: implemented (#1075); elliptic curve case: open — requires group-law axioms (Costello-Smith 2017, eq. 4); whether cvc5 closes the invariant with those axioms is untested |
| [`bitvector_ops.lean`](../StrataTest/Languages/Boole/bitvector_ops.lean) | Bitwise operators on `bvN` types | dalek-lite `scalar_specs.rs` | Implemented (#970) |
| [`bitvector_proof_mode.lean`](../StrataTest/Languages/Boole/FeatureRequests/bitvector_proof_mode.lean) | `by (bit_vector)` proof mode | VeruSAGE-Bench Vest `leb128` | Active |
| [`seq_slicing.lean`](../StrataTest/Languages/Boole/FeatureRequests/seq_slicing.lean) | Sequence slicing (`subrange`, `skip`, `take`, `drop_first`) and all 8 Core `Sequence.*` ops | dalek-lite `scalar_specs.rs`, `core_specs.rs`; Vest `leb128`, `repetition` | Implemented (#1075); remaining gap: recursive spec functions over sequences need int-based termination proofs |
| [`scalar_reduce.lean`](../StrataTest/Languages/Boole/FeatureRequests/scalar_reduce.lean) | `reduce()` spec axiom for B2 (`Scalar::from_bytes_mod_order`) | dalek-lite `scalar.rs` | Implemented (#1075); `u8_32_as_group_canonical` stays abstract pending int-based termination for recursive seq spec functions |
| [`struct_field_access.lean`](../StrataTest/Languages/Boole/FeatureRequests/struct_field_access.lean) | Struct/record types with named field access | dalek-lite `field_specs.rs`, `edwards_specs.rs` | Active |
| [`trait_spec_methods.lean`](../StrataTest/Languages/Boole/FeatureRequests/trait_spec_methods.lean) | Trait / interface with spec and proof methods; `matches` in `ensures` | VeruSAGE-Bench Vest `SecureSpecCombinator` | Active |
| [`option_matches.lean`](../StrataTest/Languages/Boole/FeatureRequests/option_matches.lean) | `Option<T>` in spec functions; `matches` in `ensures`/`exists` | VeruSAGE-Bench Vest `SecureSpecCombinator`, `leb128` | Active |
