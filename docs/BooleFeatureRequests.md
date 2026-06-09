# Boole Feature Request Inventory

This document tracks the selected Boole feature-request seeds. Fully-implemented
seeds live in [`StrataBooleTest/`](../StrataBoole/StrataBooleTest/);
seeds with at least one open gap remain in
[`StrataBooleTest/FeatureRequests/`](../StrataBoole/StrataBooleTest/FeatureRequests).

## Implemented feature requests

- **Extensional equality** (#684)
  - `a =~= b` lowers to `∀ i : k . a[i] == b[i]`.
  - Remaining gaps: named map synonyms, sequences, higher-order extensionality.
- **Array axiomatization as standalone SMT-IR pass** (#795)
  - Post-encoding pass rewrites Array-theory SMT-IR to `Map` sorts with read-over-write axioms (generated only for type pairs used); fixes type-mismatch bug for datatypes with `Map` fields.
  - Remaining Boole-syntax gaps for `[T; N]`: see Gap #15.
- **Nested `for`-loop lowering** (range-style: `for i in 0..N`)
  - Fresh Core block labels prevent inner loops from shadowing the enclosing `"for"` label; loop elimination havocs only loop-carried variables.
  - Benchmark: [`square_matrix_multiply.lean`](../StrataBoole/StrataBooleTest/square_matrix_multiply.lean).
  - Note: covers `for i in 0..N` range loops only. Iterator-based `for x in iter.iter()` is a separate gap (#23).
- **Bitvector loop variables** (`for i : bvN := init to limit`)
  - `for_to_by` and `for_downto_by` dispatch guard/step/increment to `Bv{N}.ULe/Add/Sub` when the loop variable is a bitvector type instead of `int`.
  - Benchmark: [`sha256_compact_indexed.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/sha256_compact_indexed.lean).
- **Early return** (#871)
  - `exit functionName;` exits the labeled Core block wrapping the procedure body, acting as an early return.
  - Benchmark: [`early_return.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/early_return.lean).
- **Bitwise operators on `bvN` types** (#970)
  - `&`, `|`, `^`, `>>` (UShr), `>>s` (SShr), `<<`, `~` lower to `Bv{N}.And/Or/Xor/UShr/SShr/Shl/Not` Core ops.
  - `bvWidth` helper extracts the bit-width from the Boole type and dispatches to the right-sized op.
  - Benchmark: [`bitvector_ops.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/bitvector_ops.lean) (X25519 scalar clamping with `bv8` `&` and `|`).
- **Bitvector comparisons** (#1075)
  - Unsigned (`<`, `<=`, `>`, `>=`) lower to `Bv{N}.ULt/ULe/UGt/UGe` via `toBvCmpOp` (plain comparisons on bitvector operands default to unsigned).
  - Signed (`<s`, `<=s`, `>s`, `>=s`) lower to `Bv{N}.SLt/SLe/SGt/SGe`.
  - Benchmark: [`bitvector_ops.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/bitvector_ops.lean).
- **Mutual recursion** (#599, #1167)
  - `rec function ... ;` blocks work for structural recursion over datatypes and for `int`-typed functions with `decreases`.
  - Remaining gap: int-recursive functions are opaque UFs — functional properties (e.g. `even(1) == false`) cannot be proved without unfolding axioms. Blocked by Gap #1 (`opaque`/`reveal`).
  - Benchmark: [`mutual_recursion.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/mutual_recursion.lean).
- **`choose` syntax**
  - `w := choose z : T :: pred(z)` desugars to `assert ∃ z : T . pred(z); havoc w; assume pred[z/w]`.
  - The existence assertion guards soundness: without it, an unsatisfiable `pred` silently becomes `assume false`, making every downstream obligation a false positive.
  - Benchmark: [`choose_operator.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/choose_operator.lean).
- **`decreases` annotation on functions, procedures, and `for` loops**
  - Parsing/forwarding implemented (#1075): accepted in function preconds, `spec {}` blocks, procedure headers, and `for v := init to/downto limit` loops; the `for`-loop measure is forwarded to the Core while-loop measure field and actively verified.
  - `decreases` on functions (structural): termination verification implemented (#1092).
  - `decreases <int expr>` on `rec function`: implemented (#1167). Non-negativity and strict-decrease obligations generated at each call site. Int-recursive functions are pure UFs in SMT — functional properties (e.g. `even(1) == false`) cannot be proved without unfolding axioms; blocked by Gap #1.
  - `decreases` on procedures: `decr : Option Measure` parameter on `boole_procedure`, reusing Core's existing `Measure` category; currently parsed and silently dropped.
  - Benchmark: [`decreases_metadata.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/decreases_metadata.lean).
- **`Sequence T` type and slicing ops**
  - All 8 Core inherited ops wired up; wrappers added for `Sequence.skip`, `Sequence.dropFirst`, `Sequence.subrange`.
  - Typed empty-sequence constants: `Sequence.empty_bv8/bv16/bv32/bv64/int`. Each needs a distinct token — 0-ary polymorphic `Sequence.empty` has no arguments to infer the type from.
  - Recursive spec functions over sequences: `decreases Sequence.length(s)` supported (#1167); `reconstruct` seed now active.
  - Benchmark: [`seq_slicing.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/seq_slicing.lean).
- **Inline `let`-block postconditions**
  - `ensures ({ let x = e; ... })` now lowers correctly; enables dalek-lite's `mul_clamped` postcondition style.
  - Benchmark: [`embedded_postcondition.lean`](../StrataBoole/StrataBooleTest/embedded_postcondition.lean).
- **Lambda abstraction and application**
  - `fun x : T => body` lowers to nested Core `.abs` nodes; `(f)(x)` lowers to `.app () f x`.
  - Remaining gap: first-class function values as procedure parameters / local variables still need abstract-type encoding for the SMT path.
  - Benchmark: [`lambda_closure.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/lambda_closure.lean).
- **SMT-LIB 2.7 cast operators** (`e as_int`, `e as_sint`, `e as_bv{n}`) (Gap #6)
  - `e as_int` → `Bv{n}.ToUInt` → SMT-LIB 2.7 `ubv_to_int` (unsigned); widths 1/8/16/32/64/128.
  - `e as_sint` → `Bv{n}.ToInt` → SMT-LIB 2.7 `sbv_to_int` (signed); widths 1/8/16/32/64/128.
  - `e as_bv{n}` → `Int.ToBv{n}` → SMT-LIB 2.7 `(_ int_to_bv n)` (truncating mod 2^n); widths 1/8/16/32/64/128.
  - Benchmarks: [`cast_expr.lean`](../StrataBoole/StrataBooleTest/cast_expr.lean), [`widening_casts.lean`](../StrataBoole/StrataBooleTest/widening_casts.lean), [`cast_all_directions.lean`](../StrataBoole/StrataBooleTest/cast_all_directions.lean), [`cast_nested.lean`](../StrataBoole/StrataBooleTest/cast_nested.lean).

## Semantic preservation requests

1. **Generic `opaque` / `reveal`**: Lower priority. Preserve reveals for generic spec functions instead of dropping them. Also blocks functional reasoning about int-recursive functions: without unfolding axioms, `even` and `odd` are opaque UFs and concrete values like `even(1) == false` cannot be proved. The fix is to auto-emit defining equations as SMT assertions (bounded by a trigger) when `decreases` is present — the same mechanism as Dafny's `reveal` and Verus's `reveal_with_fuel`. See [`mutual_recursion.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/mutual_recursion.lean) for a concrete example.
2. **`hide`**: Lower priority. Emit a real hiding boundary so a revealed body does not stay globally visible.
3. **`reveal_with_fuel`**: Lower priority. Preserve the requested fuel amount instead of lowering it to an unrestricted reveal.
4. **`closed` visibility**: Lower priority. Keep closed spec-function bodies hidden across module boundaries.
5. **Overflow guards**: Lower priority. Preserve `HasType`-style arithmetic overflow checks if Verus-specific guards are worth modeling directly.
6. **SMT-LIB 2.7 cast operators** (`as_int`, `as_sint`, `as_bv{n}`): Implemented.
7. **`decreases` metadata**: Implemented.

## Type/model requests

8. **Native `nat` support**: Approach TBD.
9. **Missing model types**: Add or standardize support for model types such as `Cell`, `Atomic`, `Thread`, `Rwlock`, `Unit`, and `Arithmetic_overflow`.
10. **On-demand stdlib/pervasive stubs**: Some pervasive stubs may be droppable after pruning translation output.
11. **Sequence slicing**: Implemented. Int-based termination for recursive seq functions: implemented (#1167).
12. **Generic/category typing cleanup**: Reduce `nat`/`int`/bitvector width mismatches and generic type-shape mismatches in the type-checker.
13. **Struct/record types with named field access**: `type T := { f1: A, f2: B }` declarations, `.field` accessor expressions, struct literal construction, and quantification over fixed-size field arrays (e.g. `∀ i < 5 . fe.limbs[i] < 2^51`). Used in every dalek spec function.
14. **`Option<T>` in spec functions**: Native `Option<T>` return type so fallible spec functions can be represented faithfully; currently encoded as `is_some` flag plus component functions. Every Vest parser returns `Option<(int, T)>`.
15. **Fixed-size array `[T; N]` syntax** (#795): SMT backend resolved by PR #795. Remaining Boole-syntax gaps:
    - **Repeat initializer `[expr; N]`**: `[0u32; 16]` — lower to a constant-valued Map.
    - **Array literal `[x, y, z, ...]`**: `K32: [u32; 64] = [0x428a2f98, ...]` — compact literal syntax.
    - **Mutable write-back `arr[i] = v`**: `block[i % 16] = new_w` — lower to `Map.put`.
    - Note: `FieldElement51.limbs: [u64; 5]` handled by Gap #13, not this gap.
    - Confirmed in sha256: `[u32; 64]`, `[u32; 16]`, `[u8; 64]`, `[0u32; 16]`, `K32: [u32; 64] = [...]`.
16. **Slice types and slice indexing**: `&[T]` and `&[T; N]` — length, indexing, sub-slicing. Distinct from sequence slicing (#11): slices are runtime-sized Rust borrows. Confirmed in sha256: `blocks: &[[u8; 64]]`, `blocks[k]`, `to_u32s(&blocks[k])`.

## Expressiveness requests

17. **Higher-order / lambda / closure support**: Implemented. Remaining gap: first-class function values as procedure parameters or local variables.
18. **`choose`**: Implemented.
19. **Mutual recursion / forward references**: Implemented for datatypes (#599) and `int` (#1167). Remaining gap: functional reasoning about int-recursive functions blocked by Gap #1 (unfolding axioms).
20. **Trait-spec symbol resolution**: Preserve trait-spec symbols across module boundaries.
21. **Trait / interface with spec and proof methods**: `interface` declarations bundling `spec function` and `lemma` members, with `matches` pattern syntax in `ensures` and `external_body`-style trusted bodies. Confirmed as the backbone of Vest combinators.
22. **Reusable math spec support**: `pow2`, summation, and modular arithmetic helpers for functional specs; avoids re-axiomatising arithmetic in each seed.
23. **Rust iterator protocol lowering** (`for x in iter.iter()`): Leaves symbols undefined — `Iter_Traits_Iterator_Iterator_next`, `Pervasive_ghost_decrease/invariant`, `Std_specs_Slice_spec_slice_iter`, `Option_option..isOption_option_Some`; loop locals `VERUS_iter/exec_iter/ghost_iter`. Distinct from `for i in 0..N` (implemented). Confirmed in sha256: `for block in blocks.iter()`.

## Robustness requests

24. **Datatype constructor/selector verification robustness**: Improve solver/type-checker handling for richer datatype VCs that are already emitted faithfully. The small selector/constructor seed passes; the remaining issue is larger datatype examples whose generated VCs still fail.
25. **Complex recursive type shapes**: Support more nested recursive datatype shapes during type-checking.
26. **Non-Boole SST artifacts**: Decide whether `RevealString` / `Air`-style statements need first-class treatment or an explicit erase/lower policy.

## Bitvector requests

27. **`by (bit_vector)` proof mode**: Route pure bitvector sub-goals to a bitvector decision procedure automatically. Confirmed in Vest LEB128 (`assert(...) by (bit_vector)`).
28. **`bv` rotate_left / rotate_right as primitives**: Currently emitted as `(x >> n) | (x << (w - n))` with `requires 1 <= n < w`; SMT-LIB 2 has native ops. Confirmed in sha256: `rotate_right` with n ∈ {2, 6, 7, 11, 13, 17, 18, 19, 22, 25}.

## Boole seed examples

Seeds with all gaps closed have been moved to `StrataBooleTest/`; the table below tracks all seeds regardless of location.

| Definition | Primary request(s) | Source | Current status |
| --- | --- | --- | --- |
| [`datatypes_and_selectors.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/datatypes_and_selectors.lean) | Datatype constructor/selector robustness (#24) | Verus `guide/datatypes`, `adts`; VLIR `rec_adt_structural` | Basic seed passes; richer cases still active |
| [`abstract_types_and_stubs.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/abstract_types_and_stubs.lean) | Missing model types (#9), stdlib/pervasive stubs (#10) | Verus `guide/quants`, `broadcast_proof`, `guide/higher_order_fns` | Active; `Sequence` lowering now implemented; primary gaps: Thread, Cell, Rwlock model types and pervasive stubs |
| [`nat_int_boundary.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/nat_int_boundary.lean) | Native `nat` (#8), widening coercions (#6) | Verus `quantifiers`, `guide/integers`, `power_of_2`; VLIR `rec_adt_structural` | Active |
| [`map_extensionality.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/map_extensionality.lean) | Extensional equality | Verus `guide/ext_equal` | Implemented (#684, #795); named synonyms and non-map types still open |
| [`overflow_guard.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/overflow_guard.lean) | Overflow guards (#5) | Verus `guide/overflow`, `overflow` | Lower priority |
| [`opaque_reveal_hide.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/opaque_reveal_hide.lean) | `opaque`/`reveal` (#1), `hide` (#2), `closed` (#4) | Verus `generics`, `test_expand_errors`, `debug_expand`, `modules` | Lower priority |
| [`reveal_with_fuel.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/reveal_with_fuel.lean) | `reveal_with_fuel` (#3) | Verus `test_expand_errors`, `recursion` | Lower priority |
| [`early_return.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/early_return.lean) | Early return | Verus SST `return` translation gap from `differential_status.md` | Implemented (#871) |
| [`widening_casts.lean`](../StrataBoole/StrataBooleTest/widening_casts.lean) | SMT-LIB 2.7 cast operators (#6) | Verus `guide/integers`, `quantifiers`, `statements` | Implemented |
| [`cast_expr.lean`](../StrataBoole/StrataBooleTest/cast_expr.lean) | SMT-LIB 2.7 cast operators (#6) | dalek-lite `scalar.rs` B2/B5 | Implemented |
| [`cast_all_directions.lean`](../StrataBoole/StrataBooleTest/cast_all_directions.lean) | SMT-LIB 2.7 cast operators (#6) | All three cast directions | Implemented |
| [`cast_nested.lean`](../StrataBoole/StrataBooleTest/cast_nested.lean) | SMT-LIB 2.7 cast operators (#6), `decreases` preservation (#7) | dalek-lite `bytes_seq_as_nat` / `seq_as_nat_52` (B2) | Implemented |
| [`choose_operator.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/choose_operator.lean) | `choose` (#18) | Verus `trigger_loops` (`choose_example`, `quantifier_example`) | Implemented (#1075) |
| [`higher_order_encoding.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/higher_order_encoding.lean) | Higher-order values (#17) | Verus `fun_ext`, `trait_for_fn` | Active |
| [`lambda_closure.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/lambda_closure.lean) | Lambda / closure (#17) | Local reduced Rust/Verus-style lambda example | Implemented (#1075); remaining gap: first-class function values as procedure parameters/variables |
| [`mutual_recursion.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/mutual_recursion.lean) | Mutual recursion (#19) | Verus `guide/recursion`; VLIR `mutual_recursion`, `recursion` | Implemented for datatypes (#599) and `int` (#1167); functional reasoning blocked by Gap #1 (unfolding axioms) |
| [`decreases_metadata.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/decreases_metadata.lean) | `decreases` preservation (#7) | Verus `proposal-rw2022`, `rw2022_script`, `recursion`; VLIR `LoopSimpleWithSpec` | Implemented (#1092, #1167); procedure `decreases` parsed, silently dropped |
| [`horner_poly_eval.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/horner_poly_eval.lean) | Reusable math spec (#22) | CLRS Horner’s rule, Exercise 2.3 | Type-checks; full math spec still open |
| [`embedded_postcondition.lean`](../StrataBoole/StrataBooleTest/embedded_postcondition.lean) | Inline `let`-binding blocks in `ensures` clauses | dalek-lite `montgomery.rs` `mul_clamped`, `mul_bits_be` | Implemented (#1075) |
| [`montgomery_loop_invariant.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/montgomery_loop_invariant.lean) | Relational loop invariants over two co-evolving variables | dalek-lite `montgomery.rs` `mul_bits_be` (Montgomery ladder) | Linear arithmetic case: implemented (#1075); elliptic curve case: open — requires group-law axioms (Costello-Smith 2017, eq. 4); whether cvc5 closes the invariant with those axioms is untested |
| [`bitvector_ops.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/bitvector_ops.lean) | Bitwise operators on `bvN` types | dalek-lite `scalar_specs.rs` | Implemented (#970) |
| [`bitvector_proof_mode.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/bitvector_proof_mode.lean) | `by (bit_vector)` proof mode (#27) | VeruSAGE-Bench Vest `leb128` | Active |
| [`seq_slicing.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/seq_slicing.lean) | Sequence slicing (#11) | dalek-lite `scalar_specs.rs`, `core_specs.rs`; Vest `leb128`, `repetition` | Implemented (#1075, #1167) |
| [`scalar_reduce.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/scalar_reduce.lean) | `reduce()` spec axiom for B2 (`Scalar::from_bytes_mod_order_wide`) | dalek-lite `scalar.rs` | Implemented (#1075) |
| [`struct_field_access.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/struct_field_access.lean) | Struct/record field access (#13) | dalek-lite `field_specs.rs`, `edwards_specs.rs` | Active |
| [`trait_spec_methods.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/trait_spec_methods.lean) | Trait / interface with spec methods (#21) | VeruSAGE-Bench Vest `SecureSpecCombinator` | Active |
| [`option_matches.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/option_matches.lean) | `Option<T>` in spec functions (#14) | VeruSAGE-Bench Vest `SecureSpecCombinator`, `leb128` | Active |
| [`sha256_compact_indexed.lean`](../StrataBoole/StrataBooleTest/FeatureRequests/sha256_compact_indexed.lean) | Iterator protocol lowering (#23), array syntax (#15), slice types (#16), `bv` rotate primitives (#28) | RustCrypto SHA-256 compact port (indexed `Sequence` encoding) | Active — all 17 VCs pass (#1075); open gaps: iterator protocol (#23), array syntax (#15), slice types (#16) |
