# Boole Benchmark Targets

Source: [dalek-lite](https://github.com/Beneficial-AI-Foundation/dalek-lite) — a Verus-verified Rust implementation of Curve25519/Ed25519.
Each benchmark is a real exec function with `requires`/`ensures`. The goal: run through the Verus → Boole pipeline and discharge postconditions with cvc5.

---

## Overview

The five benchmarks cover all five main source modules of the repo:

| # | Function | Protocol / Layer | Module | Total lines | Exec lines |
|---|----------|-----------------|--------|:-----------:|:----------:|
| 1 | `FieldElement51::mul` | Field arithmetic — GF(2²⁵⁵ − 19) | `field.rs` | 149 | ~50 |
| 2 | `Scalar::from_bytes_mod_order` | Scalar arithmetic — ℤ/ℓℤ | `scalar.rs` | 19 | 3 |
| 3 | `CompressedEdwardsY::decompress` | Ed25519 — point decompression | `edwards.rs` | 76 | ~36 |
| 4 | `RistrettoPoint::compress` | Ristretto / ZK — group encoding | `ristretto.rs` | 309 | ~35 |
| 5 | `MontgomeryPoint::mul_clamped` | X25519 — key exchange | `montgomery.rs` | 45 (+400†) | 3 (+400†) |

† `mul_clamped` delegates to `mul_bits_be` (the Montgomery ladder), which is ~400 lines with a loop invariant.

---

## Benchmark 1 — `FieldElement51::mul`

**149 lines** (field.rs:486–634) · ~50 exec statements

```rust
fn mul(self, _rhs: &'a FieldElement51) -> (output: FieldElement51)
    requires fe51_limbs_bounded(self, 54) && fe51_limbs_bounded(_rhs, 54),
    ensures
        fe51_as_canonical_nat(&output)
            == field_mul(fe51_as_canonical_nat(self), fe51_as_canonical_nat(_rhs)),
        fe51_limbs_bounded(&output, 52),
```

- Every Curve25519 operation — X25519, Ed25519, Ristretto — reduces to repeated calls to `mul`.
- Proving `mul` correct verifies the arithmetic foundation every higher-level proof depends on.
- No recursion, no loops, no sequences: the postcondition is a bounded-integer arithmetic claim cvc5 can discharge directly.

---

## Benchmark 2 — `Scalar::from_bytes_mod_order`

**19 lines** (scalar.rs:273–291) · 3 exec statements

```rust
pub fn from_bytes_mod_order(bytes: [u8; 32]) -> (result: Scalar)
    ensures
        scalar_as_canonical(&result) == u8_32_as_group_canonical(bytes),
        is_canonical_scalar(&result),
{
    let s_unreduced = Scalar { bytes };
    s_unreduced.reduce()
}
```

- Every Ed25519 signature passes scalars through this function. Non-canonical encodings cause **signature malleability**: two valid signatures for the same message.
- `is_canonical_scalar` is a deployed security property — several Bitcoin and TLS libraries were found vulnerable when they did not enforce it (RFC 8032 §5.2.6).
- The body is three lines; the interesting claim is entirely in the postcondition.

---

## Benchmark 3 — `CompressedEdwardsY::decompress`

**76 lines** (edwards.rs:279–354) · ~36 exec statements

```rust
pub fn decompress(&self) -> (result: Option<EdwardsPoint>)
    ensures
        is_valid_edwards_y_coordinate(field_element_from_bytes(&self.0)) <==> result.is_some(),
        result.is_some() ==> (
            edwards_y_nat(result.unwrap()) == field_element_from_bytes(&self.0)
            && edwards_z_nat(result.unwrap()) == 1
            && is_well_formed_edwards_point(result.unwrap())
            && (field_square(field_element_from_bytes(&self.0)) != 1
                    ==> edwards_x_sign_bit(result.unwrap()) == (self.0[31] >> 7))
        ),
```

- Ed25519 signature verification begins by decompressing the public key and signature point from their 32-byte encodings — this is that step.
- The postcondition has four conditions: success iff the y-coordinate is valid on the curve, correct Y, Z=1, and sign bit matching — together they fully characterise what a valid decompression means.
- Used in every SSH connection, TLS 1.3 handshake, and code-signing check that uses Ed25519.

---

## Benchmark 4 — `RistrettoPoint::compress`

**309 lines** (ristretto.rs:1104–1412) · ~35 exec statements

```rust
pub fn compress(&self) -> (result: CompressedRistretto)
    requires is_well_formed_edwards_point(self.0),
    ensures  result.0 == spec_ristretto_compress(*self),
```

where `spec_ristretto_compress` expands to:

```
u1 = (Z+Y)(Z−Y),  u2 = X·Y,  invsqrt = 1/√(u1·u2²)
→ rotation by coset representative selection
→ sign normalisation
→ serialize to 32 bytes
```

- Ristretto255 is the prime-order group used in **Bulletproofs**, **Pedersen commitments**, and **range proof systems**. It eliminates the cofactor-8 problem of raw Curve25519, which would otherwise allow forged ZK proofs. `compress` is called every time a group element is serialised — i.e., in every proof.
- The postcondition is a functional-correctness theorem linking imperative Rust to the [RISTRETTO RFC](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448) mathematical spec.
- Builds directly on Benchmark 1: once `mul` is axiomatized, all remaining field ops follow the same pattern.

---

## Benchmark 5 — `MontgomeryPoint::mul_clamped`

**45 lines** (montgomery.rs:408–452) · 3 exec statements + delegates to `mul_bits_be` (Montgomery ladder, ~400 lines)

```rust
pub fn mul_clamped(self, bytes: [u8; 32]) -> (result: Self)
    requires is_valid_montgomery_point(self),
    ensures ({
        let P = canonical_montgomery_lift(montgomery_point_as_nat(self));
        let clamped_bytes = spec_clamp_integer(bytes);
        let n = u8_32_as_nat(&clamped_bytes);
        let R = montgomery_scalar_mul(P, n);
        montgomery_point_as_nat(result) == u_coordinate(R)
    }),
```

- This is X25519: the key exchange used in TLS 1.3, Signal, WireGuard, and SSH.
- The postcondition directly states protocol correctness: the output u-coordinate equals `[n]P` on the Montgomery curve.
- Verifying this in Boole would be a mechanically checked proof of X25519 correctness end-to-end.

---

## Gap status

Legend: ○ open · ✓ done

Language feature implementations are tracked in
[`BooleFeatureRequests.md`](BooleFeatureRequests.md).
This table tracks benchmark-specific gaps. A full benchmark seed is added to
[`StrataTest/Languages/Boole/Benchmarks/`](../StrataTest/Languages/Boole/Benchmarks/)
only once all gaps for that benchmark are closed. Until then, gap-specific small
seeds live in
[`StrataTest/Languages/Boole/FeatureRequests/`](../StrataTest/Languages/Boole/FeatureRequests/).

**Shared by all five benchmarks:**

| Gap | FR# | Status | Gap seed |
|-----|-----|--------|----------|
| Struct/record field access | #13 | ○ open | [`struct_field_access.lean`](../StrataTest/Languages/Boole/FeatureRequests/struct_field_access.lean) |
| Native `nat` support | #10 | ○ open | [`nat_int_boundary.lean`](../StrataTest/Languages/Boole/FeatureRequests/nat_int_boundary.lean) |
| Recursive spec functions over sequences | #11 | ○ open | [`seq_slicing.lean`](../StrataTest/Languages/Boole/FeatureRequests/seq_slicing.lean) — basic ops (`Sequence.skip`, `Sequence.subrange`, `Sequence.take`, etc.) are implemented; remaining gap is recursive spec functions (`bytes_seq_as_nat`, `seq_as_nat_52`) that underlie `u8_32_as_group_canonical` (B2), `u8_32_as_nat` (B5), and `field_element_from_bytes` (B3, B4); these need int-based termination proofs (blocked on `@[cases]`-free recursion over `int`) |

**Additional gaps per benchmark:**

| # | Gap | FR# | Status | Notes |
|---|-----|-----|--------|-------|
| 1 | `u128` as `int` | — | ○ open | 25 cross-limb products; no new language feature needed once struct access lands — model `u64`/`u128` limbs as `int` |
| 2 | `[u8; 32]` byte arrays | — | ○ open | Model as `Map int bv8`; pattern demonstrated in [`bitvector_ops.lean`](../StrataTest/Languages/Boole/FeatureRequests/bitvector_ops.lean) |
| 2 | `reduce()` spec function | — | ✓ done | Axiom seed [`scalar_reduce.lean`](../StrataTest/Languages/Boole/FeatureRequests/scalar_reduce.lean) verifies with abstract `ByteArray32`/`Scalar` types; `u8_32_as_group_canonical` stays abstract — spelling it out recursively requires int-based termination over sequences (open gap) |
| 3 | `Option<EdwardsPoint>` return | — | ○ open | Encoding pattern demonstrated in [`option_matches.lean`](../StrataTest/Languages/Boole/FeatureRequests/option_matches.lean) and [`datatypes_and_selectors.lean`](../StrataTest/Languages/Boole/FeatureRequests/datatypes_and_selectors.lean) |
| 3 | `field_square` / `sqrt_ratio_i` axioms | — | ○ open | Needed for the full decompress body |
| 4 | Pair return type | — | ○ open | `invsqrt()` returns `(bool, FieldElement51)`; needs tuple/pair type support |
| 4 | Field op axioms | — | ○ open | `add`, `sub`, `square`, `invsqrt`, `conditional_negate`, `as_bytes` — each needs a Boole axiom |
| 5 | Inline `let`-block postcondition | — | ✓ done | Implemented; see [`embedded_postcondition.lean`](../StrataTest/Languages/Boole/FeatureRequests/embedded_postcondition.lean) and BooleFeatureRequests.md |
| 5 | Montgomery ladder invariant | — | ○ open | Non-linear group-law axioms required; [`montgomery_loop_invariant.lean`](../StrataTest/Languages/Boole/FeatureRequests/montgomery_loop_invariant.lean) covers the relational loop pattern |

