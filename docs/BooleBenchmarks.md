# Boole Benchmark Targets

Benchmarks B1–B5 come from [dalek-lite](https://github.com/Beneficial-AI-Foundation/dalek-lite) — a Verus-verified Rust implementation of Curve25519/Ed25519. Each is a real exec function with `requires`/`ensures`; the goal is to run through the Verus → Boole pipeline and discharge postconditions with cvc5.

---

## Why these benchmarks

B1–B5 cover the full stack of three widely deployed cryptographic systems: X25519 key exchange, Ed25519 signatures, and Ristretto255.

- `FieldElement51::mul` — arithmetic foundation; every curve operation reduces to repeated calls to it.
- `from_bytes_mod_order_wide` — reduces a 64-byte hash to a canonical EdDSA signing scalar; absent canonicality caused malleability vulnerabilities in OpenSSL and tinyssh (RFC 8032 §5.1.7); the uniform-output property prevents key leakage via biased nonces.
- `CompressedEdwardsY::decompress` / `RistrettoPoint::compress` — serialization at every Ed25519 verification and Ristretto255 proof.
- `MontgomeryPoint::mul_clamped` — core of X25519, used in TLS 1.3, Signal, WireGuard, and SSH.

## Overview

| # | Function | Protocol / Layer | Source | Total lines | Exec lines |
|---|----------|-----------------|--------|:-----------:|:----------:|
| 1 | `FieldElement51::mul` | Field arithmetic — GF(2²⁵⁵ − 19) | `field.rs` | 149 | ~50 |
| 2 | `Scalar::from_bytes_mod_order_wide` | Scalar arithmetic — ℤ/ℓℤ | `scalar.rs` | 49 | 13 |
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

- Foundation of all Curve25519 arithmetic; every higher-level operation reduces to `mul`.
- Postcondition: bounded-integer claim over 5-limb radix-2⁵¹ representation.

---

## Benchmark 2 — `Scalar::from_bytes_mod_order_wide`

**49 lines** (scalar.rs:300–348) · 2 exec statements

```rust
pub fn from_bytes_mod_order_wide(input: &[u8; 64]) -> (result: Scalar)
    ensures
        scalar_as_canonical(&result) == group_canonical(bytes_seq_as_nat(input@)),
        is_canonical_scalar(&result),
        is_uniform_bytes(input) ==> is_uniform_scalar(&result),
```

- Reduces a 64-byte SHA-512 hash to a canonical EdDSA signing scalar `r`.
- First postcondition: correctness — output equals input reduced mod ℓ (the function computes the right value).
- Second postcondition: canonicality — output is the unique representative in [0, ℓ) with high bit clear; absent this, two distinct byte strings can represent the same scalar, enabling signature malleability (CVE in OpenSSL and tinyssh, RFC 8032 §5.1.7).
- Third postcondition: uniformity — uniform 512-bit input produces a statistically uniform scalar; a biased nonce leaks the private key (cf. ECDSA PS3 attack).

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

- The decompression step in every Ed25519 verification (SSH, TLS 1.3, code signing).
- Four postconditions: success iff y is on the curve, correct Y, Z=1, sign bit match — fully characterising valid decompression.

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

- Ristretto255 eliminates Curve25519's cofactor-8 problem; used in `bulletproofs` (Bulletproofs, Pedersen commitments). Called on every serialised group element.
- Postcondition links the implementation to the [Ristretto RFC (RFC 9496)](https://datatracker.ietf.org/doc/html/rfc9496) spec.
- Builds on B1: once `mul` is axiomatized, remaining field ops follow the same pattern.

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

- Core scalar multiplication of X25519 (TLS 1.3, Signal, WireGuard, SSH).
- Postcondition: output u-coordinate equals `[n]P` on the Montgomery curve.

---

## Gap status

Legend: ○ open · ✓ done · → pr open

Language feature implementations are tracked in
[`BooleFeatureRequests.md`](BooleFeatureRequests.md).
This table tracks benchmark-specific gaps. A full benchmark seed is added to
[`StrataTest/Languages/Boole/Benchmarks/`](../StrataTest/Languages/Boole/Benchmarks/)
only once all gaps for that benchmark are closed. Until then, gap-specific small
seeds live in
[`StrataTest/Languages/Boole/FeatureRequests/`](../StrataTest/Languages/Boole/FeatureRequests/).

**Shared by all five benchmarks:**

| Gap | FR# | Status | Notes |
|-----|-----|--------|-------|
| Struct/record field access | #13 | ○ open | Boole has no record types with named field access; see [`struct_field_access.lean`](../StrataTest/Languages/Boole/FeatureRequests/struct_field_access.lean) |
| Native `nat` support | #10 | ○ open | `nat` must be declared abstract with manual coercion axioms; see [`nat_int_boundary.lean`](../StrataTest/Languages/Boole/FeatureRequests/nat_int_boundary.lean) |
| Recursive spec functions over sequences | #11 | → pr open (#1167) | `decreases <int expr>` implemented in `upstream/main2`; pending merge into `upstream/main`. Int-recursive functions are pure UFs in SMT — manual axioms still needed for `u8_64_as_group_canonical` (B2, B5), `seq_as_nat_52` (B1), `field_element_from_bytes` (B3, B4). `reconstruct` in [`seq_slicing.lean`](../StrataTest/Languages/Boole/FeatureRequests/seq_slicing.lean) commented until then. |

**Additional gaps per benchmark:**

| # | Gap | FR# | Status | Notes |
|---|-----|-----|--------|-------|
| 1 | `u128` intermediate products | — | ○ open | 25 u64×u64 cross-limb products are u128 in Rust; in Boole, model as `int` — no separate feature needed, resolves with Gap #13 |
| 1 | `FieldElement51.limbs: [u64; 5]` | #13 | ○ open | Sub-case of Gap #13: `limbs` is a struct field whose type is itself a fixed-size array. Planned encoding: flatten into five named `int` fields (`limb0`…`limb4`) rather than `Map int bv64` — same gap, not a separate one |
| 2 | `[u8; 64]` byte arrays | #25 | ○ open | `input: &[u8; 64]` as `Map int bv8`; SMT backend resolved by PR #795; remaining gap is Boole syntax (initializer, write-back) |
| 5 | `[u8; 32]` byte arrays | #25 | ○ open | Same as B2; SMT backend resolved by PR #795 |
| 2 | `reduce()` spec function | — | ✓ done | Axiom pattern verified in [`scalar_reduce.lean`](../StrataTest/Languages/Boole/FeatureRequests/scalar_reduce.lean); `u8_64_as_group_canonical` recursive form needs `Sequence bv8` (Gap #25); manual axioms unchanged |
| 2 | `is_uniform_scalar` axiom | — | ○ open | Probabilistic postcondition needs abstract `is_uniform_bytes`/`is_uniform_scalar` predicates as Boole axioms |
| 3 | `Option<EdwardsPoint>` return | — | ○ open | Boole has no native `Option<T>` type and no `matches` destructuring in spec clauses; see [`option_matches.lean`](../StrataTest/Languages/Boole/FeatureRequests/option_matches.lean) |
| 3 | `field_square` / `sqrt_ratio_i` axioms | — | ○ open | Needed for the full decompress body |
| 4 | Pair return type | — | ○ open | `invsqrt()` returns `(bool, FieldElement51)`; needs tuple/pair type support in Boole |
| 4 | Field op axioms | — | ○ open | `add`, `sub`, `square`, `invsqrt`, `conditional_negate`, `as_bytes` — each needs a Boole axiom |
| 5 | Inline `let`-block postcondition | — | ✓ done | Implemented; see [`embedded_postcondition.lean`](../StrataTest/Languages/Boole/embedded_postcondition.lean) |
| 5 | Montgomery ladder invariant | — | ○ open | Needs Montgomery curve differential addition axioms (Costello-Smith 2017, eq. 4); loop structure demonstrated in [`montgomery_loop_invariant.lean`](../StrataTest/Languages/Boole/FeatureRequests/montgomery_loop_invariant.lean) |

