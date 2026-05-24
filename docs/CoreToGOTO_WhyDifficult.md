# Core → CBMC GOTO: Why the Simulation Proof Isn't Trivial

**Branch:** `htd/unstructured-to-goto`
**Last refreshed:** 2026-05-23

A common reaction when looking at `Strata.Core.DetCFG` and CBMC's
GOTO format side by side is: "These two are nearly the same thing.
Both are flat instruction streams with integer PCs. The translator
is a flatten-and-relabel pass. Surely the simulation proof is mostly
trivial?"

That intuition is correct as a sketch. The forward-simulation
*kernel* — the central induction that walks one source command and
emits the corresponding GOTO instructions — is roughly 30 lines.

The proof is ~20,000 lines of Lean.

This document explains where the other ~99% lives, with concrete
examples from the actual proof, so a skeptical reader can decide for
themselves whether the difficulty is real.

---

## 1. The naive picture

(stub — see section 1)

## 2. Where the difficulty actually lives

(stub — categories with concrete examples and LoC estimates)

## 3. What the proof bought

(stub — what the 20k LoC delivers)

## 4. The "easy" part that wasn't

(stub — the kernel is small; the structural facts are large)
