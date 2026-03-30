Agreed — IEEE 754 defines overflow to ±∞ as valid behavior, so unconditionally inserting overflow assertions for Laurel float ops would produce false positives for standard Java/Python programs.

Fixed in 5cae06b2: the Laurel translator now uses the non-safe float operators by default. I also took the opportunity to unify the approach across all overflow check categories. There's now an `OverflowChecks` structure in `Core.Options`:

```lean
structure OverflowChecks where
  signedBV   : Bool := true   -- C: signed overflow is UB
  unsignedBV : Bool := false  -- C: unsigned wraps (defined)
  float64    : Bool := false  -- IEEE 754: overflow to ±∞ (defined)
```

This replaces the previous (unused) `unsignedOverflowCheck` flag. The config is threaded through `LaurelTranslateOptions` → `TranslateState` and exposed via `--overflow-checks signed,unsigned,float64` on the CLI. Users who want finite-float checking can opt in with `--overflow-checks float64`.

The `finiteFloat64` subset type idea is interesting for a future iteration — it would let users express the constraint at the type level rather than as a global flag.
