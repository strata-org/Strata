# Two-Sided Verification Check Implementation Summary

## What Was Implemented

### 1. Core SMT Layer Changes

**File: `Strata/DL/SMT/Solver.lean`**
- Added `checkSatAssuming` method to emit `(check-sat-assuming (lit₁ lit₂ ...))` commands
- This allows checking satisfiability under specific assumptions without asserting them globally

**File: `Strata/DL/Imperative/SMTUtils.lean`**
- Updated `solverResult` to parse two SMT verdicts (satisfiability and validity checks)
- Updated `dischargeObligation` to accept `satisfiabilityCheck` and `validityCheck` boolean flags
- Removed the old `reachCheck` parameter in favor of the two-sided approach

### 2. Core Encoding Changes

**File: `Strata/Languages/Core/Options.lean`**
- Added `CheckMode` enum with three variants: `full`, `validity`, `satisfiability`
- Replaced `reachCheck : Bool` with `checkMode : CheckMode`
- Default mode is `validity` (traditional verification behavior)

**File: `Strata/Languages/Core/Verifier.lean`**
- Replaced `Outcome` inductive with `VCOutcome` structure containing two `SMT.Result` fields
- Added helper methods to `VCOutcome` for interpreting the nine possible outcome combinations:
  - `isPass`: sat, unsat → always true & reachable
  - `isRefuted`: unsat, sat → always false & reachable
  - `isIndecisive`: sat, sat → true or false depending on inputs & reachable
  - `isUnreachable`: unsat, unsat → path condition contradictory
  - `isSatisfiable`: sat, unknown → can be true, reachability/validity unknown
  - `isRefutedIfReachable`: unsat, unknown → always false if reached
  - `isReachableAndCanBeFalse`: unknown, sat → can be false, satisfiability unknown
  - `isAlwaysTrueIfReachable`: unknown, unsat → always true if reached
  - `isUnknown`: unknown, unknown → solver timeout or incomplete

- Updated `VCResult` to store `Except String VCOutcome` instead of separate fields
- Updated `encodeCore` to emit two `check-sat-assuming` commands based on check mode
- Updated `dischargeObligation` to pass satisfiability and validity check flags
- Updated `verifySingleEnv` to determine which checks to perform based on check mode and property type
- Updated `preprocessObligation` to use the new `VCOutcome` structure
- Updated `getObligationResult` to construct `VCOutcome` from the two SMT results

### 3. SARIF Output Changes

**File: `Strata/Languages/Core/SarifOutput.lean`**
- Updated `outcomeToLevel` to map the nine outcome combinations to SARIF levels
- Updated `outcomeToMessage` to provide descriptive messages for each outcome
- Updated `vcResultToSarifResult` to handle `Except String VCOutcome`

### 4. Check Mode Logic

For `assert` statements:
- `full` mode: Both satisfiability and validity checks enabled
- `validity` mode: Only validity check enabled (default, traditional behavior)
- `satisfiability` mode: Only satisfiability check enabled

For `cover` statements:
- `full` mode: Both checks enabled
- `validity` mode: Only satisfiability check enabled (cover uses existential semantics)
- `satisfiability` mode: Only satisfiability check enabled

## What Still Needs to Be Done

### 1. Test Updates

All tests that check for specific outcomes need to be updated to reflect the new behavior:

**Critical**: With `validity` mode as default, tests will see different outcomes:
- Old "pass" with reachability → Now "always true if reachable" (unknown, unsat)
- Old "fail" → Now either "refuted" (unsat, sat) or "reachable and can be false" (unknown, sat)

**Files to update**:
- `StrataTest/Languages/Core/SMTEncoderTests.lean` - Update expected outcomes
- Any other test files that verify specific VCResult outcomes

### 2. CLI Integration

**File: `StrataVerify.lean` (or main executable)**
- Add `--check-mode` flag with options: `full`, `validity`, `satisfiability`
- Update help text to explain the three modes
- Ensure the flag is properly passed to `Options`

### 3. Per-Statement Annotations (Future Work)

The design document mentions per-statement overrides like `@[fullCheck]` or `@[satisfiabilityCheck]`. This would require:
- Adding annotation support to the metadata system
- Checking for annotations in `verifySingleEnv` before determining check mode
- Updating the parser to recognize these annotations

### 4. Cover Aggregation (Future Work)

The design mentions that cover statements should aggregate results across multiple paths. Currently, each path generates its own VCResult. To implement aggregation:
- Group cover obligations by their label
- Aggregate the (satisfiabilityProperty, validityProperty) pairs using disjunction
- Report a single outcome per cover statement

### 5. Documentation Updates

- Update user documentation to explain the three check modes
- Add examples showing the difference between modes
- Document the nine possible outcomes and their meanings
- Update any architecture documents that reference the old `Outcome` type

## Testing Strategy

1. **Update existing tests** to use `full` mode explicitly if they need both checks
2. **Add new tests** for each of the nine outcome combinations
3. **Test the default `validity` mode** to ensure backward compatibility
4. **Test `satisfiability` mode** for Ergo use case (detecting surely incorrect programs)

## Migration Notes

- The change is **not backward-compatible** at the API level
- All consumers of `VCResult` must be updated
- The default behavior (`validity` mode) preserves the traditional verification semantics
- Users who need the old reachability check can use `full` mode

## Key Design Decisions

1. **Default to `validity` mode**: Preserves traditional verification behavior
2. **Separate checks for assert vs cover**: Cover uses satisfiability semantics
3. **Nine-way outcome interpretation**: Provides maximum information when both checks are enabled
4. **Graceful degradation**: When a check is skipped, the outcome degrades to partial information
5. **Implementation errors wrapped in Except**: Keeps VCOutcome focused on SMT semantics
