# Add B3 Verifier: SMT-based verification for B3 programs

This PR imports and improves the B3 verification pipeline into Strata for the B3 dialect.

The tool B3 is essentially a translation from a B3 AST to SMT. Both B3 AST and SMT are dialects of Strata now. Since Strata is meant to support translations between dialects, let's support the translation in Strata itself instead of delegating it to an external tool.

## Architecture

This PR has many architectural features:

* It reuses the same code for translating B3 into an interactive SMT file and to pipe it with an SMT solver. That way, when we prove the translation to be sound, the verification will be sound but still interactive
* It supports proof and reachability checks
* It performs automatic diagnosis when a conjunction is failing (both for reachability and proofs)
* It translates a program to SMT and verifies it even in the presence of verification errors - such errors are reported separately

## What is being supported for now

* Functions with and without bodies
* Most of the B3 expression language
* Top-level axioms
* Procedures without parameters

## Module Structure

```
Verifier/
├── State.lean          - State types and basic operations
├── Conversion.lean     - B3 AST → SMT Term conversion
├── Formatter.lean      - SMT Term → SMT-LIB formatting (to be removed once #177 is merged)
├── Statements.lean     - Statement verification
├── Diagnosis.lean      - Failure diagnosis
├── Batch.lean          - Batch verification APIs
└── Transform/
    └── FunctionToAxiom.lean - Function → axiom transformation

StrataTest/Languages/B3/Verifier/
├── ConversionTests.lean - Unit tests for conversion logic
└── VerifierTests.lean   - Integration tests with Z3
```

## Testing

- `ConversionTests.lean` - B3 to SMT-LIB translation tests (4 tests)
- `VerifierTests.lean` - Solver integration tests for check, assert, reach with automatic diagnosis (6 tests)
- All tests use `#guard_msgs` for regression testing
