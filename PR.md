# Add B3 Verifier: SMT-based verification for B3 programs

This PR starts to import and improves the B3 verification pipeline into Strata for the B3 dialect.

The tool B3 is essentially a translation from a B3 AST to SMT. Both B3 AST and SMT are dialects of Strata now. Since Strata is meant to support translations between dialects, let's support the translation in Strata itself instead of delegating it to an external tool.

## Architecture

This PR has many architectural features:

* Strata reuses the same code for translating the language B3 into an interactive SMT file and to pipe it with an SMT solver. That way, when we prove the translation to be sound, the verification will be sound but still interactive
* Strata supports proof and reachability checks: SMT's 'unknown' and 'sat' are both errors for proof checks, but only 'unsat' is an error for reachability.
* Strata performs automatic recursive diagnosis when a B3 conjunction is failing both for reachability and proofs. While Strata can report multiple expressions that failed to proved in a single B3 check, Strata obviously only reports at most one unreachable expression error since all subsequent expressions are then provably unreachable.
* Strata translates a B3 program to SMT and verifies it even in the presence of conversion errors - such errors are accumulated and reported separately, allowing partial SMT generation for debugging

## What is being supported for now

* Axioms
* Functions with and without bodies. A pass transforms the former into the latter using axioms.
* All the B3 expression language except let expressions
* Procedures without parameters
  * Block, check, assert and assume statements.

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

- `ConversionTests.lean` - B3 to SMT-LIB translation tests
- `VerifierTests.lean` - Solver integration tests for check, assert, reach with automatic diagnosis
- All tests use `#guard_msgs` for regression testing
