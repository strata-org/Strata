# Requirements Document

## Introduction

This document specifies requirements for a new verification pipeline for Strata Core programs. The architecture consists of two layers:

1. A CoreSMT_Verifier that works with a restricted subset of Strata Core (satisfying isCoreSMT), translating directly to SMT and executing immediately if an interactive and incremental SMT solver is available
2. A Core_Verifier that accepts arbitrary Strata Core programs and reduces them to the isCoreSMT subset before delegating to the CoreSMT_Verifier

The goal is to migrate the successful B3 verifier architecture (streaming symbolic execution, automatic diagnosis, error accumulation) to work natively with Strata Core. For testing purposes, programs can be provided using DDM syntax which is then translated into the Strata Core AST.

## Glossary

- **Core_Verifier**: The top-level verifier that accepts arbitrary Strata Core programs, reduces them to the isCoreSMT subset, and delegates to CoreSMT_Verifier
- **CoreSMT_Verifier**: A verifier that works with the isCoreSMT subset of Strata Core, translating directly to SMT
- **Verification_State**: The state tracking SMT solver context, accumulated assumptions (from assume statements and path conditions), and declared functions during verification; used for error reporting
- **Proof_Check**: A verification that attempts to prove a property holds
- **Cover_Check**: A reachability check (failure = unreachable)
- **AssertResult**: The outcome of a proof check: proved (unsat), refuted (unsat of negation), counterexample (sat), or unknown
- **CoverResult**: The outcome of a cover check: reachable (sat), refuted (unsat), proved (unsat of negation), or reachabilityUnknown (unknown)
- **Diagnosis**: Automatic analysis of failed verifications to identify root causes through various strategies (e.g., splitting conjunctions)
- **isCoreSMT**: A predicate characterizing the subset of Strata Core AST that can be directly translated to SMT by CoreSMT_Verifier
- **Streaming_Verification**: Verification approach where statements are translated and verified incrementally without building the entire program in memory first

## Requirements

### Requirement 1: CoreSMT Statement Verification

**User Story:** As a developer, I want to verify Strata Core programs satisfying isCoreSMT using SMT solving, so that I can check correctness properties directly.

#### Acceptance Criteria

1. WHEN an assume statement is encountered, THE CoreSMT_Verifier SHALL add the expression to the SMT solver state and track it in the verification state
2. WHEN an init statement with an expression is encountered, THE CoreSMT_Verifier SHALL emit an SMT define-fun command
3. WHEN an init statement without an expression is encountered, THE CoreSMT_Verifier SHALL emit an SMT declare-fun command (unconstrained)
4. WHEN an assert statement is encountered, THE CoreSMT_Verifier SHALL perform a proof check and then add the expression to the SMT solver state (but not the verification state for reporting)
5. WHEN a check statement is encountered, THE CoreSMT_Verifier SHALL perform a proof check without modifying the SMT solver state
6. WHEN a cover statement is encountered, THE CoreSMT_Verifier SHALL perform a cover check to verify reachability
7. WHEN a block of statements is encountered, THE CoreSMT_Verifier SHALL emit SMT push/pop around the block and process each statement sequentially

### Requirement 2: Core Verifier with Reduction to isCoreSMT

**User Story:** As a developer, I want to verify arbitrary Strata Core programs by reducing them to the isCoreSMT subset, so that I can use the full language while benefiting from the simpler verifier.

#### Acceptance Criteria

1. THE Core_Verifier SHALL accept arbitrary Strata Core programs as input
2. THE Core_Verifier SHALL apply transformations to reduce programs to the isCoreSMT subset
3. THE Core_Verifier SHALL delegate verification to the CoreSMT_Verifier after reduction
4. THE Core_Verifier SHALL preserve source locations through transformations for error reporting

### Requirement 3: Function Declaration Support

**User Story:** As a developer, I want to declare uninterpreted functions in my Strata Core programs, so that I can reason about abstract function behavior using axioms.

#### Acceptance Criteria

1. WHEN a function declaration without a body is encountered, THE CoreSMT_Verifier SHALL emit an SMT declare-fun command
2. WHEN a function declaration with a body is encountered, THE CoreSMT_Verifier SHALL emit an SMT define-fun command or equivalent axiom
3. WHEN a function is called in an expression, THE CoreSMT_Verifier SHALL translate it to an SMT function application

### Requirement 4: User-Friendly Verification Results

**User Story:** As a developer, I want verification results expressed in user-friendly terms (not raw SMT sat/unsat/unknown), so that I can understand what the verification outcome means.

#### Acceptance Criteria

1. THE CoreSMT_Verifier SHALL use AssertResult for proof checks with the following outcomes:
   - proved: The assertion was verified (SMT unsat when negated)
   - refuted: The assertion is provably false (SMT unsat when asserted, discovered during diagnosis)
   - counterexample: A counterexample exists (SMT sat when negated)
   - unknown: The solver could not determine the result (SMT unknown)
2. THE CoreSMT_Verifier SHALL use CoverResult for cover checks with the following outcomes:
   - reachable: The condition is satisfiable (SMT sat)
   - refuted: The condition is unsatisfiable/unreachable (SMT unsat)
   - proved: The condition is provably reachable (SMT unsat when negated, discovered during diagnosis)
   - reachabilityUnknown: The solver could not determine reachability (SMT unknown)
3. THE CoreSMT_Verifier SHALL classify results into error and non-error categories:
   - AssertResult errors: counterexample, unknown, refuted
   - AssertResult success: proved
   - CoverResult errors: refuted
   - CoverResult success: reachable, proved
   - CoverResult warnings (non-severe): reachabilityUnknown
4. THE CoreSMT_Verifier SHALL support configurable reporting levels:
   - Errors: Always reported
   - Warnings: Optionally reported (default: not reported)
5. AssertResult SHALL be convertible to VCResult for compatibility with existing pipelines

### Requirement 5: Automatic Diagnosis

**User Story:** As a developer, I want automatic diagnosis of failed verifications, so that I can quickly identify which part of a complex assertion fails.

#### Acceptance Criteria

1. WHEN a proof check fails, THE CoreSMT_Verifier SHALL apply diagnosis strategies to identify root causes
2. THE CoreSMT_Verifier SHALL support conjunction splitting as a diagnosis strategy
3. WHEN diagnosing the right conjunct of a conjunction, THE CoreSMT_Verifier SHALL temporarily add the left conjunct to the verification state to provide context
4. WHEN a sub-expression is provably false (SMT unsat when asserted), THE CoreSMT_Verifier SHALL mark it as refuted rather than just unprovable
5. WHEN a cover check fails on a conjunction, THE CoreSMT_Verifier SHALL stop diagnosis after finding the first unreachable conjunct
6. THE CoreSMT_Verifier SHALL report all diagnosed failures with their verification state for debugging
7. THE CoreSMT_Verifier architecture SHALL support adding new diagnosis strategies in the future

### Requirement 6: Verification State Tracking

**User Story:** As a developer, I want to see the assumptions in effect when a verification fails, so that I can understand the verification context.

#### Acceptance Criteria

1. THE CoreSMT_Verifier SHALL track all assumptions (from assume statements and path conditions) in the verification state during verification
2. WHEN reporting a verification failure, THE CoreSMT_Verifier SHALL include the active verification state
3. THE CoreSMT_Verifier SHALL display the verification state in a human-readable format with source references

### Requirement 7: Strata Core AST Integration

**User Story:** As a developer, I want the verifier to work directly with Strata Core AST, so that verification is decoupled from parsing.

#### Acceptance Criteria

1. THE CoreSMT_Verifier SHALL accept Strata Core AST (Statement, Expression types) as input
2. THE CoreSMT_Verifier SHALL work with parameterless procedures as the entry point for verification
3. THE CoreSMT_Verifier SHALL support all Strata Core expression types that satisfy isCoreSMT
4. FOR testing purposes, THE Core_Verifier tests SHALL use DDM syntax to construct Strata Core AST

### Requirement 8: Test Migration

**User Story:** As a maintainer, I want all B3 verifier tests migrated to Strata Core syntax, so that we can eventually remove the B3 verifier.

#### Acceptance Criteria

1. FOR ALL existing B3 verifier tests, THE Core_Verifier SHALL produce equivalent verification results using Strata Core syntax
2. THE CoreSMT_Verifier SHALL support the same expression operators as the B3 verifier (arithmetic, boolean, comparison, quantifiers)
3. THE CoreSMT_Verifier SHALL support the same statement types as the B3 verifier (check, assert, assume, reach/cover, blocks)

### Requirement 9: Streamable Architecture

**User Story:** As a developer, I want verification to happen incrementally during parsing, so that large programs can be verified without loading everything into memory.

#### Acceptance Criteria

1. THE CoreSMT_Verifier SHALL support verifying statements as they are parsed without requiring the full program AST
2. WHEN an if statement is encountered, THE Core_Verifier SHALL be able to rewrite it to two independent verification paths on the fly
3. THE CoreSMT_Verifier SHALL maintain verification state that can be incrementally updated during streaming verification

### Requirement 10: B3 Pipeline Replacement

**User Story:** As a maintainer, I want to eventually replace the B3→SMT pipeline with a B3→Core→SMT pipeline, so that we have a single verification backend.

#### Acceptance Criteria

1. THE Core_Verifier SHALL provide an API compatible with the B3 verifier for gradual migration
2. WHEN converting B3 AST to Strata Core, THE Core_Verifier SHALL preserve source locations for error reporting
3. THE Core_Verifier SHALL support using B3 syntax for error messages during the transition period

### Requirement 11: Current Pipeline API Compatibility

**User Story:** As a maintainer, I want the new Core_Verifier to eventually replace the current Core.verify pipeline, so that we have a unified verification approach.

#### Acceptance Criteria

1. THE Core_Verifier SHALL provide a verify function that accepts a Core.Program and returns VCResults
2. THE Core_Verifier SHALL produce VCResult structures compatible with the existing Core.VCResult type
3. THE Core_Verifier SHALL support the same Options configuration as the current Core.verify function
4. THE Core_Verifier SHALL support procedure filtering (proceduresToVerify parameter) for selective verification
5. WHEN integrated as the default pipeline, THE Core_Verifier SHALL maintain backward compatibility with existing callers of Core.verify
6. THE Core_Verifier SHALL support the same diagnostic output format for IDE integration (DiagnosticModel, FileRange)

### Requirement 12: Transformation Soundness Verification

**User Story:** As a maintainer, I want to verify that Strata Core to Strata Core transformations used in the pipeline are sound, so that I can trust the verification results.

#### Acceptance Criteria

1. THE Core_Verifier pipeline SHALL support pluggable transformations that can be independently verified for soundness
2. FOR EACH transformation used in the pipeline, THE Core_Verifier SHALL provide a mechanism to prove semantic preservation
3. THE Core_Verifier SHALL support composing multiple transformations while preserving overall soundness
4. WHEN a transformation is applied, THE Core_Verifier SHALL ensure the output is semantically equivalent to the input for verification purposes

### Requirement 13: isCoreSMT Subset Predicate

**User Story:** As a developer, I want a well-defined subset of Strata Core that can be directly translated to SMT, so that the SMT conversion is total and does not need to handle all Core constructs.

#### Acceptance Criteria

1. THE Core_Verifier SHALL define an isCoreSMT predicate that characterizes the subset of Strata Core handled by CoreSMT_Verifier
2. THE Core_Verifier SHALL provide transformations that convert arbitrary Strata Core programs to the isCoreSMT subset
3. THE CoreSMT_Verifier SHALL only need to handle constructs satisfying isCoreSMT
4. THE isCoreSMT predicate SHALL be decidable and efficiently checkable
5. THE CoreSMT_Verifier SHALL be provably total for programs satisfying isCoreSMT

### Requirement 14: SMT Program Generation

**User Story:** As a developer, I want to generate the full SMT program from the verification context, so that I can debug verification issues or use external SMT tools.

#### Acceptance Criteria

1. THE CoreSMT_Verifier SHALL support generating the complete SMT program from the current verification state
2. THE Core_Verifier SHALL support generating the complete SMT program by delegating to CoreSMT_Verifier
3. ANY verifier built on top of Core_Verifier SHALL inherit the ability to generate SMT programs
4. THE verifiers SHALL use the same translation logic for both streaming verification and full program generation
5. THE verifiers SHALL support generating SMT programs at any point during verification (not just at the end)
6. THE generated SMT program SHALL include all declarations, axioms, and assertions from the verification state

### Requirement 15: Assignment to SSA Transformation

**User Story:** As a developer, I want variable assignments to be transformed to SSA form, so that CoreSMT_Verifier only needs to handle definitions.

#### Acceptance Criteria

1. THE Core_Verifier SHALL transform variable assignments to SSA (Static Single Assignment) form before delegating to CoreSMT_Verifier
2. THE CoreSMT_Verifier SHALL only need to handle variable definitions (init with expression), not reassignments
3. THE SSA transformation SHALL preserve the semantics of the original program
4. THE SSA transformation SHALL preserve source locations for error reporting

### Requirement 16: Pluggable Simplification

**User Story:** As a developer, I want optional expression simplification during verification, so that trivial assertions can be resolved without calling the SMT solver.

#### Acceptance Criteria

1. THE verification context SHALL support an optional simplifier
2. THE simplifier SHALL receive assignments (Map Ident Expression) and assumptions (List Expression)
3. THE simplifier SHALL support expression-level simplification (constant folding, arithmetic evaluation)
4. THE simplifier SHALL support substitution from assignments (assignments are expressions, not just values)
5. THE simplifier SHALL support algebraic simplifications (e.g., List.head(List.cons(x, y)) → x)
6. WHEN an assertion simplifies to true, THE CoreSMT_Verifier SHALL skip the SMT solver call
7. WHEN an assertion simplifies to false, THE CoreSMT_Verifier SHALL report failure immediately without calling SMT
8. Simplification SHALL be disableable for debugging or SMT file generation

### Requirement 17: Complete Verification Report

**User Story:** As a developer, I want a complete verification report containing all assertions and their results, so that I can understand the full verification outcome.

#### Acceptance Criteria

1. THE Core_Verifier SHALL return a complete verification report for each verification run
2. THE verification report SHALL include each assertion checked and its verification result
3. THE verification report SHALL include source locations for each assertion
4. THE verification report SHALL indicate whether each assertion was resolved by simplification or SMT
5. THE verification report SHALL include the verification state at the point of each failure
