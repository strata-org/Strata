# Requirements Document

## Introduction

This document specifies requirements for a CoreSMT verifier for Strata Core programs. The CoreSMT verifier operates on a well-defined subset of Strata Core (identified by the `isCoreSMT` predicate) and translates it directly to SMT for verification using an interactive SMT solver.

The goal is to provide a verification component that translates CoreSMT statements directly to SMT. It will work alongside the existing verifier pipeline. The verifier maintains state that can be reused across multiple verification calls.

## Glossary

- **CoreSMT_Verifier**: A verifier that accepts Strata Core statements, checks if they satisfy `isCoreSMT`, and translates them directly to SMT for verification
- **isCoreSMT**: A predicate characterizing the subset of Strata Core AST that maps 1-1 with SMT-LIB constructs
- **Diagnosis**: Automatic analysis of failed verifications to identify root causes through strategies like conjunction splitting
- **VCResult**: The existing verification result structure (reused from Core.VCResult) containing obligation, SMT result, and outcome
- **SMT_Solver_Interface**: A structure (not type class) defining an abstract interface for SMT solvers that can be passed to the verifier

## Requirements

### Requirement 1: CoreSMT Statement Verification with Internal Solver State

**User Story:** As a developer, I want to verify Strata Core statements using SMT solving with proper internal state management, so that I can check correctness properties directly.

#### Acceptance Criteria

1. WHEN an assume statement is encountered, THE CoreSMT_Verifier SHALL add the expression to the internal SMT solver state
2. WHEN an init statement with an expression is encountered, THE CoreSMT_Verifier SHALL emit an SMT define-fun command
3. WHEN an init statement without an expression is encountered, THE CoreSMT_Verifier SHALL emit an SMT declare-fun command (unconstrained). NOTE: This requires extending `Cmd.init` to support optional RHS, which is not currently implemented in the codebase.
4. WHEN an assert statement is encountered, THE CoreSMT_Verifier SHALL perform a proof check (check-sat of negation) WITHOUT modifying the SMT solver state (using push/pop)
5. WHEN a cover statement is encountered, THE CoreSMT_Verifier SHALL perform a reachability check (check-sat of the expression, where sat means reachable and unsat means unreachable)
6. WHEN a block of statements is encountered, THE CoreSMT_Verifier SHALL emit SMT push/pop around the block and process each statement sequentially
7. WHEN a function declaration without a body is encountered, THE CoreSMT_Verifier SHALL emit an SMT declare-fun command
8. WHEN a function declaration with a body is encountered, THE CoreSMT_Verifier SHALL emit an SMT define-fun command or equivalent axiom
9. WHEN a function is called in an expression, THE CoreSMT_Verifier SHALL translate it to an SMT function application
10. WHEN a statement or expression not in the isCoreSMT subset is encountered, THE CoreSMT_Verifier SHALL return an error (Except.error)
11. THE CoreSMT_Verifier SHALL accept Strata Core AST (Statement, Expression types) as input
12. THE CoreSMT_Verifier SHALL build VCResult structures that use the internal solver state for error reporting
13. THE CoreSMT_Verifier SHALL reuse the existing Env structure where appropriate for environment management

### Requirement 2: isCoreSMT Subset Predicate

**User Story:** As a developer, I want a well-defined subset of Strata Core that maps 1-1 with SMT-LIB constructs, so that the SMT conversion is total and straightforward.

#### Acceptance Criteria

1. THE CoreSMT_Verifier SHALL define an isCoreSMT predicate that characterizes the subset of Strata Core that maps 1-1 with SMT-LIB
2. THE isCoreSMT predicate SHALL include only constructs with direct SMT-LIB equivalents (assume→assert, init→define-fun/declare-fun, assert/check→check-sat, cover→check-sat, block→push/pop, funcDecl→declare-fun/define-fun)
3. THE isCoreSMT predicate SHALL exclude constructs without direct SMT-LIB equivalents (if-then-else statements, loops, goto, procedure calls)
4. THE CoreSMT_Verifier SHALL accept any Strata Core program as input (not just those satisfying isCoreSMT)
5. THE CoreSMT_Verifier SHALL return an Except type where the error case indicates the input does not satisfy isCoreSMT
6. THE isCoreSMT predicate SHALL be decidable and efficiently checkable

### Requirement 3: Verification Result Reporting

**User Story:** As a developer, I want verification results expressed using the existing VCResult structure, so that I can integrate with existing pipelines.

#### Acceptance Criteria

1. THE CoreSMT_Verifier SHALL reuse the existing Core.VCResult structure for reporting verification outcomes
2. THE CoreSMT_Verifier SHALL extend the existing Core.Outcome enumeration to include a "refuted" case for assertions that are provably false (not just unprovable)
3. THE CoreSMT_Verifier SHALL support error accumulation and continuation despite errors when configured

### Requirement 4: Automatic Diagnosis

**User Story:** As a developer, I want automatic diagnosis of failed verifications, so that I can quickly identify which part of a complex assertion fails.

#### Acceptance Criteria

1. THE CoreSMT_Verifier SHALL support configurable automatic diagnosis (settable via context)
2. WHEN a proof check fails and diagnosis is enabled, THE CoreSMT_Verifier SHALL apply diagnosis strategies to identify root causes
3. THE CoreSMT_Verifier SHALL support conjunction splitting as a diagnosis strategy
4. WHEN diagnosing the right conjunct of a conjunction, THE CoreSMT_Verifier SHALL temporarily add the left conjunct to provide context
5. WHEN a sub-expression is provably false (SMT unsat when asserted), THE CoreSMT_Verifier SHALL mark it as refuted rather than just unprovable
6. WHEN a cover check fails on a conjunction, THE CoreSMT_Verifier SHALL stop diagnosis after finding the first unreachable conjunct
7. THE CoreSMT_Verifier SHALL report all diagnosed failures with their context for debugging
8. THE diagnosis functionality SHALL be migrated from the existing B3 verifier implementation

### Requirement 5: Test Migration via B3 to Core Conversion

**User Story:** As a maintainer, I want to keep existing B3 tests using B3 syntax but verify them through Core, so that the CoreSMT verifier can be validated against known test cases without rewriting tests.

#### Acceptance Criteria

1. THE PR SHALL include a B3 AST to Core AST converter
2. THE B3 to Core converter SHALL translate B3 expressions to Core expressions
3. THE B3 to Core converter SHALL translate B3 statements (check, assert, assume, reach) to Core statements (assert, assert, assume, cover)
4. THE B3 to Core converter SHALL translate B3 function declarations to Core function declarations
5. FOR ALL existing B3 verifier tests, verification via B3→Core→CoreSMT SHALL produce equivalent results to the original B3→SMT path
6. THE PR SHALL remove the direct B3 to SMT translation once migration is complete
7. THE tests SHALL continue to use B3 DDM syntax (no test rewriting required)

### Requirement 6: Public Interface with State Reuse

**User Story:** As a developer, I want to verify a list of statements and get back updated state, so that I can reuse the state for subsequent verifications.

#### Acceptance Criteria

1. THE CoreSMT_Verifier public interface SHALL accept a list of statements to verify
2. THE CoreSMT_Verifier public interface SHALL return both verification results AND updated state
3. THE returned state SHALL be reusable for subsequent verification calls
4. WHEN a block statement is encountered in the list, THE CoreSMT_Verifier SHALL internally handle push/pop for the block scope
5. THE CoreSMT_Verifier SHALL support processing a prelude (statements) to initialize state before verification

### Requirement 7: SMT Solver Interface as Type

**User Story:** As a developer, I want to pass my own interactive SMT solver to the verifier, so that I can use different solver backends.

#### Acceptance Criteria

1. THE CoreSMT_Verifier SHALL accept an SMT solver interface as a parameter (structure/type, NOT type class)
2. THE SMT solver interface SHALL define types for SMT expressions and sorts
3. THE SMT solver interface SHALL provide methods to build SMT expressions (constants, variables, operations, quantifiers)
4. THE SMT solver interface SHALL provide IO methods to send SMT commands (declare-sort, declare-fun, define-fun, assert, check-sat, check-sat-assuming, push, pop)
5. THE SMT solver interface SHALL provide IO methods to receive SMT results (sat/unsat/unknown, models)
6. THE SMT solver interface SHALL support incremental solving (push/pop scopes)
7. THE SMT solver interface SHALL support model extraction when check-sat returns sat or unknown
8. THE SMT solver interface SHALL support check-sat-assuming for checking with temporary assumptions
9. FOR testing, THE implementation SHALL provide a default solver instance using the SMT dialect and cvc5 solver
