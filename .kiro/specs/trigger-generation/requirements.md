# Requirements Document

## Introduction

This feature adds support for manual trigger generation in Boogie quantifiers within the Strata verification framework. Manual triggers allow users to specify patterns that guide SMT solvers in instantiating quantified formulas, improving verification performance and predictability.

## Requirements

### Requirement 1

**User Story:** As a verification engineer, I want to specify manual triggers in Boogie quantifiers, so that I can control when and how quantified formulas are instantiated by the SMT solver.

#### Acceptance Criteria

1. WHEN a user writes `forall x : int :: { f(x) } f(x) > 0` THEN the system SHALL parse the trigger pattern `{ f(x) }`
2. WHEN a quantifier contains trigger patterns THEN the system SHALL validate that all variables in triggers are bound by the quantifier
3. WHEN a quantifier contains multiple trigger patterns THEN the system SHALL support syntax like `{ f(x) } { g(x, y) }`
4. WHEN a quantifier contains multi-term trigger patterns THEN the system SHALL support syntax like `{ f(x), g(x) }`

### Requirement 2

**User Story:** As a verification engineer, I want manual triggers to be translated to SMT2 format, so that the SMT solver receives proper instantiation hints.

#### Acceptance Criteria

1. WHEN a quantifier with trigger `{ f(x) }` is processed THEN the system SHALL generate SMT2 output containing `:pattern ((f x))`
2. WHEN a quantifier has multiple triggers `{ f(x) } { g(x, y) }` THEN the system SHALL generate multiple `:pattern` attributes in SMT2
3. WHEN a quantifier has multi-term triggers `{ f(x), g(x) }` THEN the system SHALL generate SMT2 with pattern `((f x) (g x))`
4. WHEN a quantifier has no triggers THEN the system SHALL generate SMT2 without `:pattern` attributes (backward compatibility)

### Requirement 3

**User Story:** As a verification engineer, I want proper error handling for invalid trigger patterns, so that I receive clear feedback when triggers are malformed.

#### Acceptance Criteria

1. WHEN a trigger references an unbound variable THEN the system SHALL produce an error message identifying the unbound variable
2. WHEN a trigger contains an undefined function THEN the system SHALL produce an error message about the undefined identifier
3. WHEN a trigger pattern is empty `{ }` THEN the system SHALL produce an appropriate error or handle gracefully
4. WHEN trigger expressions are syntactically invalid THEN the system SHALL provide clear parse error messages

### Requirement 4

**User Story:** As a verification engineer, I want nested quantifiers with triggers to be handled intelligently, so that I can write natural quantifier expressions without worrying about internal representation details.

#### Acceptance Criteria

1. WHEN nested quantifiers have triggers that cover all variables THEN the system SHALL flatten the quantifiers into a single quantifier
2. WHEN nested quantifiers have triggers with incomplete variable coverage THEN the system SHALL preserve the nested structure
3. WHEN flattening occurs THEN the system SHALL maintain the logical equivalence of the original formula
4. WHEN variable coverage is incomplete THEN the system SHALL optionally warn about potential instantiation issues

### Requirement 5

**User Story:** As a verification engineer, I want trigger generation to integrate seamlessly with existing Boogie verification workflows, so that I can adopt triggers incrementally without breaking existing code.

#### Acceptance Criteria

1. WHEN existing Boogie code without triggers is processed THEN the system SHALL continue to work exactly as before
2. WHEN mixed code with and without triggers is processed THEN the system SHALL handle both cases correctly
3. WHEN verification results are generated THEN the system SHALL maintain the same output format and success/failure semantics
4. WHEN SMT2 files are generated THEN the system SHALL produce valid SMT2 syntax that works with standard solvers

### Requirement 6

**User Story:** As a verification engineer, I want comprehensive testing of trigger functionality, so that I can trust the implementation is correct and robust.

#### Acceptance Criteria

1. WHEN trigger functionality is implemented THEN the system SHALL include tests for basic trigger translation
2. WHEN SMT2 output is generated THEN the system SHALL include tests that validate the presence of `:pattern` attributes
3. WHEN nested quantifiers are processed THEN the system SHALL include tests for flattening behavior with expected outputs
4. WHEN error conditions occur THEN the system SHALL include tests that verify appropriate error messages are generated