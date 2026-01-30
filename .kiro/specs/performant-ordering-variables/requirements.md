# Performant Ordering Variable Numbering - Requirements

## Executive Summary

This specification describes the migration of Strata's variable representation from the current system to **Performant Ordering** - a unified variable numbering scheme using globally unique natural numbers. This change affects both lambda calculus (bound variables) and imperative layer (free variables), replacing all relative indexing schemes with a single, transformation-friendly approach.

**Key Change:** All variables (lambda-bound and imperative-declared) are identified by unique natural numbers assigned from a global counter, with no relative counting or context-dependent indexing.

## Current State

Strata currently uses different variable representation schemes across its layers:
- **Lambda calculus**: Uses De Bruijn indices for bound variables (bvar) - relative counting from binding site
- **Imperative layer**: Uses string-based identifiers for free variables (fvar)
- **Mixed approach**: Leads to complex index shifting, weakening, and lifting operations

## Problems with Current Approach

1. **Complexity**: Index shifting logic is error-prone and difficult to prove correct
2. **Transformation friction**: Variables change identity during transformations
3. **Dual reasoning**: Different proof strategies for lambda-bound vs imperative variables
4. **Boundary cases**: Complex interactions between bvar and fvar
5. **Canonicity overhead**: De Bruijn requires normalization, but Strata prioritizes semantic equivalence

## Proposed Solution: Performant Ordering

**Core Concept**: All variables are identified by globally unique natural numbers assigned from a monotonically increasing counter.

**Benefits**:
- **Simplicity**: No index shifting, no relative counting
- **Stability**: Variables maintain identity across all transformations
- **Unified reasoning**: Single proof strategy for all variables
- **Transformation-friendly**: Fresh variable generation is trivial and local
- **Strata-optimized**: Perfect for multi-stage transformation pipelines

**Trade-off Accepted**: Loss of canonical representation (alpha-equivalent terms may differ syntactically), but semantic equivalence is what matters for verification.

## Glossary

- **Performant Ordering**: Variable numbering scheme using globally unique natural numbers
- **nextFree**: Counter representing the next available fresh variable number
- **NextFree α**: Generic structure containing content of type α and a nextFree counter
- **FreshM**: State monad for generating fresh variable numbers
- **bvar**: Bound variable (lambda-bound, quantifier-bound) - now uses Performant Ordering
- **fvar**: Free variable (imperative-declared) - now uses Performant Ordering
- **LExpr**: Lambda expressions in the Lambda dialect
- **Cmd**: Commands in the Imperative dialect
- **VarContext**: Mapping from variable numbers to metadata (name, type) for display/debugging
- **Unified numbering**: Single numbering space shared by both bvar and fvar

---

## Requirements

### Requirement 1: Unified Variable Representation

**User Story**: As a language designer, I want all variables to use a single numbering scheme, so that there's no distinction between lambda-bound and imperative variable numbering.

#### Acceptance Criteria

1.1. WHEN a variable is represented in the AST, THE System SHALL use a natural number as its unique identifier

1.2. WHEN a lambda parameter is declared, THE System SHALL assign it a unique number from nextFree

1.3. WHEN an imperative variable is declared, THE System SHALL assign it a unique number from nextFree

1.4. WHEN a quantifier binds a variable, THE System SHALL assign it a unique number from nextFree

1.5. WHERE variables are used, THE System SHALL reference them by their assigned number

### Requirement 2: NextFree Structure with Fresh Counter

**User Story**: As a compiler developer, I want programs to track the next available variable number, so that fresh variable generation is guaranteed to be unique.

#### Acceptance Criteria

2.1. WHEN a NextFree is defined, THE System SHALL include a nextFree field of type Nat

2.2. WHEN a NextFree is created, THE System SHALL initialize nextFree to 0 (or to the next available number if continuing from a previous context)

2.3. WHEN a fresh variable is needed, THE System SHALL use the current nextFree value and increment it

2.4. WHERE multiple types of variables exist (lambda-bound, imperative, quantifier-bound), THE System SHALL use the same nextFree counter for all of them

2.5. WHERE all variables in a program, THE System SHALL maintain the invariant that all variable numbers are strictly less than nextFree

### Requirement 3: Fresh Variable Generation

**User Story**: As a transformation developer, I want to generate fresh variables using a state monad, so that uniqueness is guaranteed by construction.

#### Acceptance Criteria

3.1. WHEN generating a fresh variable, THE System SHALL provide a FreshM monad that returns the current nextFree and increments it

3.2. WHEN multiple fresh variables are needed, THE System SHALL thread the state through all generations

3.3. WHEN a transformation completes, THE System SHALL return an updated NextFree with the new nextFree value

3.4. WHERE fresh variable generation occurs, THE System SHALL guarantee that the returned number was not previously used in the program

### Requirement 4: Lambda Calculus Operations

**User Story**: As a lambda calculus implementer, I want substitution and beta reduction to work without index shifting, so that operations are simpler and proofs are easier.

#### Acceptance Criteria

4.1. WHEN performing beta reduction (λ x₄₂. body) arg, THE System SHALL substitute all occurrences of variable 42 in body with arg, without any index adjustment

4.2. WHEN performing substitution body[x₄₂ := arg], THE System SHALL replace all occurrences of variable 42 with arg, without shifting any other variables

4.3. WHEN performing alpha conversion, THE System SHALL generate a fresh variable number and replace the old parameter number with the new one, without any index adjustment

4.4. WHERE lambda expressions are evaluated, THE System SHALL NOT perform any index shifting, weakening, or lifting operations

### Requirement 5: Imperative Operations

**User Story**: As an imperative language implementer, I want variable declarations and assignments to use unique numbers, so that shadowing is impossible and variable tracking is unambiguous.

#### Acceptance Criteria

5.1. WHEN an init command declares a variable, THE System SHALL assign it a unique number from nextFree

5.2. WHEN a set command modifies a variable, THE System SHALL reference it by its unique number

5.3. WHEN a havoc command randomizes a variable, THE System SHALL reference it by its unique number

5.4. WHERE multiple variables with the same display name exist, THE System SHALL distinguish them by their unique numbers

5.5. WHEN inlining procedures, THE System SHALL generate fresh numbers for all parameters and locals

### Requirement 6: Pretty Printing and Display

**User Story**: As a developer debugging programs, I want variable numbers to be resolved to unambiguous readable names, so that output is human-friendly and clear even with shadowing.

#### Acceptance Criteria

6.1. WHEN displaying a variable, THE System SHALL resolve its number to a display name using VarContext

6.2. WHEN a variable number cannot be resolved, THE System SHALL display it as @N (e.g., @42)

6.3. WHEN multiple variables share the same display name, THE System SHALL disambiguate using @N suffix where N is the shadowing count

6.4. WHERE a variable is the most recent with its name, THE System SHALL display it with the plain name (no suffix)

6.5. WHERE a variable is shadowed by N later variables with the same name, THE System SHALL display it as name@N

6.6. WHEN formatting expressions, THE System SHALL use VarContext to make output readable and unambiguous

6.7. WHERE VarContext tracks variables, THE System SHALL maintain declaration order to compute shadowing counts

### Requirement 7: Scope and Shadowing

**User Story**: As a language designer, I want shadowing to be impossible by construction, so that variable references are always unambiguous.

#### Acceptance Criteria

7.1. WHEN a new variable is declared, THE System SHALL assign it a unique number that has never been used

7.2. WHERE two variables have the same display name, THE System SHALL distinguish them by their unique numbers

7.3. WHEN a variable goes out of scope, THE System SHALL NOT reuse its number

7.4. WHERE variable lookup occurs, THE System SHALL use the unique number, not the display name

### Requirement 8: Transformation Correctness

**User Story**: As a verification engineer, I want transformations to preserve program semantics, so that verification results are trustworthy.

#### Acceptance Criteria

8.1. WHEN a transformation generates fresh variables, THE System SHALL prove that the fresh numbers are not in the original program

8.2. WHEN a transformation preserves variables, THE System SHALL prove that variable numbers remain unchanged

8.3. WHEN a transformation performs substitution, THE System SHALL prove that semantics are preserved

8.4. WHERE transformations compose, THE System SHALL prove that the composition preserves semantics

8.5. WHEN a transformation completes, THE System SHALL prove that all variables in the result are below the new nextFree

### Requirement 9: Type System Integration

**User Story**: As a type system maintainer, I want type checking to work with variable numbers, so that type safety is preserved.

#### Acceptance Criteria

9.1. WHEN type checking a variable reference, THE System SHALL look up its type using the variable number

9.2. WHEN a variable is declared, THE System SHALL associate its number with its type

9.3. WHEN type checking lambda expressions, THE System SHALL track parameter types by their numbers

9.4. WHERE type environments are maintained, THE System SHALL map variable numbers to types

### Requirement 10: Evaluation and Semantics

**User Story**: As a semantics implementer, I want evaluation to work with variable numbers, so that runtime behavior is correct.

#### Acceptance Criteria

10.1. WHEN evaluating a variable reference, THE System SHALL look up its value using the variable number

10.2. WHEN a variable is assigned, THE System SHALL update the value at its number

10.3. WHEN evaluating lambda application, THE System SHALL substitute using variable numbers without shifting

10.4. WHERE evaluation environments are maintained, THE System SHALL map variable numbers to values

### Requirement 11: SMT Backend Integration

**User Story**: As a verification backend developer, I want SMT encoding to generate unique variable names, so that verification conditions are correct.

#### Acceptance Criteria

11.1. WHEN encoding a variable to SMT, THE System SHALL generate a unique SMT identifier

11.2. WHEN multiple variables share a display name, THE System SHALL use @N suffixes in SMT (e.g., x, x@1, x@2)

11.3. WHEN encoding expressions, THE System SHALL resolve variable numbers to SMT identifiers

11.4. WHERE SMT variable names are generated, THE System SHALL maintain a mapping from variable numbers to SMT identifiers

### Requirement 12: Elimination of old() Construct

**User Story**: As a verification engineer, I want to reference pre-state values of global variables using explicit variable identifiers instead of the `old()` construct, so that variable semantics are uniform and clear.

#### Acceptance Criteria

12.1. WHEN a procedure postcondition needs to reference a pre-state value of a global variable, THE System SHALL use an explicit variable identifier for the old value

12.2. WHEN translating procedures with modifies clauses, THE System SHALL generate fresh identifiers for old values of modified globals

12.3. WHERE the `old()` construct previously existed for globals, THE System SHALL replace it with old identifier references

12.4. WHEN evaluating postconditions, THE System SHALL look up pre-state values using old identifiers

12.5. WHERE procedure contracts are specified, THE System SHALL NOT use the `old()` construct for global variables

12.6. WHEN a global variable is not in the modifies clause, THE System SHALL NOT generate an old identifier for it

12.7. WHERE the modifies clause is defined, THE System SHALL store both current and old identifiers for each modified global

12.8. WHEN displaying old identifiers, THE System SHALL use "old " prefix (e.g., "old g")

### Requirement 13: Compilation and Testing

**User Story**: As a project maintainer, I want the refactored code to compile and pass all tests, so that the system remains functional.

#### Acceptance Criteria

13.1. WHEN all changes are complete, THE System SHALL compile without errors using `lake build`

13.2. WHEN tests are run, THE System SHALL pass all existing tests using `lake test`

13.3. WHERE proofs are affected, THE System SHALL restore all proofs to working state

13.4. WHEN the migration is complete, THE System SHALL have no remaining `sorry` placeholders
