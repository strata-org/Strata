# B3-like Syntax for Strata Core - Implementation Plan

## Goal
Implement a B3-like concrete syntax tree (CST) for Strata Core with bidirectional conversion to/from Strata Core's AST (Statement).

## Base Branch
`add-func-decl-to-statements`

## Target Branch
`b3-like-syntax-strata-core`

## Key Design Decisions
- Parse statements (not top-level programs) since we'll add function/type/datatype/procedure declarations to statements later
- No semicolons (like B3)
- Expression language similar to B3
- Support: functions (no when/injective/taggers), datatypes (Strata Core syntax), assume statements
- No support yet: axiom statements, procedures (will add later)
- Almost a superset of B3 (except no axioms, only assumes)

## Tasks

### Phase 1: Setup and Branch Creation
- [x] Create CURRENT_PLAN.md
- [x] Fetch and checkout add-func-decl-to-statements branch
- [x] Create new branch b3-like-syntax-strata-core from add-func-decl-to-statements

### Phase 2: Define CoreCST DDM Dialect
- [x] Create Strata/Languages/Core/DDMTransform/ParseCST.lean
- [x] Define Expression category with B3-like operators:
  - Literals (nat, bool, string)
  - Variables (identifiers)
  - Logical operators (not, and, or, implies, iff, etc.)
  - Comparison operators (==, !=, <, <=, >, >=)
  - Arithmetic operators (+, -, *, div, mod, neg)
  - Conditionals (if-then-else)
  - Let expressions
  - Function calls
  - Quantifiers (forall, exists) with patterns
  - Labeled expressions
- [x] Define Statement category:
  - Variable declarations (var with type/autoinv/init)
  - Value declarations (val)
  - Assignment
  - Havoc/reinit
  - Assertions (assert, assume, check, reach/cover)
  - Control flow (if-else, loop with invariants, exit, return)
  - Blocks
  - Choice statements
  - Labeled statements
  - Forall statements
- [x] Define Function declarations:
  - Function parameters (no injective, no when clause, no taggers)
  - Function body with expression
- [x] Define Datatype declarations (matching Strata Core syntax)
- [x] Define Type declarations
- [x] Add #strata_gen directive

### Phase 3: Define CoreAST DDM Dialect
- [x] Create Strata/Languages/Core/DDMTransform/DefinitionAST.lean
- [x] Define AST with de Bruijn indices for variables
- [x] Define Expression AST (canonical forms, no syntactic sugar)
- [x] Define Statement AST (canonical forms)
- [x] Define Declaration AST (functions, types, datatypes)
- [x] Add metadata transformation functions (mapMetadata)
- [x] Add #strata_gen directive

### Phase 4: CST ↔ AST Conversion
- [x] Create Strata/Languages/Core/DDMTransform/Conversion.lean
- [x] Define conversion error types:
  - CSTToASTError (unresolved identifiers, etc.)
  - ASTToCSTError (out of bounds indices, etc.)
- [x] Implement CST → AST conversion framework:
  - Name resolution (identifiers to de Bruijn indices)
  - Context management for variable scoping
  - Expression conversion (placeholder)
  - Statement conversion (placeholder)
  - Declaration conversion (placeholder)
- [x] Implement AST → CST conversion framework:
  - De Bruijn indices to names
  - Context management for name generation
  - Expression conversion (placeholder)
  - Statement conversion (placeholder)
  - Declaration conversion (placeholder)
- [ ] Handle special cases:
  - Shadowed variables
  - Old expressions (if needed)
  - Nested scopes

### Phase 5: Integration with Strata Core
- [ ] Create conversion from CoreAST to Core.Statement
- [ ] Create conversion from Core.Statement to CoreAST
- [ ] Handle unsupported features gracefully (return errors)
- [ ] Map between DDM metadata and Core metadata

### Phase 6: Testing
- [ ] Create test file with simple statements
- [ ] Test expression parsing and formatting
- [ ] Test statement parsing and formatting
- [ ] Test function declarations
- [ ] Test datatype declarations
- [ ] Test round-trip conversion (CST → AST → CST)
- [ ] Test conversion to/from Core.Statement
- [ ] Test error handling (unresolved names, out of bounds, etc.)

### Phase 7: Documentation
- [ ] Add module documentation to ParseCST.lean
- [ ] Add module documentation to DefinitionAST.lean
- [ ] Add module documentation to Conversion.lean
- [ ] Document limitations and unsupported features
- [ ] Add examples in comments

## Completion Criteria
- DDM definition for CoreCST (concrete syntax)
- DDM definition for CoreAST (abstract syntax with de Bruijn indices)
- Bidirectional conversion between CoreCST and CoreAST
- Conversion to/from Core.Statement
- All conversions handle errors appropriately
- Basic test cases pass

## Notes
- Start with minimal feature set, can extend later
- Follow B3 structure closely for consistency
- Keep conversion logic separate from dialect definitions
- Use B3 conversion code as reference implementation
