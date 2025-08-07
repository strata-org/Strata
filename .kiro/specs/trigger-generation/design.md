# Design Document

## Overview

This document outlines the design for implementing manual trigger support in Boogie quantifiers within the Strata verification framework. The implementation will extend the existing quantifier parsing and SMT2 translation infrastructure to support user-specified trigger patterns.

## Architecture

### High-Level Components

1. **Parser Extension**: Extend Boogie grammar to recognize trigger syntax `{ expr1, expr2, ... }`
2. **AST Representation**: Add trigger information to quantifier AST nodes
3. **Type Checking**: Validate trigger expressions and variable bindings
4. **SMT2 Translation**: Generate appropriate `:pattern` attributes in SMT2 output
5. **Quantifier Optimization**: Implement nested quantifier flattening based on trigger coverage

### Data Flow

```
Boogie Source → Parser → AST with Triggers → Type Checker → SMT2 Generator → SMT2 with Patterns
```

## Components and Interfaces

### 1. Grammar Extension

**Location**: `Strata/Languages/Boogie/` grammar files

**Changes**:
- Add `Trigger` and `Triggers` syntax categories
- Extend quantifier syntax to include optional trigger specifications
- Support multiple trigger patterns and multi-term patterns

**Syntax**:
```
Trigger ::= '{' ExprList '}'
Triggers ::= Trigger+
Quantifier ::= 'forall' Bindings ('::' Triggers)? '::' Expr
```

### 2. AST Representation

**Location**: `Strata/Languages/Boogie/Expressions.lean`

**Changes**:
- Add `TriggerPattern` type to represent individual trigger patterns
- Add `triggers : Option (List TriggerPattern)` field to quantifier expressions
- Ensure trigger expressions are properly typed and scoped

**Types**:
```lean
structure TriggerPattern where
  expressions : List Expr
  
inductive Expr where
  | forall (bindings : DeclList) (triggers : Option (List TriggerPattern)) (body : Expr)
  -- ... other cases
```

### 3. Type Checking Enhancement

**Location**: `Strata/Languages/Boogie/ExpressionType.lean`

**Responsibilities**:
- Validate that trigger expressions are well-typed
- Check that all variables in triggers are bound by the quantifier
- Ensure trigger expressions don't contain free variables
- Validate function calls in trigger patterns

**Key Functions**:
```lean
def validateTriggerPattern (env : TEnv) (bindings : DeclList) (pattern : TriggerPattern) : Result Unit
def checkTriggerCoverage (bindings : DeclList) (patterns : List TriggerPattern) : CoverageInfo
```

### 4. SMT2 Translation

**Location**: `Strata/Languages/Boogie/SMTEncoder.lean`

**Responsibilities**:
- Generate `:pattern` attributes for quantifiers with triggers
- Handle multiple trigger patterns correctly
- Support multi-term patterns within single `:pattern` attributes
- Maintain backward compatibility for quantifiers without triggers

**Key Functions**:
```lean
def translateTriggerPattern (pattern : TriggerPattern) : SMT2.Pattern
def addPatternsToQuantifier (quantifier : SMT2.Quantifier) (patterns : List TriggerPattern) : SMT2.Quantifier
```

**Output Format**:
```smt2
(forall ((x Int)) (! (> (f x) 0) :pattern ((f x))))
(forall ((x Int) (y Int)) (! (> (+ (f x) (g x y)) 0) :pattern ((f x)) :pattern ((g x y))))
```

### 5. Quantifier Flattening

**Location**: `Strata/Languages/Boogie/QuantifierOptimization.lean` (new file)

**Algorithm**:
1. Analyze nested quantifiers for trigger patterns
2. Determine variable coverage by triggers
3. If triggers cover all variables from outer quantifiers, flatten
4. Preserve nested structure if coverage is incomplete
5. Generate warnings for incomplete coverage

**Key Functions**:
```lean
def analyzeVariableCoverage (outerBindings : DeclList) (innerTriggers : List TriggerPattern) : CoverageAnalysis
def flattenQuantifiers (outer : Quantifier) (inner : Quantifier) : Option Quantifier
def shouldFlatten (coverage : CoverageAnalysis) : Bool
```

## Data Models

### TriggerPattern
```lean
structure TriggerPattern where
  expressions : List Expr
  sourceInfo : SourceInfo
```

### CoverageAnalysis
```lean
structure CoverageAnalysis where
  coveredVars : Set String
  uncoveredVars : Set String
  isComplete : Bool
```

### Enhanced Quantifier
```lean
structure QuantifierExpr where
  bindings : DeclList
  triggers : Option (List TriggerPattern)
  body : Expr
  isFlattened : Bool
```

## Error Handling

### Error Types

1. **UnboundVariableInTrigger**: Variable in trigger not bound by quantifier
2. **UndefinedFunctionInTrigger**: Function call in trigger references undefined function
3. **EmptyTriggerPattern**: Trigger pattern contains no expressions
4. **InvalidTriggerExpression**: Trigger expression is not well-formed
5. **IncompleteTriggerCoverage**: Warning when triggers don't cover all variables

### Error Messages

```lean
def formatTriggerError (error : TriggerError) : String :=
  match error with
  | .unboundVariable var => s!"Unbound variable '{var}' in trigger pattern"
  | .undefinedFunction fn => s!"Undefined function '{fn}' in trigger pattern"
  | .emptyPattern => "Empty trigger pattern not allowed"
  | .incompleteCoverage vars => s!"Trigger pattern does not cover variables: {vars}"
```

## Testing Strategy

### Unit Tests

1. **Parser Tests**: Verify correct parsing of trigger syntax variations
2. **Type Checker Tests**: Validate error detection for malformed triggers
3. **SMT2 Generation Tests**: Confirm correct `:pattern` attribute generation
4. **Flattening Tests**: Test quantifier flattening logic with various scenarios

### Integration Tests

1. **End-to-End Verification**: Complete Boogie programs with triggers
2. **SMT Solver Integration**: Verify generated SMT2 works with actual solvers
3. **Performance Tests**: Measure impact on verification time
4. **Regression Tests**: Ensure existing functionality remains unaffected

### Test Categories

1. **Basic Trigger Translation**: Simple trigger patterns work correctly
2. **Multiple Triggers**: Multiple trigger patterns generate correct SMT2
3. **Multi-term Triggers**: Comma-separated expressions in single trigger
4. **Nested Quantifier Flattening**: Complex nested scenarios
5. **Error Handling**: All error conditions produce appropriate messages
6. **Backward Compatibility**: Existing code continues to work

## Implementation Phases

### Phase 1: Core Infrastructure
- Grammar extension for trigger syntax
- AST representation updates
- Basic parsing functionality

### Phase 2: Type Checking
- Trigger validation logic
- Variable binding checks
- Error message generation

### Phase 3: SMT2 Translation
- Pattern attribute generation
- Multiple trigger support
- Multi-term pattern handling

### Phase 4: Quantifier Optimization
- Variable coverage analysis
- Flattening algorithm implementation
- Warning generation for incomplete coverage

### Phase 5: Testing and Integration
- Comprehensive test suite
- Performance optimization
- Documentation updates

## Performance Considerations

### Parsing Performance
- Trigger parsing adds minimal overhead to existing quantifier parsing
- Use efficient data structures for trigger pattern storage

### Type Checking Performance
- Variable coverage analysis is O(n*m) where n=variables, m=trigger expressions
- Cache coverage analysis results to avoid recomputation

### SMT2 Generation Performance
- Pattern generation is linear in number of trigger patterns
- No significant impact on overall SMT2 generation time

### Memory Usage
- Trigger patterns stored as lightweight expression lists
- Minimal memory overhead per quantifier

## Security Considerations

### Input Validation
- All trigger expressions must pass standard expression validation
- No special security concerns beyond normal expression handling

### SMT2 Output Safety
- Generated `:pattern` attributes use standard SMT2 syntax
- No risk of SMT2 injection or malformed output

## Backward Compatibility

### Existing Code
- All existing Boogie code without triggers continues to work unchanged
- No modifications required to existing verification workflows

### API Compatibility
- New trigger-related functions are additive
- Existing APIs maintain same signatures and behavior

### Output Compatibility
- SMT2 output for non-trigger quantifiers remains identical
- Verification results maintain same format and semantics