# TypeScript Frontend for Strata

This directory contains a manual TypeScript frontend for Strata that translates TypeScript programs to Strata's internal representation for analysis and verification.

## Architecture Overview

The TypeScript frontend consists of several key components that work together to parse, translate, and evaluate TypeScript code:

### Core Files

#### `js_ast.lean` - AST Node Definitions
This file defines the **structure of TypeScript AST nodes** in Lean. Each TypeScript construct (variables, functions, expressions, etc.) has a corresponding Lean structure.

**Key components:**
- `BaseNode` - Common fields for all AST nodes (location, type info)
- Type definitions: `TS_TSNumberKeyword`, `TS_TSBooleanKeyword`, `TS_TSStringKeyword`
- Expression types: `TS_BinaryExpression`, `TS_CallExpression`, `TS_Identifier`, etc.
- Statement types: `TS_VariableDeclaration`, `TS_FunctionDeclaration`, `TS_IfStatement`, etc.
- Root types: `TS_Program`, `TS_File`

**What students modify:** Add new `structure` definitions for unsupported TypeScript constructs, then add them to the appropriate `inductive` type.

#### `TS_to_Strata.lean` - Translation Engine
This file contains the **core translation logic** that converts TypeScript AST nodes into Strata's internal representation (CallHeap statements).

**Key functions:**
- `translate_expression` - Converts TypeScript expressions to Strata expressions
- `translate_statement` - Converts TypeScript statements to Strata statements  
- `TS_type_to_HMonoTy` - Maps TypeScript types to Strata heap types
- `extract_type_from_annotation` - Handles TypeScript type annotations

**What students modify:** Add new translation cases for the AST nodes they added to `js_ast.lean`.

#### `TSStrataStatement.lean` - Statement Wrappers
This file provides **TypeScript-specific aliases** for Strata's generic CallHeap statements. It's mostly just type aliases to make the code more readable.

**Contents:**
```lean
abbrev TSStrataStatement := CallHeapStrataStatement
abbrev TSStrataExpression := CallHeapStrataExpression
-- etc.
```

**What students modify:** Usually nothing - this file rarely needs changes.

#### `TSStrataEval.lean` - Evaluation Helpers
Contains **utility functions** for evaluating TypeScript constructs within Strata's evaluation framework.

**What students modify:** May need to add evaluation helpers for complex new constructs.

#### `TSFunction.lean` - Function Utilities  
Contains **function-specific utilities** and helpers for handling TypeScript function declarations and calls.

**What students modify:** May need updates when adding new function-related features.

## Currently Supported Features

### Data Types
- `number` - Numeric literals and arithmetic
- `string` - String literals  
- `boolean` - Boolean literals and logic
- `null` - Null values

### Expressions
- **Binary expressions**: `+`, `-`, `*`, `/`, `%`, `==`, `!=`, `<`, `>`, `<=`, `>=`
- **Logical expressions**: `&&`, `||`
- **Unary expressions**: `-`, `!`
- **Assignment expressions**: `=`
- **Conditional expressions**: `condition ? true_val : false_val`
- **Member expressions**: `obj[0]`, `obj[1]` (numeric keys only)
- **Call expressions**: `func(arg1, arg2)`

### Statements
- **Variable declarations**: `let x: number = 5;`
- **Function declarations**: `function name(params): returnType { ... }`
- **If statements**: `if (condition) { ... } else { ... }`
- **Return statements**: `return value;`
- **Expression statements**: `x + 5;`
- **Block statements**: `{ ... }`

### Objects
- Objects with **numeric keys only**: `{0: value1, 1: value2}`
- Member access with numeric indices: `obj[0]`

## Running Tests

### Prerequisites
```bash
# Install Node.js dependencies
npm install -g ts-node typescript
npm install @babel/parser @babel/types @babel/traverse @babel/generator

# Install Python dependencies
pip install tqdm

# Build Strata
lake build StrataTypeScriptRunner
```

### Running Conformance Tests
```bash
# Run all TypeScript tests
cd conformance_testing
python3 conformance_cli.py test ../StrataTest/Languages/TypeScript -l typescript -v

# Run a specific test file
python3 conformance_cli.py test ../StrataTest/Languages/TypeScript/test_variables.ts -l typescript -v
```

### Test262 Test Suite
This directory also contains modified tests from **Test262**, the official ECMAScript conformance test suite. Test262 is the standard test suite used to validate JavaScript engines and ensure they correctly implement the ECMAScript specification.

**About Test262:**
- Official test suite for JavaScript/ECMAScript compliance
- Contains thousands of tests covering all language features
- Used by browser vendors and JavaScript engine developers
- Tests both positive cases (should work) and negative cases (should throw errors)

**Modified Test262 Files:**
The Test262 files in this directory have been adapted for the Strata TypeScript frontend. Note that many don't work yet because the test harness itself uses `assertThrows` statements, which require **function pointers** (passing functions as arguments) - a feature not yet supported in our frontend.

**Using Test262 Tests:**
Students can use these as reference implementations and test cases when adding new features. The tests show expected behavior for various JavaScript constructs and edge cases. Once function pointers are implemented, many more Test262 tests will become runnable.

For more information about Test262, see: https://github.com/tc39/test262

### Understanding Test Results
- **Pass**: Native TypeScript execution matches Strata evaluation
- **Fail**: Mismatch between native and Strata results
- **Failed files** are saved to `failures/` directory for debugging

## Student Development Workflow

### 1. Identify Missing Feature
Run conformance tests to see what fails:
```bash
cd conformance_testing
python3 conformance_cli.py test ../StrataTest/Languages/TypeScript -l typescript -v
```

### 2. Add AST Definition
Add the structure to `js_ast.lean`:
```lean
structure TS_YourNewConstruct extends BaseNode where
  field1 : Type1
  field2 : Type2
deriving Repr, Lean.FromJson, Lean.ToJson
```

### 3. Add to Inductive Type
Add your construct to the appropriate inductive (TS_Expression or TS_Statement):
```lean
inductive TS_Statement where
  -- ... existing cases ...
  | TS_YourNewConstruct : TS_YourNewConstruct → TS_Statement
```

### 4. Implement Translation
Add translation logic in `TS_to_Strata.lean`:
```lean
def translate_your_construct (construct: TS_YourNewConstruct) (ctx: TranslationContext) : 
    TranslationContext × List TSStrataStatement := 
  -- Your implementation here
```

### 5. Test and Debug
```bash
lake build StrataTypeScriptRunner
python3 conformance_cli.py test ../StrataTest/Languages/TypeScript/your_test.ts -l typescript -v
```

### 6. Iterate
- **Parse errors** → Fix AST structure
- **Translation errors** → Fix translation logic  
- **Wrong results** → Check semantic correctness

## Common Error Messages

### "no inductive constructor matched"
- **Cause:** AST structure in `js_ast.lean` doesn't match what the parser generates
- **Fix:** Check the AST structure and adjust your Lean definitions

### "Native execution failed"
- **Cause:** TypeScript code has syntax errors or uses unsupported features
- **Fix:** Simplify the test case or check TypeScript syntax

### "Value mismatches"
- **Cause:** Translation logic doesn't match native TypeScript semantics
- **Fix:** Debug the translation in `TS_to_Strata.lean`

### "Failed to convert JSON to Node"
- **Cause:** Field name or structure mismatch in AST definition
- **Fix:** Check that your Lean structure matches the expected format

## Debugging Tips

1. **Start simple**: Begin with the most basic version of a feature
2. **Test incrementally**: Get simple cases working before complex ones
3. **Compare with working examples**: Look at existing test files that pass
4. **Check the roadmap**: See `FEATURES_ROADMAP.md` for implementation priorities

## Next Steps

See `FEATURES_ROADMAP.md` for a comprehensive list of features to implement, organized by priority. Start with Priority 1 features like loops and arrays for maximum impact.

This manual approach gives you complete control over how TypeScript constructs map to Strata's internal representation, making it perfect for educational purposes and incremental development.
