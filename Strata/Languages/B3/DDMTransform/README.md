# B3 DDM Transform

This directory contains the DDM (Dialect Definition Mechanism) support for the B3 language, providing parser and pretty-printer functionality.

## Files

### Parse.lean
Defines the B3 dialect using DDM syntax. This includes:
- Type declarations (bool, int, string)
- Expression operators (binary, unary, logical)
- Statement operators (assign, check, assume, assert, etc.)
- Control flow constructs (if, loop, exit, return)

The dialect definition uses DDM's declarative syntax to specify:
- Operator precedence and associativity
- Pretty-printing format
- Parsing rules

### Translate.lean
Provides translation from DDM's concrete syntax tree to B3's abstract syntax tree. This includes:
- Expression translation (literals, operators, variables)
- Statement translation (assignments, assertions, control flow)
- Type translation
- Binding management for scoped variables

## Usage

The DDM dialect can be used with `#strata` blocks (similar to Boogie) to parse B3 programs directly in Lean files.

## Comparison with Boogie

This implementation follows the same pattern as `Strata/Languages/Boogie/DDMTransform/`:
- `Parse.lean` defines the dialect syntax
- `Translate.lean` converts DDM AST to language-specific AST
- The structure is simplified for B3's smaller feature set

## Current Limitations

The current implementation provides a minimal working dialect with:
- Basic expression operators
- Core statement types
- Simple control flow

Additional features from B3 (quantifiers, patterns, procedure calls, etc.) can be added incrementally by extending both Parse.lean and Translate.lean.
