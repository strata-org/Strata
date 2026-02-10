---
inclusion: fileMatch
fileMatchPattern: ['StrataTest/**/*.lean', 'Strata/Transform/**/*.lean']
---

# Property-Based Testing for Strata Transformations

Use Plausible for property-based testing of transformations. Three-step process: build generators, write measurement functions, define properties.

## Generator Design

**Control depth to prevent infinite recursion:**
- Depth 0: Generate leaves (constants, variables)
- Depth > 0: Generate compound structures with depth-1 subexpressions
- Keep depth 2-4 for reasonable test cases

**Generate diverse cases:**
- Expressions: constants, variables, operations (`Int.Add`, `Bool.And`), conditionals
- Statements: commands (assign, assert, assume, havoc), control flow (if, loop, block)
- Bias towards operations over constants for interesting tests

**Key types from `Strata/Languages/Core/`:**
- `Expression.Expr` (Expressions.lean)
- `Statement` (Statement.lean)
- `Command` (atomic operations)
- `CoreIdent` (identifiers)

## Measurement Functions

Write **total** (not `partial`) Lean functions to measure program properties.

**Essential measurements:**
- Structural counts: calls, loops, if-statements, assertions, assumptions
- Size: AST node count for expressions/statements
- Variables: free variables, modified variables

**Design patterns:**
- Make compositional: `countX_stmt` for single, `countX_stmts` for lists (use fold)
- Test with `#guard` before using in properties
- Total functions are easier to reason about and use in proofs

## Property Categories

**Structural (universal):**
- Idempotence: `transform(transform(x)) = transform(x)`
- Size monotonicity: `size(transform(x)) ≤ size(x)`
- Variable preservation: `vars(transform(x)) ⊆ vars(x)`

**Transformation-specific:**
- CallElim: call count decreases or stays same
- LoopElim: loop count becomes zero
- DetToNondet: deterministic constructs eliminated

**Semantic (when feasible):**
- Evaluation equivalence: `eval(transform(x)) = eval(x)`
- Type preservation: `typeOf(transform(x)) = typeOf(x)`

**Algebraic laws (for optimizations):**
- Identity: `x * 1 = x`, `x + 0 = x`, `x && true = x`
- Annihilation: `x * 0 = 0`, `x || false = x`
- Conditionals: `if true then t else e = t`

**Property testing pattern:**
1. Generate random input
2. Measure property in original
3. Apply transformation
4. Measure property in result
5. Assert relationship holds

## Testing Workflow

**Run tests:** Use Plausible interface, configure test count, examine counterexamples
**Debug failures:** Plausible shrinks to minimal case → test manually → verify helpers → simplify further

## Key Files

| Component | Location |
|-----------|----------|
| Expression AST | `Strata/DL/Lambda/LExpr.lean` |
| Statement AST | `Strata/DL/Imperative/Stmt.lean` |
| Strata Core expressions | `Strata/Languages/Core/Expressions.lean` |
| Strata Core statements | `Strata/Languages/Core/Statement.lean` |
| Transformations | `Strata/Transform/*.lean` |
| Transform tests | `StrataTest/Transform/*.lean` |

## Implementation Checklist

1. Add Plausible dependency to lakefile
2. Create generators with depth control (2-4 levels)
3. Write total measurement functions, test with `#guard`
4. Define structural properties (idempotence, size, variables)
5. Add transformation-specific properties
6. Test algebraic laws for optimizations
7. Run tests, debug counterexamples, iterate

**Critical:** Always make generators depth-bounded and measurement functions total.

