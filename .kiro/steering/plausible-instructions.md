---
inclusion: fileMatch
fileMatchPattern: ['**/StrataTest/**/*.lean', '**/Examples/**/*.lean']
---

# Plausible Property-Based Testing

Use Plausible for property-based testing in Strata test files. It finds counter-examples to propositions by generating random test cases.

## When to Use

- Testing transformation correctness properties (e.g., `DetToNondetCorrect.lean`, `CallElimCorrect.lean`)
- Validating semantic equivalences between program representations
- Testing expression evaluation properties (Lambda, Imperative dialects)
- Verifying type system properties
- Quick sanity checks before formal proofs

## Required Type Class Instances

For custom types to work with Plausible, implement these three instances:

1. **`Repr α`** - String representation (use `deriving Repr` when possible)
2. **`Shrinkable α`** - Reduces counter-examples to minimal cases
3. **`Arbitrary α`** - Random value generator

## Implementation Patterns

### Simple Algebraic Types
Use automatic derivation:
```lean
inductive MyType where
  | case1 : Nat → MyType
  | case2 : Bool → MyType
  deriving Repr, Arbitrary
```

### Dependent Types with Invariants
Manually implement instances to maintain invariants:
```lean
structure BoundedNat where
  val : Nat
  h : val < 100
  deriving Repr

instance : Shrinkable BoundedNat where
  shrink := fun ⟨n, _⟩ =>
    (Shrinkable.shrink n).filterMap fun n' =>
      if h : n' < 100 then some ⟨n', h⟩ else none

instance : Arbitrary BoundedNat :=
  ⟨do
    let n ← SampleableExt.interpSample (Fin 100)
    return ⟨n.val, n.isLt⟩⟩
```

### Product Types
Shrink components independently:
```lean
instance : Shrinkable (α × β) where
  shrink := fun (a, b) =>
    (Shrinkable.shrink a).map (·, b) ++
    (Shrinkable.shrink b).map (a, ·)
```

### Strata-Specific Types
For Lambda expressions, Imperative statements, or Boogie constructs, ensure generators produce well-typed, valid AST nodes.

## Usage Modes

### Tactic Mode (Preferred)
```lean
example (xs ys : Array Nat) : xs.size = ys.size → xs = ys := by
  plausible  -- Finds: xs := #[0], ys := #[1]
```

### Programmatic Mode
```lean
#eval Testable.check <| ∀ (x y : Nat), x + y = y + x  -- Success
```

### Configuration
```lean
example (a b : Bool) : a = b := by
  plausible (config := {quiet := true, numInst := 1000})
```

## Testing Workflow

1. **Write property** as a Lean proposition
2. **Add Plausible instances** for custom types (if needed)
3. **Run test** with `plausible` tactic or `#eval Testable.check`
4. **Interpret results**:
   - Counter-example found → property is false
   - Success → property likely holds (not a proof)
   - Use counter-examples to refine properties or fix bugs

## Common Pitfalls

- **Missing instances**: Ensure `Repr`, `Shrinkable`, and `Arbitrary` are all implemented
- **Invalid generators**: Generators must respect type invariants (use guards or filtered generation)
- **Non-decidable properties**: Plausible requires decidable propositions
- **Over-constrained shrinking**: Shrinking should preserve the counter-example property

## Integration with Strata

- Place property tests in `StrataTest/` mirroring the `Strata/` structure
- Test transformation correctness before attempting formal proofs
- Use Plausible to validate semantic preservation properties
- Generate test cases for edge cases in dialect implementations
