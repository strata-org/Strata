---
inclusion: always
---

# Writing Proofs for Strata

## Process Overview

**Basic three-step process:**
1. **Write informal hierarchical proof** (as Lean comments)
2. **Create Lean template with sorry's** for key intermediate results
3. **Fill in the sorry's** to complete the formal proof

**Extended four-step process** (when intermediate results need induction):
1. **Write informal hierarchical proof** - identify which steps need induction
2. **Create initial template** - mark where separate lemmas are needed
3. **Add separate lemmas** - create lemmas for facts requiring induction
4. **Fill in all sorry's** - complete both helper lemmas and main theorem

## Informal Proof Style

Use hierarchical structure with Lean-inspired keywords:

### Keywords

- `suffices assume ... show ...` - reduce goal
- `obtain ... with ...` - introduce witness
- `case` - proof by cases
- `done` - final step proving the goal
- `by` - justification

### Structure

```lean
/-
Theorem: Statement of theorem

Proof:
  1. First major step
     by justification
  
  2. Second major step
     2.1. Substep
          by justification
     2.2. Another substep
          by justification
     2.3. done
          by 2.1 and 2.2
  
  3. done
     by 1 and 2
-/
theorem name : statement := by
  -- Formal Lean proof here
```

## Complete Example: List Length and Append

### Step 1: Informal Hierarchical Proof

```lean
/-
Theorem: For all lists xs and ys, length(append(xs, ys)) = length(xs) + length(ys)

Proof: By induction on xs.

  Base case (xs = nil):
    1. append(nil, ys) = ys
       by definition of append
    
    2. length(append(nil, ys)) = length(ys)
       by 1
    
    3. length(nil) + length(ys) = 0 + length(ys) = length(ys)
       by definition of length
    
    4. done
       by 2 and 3

  Inductive case (xs = cons x xs'):
    Assume: length(append(xs', ys)) = length(xs') + length(ys)  [IH]
    
    1. append(cons x xs', ys) = cons x (append(xs', ys))
       by definition of append
    
    2. length(append(cons x xs', ys)) = length(cons x (append(xs', ys)))
       by 1
    
    3. length(cons x (append(xs', ys))) = 1 + length(append(xs', ys))
       by definition of length
    
    4. 1 + length(append(xs', ys)) = 1 + (length(xs') + length(ys))
       by IH
    
    5. 1 + (length(xs') + length(ys)) = (1 + length(xs')) + length(ys)
       by arithmetic
    
    6. 1 + length(xs') = length(cons x xs')
       by definition of length
    
    7. done
       by 2, 3, 4, 5, 6
-/
```

### Step 2: Lean Template with sorry's

The Lean template should mirror the structured natural language proof. Each major step in the informal proof becomes a `have` statement or tactic application, with `sorry` for non-trivial intermediate results.

```lean
-- Simple list type for demonstration
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

def length {α : Type} : MyList α → Nat
  | .nil => 0
  | .cons _ tail => 1 + length tail

def append {α : Type} : MyList α → MyList α → MyList α
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (append xs ys)

theorem length_append {α : Type} (xs ys : MyList α) : 
  length (append xs ys) = length xs + length ys := by
  -- Proof by induction on xs
  induction xs with
  | nil =>
    -- Base case: xs = nil
    -- Step 1: append(nil, ys) = ys by definition
    have h1 : append .nil ys = ys := sorry
    -- Step 2-4: Conclude the base case
    sorry
  | cons x xs' ih =>
    -- Inductive case: xs = cons x xs'
    -- IH: length(append(xs', ys)) = length(xs') + length(ys)
    
    -- Step 1: append(cons x xs', ys) = cons x (append(xs', ys))
    have h1 : append (.cons x xs') ys = .cons x (append xs' ys) := sorry
    
    -- Step 2-3: length of the result
    have h2 : length (append (.cons x xs') ys) = 1 + length (append xs' ys) := sorry
    
    -- Step 4: Apply IH
    have h3 : 1 + length (append xs' ys) = 1 + (length xs' + length ys) := sorry
    
    -- Step 5-7: Arithmetic and conclude
    sorry
```

### Step 3: Fill in the sorry's

Now fill in each `sorry` with the actual proof. The structure remains the same, but we replace placeholders with real tactics.

```lean
-- Simple list type for demonstration
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

def length {α : Type} : MyList α → Nat
  | .nil => 0
  | .cons _ tail => 1 + length tail

def append {α : Type} : MyList α → MyList α → MyList α
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (append xs ys)

theorem length_append {α : Type} (xs ys : MyList α) : 
  length (append xs ys) = length xs + length ys := by
  -- Proof by induction on xs
  induction xs with
  | nil =>
    -- Base case: xs = nil
    -- Steps 1-4: Simplify using definitions
    simp [append, length]
  | cons x xs' ih =>
    -- Inductive case: xs = cons x xs'
    -- IH: length(append(xs', ys)) = length(xs') + length(ys)
    
    -- Steps 1-3: Simplify using definitions
    simp [append, length]
    -- Step 4: Apply IH
    rw [ih]
    -- Steps 5-7: Arithmetic
    omega
```

## Example with Separate Lemma: When Intermediate Result Needs Induction

This example shows a **four-step process** when you discover an intermediate result needs induction.

### Step 1: Informal Proof

```lean
/-
Theorem: For all lists xs, reverse(reverse(xs)) = xs

Proof: By induction on xs.

  Base case (xs = nil):
    1. reverse(nil) = nil
       by definition
    2. reverse(reverse(nil)) = reverse(nil) = nil
       by 1
    3. done

  Inductive case (xs = cons x xs'):
    Assume: reverse(reverse(xs')) = xs'  [IH]
    
    1. reverse(cons x xs') = append(reverse(xs'), cons x nil)
       by definition of reverse
    
    2. reverse(reverse(cons x xs')) = reverse(append(reverse(xs'), cons x nil))
       by 1
    
    3. reverse(append(ys, zs)) = append(reverse(zs), reverse(ys))  [LEMMA - needs induction!]
       by separate lemma (requires induction on ys)
    
    4. reverse(append(reverse(xs'), cons x nil)) = 
       append(reverse(cons x nil), reverse(reverse(xs')))
       by 3
    
    5. reverse(cons x nil) = cons x nil and reverse(reverse(xs')) = xs'
       by definition and IH
    
    6. append(cons x nil, xs') = cons x xs'
       by definition of append
    
    7. done
       by 2, 4, 5, 6
-/
```

### Step 2: Initial Template (without helper lemma)

Start with the template for the main theorem. Notice we need a fact but don't have it yet:

```lean
theorem reverse_reverse {α : Type} (xs : MyList α) :
  reverse (reverse xs) = xs := by
  induction xs with
  | nil =>
    -- Base case
    sorry
  | cons x xs' ih =>
    -- Inductive case
    -- IH: reverse(reverse(xs')) = xs'
    
    -- Step 1-2: Unfold definitions
    have h1 : reverse (.cons x xs') = append (reverse xs') (.cons x .nil) := sorry
    have h2 : reverse (reverse (.cons x xs')) = 
              reverse (append (reverse xs') (.cons x .nil)) := sorry
    
    -- Step 3: We need reverse(append(ys, zs)) = append(reverse(zs), reverse(ys))
    -- The informal proof says this requires induction - we need a separate lemma!
    have h3 : reverse (append (reverse xs') (.cons x .nil)) = 
              append (reverse (.cons x .nil)) (reverse (reverse xs')) := 
      sorry  -- TODO: This needs a separate lemma with induction
    
    -- Steps 4-7: Simplify and conclude
    sorry
```

### Step 3: Add the Separate Lemma

Recognize that step 3 needs induction, so create a separate lemma:

```lean
-- Helper lemma that requires induction - discovered we need this!
theorem reverse_append {α : Type} (xs ys : MyList α) :
  reverse (append xs ys) = append (reverse ys) (reverse xs) := by
  sorry  -- This needs its own induction proof

theorem reverse_reverse {α : Type} (xs : MyList α) :
  reverse (reverse xs) = xs := by
  induction xs with
  | nil =>
    -- Base case
    sorry
  | cons x xs' ih =>
    -- Inductive case
    -- IH: reverse(reverse(xs')) = xs'
    
    -- Step 1-2: Unfold definitions
    have h1 : reverse (.cons x xs') = append (reverse xs') (.cons x .nil) := sorry
    have h2 : reverse (reverse (.cons x xs')) = 
              reverse (append (reverse xs') (.cons x .nil)) := sorry
    
    -- Step 3: Apply the separate lemma (which requires induction)
    have h3 : reverse (append (reverse xs') (.cons x .nil)) = 
              append (reverse (.cons x .nil)) (reverse (reverse xs')) := 
      reverse_append (reverse xs') (.cons x .nil)
    
    -- Steps 4-7: Simplify and conclude
    sorry
```

### Step 4: Fill in All sorry's

Now complete both the helper lemma and the main theorem:

```lean
-- Helper lemma - proved separately with its own induction
theorem reverse_append {α : Type} (xs ys : MyList α) :
  reverse (append xs ys) = append (reverse ys) (reverse xs) := by
  induction xs with
  | nil =>
    simp [append, reverse]
    -- Need to show: reverse ys = append (reverse ys) nil
    sorry  -- Would need append_nil lemma
  | cons x xs' ih =>
    simp [append, reverse]
    rw [ih]
    -- Need associativity of append
    sorry  -- Would need append_assoc lemma

theorem reverse_reverse {α : Type} (xs : MyList α) :
  reverse (reverse xs) = xs := by
  induction xs with
  | nil =>
    simp [reverse]
  | cons x xs' ih =>
    simp [reverse]
    rw [reverse_append]  -- Use the separate lemma
    simp [reverse, ih]
```

## Another Example: Case Splitting

### Step 1: Informal Proof

```lean
/-
Theorem: For all natural numbers n and m, max(n, m) = max(m, n)

Proof: By cases on whether n ≤ m.

  Case 1 (n ≤ m):
    1. max(n, m) = m
       by definition of max when n ≤ m
    
    2. m ≥ n, so max(m, n) = m
       by definition of max when m ≥ n
    
    3. done
       by 1 and 2

  Case 2 (n > m):
    1. max(n, m) = n
       by definition of max when n > m
    
    2. n > m means m < n, so max(m, n) = n
       by definition of max when m < n
    
    3. done
       by 1 and 2
-/
```

### Step 2: Template with sorry's

```lean
theorem max_comm (n m : Nat) : max n m = max m n := by
  -- Proof by cases on n ≤ m
  cases Nat.le_total n m with
  | inl h_le =>
    -- Case 1: n ≤ m
    -- Step 1: max(n, m) = m
    have h1 : max n m = m := sorry
    -- Step 2: max(m, n) = m
    have h2 : max m n = m := sorry
    -- Step 3: Conclude
    sorry
  | inr h_ge =>
    -- Case 2: m ≤ n (equivalently, n ≥ m)
    -- Step 1: max(n, m) = n
    have h1 : max n m = n := sorry
    -- Step 2: max(m, n) = n
    have h2 : max m n = n := sorry
    -- Step 3: Conclude
    sorry
```

### Step 3: Fill in sorry's

```lean
theorem max_comm (n m : Nat) : max n m = max m n := by
  -- Proof by cases on n ≤ m
  cases Nat.le_total n m with
  | inl h_le =>
    -- Case 1: n ≤ m
    simp [max, h_le]
    have h_ge : m ≥ n := h_le
    simp [max, h_ge]
  | inr h_ge =>
    -- Case 2: m ≤ n
    have h_not_le : ¬(n ≤ m) := Nat.not_le.mpr (Nat.lt_of_le_of_ne h_ge (Ne.symm ·))
    simp [max, h_not_le, h_ge]
```

## Guidelines

**Use hierarchical structure when helpful:**
- Simple proofs: Just write the intuition
- Complex proofs: Number steps (1, 2, 3, ...)
- Very complex: Add substeps (2.1, 2.2, ...)

**Justifications:**
- Explain why each step follows
- Reference previous steps when useful
- Cite theorems/definitions used

**Template with sorry's:**
- Each major step in the informal proof should appear in the template
- Use `have` statements for simple intermediate results
- Create separate lemmas for complex intermediate results, especially those requiring induction
- **Rule of thumb**: If the informal proof says "by induction", make it a separate lemma
- The template structure should mirror the informal proof
- This makes it clear what needs to be proved and helps catch gaps

**Using `plausible` instead of `sorry`:**
- Where possible, use the `plausible` tactic instead of `sorry` in templates
- `plausible` attempts to find counterexamples to false statements
- This helps catch logical errors early - if `plausible` finds a counterexample, your assertion is wrong!
- If `plausible` succeeds (no counterexample found), it doesn't prove the statement but gives confidence
- Use `sorry` only when `plausible` is not applicable (e.g., for propositions without decidable instances)

**Choosing between `have` and separate lemmas:**
- Use `have` for: definitional equalities, simple rewrites, direct applications of existing lemmas
- Use separate lemmas for: results requiring induction, complex case analysis, reusable facts
- When in doubt, prefer separate lemmas for better modularity and reusability

**Be flexible:**
- Don't force structure on trivial proofs
- Add detail where reasoning is subtle
- Use keywords (`suffices`, `obtain`, `case`) when they clarify

**When to add detail:**
- When a step isn't obvious
- When there might be a gap
- When the reasoning is the interesting part

## Workflow

1. **Write informal proof first** - Think through the logic, identify cases and induction structure
2. **Create Lean template** - Translate structure to Lean with `plausible` or `sorry` for non-trivial steps
3. **Check template compiles** - Verify the structure is correct before filling in proofs
   - If `plausible` finds a counterexample, your assertion is wrong - revisit the informal proof!
4. **Fill in sorry's/plausibles** - Replace each placeholder with actual tactics
5. **Iterate** - If a step fails, revisit the informal proof

## Benefits

- Catches logical gaps before writing Lean
- Makes proof structure clear
- Template with sorry's ensures the proof architecture is sound
- Easier to debug when Lean proof fails
- Documents proof strategy for readers
- Allows incremental development (template first, then fill in)

## Key Points

- **Write informal proof first** - Think through the logic before coding
- **Create template that mirrors informal proof** - Each major step should be visible
- **Use `plausible` or `sorry` strategically** - Mark non-trivial intermediate results
  - Prefer `plausible` to catch false assertions early via counterexamples
  - Fall back to `sorry` when `plausible` is not applicable
- **Choose `have` vs separate lemmas wisely**:
  - `have` for simple facts (definitional equalities, direct lemma applications)
  - Separate lemmas for facts requiring induction or complex proofs
  - If informal proof says "by induction", make it a separate lemma
- **Add structure when it helps** - Use numbering for complex proofs
- **Justify non-obvious steps** - Explain the reasoning
- **Be flexible** - Don't force structure on simple proofs

## Quick Reference: `have` vs Separate Lemma

| Use `have` when... | Use separate lemma when... |
|-------------------|---------------------------|
| Follows by definition | Requires induction |
| Simple rewrite | Complex case analysis |
| Direct application of existing lemma | Reusable across multiple proofs |
| One-line proof | Multi-step proof |
| Only used once in this proof | General fact worth naming |

**Example decision process:**
- "We need: `append xs nil = xs`" → Check informal proof
- Informal says "by induction on xs" → **Separate lemma**
- Informal says "by definition of append" → **`have` statement**

The goal: Make it harder to prove things that aren't true by thinking through the logic explicitly, and make the proof development process incremental and manageable.
