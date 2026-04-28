# Denotational Semantics

## 1. What Exists Right Now

### a. SMT Denotation

- denoteTerm (and similar) — interpret a term based on context
- denoteQuery — universally quantifies all free variables, uninterpreted functions, etc. and returns a single Lean Prop
- translateTerm, translateQuery — syntactic translation to produce Lean expressions for proving goals
- gen_smt_vcs — transforms these into idiomatic Lean expressions using definitional equality with the SMT denotation (uses native_decide to bridge the gap)

### b. Lambda Denotation

- Structured differently from SMT: parameterized by interpretations (e.g. for functions, types) and valuations (free variables and type variables)
- Conditions on interpretations for concrete functions (must agree with body), built-in functions with evaluator, and datatypes
- Polymorphism means we have to thread through the type variable valuations, which may not definitionally reduce

### c. Major Differences Between SMT and Lambda

1. Factory in Lambda vs builtins in SMT
2. Polymorphism (likely to cause definitional equality problems)
3. Concrete functions (including recursive functions)
4. Datatypes
5. bool denotes to Bool, so we need Classical.propDecidable

## 2. What We Want

Something similar to SMT proof goals but for Lambda — an idiomatic Lean translation of goals. Most likely: a version of Lambda semantics similar to denoteQuery + a proof of equivalence with the existing semantics (validity).

### Considerations

1. No longer just a single Lean expression: we also want definitions of concrete functions in the Factory + datatypes
2. The idea is to show that these generated functions/datatypes (or user-provided ones) are consistent (satisfy certain properties)
   - Will need to show that definitions are unique up to isomorphism so that this suffices to prove validity
3. No longer just definitional equality: will need proof scripts to prove these properties
4. For factories, probably use typeclasses to say that the Factory includes the standard int/bool operations (everything defined via concreteEval), so we don't reason about concreteEval directly — we can't deal with concreteEval via metaprogramming in general, since it is an arbitrary Lean 
function, not syntax

### Key Challenges

1. Getting Lean definitional equality / metaprogramming to work (limited experience here)
2. Proving equivalence between versions of semantics
3. Polymorphism
4. Showing isomorphism results (fine in theory, getting it to work in Lean will be annoying)