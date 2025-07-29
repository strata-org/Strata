Thank you for your interest in contributing to Strata! We greatly value
feedback and contributions from the community. Please read this
document before submitting any [pull
requests](#submitting-a-pull-request) or [issues](#filing-an-issue).

# Style Rationale

We aim for Strata to be both highly trustworthy and widely adopted. To
facilitate this, we have several subsidiary goals.

* **Allow multiple implementations.** These could be in other ITPs or
standard programming languages. In particular, we would like it to be
easy to generate Strata code from front ends written in other languages.

* **Lower barriers to contribution.** We would like contribution from a
broad community of users, and don't want to insist that they write Lean
code. And, if they write Lean code, we don't want it to need to use the
most complex features of the language.

* **Enable verification of production tools.** Ultimately, the code for
Strata is a tool implementation rather than an academic formalization.
Any verification we do is to convince ourselves that our tools are correct
Therefore, the primary artifacts are the executable definitions, which
should form the basis for a usable tool.

These goals lead us to limit the use of certain Lean constructs, and to
clearly separate implementation from proof.

## Semantic Style Guidelines

### Avoid Partial Functions

When writing programs, rather than proofs, it can be tempting to use
`partial` functions. In some cases, for top-level code that handles
system interaction, file I/O, concurrency, and similar functionality,
this can be okay. However, because we aim for it to be possible to
verify core functionality, we prefer that operations over programs or
terms -- such as transformation, verification condition generation, or
testing -- be total functions that can, at least in principle, be the
subject of proof.

In some cases, however, it may be valuable to prove properties of code
that may, in fact, not terminate. For this use case, we prefer the use
of `partial_fixpoint` instead of `partial`, and to structure the code
such that `partial_fixpoint` is possible.

### Produce Feedback on Failure

To avoid partial functions, it is sometimes necessary to allow functions
to indicate failure or the lack of a useful result.  When constructing
formal semantics and other purely proof-oriented developments, making
things as concise as possible is often the goal, and the `Option` type
is the simplest way to make a partial function total.

When producting a tool for production use, however, helpful feedback is
critical. Because of this, we prefer using failure types that carry
information about what went wrong. So, for instance, a type checker
should have a return type that includes an error message indicating what
went wrong in the case where its input is not well-typed.

For example, consider a function to calculate the median of a list of
numbers. Although there are calculations to get around this, let's
assume this is only well-defined for lists of odd length. We might write
something like:

```lean
def median (xs : List Int) : String ⊕ Int :=
  if xs.length = 0 then .inl "Empty list"
  else if xs.length % 2 = 0 then .inl "List of even size"
  else .inr (List.mergeSort xs)[xs.length / 2]!
```

In principle, both error cases could be handled by the `xs.length % 2 =
0` check. When optimizing for a production implementation, however, it
can be useful to provide different feedback for an empty list.

### Prefer Extrinsic Proofs

Given the `median` function above, we may want to know that it always
produces an `Int` given a list of even size. We could have included a
precondition that the list has even size, avoiding the need for error
handling, but that would have precluded the possibility of providing
useful feedback in the case of working with unfiltered input.

However, if we happen to know we're working with a list of odd size,
we can write a theorem that shows that `median` will always return an
`Int` value.

```lean
theorem medianOddRight
  (xs : List Int)
  (isOdd : ¬ (xs.length % 2 = 0)) :
  (median xs).isRight := by
  unfold median
  if h1: xs.length = 0 then
    simp [h1] at isOdd
  else if h2: xs.length % 2 = 0 then
    simp [h1, h2, isOdd]; contradiction
  else simp [h1, h2]
```

### Wrap Feedback-Producing Functions for Proof

When doing proofs, it's often the case that you only care whether a
function succeeded or failed, and not why, so the extra information in
the implementation can clutter things up.

```lean
def median' (xs : List Int) (isOdd : ¬ (xs.length % 2 = 0)) : Int :=
  let res := median xs
  have right : res.isRight := medianOddRight xs isOdd
  match res with
  | .inl s => by simp at right
  | .inr m => m
```

### Write Tests for Your Code

We encourage contributors to test their code, even if it is
verified. Strata's Lean code extensively uses `#guard_msgs` for three
main purposes:

* For unit tests immediately after somewhat complicated functions
  (e.g., type unification, etc.). These indicate -- sooner rather than
  later -- if/when any changes break core functionality. They also aid
  in code comprehension by providing usage examples.

* For higher-level tests, e.g., in the `StrataTest` directory, which
  does not contain an end-to-end Strata application but tests for core
  components (e.g., just the DDM, just the partial evaluator of a
  specific dialect, etc.). These tests serve as guides to understand
  how to set up, use, and compose these core components.

* In the `Examples` directories (e.g.,
  `Strata/Languages/[Boogie|C_Simp]/Examples`), which showcase
  end-to-end Strata applications and may include output from external
  solvers.

## Syntactic Style Guidelines

### Naming Conventions

* File names should be in `UpperCamelCase.<extension>`.
* Function names should use `lowerCamelCase`.
* Type names (e.g., inductive types, structures, etc.) should use
  `UpperCamelCase`.
* Proofs and theorem names should use `snake_case`.

### Line Length

Keep lines under 80 characters, never exceeding 100 characters.

### File Organization

The file header should contain:
* the copyright information,
* a list of all authors and contributors to the file.

All imports should be done immediately after this header. All files
should have a module docstring (`/-!  ... -/`) immediately following
the imports, like so:

```
/-!
# Title

In this file, we define... and prove...

## Main Results
...
-/
```

We recommend using `section`s or `namespace`s for code
organization. Using a visual separator (e.g., an 80-character line
formed by `-`) is also acceptable. The use of module docstring for
sectioning comments, with appropriate levels of headings, is strongly
encouraged.

### Documentation Style

Every major function and theorem must be documented (NOTE: use `/--
... -/` and NOT `/- ... -/`). Use backticks to format code or math
expressions in the docstring (e.g., `x + y`).

Describe implementation-level details in single- (`--`) or multi-line
comments (`/- .. -/`) interspersed with the code.

# Submitting a Pull Request

* **Focused Changes**: Create small, focused PRs that address a single
issue or implement a specific feature.

* **Maintainable Proofs**: Write any proofs in a maintainable way,
even if doing so causes them to become more verbose. Strata follows the
***no nonterminal `simp`*** rule, which says that unless `simp` is
closing the goal, it should always be converted to a `simp only [X, Y,
Z]` call.

* **External Dependencies**: Do not introduce any new external
dependencies into the codebase -- be mindful of what you
import. Exceptions are possible, but only when absolutely necessary.

* **Documentation**: Add relevant documentation and comments to your
code. Please refer to the [Syntactic Style
Guidelines](#syntactic-style-guidelines).

# Filing an Issue

When filing an issue, first check whether the same issue has already
been reported previously by someone else. In your issue, include
details like:

* Illustrative, minimal, and reproducible test cases
* Commit hash of Strata that you used
* Suggested modifications, if any

# What to Expect

* **Be Patient**: Reviewing your contribution may take some time!
   The necessary conditions for a PR to the `main` branch to be merged are:
    - All CI checks must pass on your PR.
    - No changes must be requested.
    - All conversations must be resolved.
    - Approval from at least two Strata maintainers is required.

* **Not All PRs Get Merged**: We value every contribution. However, to
enable code maintainability and quality, we will merge only those PRs
that align with our priorities and goals.

* **Work in Progress**: Strata is under development and things can
change rapidly.
