---
description: "Review code for correctness, Lean patterns, and architecture"
argument-hint: "[--comment] [PR-number-or-URL] [files...]"
allowed-tools: ["Bash", "Read", "Agent", "Bash(gh pr comment:*)", "Bash(gh pr diff:*)", "Bash(gh pr view:*)", "Bash(gh pr checkout:*)"]
---

# Strata Code Review

Review the current diff (or specified files) for correctness bugs, Lean-specific pattern violations, and architectural issues. Reports findings inline by default; with `--comment` posts them as PR comments.

**Arguments:** "$ARGUMENTS"

## Setup

1. Parse arguments:
   - If `--comment` is present, output will be posted as a PR comment (via `gh pr comment`).
   - If a PR number or URL is given (e.g. `123` or `https://github.com/.../pull/123`), check out that PR first.
   - If file paths are given, scope the review to those files only.
   - Otherwise, review the full diff against the base branch.

2. Check out the PR if needed:
   - If a PR number/URL was provided and we are not already on that branch:
     1. Stash any uncommitted changes: `git stash`
     2. Check out the PR: `gh pr checkout <number>`
     3. Inform the user which branch we switched to.
   - If no PR number was given, stay on the current branch.

3. Determine the diff to review:
   - If on a feature branch: `git diff main...HEAD`
   - If there are unstaged changes: `git diff`
   - Prefer the branch diff unless the user specified files.

## Review Dimensions

Launch 4 parallel agents, each reviewing the same diff from a different angle:

### Agent 1: PR Consistency & Justification

Read the PR description (or commit messages if no PR exists). Then:
- Check whether every change in the diff is explained by or consistent with the stated purpose.
- Flag changes that appear unrelated, unjustified, or contradictory to the description.
- Flag if the description claims something that the diff does not actually accomplish.

### Agent 2: Contextual Correctness & Semantics

Read not just the diff but the surrounding code — callers, callees, sibling definitions, and the broader pipeline context. Then:
- Identify overlap or contradiction with existing code (duplicated logic, conflicting invariants).
- Think carefully about the semantics of the changes. Be skeptical — do not assume correctness.
- Identify edge cases and counterexamples where behavior is unspecified or ambiguous.
- Reason about how the changes interact with other parts of the pipeline. Try to construct concrete counterexamples when behavior is uncertain.
- Identify undocumented invariants and subtle assumptions the code relies on. These are valuable even if the code is correct today — they may drift out of sync later, and they are candidates for eventual formal proof. Flag them explicitly so the author can decide whether to document, assert, or prove them.
- Flag logic errors, off-by-one mistakes, incorrect pattern matches, dead code paths.
- Flag regressions: changes that break existing invariants visible in context.

### Agent 3: Test Coverage & Proof Opportunities

Look for:
- **Missing tests**: identify concrete test cases that should exist for the changed code but don't. Tests are always a necessity.
- **Proof opportunities**: look for places where a formal proof could integrate with existing semantics and definitions in the codebase. Proofs should not be trivial or invent new definitions — only suggest proofs that tie into existing structures.
- Note: proof opportunities may not always exist. Always suggest tests; suggest proofs only when they are meaningful.

### Agent 4: Lean-Specific Patterns (when applicable)

If the diff touches proof code or tactic blocks, look for:
- **Opacity violations**: `unfold`/`simp [X]` used on definitions from other modules that aren't marked `@[expose]`
- **Unnecessary hypotheses**: hypotheses added that aren't justified by a counter-example or call-site trace
- **Tactic style**: bare `simp` not closing a goal, `by ...` blocks that should be `have` blocks, auto-generated names used without `rename_i`
- **Proof structure**: proofs that fight module boundaries instead of proving lemmas where definitions are transparent
- **Naming**: auto-generated hypothesis names, unnamed `have` blocks, use of `this`

If the diff is purely code (no proofs), skip this agent.

### Agent 5: Architecture & Design

Look for:
- Coupling between modules that should be independent
- Definitions placed in wrong modules (e.g., a lemma about `Foo.bar` proved far from `bar`'s definition)
- Abstraction leaks: downstream code depending on implementation details
- Module boundary violations
- Large functions that should be decomposed
- Duplication that indicates a missing abstraction

## Scoring

Each agent scores findings on a 4-level scale:
- **Critical**: Definitely wrong, will cause failures or unsoundness
- **Important**: Very likely a problem, should be fixed before merge
- **Suggestion**: Could be improved, not blocking
- **Note**: Observation, no action needed

## Output

### If `--comment` is NOT present (default):

Print findings grouped by severity:

```markdown
## Review Summary

### Critical (N)
- [Correctness] Description — `file:line`
- [Lean] Description — `file:line`

### Important (N)
- [Architecture] Description — `file:line`

### Suggestions (N)
- [Lean] Description — `file:line`

### Verdict
<one-line summary: "Looks good" / "N issues to address before merge" / etc.>
```

### If `--comment` IS present:

1. Verify a PR exists for this branch: `gh pr view`
2. Format findings as above
3. Post via `gh pr comment --body "..."`

## Style Rules (all agents should watch for these)

- **Opacity changes**: Flag any change that increases visibility (`public`, `@[expose]`, removing `private`, etc.). These are sometimes needed but often not. If you can identify a concrete reason the change is necessary (e.g., a downstream module needs to unfold the definition), note the reason. Otherwise flag it as needing justification from the author.
- **Partial functions**: If a function becomes partial (e.g., uses `panic!`, `Option.get!`, `sorry`, incomplete match), flag it. Partial functions should be avoided. If one is introduced, there must be a comment explaining why totality is not achievable here, and that justification must be sound.
- **Inefficient patterns**: Flag list-building by repeated append in a loop (O(n^2)). Prefer cons + reverse, or Array operations.
- **Hard-coded constants**: Flag magic numbers or string literals that duplicate or relate to constants defined elsewhere in the codebase. Constants should be defined once and referenced. Look for subtle dependencies where two constants must stay in sync.
- **Axioms**: Immediately flag any introduction of `axiom`, `sorry`, `native_decide`, `Decidable.decide` on undecidable propositions, `unsafeCoerce`, or any other mechanism that introduces an unproven assumption into the trusted kernel. Also flag implicit axioms: uses of `Classical.choice` or `propext` where constructive alternatives exist, and any pattern where totality or termination is bypassed (`partial def`, `decreasing_by sorry`). These are always Critical-severity findings.

## Guidelines

- Be precise: cite file paths and line numbers for every finding.
- No false positives: if uncertain, downgrade to Suggestion or omit.
- No style nitpicks unless they violate the rules above or the Lean proof rules.
- Don't flag things a type checker or `lake build` would catch (type errors, syntax).
- Don't flag pre-existing issues outside the diff.
- Keep output concise. One sentence per finding.
