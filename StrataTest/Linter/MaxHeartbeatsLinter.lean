/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/- Import an ordinary Strata module rather than the linter directly.
The maxHeartbeats linter becomes active transitively via `Strata.Init`
(every leaf module `public import`s it) rather than from a direct linter import.-/
import Strata.DL.Util.Counter

/-! Tests for the maxHeartbeats linter: overrides must be scoped with `in` and followed by a
comment explaining why they are needed. -/

set_option linter.strata.maxHeartbeats true

namespace Strata.Linter.MaxHeartbeatsTest

-- Scoped with `in` and followed by a line comment: accepted.
#guard_msgs in
set_option maxHeartbeats 400000 in
-- This budget is needed for the test.
theorem scopedWithComment : True := trivial

-- A block comment is accepted too, also on the same line as `in`.
#guard_msgs in
set_option maxHeartbeats 400000 in /- This budget is needed for the test. -/
theorem scopedWithBlockComment : True := trivial

-- `synthInstance.maxHeartbeats` is covered as well.
#guard_msgs in
set_option synthInstance.maxHeartbeats 40000 in
-- This budget is needed for the test.
theorem scopedSynthInstanceWithComment : True := trivial

-- Scoped but without a comment: rejected.
/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 400000 in
theorem scopedWithoutComment : True := trivial

-- `synthInstance.maxHeartbeats` without a comment: rejected.
/--
error: `set_option synthInstance.maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 40000 in
theorem scopedSynthInstanceWithoutComment : True := trivial

-- The tactic form is checked too.
/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
theorem tacticWithoutComment : True := by
  set_option maxHeartbeats 400000 in
  trivial

#guard_msgs in
theorem tacticWithComment : True := by
  set_option maxHeartbeats 400000 in
  -- This budget is needed for the test.
  trivial

-- In the middle of a longer tactic proof, after other tactics and before further ones.
/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
theorem midProofWithoutComment (p : Prop) (h : p) : p ∧ True := by
  constructor
  · set_option maxHeartbeats 400000 in
    exact h
  · trivial

#guard_msgs in
theorem midProofWithComment (p : Prop) (h : p) : p ∧ True := by
  constructor
  · set_option maxHeartbeats 400000 in
    -- This budget is needed for the test.
    exact h
  · trivial

-- Term mode.
/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
theorem termWithoutComment : True ∧ True :=
  ⟨(set_option maxHeartbeats 400000 in trivial), trivial⟩

#guard_msgs in
theorem termWithComment : True ∧ True :=
  ⟨(set_option maxHeartbeats 400000 in -- This budget is needed for the test.
    trivial), trivial⟩

-- A docstring on the wrapped declaration justifies the override.
#guard_msgs in
set_option maxHeartbeats 400000 in
/-- This budget is needed for the test. -/
theorem withDocstring : True := trivial

-- Chained `set_option ... in`: the comment may follow a later `in` of the chain.
#guard_msgs in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 1000 in
-- This budget is needed for the test.
theorem chainedWithComment : True := trivial

#guard_msgs in
set_option maxRecDepth 1000 in
set_option maxHeartbeats 400000 in
-- This budget is needed for the test.
theorem chainedOtherOrder : True := trivial

#guard_msgs in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 1000 in
/-- This budget is needed for the test. -/
theorem chainedWithDocstring : True := trivial

-- A chain without any comment is still rejected.
/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 1000 in
theorem chainedWithoutComment : True := trivial

-- An empty comment does not justify the override.
/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 400000 in --
theorem emptyLineComment : True := trivial

/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 400000 in /-  -/
theorem emptyBlockComment : True := trivial

-- Unscoped (no `in`): rejected, since it would affect every later declaration.
/--
error: Unscoped `set_option maxHeartbeats` is not allowed: it affects every later declaration.
Raising the heartbeat budget usually means the proof is inefficient. Prefer refactoring it so that the default budget suffices. If that is unavoidable, scope the option to the individual definition or theorem that needs it and comment why:
```
set_option maxHeartbeats N in
-- comment explaining why this is necessary
theorem ... := ...
```

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 400000

-- A comment after an unscoped option does not make it acceptable.
/--
error: Unscoped `set_option maxHeartbeats` is not allowed: it affects every later declaration.
Raising the heartbeat budget usually means the proof is inefficient. Prefer refactoring it so that the default budget suffices. If that is unavoidable, scope the option to the individual definition or theorem that needs it and comment why:
```
set_option maxHeartbeats N in
-- comment explaining why this is necessary
theorem ... := ...
```

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 400000
-- A comment does not help here.

-- Other options are left alone, including the linter's own option.
#guard_msgs in
set_option maxRecDepth 1000 in
theorem otherOption : True := trivial

#guard_msgs in
set_option linter.strata.maxHeartbeats true in
theorem linterOption : True := trivial

-- The linter can be disabled.
section
set_option linter.strata.maxHeartbeats false

#guard_msgs in
set_option maxHeartbeats 400000 in
theorem disabled : True := trivial
end

-- An inline `set_option linter.strata.maxHeartbeats false in` silences the linter for the
-- `maxHeartbeats` override it wraps (it must come before the override in the chain), whether that
-- override is scoped or not, and does not leak to later commands.
#guard_msgs in
set_option linter.strata.maxHeartbeats false in
set_option maxHeartbeats 400000 in
theorem inlineDisabled : True := trivial

#guard_msgs in
set_option linter.strata.maxHeartbeats false in
set_option maxHeartbeats 400000

-- Disabling the linter inside the override does not help: the override is checked with the
-- options in effect where it appears.
/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 400000 in
set_option linter.strata.maxHeartbeats false in
theorem disabledAfterOverride : True := trivial

/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 400000 in
theorem notLeaked : True := trivial

-- Inside a tactic proof.
#guard_msgs in
theorem inlineDisabledTactic : True := by
  set_option linter.strata.maxHeartbeats false in
  set_option maxHeartbeats 400000 in
  trivial

-- An inline `set_option linter.strata.maxHeartbeats true in` enables the linter for that one
-- command even when it is off for the surrounding section.
section
set_option linter.strata.maxHeartbeats false

#guard_msgs in
set_option maxHeartbeats 400000 in
theorem offInSection : True := trivial

/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option linter.strata.maxHeartbeats true in
set_option maxHeartbeats 400000 in
theorem inlineEnabled : True := trivial

#guard_msgs in
set_option linter.strata.maxHeartbeats true in
set_option maxHeartbeats 400000 in
-- This budget is needed for the test.
theorem inlineEnabledWithComment : True := trivial
end

-- `linter.all` is resolved the way Lean resolves it: it sets the default for a linter that has no
-- explicit setting, and an explicit `linter.strata.maxHeartbeats` wins over it.
/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option linter.all false in
set_option linter.strata.maxHeartbeats true in
set_option maxHeartbeats 400000 in
theorem allFalseExplicitTrueInline : True := trivial

-- Explicit `false` wins over `linter.all true`.
section
set_option linter.strata.maxHeartbeats false

#guard_msgs in
set_option linter.all true in
set_option maxHeartbeats 400000 in
theorem explicitFalseBeatsAllTrue : True := trivial
end

-- Only overrides that raise the budget are flagged: lowering it, e.g. to make a test fail
-- fast, or keeping the default, is fine.
#guard_msgs in
set_option maxHeartbeats 1000 in
theorem lowered : True := trivial

#guard_msgs in
set_option maxHeartbeats 200000 in
theorem sameAsDefault : True := trivial

#guard_msgs in
set_option synthInstance.maxHeartbeats 1000 in
theorem loweredSynthInstance : True := trivial

-- Lowering globally is harmless as well. The section keeps the lowered budget from leaking into
-- the rest of the file.
section
#guard_msgs in
set_option maxHeartbeats 1000
end

-- Just above the default is flagged, as is `0` (unlimited).
/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 200001 in
theorem justAboveDefault : True := trivial

/--
error: `set_option maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 0 in
theorem unlimited : True := trivial

-- `synthInstance.maxHeartbeats` is compared with its own default (20000).
/--
error: `set_option synthInstance.maxHeartbeats` suggests an inefficient proof. Prefer refactoring it so that the default heartbeat budget suffices. If that is unavoidable, add a comment right after `in` explaining why the larger budget is necessary.

Note: This linter can be disabled with `set_option linter.strata.maxHeartbeats false`
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 30000 in
theorem synthInstanceAboveDefault : True := trivial

end Strata.Linter.MaxHeartbeatsTest
