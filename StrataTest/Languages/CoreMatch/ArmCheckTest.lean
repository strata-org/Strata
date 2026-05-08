/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.CoreMatch.CoreMatch
import Strata.Languages.CoreMatch.ArmCheck

/-!
Tests for the `ArmCheck` redundancy and exhaustiveness checker. They
cover every `ArmIssue` constructor plus the positive cases of full
constructor coverage and a wildcard covering the missing arms.
-/

open Strata.CoreMatch
open Strata.CoreMatch.ArmCheck
open Lambda

namespace CoreMatchArmCheckTest

private def colorCtors : List String := ["Red", "Green", "Blue"]

private def hasIssue (issues : List ArmIssue) (target : ArmIssue) : Bool :=
  issues.contains target

private def hasNonExhaustiveOf (issues : List ArmIssue) (missing : List String) : Bool :=
  issues.any fun
    | .nonExhaustive m => m == missing
    | _ => false


/-! Positive cases (no issues) -/

-- Full constructor cover, no wildcard.
#guard (checkAgainst colorCtors [some "Red", some "Green", some "Blue"]).isEmpty

-- Wildcard covering exactly the missing ctor.
#guard (checkAgainst colorCtors [some "Red", some "Green", none]).isEmpty

-- Wildcard covering all missing ctors at once.
#guard (checkAgainst colorCtors [some "Red", none]).isEmpty

-- Single wildcard covering everything.
#guard (checkAgainst colorCtors [none]).isEmpty


/-! Non-exhaustive

Missing constructors with no wildcard ⇒ `.nonExhaustive`. -/

#guard hasNonExhaustiveOf (checkAgainst colorCtors [some "Red"])
                          ["Green", "Blue"]
#guard hasNonExhaustiveOf (checkAgainst colorCtors [some "Red", some "Green"])
                          ["Blue"]
#guard hasNonExhaustiveOf (checkAgainst colorCtors []) colorCtors


/-! Duplicate constructor -/

#guard hasIssue (checkAgainst colorCtors [some "Red", some "Red"])
                (.duplicateConstructor "Red")
#guard hasIssue (checkAgainst colorCtors [some "Red", some "Red", some "Red"])
                (.duplicateConstructor "Red")

-- Two distinct duplicates: both reported.
#guard let issues := checkAgainst colorCtors
                       [some "Red", some "Red", some "Green", some "Green"]
       hasIssue issues (.duplicateConstructor "Red")
       && hasIssue issues (.duplicateConstructor "Green")


/-! Unknown constructor -/

#guard hasIssue (checkAgainst colorCtors [some "Purple"])
                (.unknownConstructor "Purple")
#guard hasIssue (checkAgainst colorCtors [some "Red", some "NotAColor"])
                (.unknownConstructor "NotAColor")


/-! Multiple wildcards -/

#guard hasIssue (checkAgainst colorCtors [some "Red", none, none])
                .multipleWildcards
#guard hasIssue (checkAgainst colorCtors [none, none, none])
                .multipleWildcards


/-! Redundant wildcard -/

-- Wildcard arm where every constructor is already explicitly covered.
#guard hasIssue (checkAgainst colorCtors
                              [some "Red", some "Green", some "Blue", none])
                .redundantWildcard


/-! Multiple issues at once

A single check can report multiple distinct issues. -/

#guard let issues := checkAgainst colorCtors
                       [some "Red", some "Red", some "Purple"]
       hasIssue issues (.duplicateConstructor "Red")
       && hasIssue issues (.unknownConstructor "Purple")
       && hasNonExhaustiveOf issues ["Green", "Blue"]


/-! `check` against a real `LDatatype` -/

private def color : LDatatype Unit :=
  { name := "Color", typeArgs := []
    constrs := [
      { name := ⟨"Red",   ()⟩, args := [] },
      { name := ⟨"Green", ()⟩, args := [] },
      { name := ⟨"Blue",  ()⟩, args := [] }],
    constrs_ne := by decide }

#guard (check color [some "Red", some "Green", some "Blue"]).isEmpty
#guard hasNonExhaustiveOf (check color [some "Red"]) ["Green", "Blue"]


/-! `MArm.key` and `MStmtArm.key` projections

The same checker drives expression-level and statement-level matches
through these abstract-key projections. -/

#guard MArm.key (.ctor "Red" (.core (.intConst () 0))) == some "Red"
#guard MArm.key (.wild (.core (.intConst () 0))) == none

#guard MStmtArm.key (.ctor "Red" []) == some "Red"
#guard MStmtArm.key (.wild []) == none


/-! Issue formatting

Each issue formats to a non-empty diagnostic string. -/

#guard !(ArmIssue.format (.unknownConstructor "X")).isEmpty
#guard !(ArmIssue.format (.duplicateConstructor "X")).isEmpty
#guard !(ArmIssue.format .multipleWildcards).isEmpty
#guard !(ArmIssue.format .redundantWildcard).isEmpty
#guard !(ArmIssue.format (.nonExhaustive ["X"])).isEmpty


end CoreMatchArmCheckTest
