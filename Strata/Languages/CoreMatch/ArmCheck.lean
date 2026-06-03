/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.CoreMatch.CoreMatch
public import Strata.Languages.Core.TypeDecl
public import Strata.DL.Lambda.TypeFactory

/-!
Redundancy and exhaustiveness checking for `match` arms. The check
is shared between expression-level and statement-level matches via
the `ArmKey` projection.
-/

namespace Strata.CoreMatch.ArmCheck

open Strata.CoreMatch Lambda

public section

inductive ArmIssue where
  | unknownConstructor (name : String)
  | duplicateConstructor (name : String)
  | multipleWildcards
  | redundantWildcard
  | nonExhaustive (missing : List String)
  deriving Repr, BEq

@[expose]
def ArmIssue.format : ArmIssue → String
  | .unknownConstructor n   => s!"unknown constructor '{n}' in match arm"
  | .duplicateConstructor n => s!"duplicate match arm for constructor '{n}'"
  | .multipleWildcards      => "match has more than one wildcard arm"
  | .redundantWildcard      => "wildcard arm is redundant: every constructor is covered explicitly"
  | .nonExhaustive missing  => s!"non-exhaustive match: no arm for constructors: {missing}"

/-- An arm projected to its identity for checking: `some ctor` for a
constructor arm, `none` for a wildcard. -/
@[expose] abbrev ArmKey := Option String

/-- Check a match's arms against the scrutinee datatype's
constructors. `ctorNames` must be in declaration order; `keys` in
source order. -/
@[expose]
def checkAgainst (ctorNames : List String) (keys : List ArmKey) : List ArmIssue := Id.run do
  let mut issues   : List ArmIssue := []
  let mut seen     : List String := []
  let mut wildcards : Nat := 0
  for key in keys do
    match key with
    | none =>
      wildcards := wildcards + 1
      if wildcards > 1 then issues := .multipleWildcards :: issues
    | some n =>
      if !ctorNames.contains n then issues := .unknownConstructor n :: issues
      else if seen.contains n  then issues := .duplicateConstructor n :: issues
      else seen := n :: seen
  let missing := ctorNames.filter (!seen.contains ·)
  if wildcards > 0 then
    if missing.isEmpty then issues := .redundantWildcard :: issues
  else
    if !missing.isEmpty then issues := .nonExhaustive missing :: issues
  return issues.reverse

@[expose]
def check (dt : LDatatype Unit) (keys : List ArmKey) : List ArmIssue :=
  checkAgainst (dt.constrs.map (·.name.name)) keys

@[expose]
def MArm.key : MArm → ArmKey
  | .ctor c _ => some c | .wild _ => none

@[expose]
def MStmtArm.key : MStmtArm → ArmKey
  | .ctor c _ => some c | .wild _ => none

end

end Strata.CoreMatch.ArmCheck
