/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Util.LabelGen
public import Strata.Languages.Core.Identifiers
open Core Lambda

/-! ## Strata Core Identifier Generator
  This file contains a Strata Core Identifier generator `CoreGenState.gen`, where the
  uniqueness of the generated identifiers is designed to be provable. It relies on a
  `StringGenState` to generate unique strings (See `StringGen.lean`).

  Also see `LabelGen.lean` for the generic type class for a unique label generator.
  The well-formedness theorems and the `LabelGen.WFLabelGen` instance are in
  `CoreGenProps.lean`.
-/

namespace Core
public section

structure CoreGenState where
  cs : StringGenState
  generated : List CoreIdent := []

def CoreGenState.WF (σ : CoreGenState)
  := StringGenState.WF σ.cs ∧
    List.map (fun s => (⟨s, ()⟩ : CoreIdent)) σ.cs.generated.unzip.snd = σ.generated ∧
    σ.generated.Nodup

instance : HasSubset CoreGenState where
  Subset σ₁ σ₂ := σ₁.generated.Subset σ₂.generated

@[simp]
def CoreGenState.emp : CoreGenState := { cs := .emp, generated := [] }

/-- A CoreIdent generator
    NOTE: we need to wrap the prefix into a CoreIdent in order to conform with the interface of UniqueLabelGen.gen
    TODO: Maybe use genIdent or genIdents?
    -/
def CoreGenState.gen (pf : CoreIdent) (σ : CoreGenState)
  : CoreIdent × CoreGenState :=
  let (s, cs') := StringGenState.gen pf.name σ.cs
  let newIdent : CoreIdent := ⟨s, ()⟩
  let newState : CoreGenState := { cs := cs', generated := newIdent :: σ.generated }
  (newIdent, newState)

abbrev CoreGenM := StateM CoreGenState

/-- Generate a name with prefix `pf` that is not in `taken`, retrying
    `CoreGenState.gen`, which knows only the names it generated, until the name
    avoids `taken`. `taken.size + 1` calls suffice. -/
def CoreGenState.genAvoiding (taken : Std.HashSet String) (pf : CoreIdent) :
    CoreGenM CoreIdent :=
  go taken.size
where
  /-- Draw a name, and draw again, at most `fuel` more times, while it is in `taken`. -/
  go : Nat → CoreGenM CoreIdent
    | 0 => CoreGenState.gen pf
    | fuel + 1 => do
      let n ← CoreGenState.gen pf
      if taken.contains n.name then go fuel else pure n

end
end Core
