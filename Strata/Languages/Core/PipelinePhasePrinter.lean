/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Pipeline.LifelineTable

/-! # Rendering a phase list's contracts as a table

Presentation only: it reads the phases' declared contracts and formats them, so
it needs the phase vocabulary and nothing from the verifier. The rendering
itself is `Strata.Pipeline.lifelineTable`, shared with every other pipeline that
declares contracts; what belongs here is only the Core-specific part, namely how
a `ProgramFact` earns its column label. -/

public section

namespace Core

/-! ### Rendering a pipeline's contracts as a table

`phaseTable` renders a phase list as a dependency table: one numbered row per
phase in run order, one column per fact, each cell a lifeline symbol read
against the facts holding at that point in the pipeline. `entryFacts` seeds the
facts assumed to hold on entry; a `consumer` (a name and the facts it requires,
e.g. the verification back end) becomes a final requirements-only row. -/

/-- Column label for a fact: drop a leading `no`, capitalize the first letter,
    and follow it with the next capital (an acronym like `CFGBodies` → `CF`) or
    the initial of the next word (`BetaRedexes` → `BR`). -/
private def phaseTableLabelOf (name : String) : Strata.Pipeline.ColumnLabel :=
  let cs := name.toList
  match (if cs.take 2 == ['n', 'o'] then cs.drop 2 else cs) with
  | [] => { first := '?' }
  | c :: rest =>
    let second := match rest with
      | [] => c
      | d :: _ => if d.isUpper then d else (rest.find? (·.isUpper)).getD d
    { first := c.toUpper, second := some second }

/-- `phaseTableLabelOf` for every fact, falling back to the name's first two
    letters and then to a generated letter, taking the first candidate no
    earlier label used, so `noPolymorphicFunctions` reads `Po` beside
    `noPrecondsFromFuncs`' `PF`. Mirrors `Strata.Laurel.shapeLabels`, which does
    the same for shape paths. -/
private def phaseTableLabels : List Strata.Pipeline.ColumnLabel :=
  (ProgramFact.all.foldl (init := ([] : List Strata.Pipeline.ColumnLabel)) fun taken f =>
    let base := phaseTableLabelOf f.name
    let cs := (if f.name.toList.take 2 == ['n', 'o'] then f.name.toList.drop 2
               else f.name.toList)
    let letters := (List.range 26).map fun i => Char.ofNat ('a'.toNat + i)
    let cands : List Strata.Pipeline.ColumnLabel :=
      [ base,
        { first := base.first, second := cs[1]? } ]
      ++ letters.map (fun c => { first := base.first, second := some c })
    ((cands.find? (· ∉ taken)).getD
      { first := base.first,
        second := some (Char.ofNat ('a'.toNat + taken.length % 26)) } :: taken)).reverse

/-- Render `phases` as the dependency table. See the section comment. -/
def phaseTable (phases : List PipelinePhase)
    (entryFacts : ProgramFactSet := ProgramFactSet.empty)
    (consumer : Option (String × ProgramFactSet) := none) : String :=
  Strata.Pipeline.lifelineTable
    (facts := ProgramFact.all)
    (labels := phaseTableLabels)
    (factNames := ProgramFact.all.map (·.name))
    (rows := phases.map fun p =>
      { name := p.phase.name
        requires := fun f => decide (f ∈ p.requires)
        establishes := fun f => decide (f ∈ p.establishes)
        preserves := fun f => decide (f ∈ p.preserves) })
    (entryHolds := fun f => decide (f ∈ entryFacts))
    (consumer := consumer.map fun (nm, needed) => (nm, fun f => decide (f ∈ needed)))

end Core

end -- public section
