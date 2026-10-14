/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelCompilationPipeline
public import Strata.Pipeline.LifelineTable

/-! # The shape lifeline table

The Laurel view of `Strata.Pipeline.lifelineTable`, the renderer `Core.phaseTable` also uses.
The fact a column tracks is that **the shape is absent**, and that is what lets Laurel reuse
the renderer unchanged: absence behaves exactly as a Core fact does, so `removes` establishes
it, `unsupported` requires it, and a pass *preserves* it whenever it does not create the shape. -/

public section

namespace Strata.Laurel

/-- Shapes with a column: those some pass declares `unsupported`, in the order the first
    pass to reject one appears. -/
def tableShapes : List NodeKind :=
  allPasses.foldl (init := []) fun acc p =>
    p.unsupported.foldl (init := acc) fun acc k => if acc.contains k then acc else acc ++ [k]

/-- The owner segment and the segments after it, e.g.
    `StmtExpr.While.postTest.true` → `("StmtExpr", ["While", "postTest", "true"])`. -/
private def splitOwner (path : String) : String × List String :=
  match path.splitOn "." with
  | [] => ("?", ["?"])
  | owner :: rest => (owner, if rest.isEmpty then [owner] else rest)

/-- Short column label for a shape: initials of the path after the owner, falling back to a
    prefix of its leading segment, then the owner's initial, then a letter, taking the first
    candidate no earlier label used. Mirrors `Core`'s label function, which does the same for
    fact names. -/
def shapeLabels : List (NodeKind × Strata.Pipeline.ColumnLabel) :=
  (tableShapes.foldl (init := ([] : List (NodeKind × Strata.Pipeline.ColumnLabel))) fun taken k =>
    let (owner, segs) := splitOwner (NodeKind.name k)
    let leaf := ((segs.head?).getD "?").toList
    let ini := segs.filterMap (fun s => s.toList.head?)
    let o := ((owner.toList.head?.map (·.toLower)).getD '?')
    let first := ((ini.head?).getD '?').toUpper
    let letters := (List.range 26).map fun i => Char.ofNat ('a'.toNat + i)
    let cands : List Strata.Pipeline.ColumnLabel :=
      [ { first := first },
        { first := first, second := ini[1]? },
        { first := ((leaf.head?).getD '?').toUpper, second := leaf[1]? },
        { first := o, second := some first },
        { first := o, second := some ((leaf[1]?.map (·.toUpper)).getD '?') } ]
      ++ letters.map (fun c => { first := first, second := some c })
      ++ letters.map (fun c => { first := o, second := some c })
    let used := taken.map (·.2)
    ((k, (cands.find? (· ∉ used)).getD
            { first := first,
              second := some (Char.ofNat ('a'.toNat + taken.length % 26)) }) :: taken)).reverse

/-- Render the Laurel passes as the shape lifeline table. See the module comment. -/
def shapeLifelineTable : String :=
  let shapes := tableShapes
  Strata.Pipeline.lifelineTable
    (facts := shapes)
    (labels := shapeLabels.map (·.2))
    (factNames := shapes.map NodeKind.name)
    (rows := allPasses.toList.map fun p =>
      ({ name := p.name
         requires := fun k => p.unsupported.contains k
         establishes := fun k => p.removes.contains k
         preserves := fun k => !p.creates.contains k } : Strata.Pipeline.LifelineRow NodeKind))
    -- A shape that can be written in source is present to begin with, so its absence
    -- does not hold on entry.
    (entryHolds := fun k => !NodeKind.inSource k)
    (rowHeading := "pass")
    -- Shape paths are long, so the glossary wraps every three entries rather than
    -- using Core's first-four-then-the-rest split.
    (glossaryLayout := fun named =>
      (List.range ((named.length + 2) / 3)).map fun i =>
        "   ".intercalate ((named.drop (i * 3)).take 3))

/-- `shapeLifelineTable` in a fenced code block, for rendering in Markdown. -/
def shapeLifelineTableMarkdown : String :=
  "```\n" ++ shapeLifelineTable ++ "\n```\n"

end Strata.Laurel

end -- public section
