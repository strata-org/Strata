/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! # Rendering a lifeline table

One row per step of a pipeline in run order, one column per tracked fact, each
cell a symbol read against the facts holding at that point. Presentation only,
and deliberately ignorant of what a fact or a step is: a caller supplies the
columns, the row names, and three predicates per row saying which facts that row
requires, establishes and preserves.

That is the whole interface, so any pipeline whose steps declare contracts can
render one. `Core.phaseTable` passes its `ProgramFact`s and `PipelinePhase`s;
Laurel passes node-kind shapes and passes, tracking the *absence* of a shape.

Unlike a composition checker, the walk does not stop at an unmet requirement, so
every breakage shows at once.
-/

public section

namespace Strata.Pipeline

structure ColumnLabel where
  first : Char
  second : Option Char := none
deriving DecidableEq

def ColumnLabel.render (l : ColumnLabel) : String :=
  String.ofList (l.first :: l.second.toList)

/-- A row of a lifeline table: a name for the leftmost column, and the facts it
    requires of its input, guarantees on its output, and carries over when they
    held on its input. -/
structure LifelineRow (F : Type) where
  name : String
  requires : F → Bool
  establishes : F → Bool
  preserves : F → Bool

/-- Lifeline symbol for a fact at one row: `+`/`-` required, holds, and still
    holds / is dropped after, `#` required and does not hold, `V` established,
    `|`/`:` preserved and holds / would hold, `'` dropped, blank neither. -/
private def lifelineCellChar (req est pres held : Bool) : Char :=
  if req then (if !held then '#' else if est || pres then '+' else '-')
  else if est then 'V'
  else if pres then (if held then '|' else ':')
  else if held then '\''
  else ' '

/-- `#`, `+` and `-` mark exactly the required facts, `#` exactly the unmet
    ones, and otherwise `V`, `+` and `|` exactly the facts that hold after. -/
private theorem lifelineCellChar_spec : ∀ req est pres held : Bool,
    let c := lifelineCellChar req est pres held
    (['#', '+', '-'].contains c = req) ∧ ((c == '#') = (req && !held)) ∧
    (!(req && !held) → ['V', '+', '|'].contains c = (est || pres && held)) := by
  decide

private def ltPadR (w : Nat) (s : String) : String :=
  s ++ String.ofList (List.replicate (w - s.length) ' ')

private def ltPadL (w : Nat) (s : String) : String :=
  String.ofList (List.replicate (w - s.length) ' ') ++ s

private def ltRStrip (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (· == ' ')).reverse

/-- One character per fact, in column order, for the cells of a row. -/
private def ltBody (cells : List Char) : String :=
  String.join (cells.map fun c => String.ofList [c] ++ " ")

/-- Each row's rendered string paired with its cells, threading the facts that
    hold on entry to it. A row establishes a fact, or carries it over when it
    already held and the row preserves it. -/
private def ltDataRows {F : Type} (facts : List F) (nameW : Nat) :
    Nat → (F → Bool) → List (LifelineRow F) → List (String × List Char)
  | _, _, [] => []
  | pos, held, r :: rest =>
    let cells := facts.map fun f =>
      lifelineCellChar (r.requires f) (r.establishes f) (r.preserves f) (held f)
    let row := ltRStrip (ltPadL 2 (toString pos) ++ " " ++
                         ltPadR nameW r.name ++ ltBody cells)
    let held' := fun f => r.establishes f || (held f && r.preserves f)
    (row, cells) :: ltDataRows facts nameW (pos + 1) held' rest

/-- Render `rows` against `facts` as a lifeline table: legend, column glossary,
    staggered two-line header, then one numbered row per step.

    `labels` are the short column headings and `factNames` the full names for
    the glossary, both in `facts` order. `entryHolds` seeds the facts assumed on
    entry. A `consumer` (a name and the facts it needs, e.g. a verification back
    end) becomes a final requirements-only row. `glossaryLayout` breaks the
    `label: name` glossary into lines; the default puts four on the first line
    and the rest on the second, which suits a dozen short fact names. -/
def lifelineTable {F : Type} (facts : List F) (labels : List ColumnLabel)
    (factNames : List String)
    (rows : List (LifelineRow F)) (entryHolds : F → Bool)
    (consumer : Option (String × (F → Bool)) := none)
    (rowHeading : String := "phase")
    (glossaryLayout : List String → List String := fun named =>
      ["   ".intercalate (named.take 4), "   ".intercalate (named.drop 4)]) : String :=
  let consumerName := (consumer.map (·.1)).getD ""
  let nameW := (rows.map (·.name) ++ [consumerName]).foldl
                 (fun w s => max w s.length) (max 5 rowHeading.length) + 1
  let indent := 3 + nameW
  let dataRows := ltDataRows facts nameW 1 entryHolds rows
  let finalHeld := rows.foldl
    (fun held r f => r.establishes f || (held f && r.preserves f)) entryHolds
  let consumerRow : Option (String × List Char) := consumer.map fun (nm, needed) =>
    let cells := facts.map fun f =>
      if needed f then (if finalHeld f then '+' else '#') else ' '
    (ltRStrip ("   " ++ ltPadR nameW nm ++ ltBody cells), cells)
  let hdr1 := ltRStrip (String.ofList (List.replicate indent ' ') ++
    String.join (labels.zipIdx.map fun (l, i) =>
      if i % 2 == 0 then ltPadR 2 l.render else "  "))
  let hdr2 := ltRStrip (ltPadR indent rowHeading ++
    String.join (labels.zipIdx.map fun (l, i) =>
      if i % 2 == 1 then ltPadR 2 l.render else "  "))
  let allCells := (dataRows.map (·.2)).flatten ++ ((consumerRow.map (·.2)).getD [])
  -- `#` is the cell a reader is looking for — a requirement that does not hold —
  -- so it is explained before the symbols that report business as usual.
  let legendEntries : List (Char × String) :=
    [('#', "# required here, and does not hold"),
     ('V', "V starts holding here"),
     ('|', "| holds, and is carried on"),
     ('+', "+ required here, holds, and is carried on"),
     ('-', "- required here, holds, and is dropped here"),
     ('\'', "' was holding, and is dropped here"),
     (':', ": not holding, but would be carried"),
     (' ', "(blank) not holding, and would not be carried")]
  let usedEntries := (legendEntries.filter (fun (c, _) => allCells.contains c)).map (·.2)
  let legendLines := ([("   ".intercalate (usedEntries.take 3)),
                       ("   ".intercalate ((usedEntries.drop 3).take 3)),
                       ("   ".intercalate (usedEntries.drop 6))]).filter (· != "")
  let named := (labels.zip factNames).map (fun (l, n) => s!"{l.render}: {n}")
  let namedLines := glossaryLayout named
  let rowLines := dataRows.map (·.1) ++ (consumerRow.map (·.1)).toList
  "\n".intercalate (legendLines ++ namedLines ++ ["", hdr1, hdr2] ++ rowLines)

end Strata.Pipeline

end -- public section
