/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase

/-! # Rendering a phase list's contracts as a table

Presentation only: it reads the phases' declared contracts and formats them, so
it needs the phase vocabulary and nothing from the verifier. -/

public section

namespace Core

/-! ### Rendering a pipeline's contracts as a table

`phaseTable` renders a phase list as a dependency table: one numbered row per
phase in run order, one column
per fact, each cell a lifeline symbol read against the facts holding at that
point in the pipeline. `entryFacts` seeds the facts assumed to hold on entry; a
`consumer` (a name and the facts it requires, e.g. the verification back end)
becomes a final requirements-only row. Unlike the composition checker, the walk
does not stop at the first unmet requirement — it treats each as satisfied and
carries on — so every breakage shows at once. -/

/-- Lifeline symbol for a fact at one phase: `V` established, `+`/`#` required
    and holds / does not hold, `|`/`:` preserved and holds / would hold, `'`
    dropped, blank neither. -/
private def phaseCellChar (req est pres held : Bool) : Char :=
  if est then 'V'
  else if req then (if held then '+' else '#')
  else if pres then (if held then '|' else ':')
  else if held then '\''
  else ' '

/-- Two-character column label for a fact: drop a leading `no`, capitalize the
    first letter, and follow it with the next capital (an acronym like
    `CFGBodies` → `CF`) or the initial of the next word (`BetaRedexes` → `BR`). -/
private def phaseTableLabelOf (name : String) : String :=
  let cs := name.toList
  match (if cs.take 2 == ['n', 'o'] then cs.drop 2 else cs) with
  | [] => "?"
  | c :: rest =>
    let second := match rest with
      | [] => c
      | d :: _ => if d.isUpper then d else (rest.find? (·.isUpper)).getD d
    String.ofList [c.toUpper, second]

/-- `phaseTableLabelOf` for every fact, widening a collision to three letters so
    `noPolymorphicFunctions` reads `PoF` beside `noPrecondsFromFuncs`' `PF`. -/
private def phaseTableLabels : List String :=
  (ProgramFact.all.foldl (init := ([] : List String)) fun taken f =>
    let base := phaseTableLabelOf f.name
    let widened :=
      let cs := (if f.name.toList.take 2 == ['n', 'o'] then f.name.toList.drop 2
                 else f.name.toList)
      match cs with
      | c :: d :: _ => String.ofList [c.toUpper, d] ++ base.drop 1
      | _ => base
    (if base ∈ taken then widened else base) :: taken).reverse

private def phTblPadR (w : Nat) (s : String) : String :=
  s ++ String.ofList (List.replicate (w - s.length) ' ')

private def phTblPadL (w : Nat) (s : String) : String :=
  String.ofList (List.replicate (w - s.length) ' ') ++ s

private def phTblRStrip (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (· == ' ')).reverse

/-- One character per fact (in `ProgramFact.all` order) for the cells of a row. -/
private def phTblBody (cells : List Char) : String :=
  String.join (cells.map fun c => String.ofList [c] ++ " ")

/-- Each phase's row string paired with its cells, threading the facts that hold
    on entry to it. -/
private def phaseTableDataRows (nameW : Nat) :
    Nat → ProgramFactSet → List PipelinePhase → List (String × List Char)
  | _, _, [] => []
  | pos, σ, p :: rest =>
    let cells := ProgramFact.all.map fun f =>
      phaseCellChar (f ∈ p.requires) (f ∈ p.establishes) (f ∈ p.preserves) (f ∈ σ)
    let row := phTblRStrip (phTblPadL 2 (toString pos) ++ " " ++
                            phTblPadR nameW p.phase.name ++ phTblBody cells)
    let σ' := Strata.Pipeline.applyPhase p.establishes p.preserves σ
    (row, cells) :: phaseTableDataRows nameW (pos + 1) σ' rest

/-- Render `phases` as the dependency table. See the section comment. -/
def phaseTable (phases : List PipelinePhase)
    (entryFacts : ProgramFactSet := ProgramFactSet.empty)
    (consumer : Option (String × ProgramFactSet) := none) : String :=
  let labels := phaseTableLabels
  let consumerName := (consumer.map (·.1)).getD ""
  let nameW := (phases.map (·.phase.name) ++ [consumerName]).foldl
                 (fun w s => max w s.length) 5 + 1
  let indent := 3 + nameW
  let dataRows := phaseTableDataRows nameW 1 entryFacts phases
  let finalσ := phases.foldl (fun σ p =>
      Strata.Pipeline.applyPhase p.establishes p.preserves σ) entryFacts
  let consumerRow : Option (String × List Char) := consumer.map fun (nm, needed) =>
    let cells := ProgramFact.all.map fun f =>
      if f ∈ needed then (if f ∈ finalσ then '+' else '#') else ' '
    (phTblRStrip ("   " ++ phTblPadR nameW nm ++ phTblBody cells), cells)
  let hdr1 := phTblRStrip (String.ofList (List.replicate indent ' ') ++
    String.join (labels.zipIdx.map fun (l, i) => if i % 2 == 0 then l else "  "))
  let hdr2 := phTblRStrip (phTblPadR indent "phase" ++
    String.join (labels.zipIdx.map fun (l, i) => if i % 2 == 1 then l else "  "))
  let allCells := (dataRows.map (·.2)).flatten ++ ((consumerRow.map (·.2)).getD [])
  -- `#` is the cell a reader is looking for — a requirement that does not hold —
  -- so it is explained before the symbols that report business as usual.
  let legendEntries : List (Char × String) :=
    [('#', "# required here, and does not hold"),
     ('V', "V starts holding here"),
     ('|', "| holds, and is carried on"),
     ('+', "+ required here, and holds"),
     ('\'', "' was holding, and is dropped here"),
     (':', ": not holding, but would be carried"),
     (' ', "(blank) not holding, and would not be carried")]
  let usedEntries := (legendEntries.filter (fun (c, _) => allCells.contains c)).map (·.2)
  let legendLines := ([("   ".intercalate (usedEntries.take 3)),
                       ("   ".intercalate ((usedEntries.drop 3).take 3)),
                       ("   ".intercalate (usedEntries.drop 6))]).filter (· != "")
  let named := (labels.zip (ProgramFact.all.map (·.name))).map (fun (l, n) => s!"{l}: {n}")
  let namedLines := [("   ".intercalate (named.take 4)), ("   ".intercalate (named.drop 4))]
  let rows := dataRows.map (·.1) ++ (consumerRow.map (·.1)).toList
  "\n".intercalate (legendLines ++ namedLines ++ ["", hdr1, hdr2] ++ rows)

end Core

end -- public section
