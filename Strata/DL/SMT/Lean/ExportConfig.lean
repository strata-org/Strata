/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # Configuration of the Lean export

`Core.VerifyOptions` carries an `ExportConfig`. These types stand below query preparation, so
that the options need not import the verifier.
-/

public section

namespace Core.LeanExport

/-- Which of the validity checks that come up for export get a Lean theorem file, by the
solver's answer. docs/LeanExport.md says which validity checks come up. -/
inductive Scope where
  /-- The checks the solver leaves undecided: `unknown`, or a timeout. -/
  | undecided
  /-- A check with any answer, also one the solver is not asked. -/
  | all
deriving Repr, BEq, Inhabited

/-- The scope names `Scope.ofString?` accepts, for help and error text. -/
def Scope.options : String :=
  "'undecided' (the checks the solver answers `unknown` or times out on) or \
   'all' (the checks with any answer, and those it is not asked)"

def Scope.ofString? : String → Option Scope
  | "undecided" => some .undecided
  | "all" => some .all
  | _ => none

/-- What the solver said about a validity check, as far as the export needs it. -/
inductive Answer where
  /-- `unsat`: the solver found the query valid. -/
  | proved
  /-- `unsat` from a solver session that walks several checks. The session may hold more than
  the check's own query (axioms its pruning drops, definitions of earlier checks), so the
  answer need not hold for the query as the file states it. -/
  | provedInSession
  /-- `sat`: the solver found a counterexample. -/
  | refuted
  | unknown
  | timeout
  /-- A crash, or an error the solver reported for the check. -/
  | error
  /-- The solver was not run. -/
  | notAsked
deriving Repr, BEq, Inhabited

/-- The answers that leave the check undecided. -/
def Answer.undecided : Answer → Bool
  | .unknown | .timeout => true
  | _ => false

/-- Whether `scope` covers a validity check the solver answered with `answer`. -/
def Scope.covers (scope : Scope) (answer : Answer) : Bool :=
  scope == .all || answer.undecided

/-- What became of a validity check that was in scope. -/
inductive Stage where
  /-- Its file was written. -/
  | exported
  /-- Its file exists already and is left as it is. -/
  | kept
  /-- The query has no Lean form here, is above a size limit, or has a variable that is named
  like a function. -/
  | preparationFailure
  /-- Its file could not be written. -/
  | writeFailure
deriving Repr, BEq, Inhabited

instance : ToString Stage where
  toString
    | .exported => "exported"
    | .kept => "kept"
    | .preparationFailure => "preparationFailure"
    | .writeFailure => "writeFailure"

/-- One validity check that was in scope, and what became of it. -/
structure Event where
  label : String
  stage : Stage
  /-- The file, for `exported` and `kept`. -/
  file : Option System.FilePath := none
  diagnostic : String := ""

/-- Where the files go, which checks get one, and who is told what happened. -/
structure ExportConfig where
  directory : System.FilePath
  scope : Scope := .undecided
  /-- The longest proposition, in bytes of text, that is written. A check whose proposition is
  longer writes no file and is reported. -/
  maxFileBytes : Nat := 8 * 1024 * 1024
  observe : Event → IO Unit := fun _ => pure ()

end Core.LeanExport
