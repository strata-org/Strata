/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.Parser.Basic

namespace Lean.Parser.PrattParsingTables

private def addLeadingParser (tables : PrattParsingTables) (p : Parser) (prio : Nat) : PrattParsingTables :=
  let addTokens (tks : List Token) : PrattParsingTables :=
    let tks    := tks.map Name.mkSimple
    let tables := tks.eraseDups.foldl (init := tables) fun tables tk =>
      { tables with leadingTable := tables.leadingTable.insert tk (p, prio) }
    tables
  match p.info.firstTokens with
  | FirstTokens.tokens tks    => addTokens tks
  | FirstTokens.optTokens tks => addTokens tks
  | _ => { tables with leadingParsers := (p, prio) :: tables.leadingParsers }

private def addTrailingParser (tables : PrattParsingTables) (p : TrailingParser) (prio : Nat) : PrattParsingTables :=
  let addTokens (tks : List Token) : PrattParsingTables :=
    let tks := tks.map fun tk => Name.mkSimple tk
    tks.eraseDups.foldl (init := tables) fun tables tk =>
      { tables with trailingTable := tables.trailingTable.insert tk (p, prio) }
  match p.info.firstTokens with
  | FirstTokens.tokens tks    => addTokens tks
  | FirstTokens.optTokens tks => addTokens tks
  | _                         => { tables with trailingParsers := (p, prio) :: tables.trailingParsers }

def addParser (tables : PrattParsingTables) (leading : Bool) (p : Parser) (prio : Nat) : PrattParsingTables :=
  match leading, p with
  | true, p  => addLeadingParser tables p prio
  | false, p => addTrailingParser tables p prio

end Lean.Parser.PrattParsingTables
