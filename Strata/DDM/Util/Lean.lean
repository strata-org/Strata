/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.Expr
import Lean.Parser.Types
import Lean.ResolveName

open Lean Parser

namespace Lean

/- Creates a local variable name from a string -/
def mkLocalDeclId (name : String) : TSyntax `Lean.Parser.Command.declId :=
  let dName := .anonymous |>.str name
  .mk (.ident .none name.toRawSubstring dName [])

partial def mkErrorMessage (c : InputContext) (pos : String.Pos.Raw) (stk : SyntaxStack) (e : Parser.Error) (isSilent : Bool := false) : Message := Id.run do
  let mut pos := pos
  let mut endPos? := none
  let mut e := e
  unless e.unexpectedTk.isMissing do
    -- calculate error parts too costly to do eagerly
    if let some r := e.unexpectedTk.getRange? then
      pos := r.start
      endPos? := some r.stop
    let unexpected := match e.unexpectedTk with
      | .ident .. => "unexpected identifier"
      | .atom _ v => s!"unexpected token '{v}'"
      | _         => "unexpected token"  -- TODO: categorize (custom?) literals as well?
    e := { e with unexpected }
    -- if there is an unexpected token, include preceding whitespace as well as the expected token could
    -- be inserted at any of these places to fix the error; see tests/lean/1971.lean
    if let some trailing := lastTrailing stk then
      if trailing.stopPos == pos then
        pos := trailing.startPos
  { fileName := c.fileName
    pos := c.fileMap.toPosition pos
    endPos := c.fileMap.toPosition <$> endPos?
    keepFullRange := true
    isSilent := isSilent
    data := toString e }
where
  -- Error recovery might lead to there being some "junk" on the stack
  lastTrailing (s : SyntaxStack) : Option Substring.Raw :=
    s.toSubarray.findSomeRevM? (m := Id) fun stx =>
      if let .original (trailing := trailing) .. := stx.getTailInfo then pure (some trailing)
        else none

def mkStringMessage (c : InputContext) (pos : String.Pos.Raw) (msg : String) (isSilent : Bool := false) : Message :=
  mkErrorMessage c pos SyntaxStack.empty { unexpected := msg } (isSilent := isSilent)

instance : Quote Int where
  quote
  | Int.ofNat n => Syntax.mkCApp ``Int.ofNat #[quote n]
  | Int.negSucc n => Syntax.mkCApp ``Int.negSucc #[quote n]

/- Returns an identifier from a string. -/
def localIdent (name : String) : Ident :=
  let dName := .anonymous |>.str name
  .mk (.ident .none name.toRawSubstring dName [])

/-- Create a canonical identifier. -/
def mkCanIdent (src : Lean.Syntax) (val : Name) : Ident :=
  mkIdentFrom src val true

/--
Create an identifier to a fully qualified Lean name
-/
def mkRootIdent (name : Name) : Ident :=
  let rootName := `_root_ ++ name
  .mk (.ident .none name.toString.toRawSubstring rootName [.decl name []])

end Lean

public section
namespace Strata.Lean

@[inline]
def arrayToExpr (level : Level) (type : Expr) (a : Array Expr) : Expr :=
  let init := mkApp2 (mkConst ``Array.mkEmpty [level]) type (toExpr a.size)
  let pushFn := mkApp (mkConst ``Array.push [level]) type
  a.foldl (init := init) (mkApp2 pushFn)

def listToExpr (level : Level) (type : Lean.Expr) (es : List Lean.Expr) : Lean.Expr :=
  let nilFn  := mkApp (mkConst ``List.nil [level]) type
  let consFn := mkApp (mkConst ``List.cons [level]) type
  es.foldr (init := nilFn) (mkApp2 consFn)

@[inline]
def optionToExpr (type : Lean.Expr) (a : Option Lean.Expr) : Lean.Expr :=
  match a with
  | none => mkApp (mkConst ``Option.none [levelZero]) type
  | some a => mkApp2 (mkConst ``Option.some [levelZero]) type a


end Strata.Lean
end section
