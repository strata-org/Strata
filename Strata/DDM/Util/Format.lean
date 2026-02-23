/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DDM.Util.String

namespace Std.Format

def appendSpaces (s : String) (n : Nat) : String :=
  n.fold (init := s) (fun _ _ u => u.push ' ')

def sline (s : String) (indent : Nat) : String :=
  appendSpaces "" indent ++ s ++ "\n"

def repr (fmt : Std.Format) (indent : Nat) : String :=
  match fmt with
  | .nil => sline "nil" indent
  | .line => sline "line" indent
  | .align n => sline s!"align {n}" indent
  | .text msg => sline s!"text {Strata.escapeStringLit msg}" indent
  | .nest n fmt => sline s!"nest {n}" indent ++ repr fmt (indent + 2)
  | .append x y => repr x indent ++ repr y indent
  | .group f _ => sline "group" indent ++ repr f (indent + 2)
  | .tag n f => sline s!"tag {n}" indent ++ repr f (indent + 2)

structure RenderState where
  soFar : String

def RenderState.needIndent (s : RenderState) : Bool := s.soFar.back == '\n'

abbrev RenderM := ReaderT Nat (StateM RenderState)

def app (n : String) : RenderM Unit := do
  if n.isEmpty then
    return ()
  let indent ← read
  modify fun s =>
    let t := s.soFar
    let t := if s.needIndent then
                appendSpaces t indent
              else
                t
    { soFar := t ++ n }

partial
def renderAux (a : Array Std.Format) : RenderM Unit :=
  match a.back? with
  | none => pure ()
  | some fmt =>
    let a := a.pop
    match fmt with
    | .nil =>
      renderAux a
    | .line =>
      renderAux a
    | .align _ => do
      renderAux a
    | .text msg => do
      let lines := msg.splitLines.toArray
      for line in lines.pop do
        app line
        app "\n"
      app lines.back!
      renderAux a
    | .nest n fmt =>  do
      (fun indent => renderAux #[fmt] (indent + n.toNat))
      renderAux a
    | .append x y =>
      renderAux (a |>.push y |>.push x)
    | .group f _ =>
      renderAux (a |>.push f)
    | .tag _ f =>
      renderAux (a |>.push f)

/-- Alternative render format for string -/
def render (fmt : Std.Format) : String :=
  renderAux #[fmt] 0 { soFar := "" } |>.snd |>.soFar

end Std.Format
