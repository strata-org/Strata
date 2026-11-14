/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module

namespace Cortex.FieldCasts

open Imperative Lambda

public section

def ident (n : String) : Core.Expression.Ident := ⟨n, ()⟩

def lowerBody (p : UnorderedProgram) (b : Body) : Except String Body := do
  let mut n := 0
  let mut tmps : List (String × LMonoTy) := []
  let mut blocks : List (Label × LBlock) := []
  for (l, blk) in b.cfg.blocks do
    let mut cmds : List IRCmd := []
    for c in blk.cmds do
      match c with
      | .readField x _ f md =>
        let t ← fieldMono p f
        cmds := cmds ++ [c, .cast x (mangle t) (mkFvar x.name) .assume md]
      | .writeField o f v md =>
        let tmp := fieldValueVar n
        n := n + 1
        tmps := tmps ++ [(tmp, ← fieldMono p f)]
        cmds := cmds ++ [.cmd (.set (ident tmp) (.det v) md), .writeField o f (mkFvar tmp) md]
      | .readElem x _ _ ty md =>
        cmds := cmds ++ [c, .cast x (mangle (← elemMono ty)) (mkFvar x.name) .assume md]
      | .writeElem a i v ty md =>
        let tmp := fieldValueVar n
        n := n + 1
        tmps := tmps ++ [(tmp, ← elemMono ty)]
        cmds := cmds ++ [.cmd (.set (ident tmp) (.det v) md), .writeElem a i (mkFvar tmp) ty md]
      | c => cmds := cmds ++ [c]
    let blk' : LBlock := { blk with cmds }
    blocks := blocks ++ [(l, blk')]
  if tmps.isEmpty then return { b with cfg := { b.cfg with blocks } }
  let entry := "$fieldCastsEntry"
  let init : List IRCmd := tmps.map fun (x, t) => .cmd (.init (ident x) (mono t) .nondet .empty)
  return { b with cfg := { entry, blocks := (entry, { cmds := init, transfer := .goto b.cfg.entry }) :: blocks } }

def run (p : UnorderedProgram) : Except String UnorderedProgram := do
  let procs ← p.procedures.mapM fun pr => do
    let body ← match pr.body with
      | some b => some <$> lowerBody p b
      | none => pure none
    return { pr with body }
  return { p with procedures := procs }

end

end Cortex.FieldCasts
