/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module

namespace Cortex.InoutArgs

open Imperative Lambda

public section

def ident (n : String) : Core.Expression.Ident := ⟨n, ()⟩

def inoutPositions (p : Procedure) : List (Nat × Nat) :=
  p.outputs.zipIdx.filterMap fun ((x, _), j) =>
    (p.inputs.findIdx? (·.1.name == x.name)).map (·, j)

def inPlace (lhs : List Core.Expression.Ident) (args : List Expr) (i j : Nat) : Bool :=
  match args[i]?, lhs[j]? with
  | some (.fvar _ y _), some x => y == x && lhs.count x == 1
  | _, _ => false

def withDecls (b : Body) (decls : List IRCmd) : Body :=
  let cfg := b.cfg
  if cfg.blocks.any (fun (_, blk) => blk.transfer.targets.contains cfg.entry)
      || b.handlers.any (·.target == cfg.entry) then
    let entry := freshLabel "$inoutDecl" cfg.labels
    { b with cfg := { entry, blocks := (entry, { cmds := decls, transfer := .goto cfg.entry }) :: cfg.blocks } }
  else
    { b with cfg := { cfg with blocks := cfg.blocks.map fun (l, blk) =>
        if l == cfg.entry then (l, { blk with cmds := decls ++ blk.cmds }) else (l, blk) } }

def lowerBody (prog : UnorderedProgram) (used : List String) (b : Body) : Body := Id.run do
  let mut used := used
  let mut decls : List IRCmd := []
  let mut blocks : List (Label × LBlock) := []
  for (l, blk) in b.cfg.blocks do
    let mut cmds : List IRCmd := []
    for c in blk.cmds do
      match c with
      | .call lhs q args md =>
        match prog.findProcedure? q with
        | some p =>
          let mut lhs' := lhs
          let mut args' := args
          let mut pre : List IRCmd := []
          let mut post : List IRCmd := []
          for (i, j) in inoutPositions p do
            match args[i]?, lhs[j]?, p.inputs[i]? with
            | some a, some x, some (_, ty) =>
              if p.throws.isSome || !inPlace lhs args i j then
                let t := freshLabel "$inoutArg" used
                used := used ++ [t]
                decls := decls ++ [.cmd (.init (ident t) ty .nondet .empty)]
                pre := pre ++ [.cmd (.set (ident t) (.det a) md)]
                args' := args'.set i (mkFvar t)
                lhs' := lhs'.set j (ident t)
                post := post ++ [.cmd (.set x (.det (mkFvar t)) md)]
            | _, _, _ => pure ()
          cmds := cmds ++ pre ++ [.call lhs' q args' md] ++ post
        | none => cmds := cmds ++ [c]
      | c => cmds := cmds ++ [c]
    let blk' : LBlock := { blk with cmds }
    blocks := blocks ++ [(l, blk')]
  let b' := { b with cfg := { b.cfg with blocks } }
  return if decls.isEmpty then b' else withDecls b' decls

def run (prog : UnorderedProgram) : Except String UnorderedProgram :=
  let globals := prog.globals.map (·.1.name)
  .ok (prog.mapProcedures fun p =>
    { p with body := p.body.map fun b =>
      lowerBody prog (globals ++ (p.inputs ++ p.outputs).map (·.1.name) ++ b.assignedNames) b })

def pass : Pass := Pass.onUnordered "InoutArgs" run

end

end Cortex.InoutArgs
