/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module

namespace Cortex.LowerGlobals

open Imperative Lambda

public section

partial def fvarsOf (e : Expr) : List String :=
  match e with
  | .fvar _ n _ => [n.name]
  | .app _ a b | .eq _ a b => fvarsOf a ++ fvarsOf b
  | .ite _ c t f => fvarsOf c ++ fvarsOf t ++ fvarsOf f
  | .abs _ _ _ b => fvarsOf b
  | .quant _ _ _ _ tr b => fvarsOf tr ++ fvarsOf b
  | _ => []

def eOrN : ExprOrNondet Core.Expression → List Expr
  | .det e => [e]
  | .nondet => []

def cmdExprs : IRCmd → List Expr
  | .cmd (.init _ _ e _) | .cmd (.set _ e _) => eOrN e
  | .cast _ _ e _ _ => [e]
  | .cmd (.assert _ b _) | .cmd (.assume _ b _) | .cmd (.cover _ b _) => [b]
  | .readField _ o _ _ | .instanceOf _ o _ _ => [o]
  | .writeField o _ v _ => [o, v]
  | .newArray _ _ len _ => [len]
  | .readElem _ a i _ _ => [a, i]
  | .writeElem a i v _ _ => [a, i, v]
  | .arrayLength _ a _ => [a]
  | .call _ _ args _ | .virtualCall _ _ _ args _ => args
  | .throw e _ => [e]
  | .new .. => []

def cmdWrites : IRCmd → List String
  | .cmd (.init x ..) | .cmd (.set x ..) | .cast x .. | .new x .. | .readField x .. | .instanceOf x .. => [x.name]
  | .newArray x .. | .readElem x .. | .arrayLength x .. => [x.name]
  | .call lhs .. | .virtualCall lhs .. => lhs.map (·.name)
  | _ => []

def transferExprs : DetTransferCmd Label Core.Expression → List Expr
  | .condGoto c _ _ _ => [c]
  | .finish _ => []

structure Eff where
  reads : List String := []
  writes : List String := []

def addUniq (xs ys : List String) : List String := ys.foldl (fun acc y => if acc.contains y then acc else acc ++ [y]) xs

def directEff (gs : List String) (p : Procedure) : Eff :=
  match p.body with
  | none => { reads := gs, writes := gs }
  | some b =>
    let cmds := b.cfg.blocks.flatMap fun (_, blk) => blk.cmds
    -- A precondition is checked at each call and assumed on entry, so the globals it mentions
    -- must reach the procedure like the ones its body reads.
    let exprs := cmds.flatMap cmdExprs ++ b.cfg.blocks.flatMap (fun (_, blk) => transferExprs blk.transfer)
      ++ p.requires.map (·.cond)
    let reads := gs.filter fun g => exprs.any fun e => (fvarsOf e).contains g
    let writes := gs.filter fun g => cmds.any fun c => (cmdWrites c).contains g
    { reads, writes }

def calleesOf (prog : UnorderedProgram) (p : Procedure) : List String :=
  match p.body with
  | none => []
  | some b => b.cfg.blocks.flatMap fun (_, blk) => blk.cmds.flatMap (IRCmd.callees prog)

def effects (prog : UnorderedProgram) : Std.HashMap String Eff := Id.run do
  let gs := prog.globals.map (·.1.name)
  let mut eff : Std.HashMap String Eff := prog.procedures.foldl (fun m p => m.insert p.name (directEff gs p)) {}
  let mut changed := true
  let mut fuel := prog.procedures.length * (gs.length + 1) + 2
  while changed && fuel > 0 do
    changed := false
    fuel := fuel - 1
    for p in prog.procedures do
      let e := eff.getD p.name {}
      let mut r := e.reads
      let mut w := e.writes
      for q in calleesOf prog p do
        let qe := eff.getD q {}
        r := addUniq r (qe.reads ++ qe.writes)
        w := addUniq w qe.writes
      if r.length != e.reads.length || w.length != e.writes.length then
        eff := eff.insert p.name { reads := r, writes := w }
        changed := true
  return eff

def ident (n : String) : Core.Expression.Ident := ⟨n, ()⟩

def isEntry (p : Procedure) : Bool :=
  match p.md.findElem Imperative.MetaData.interpretEntry with
  | some { value := .switch true, .. } => true
  | _ => false

def run (prog : UnorderedProgram) : Except String UnorderedProgram :=
  if prog.globals.isEmpty then .ok prog else do
  prog.refuseVirtualCalls "LowerGlobals"
  let eff := effects prog
  let gty := fun (g : String) => ((prog.globals.find? (·.1.name == g)).map (·.2)).getD (mono .int)
  let order := prog.globals.map (·.1.name)
  let insOf := fun (n : String) => let e := eff.getD n {}; order.filter fun g => e.reads.contains g || e.writes.contains g
  let outsOf := fun (n : String) => let e := eff.getD n {}; order.filter e.writes.contains
  let outTy := fun (q : String) (i : Nat) =>
    (((prog.findProcedure? q).bind fun pr => pr.outputs[i]?).map (·.2)).getD (mono .int)
  let lowerBody := fun (params : List String) (entryCmds : List IRCmd) (b : Body) => Id.run do
    let mut used : List String := params ++ order ++ b.assignedNames
    let mut tmps : List IRCmd := []
    let mut blocks : List (Label × LBlock) := []
    for (l, blk) in b.cfg.blocks do
      let mut cmds : List IRCmd := []
      for c in blk.cmds do
        match c with
        | .call lhs q args md =>
          let outs := outsOf q
          let thrown := lhs.any (·.name == "$callThrown")
          let mut lhs' : List Core.Expression.Ident := []
          let mut post : List IRCmd := []
          for (x, i) in lhs.zipIdx do
            if outs.contains x.name then
              let tmp := freshLabel "$callResult" used
              used := used ++ [tmp]
              tmps := tmps ++ [.cmd (.init (ident tmp) (outTy q i) .nondet .empty)]
              lhs' := lhs' ++ [ident tmp]
              let v : Expr := if thrown then .ite () (mkFvar "$callThrown") (mkFvar x.name) (mkFvar tmp) else mkFvar tmp
              post := post ++ [.cmd (.set x (.det v) md)]
            else
              lhs' := lhs' ++ [x]
          cmds := cmds ++ [.call (lhs' ++ outs.map ident) q (args ++ (insOf q).map mkFvar) md] ++ post
        | c => cmds := cmds ++ [c]
      let blk' : LBlock := { blk with cmds }
      blocks := blocks ++ [(l, blk')]
    let pre := entryCmds ++ tmps
    if pre.isEmpty then return { b with cfg := { b.cfg with blocks } }
    let entry := freshLabel "$globalsEntry" (blocks.map (·.1))
    return { b with cfg := { entry, blocks := (entry, { cmds := pre, transfer := .goto b.cfg.entry }) :: blocks } }
  let procs := prog.procedures.map fun p =>
    if isEntry p then
      { p with body := p.body.map (lowerBody ((p.inputs ++ p.outputs).map (·.1.name)) (prog.globalInit.map .cmd)) }
    else
    { p with
      inputs := p.inputs ++ (insOf p.name).map fun g => (ident g, gty g)
      outputs := p.outputs ++ (outsOf p.name).map fun g => (ident g, gty g)
      body := p.body.map (lowerBody ((p.inputs ++ p.outputs).map (·.1.name)) []) }
  .ok { prog with procedures := procs, globals := [], globalInit := [] }

def pass : Pass := Pass.onUnordered "LowerGlobals" run

end

end Cortex.LowerGlobals
