/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module

namespace Cortex.LowerDispatch

open Imperative Lambda

public section

def testVar : String := "$dispatchTest"

def ident (n : String) : Core.Expression.Ident := ⟨n, ()⟩

structure St where
  blocks : Array (Label × LBlock) := #[]
  fresh : Nat := 0
  added : Array (Label × Label) := #[]

abbrev M := StateM St

def freshLabel (origin : Label) (base : String) : M Label := do
  let s ← get
  let l := s!"{base}$vd{s.fresh}"
  set { s with fresh := s.fresh + 1, added := s.added.push (origin, l) }
  return l

def addBlock (l : Label) (b : LBlock) : M Unit :=
  modify fun s => { s with blocks := s.blocks.push (l, b) }

def chain (origin : Label) (lhs : List Core.Expression.Ident) (owner : TypeName) (meth : String)
    (args : List Expr) (md : MD) (join : Label) : List TypeName → M Label
  | [] => do
    let l ← freshLabel origin "$dispatch_default"
    addBlock l { cmds := [.call lhs (implName owner meth) args md], transfer := .goto join }
    return l
  | d :: ds => do
    let next ← chain origin lhs owner meth args md join ds
    let yes ← freshLabel origin "$dispatch"
    addBlock yes { cmds := [.call lhs (implName d meth) args md], transfer := .goto join }
    let test ← freshLabel origin "$dispatch_test"
    addBlock test { cmds := [.instanceOf (ident testVar) (args.headD (mkFvar "")) d md],
                    transfer := .condGoto (mkFvar testVar) yes next md }
    return test

partial def splitBlock (prog : Program) (origin label : Label) (pre : Array IRCmd) :
    List IRCmd → DetTransferCmd Label Core.Expression → M Unit
  | [], tr => addBlock label { cmds := pre.toList, transfer := tr }
  | c :: cs, tr =>
    match c with
    | .virtualCall lhs owner meth args md =>
      match prog.overriders owner meth with
      | [] => splitBlock prog origin label (pre.push (.call lhs (implName owner meth) args md)) cs tr
      | ds => do
        let join ← freshLabel origin "$dispatch_join"
        let first ← chain origin lhs owner meth args md join ds
        addBlock label { cmds := pre.toList, transfer := .goto first }
        splitBlock prog origin join #[] cs tr
    | _ => splitBlock prog origin label (pre.push c) cs tr

def lowerBody (prog : Program) (b : Body) : Body :=
  let act : M Unit := do
    for (l, blk) in b.cfg.blocks do
      splitBlock prog l l #[] blk.cmds blk.transfer
  let ((), st) := act.run {}
  if st.fresh == 0 then { b with cfg := { b.cfg with blocks := st.blocks.toList } } else
  let entry := "$dispatchEntry"
  let init : LBlock := { cmds := [.cmd (.init (ident testVar) (mono .bool) .nondet .empty)],
                         transfer := .goto b.cfg.entry }
  let handlers := b.handlers.map fun h =>
    { h with covered := h.covered ++ (st.added.toList.filter fun (o, _) => h.covered.contains o).map (·.2) }
  { cfg := { entry, blocks := (entry, init) :: st.blocks.toList }, handlers }

def run (m : Module) : Except String Module :=
  let prog := m.program
  .ok (m.mapProcedures fun p => { p with body := p.body.map (lowerBody prog) })

def pass : Pass := { name := "LowerDispatch", run }

end

end Cortex.LowerDispatch
