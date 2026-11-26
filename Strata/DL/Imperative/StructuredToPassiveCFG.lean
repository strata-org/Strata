/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.PassiveVCGen
public import Strata.Transform.StructuredToUnstructured

/-! # Deterministic CFGs to passification CFGs

`StructuredToUnstructured.stmtsToCFG` lowers structured statements to a
deterministic CFG, whose branch `condGoto p lt lf` goes to `lt` when `p` holds
and to `lf` otherwise. `PassiveVCGen` works on nondeterministic CFGs, whose
`goto ls` chooses among `ls` with no guard.

A branch cannot become `goto [lt, lf]`: that drops `p`, and lets the `lt` path
run with `p` false. Instead each guard becomes an `assume` on its edge:

```
  B: … ; condGoto p lt lf
```
becomes
```
  B:  … ; goto [$gT$B$lt, $gF$B$lf]
  $gT$B$lt: assume p     ; goto [lt]
  $gF$B$lf: assume (¬ p) ; goto [lf]
```

An unconditional jump (`condGoto p l l`, which is how `goto l` is represented)
becomes `goto [l]`: both edges lead to `l`, so the guard constrains nothing.
`finish` becomes `goto []`.

A residual `call` is an error: the caller runs call elimination first, and
dropping a call would be unsound. -/

namespace Imperative
namespace StructuredToPassiveCFG

open PassiveVCGen (PBlock PCFG mkBlock)

public section

variable {P : PureExpr}

/-- Translate an extended command, failing on a residual procedure call. -/
def cmdExtToCmd (c : CmdExt P) : Except String (Cmd P) :=
  match c with
  | .cmd c'          => .ok c'
  | .call procName _ _ _ =>
    .error s!"structured-to-passive lowering: encountered an un-eliminated call \
              to '{procName}'. Run call elimination before lowering to a \
              passification CFG."

/-- Translate a command list, threading the first error. -/
def cmdExtsToCmds (cs : List (CmdExt P)) : Except String (List (Cmd P)) :=
  cs.mapM cmdExtToCmd

/-- Translate one deterministic block into its passification block and the
    bridge blocks its branch needs, with bridge labels fresh for `taken` (which
    is returned extended with them). -/
def convertBlock [HasBool P] [HasBoolOps P]
    (taken : Std.HashSet String) (label : String) (blk : DetBlock String (CmdExt P) P)
    : Except String (List (String × PBlock P) × Std.HashSet String) := do
  let cmds ← cmdExtsToCmds blk.cmds
  match blk.transfer with
  | .finish md =>
    .ok ([(label, { mkBlock cmds [] md with md := blk.md })], taken)
  | .condGoto p lt lf md =>
    if lt == lf then
      .ok ([(label, { mkBlock cmds [lt] md with md := blk.md })], taken)
    else
      let tl := Strata.Name.freshName taken s!"$gT${label}${lt}"
      let taken := taken.insert tl
      let fl := Strata.Name.freshName taken s!"$gF${label}${lf}"
      let taken := taken.insert fl
      let mainBlk : PBlock P := { mkBlock cmds [tl, fl] md with md := blk.md }
      let trueBridge : PBlock P :=
        mkBlock [HasPassiveCmds.assume (P := P) (CmdT := Cmd P) "" p .empty] [lt]
      let falseBridge : PBlock P :=
        mkBlock [HasPassiveCmds.assume (P := P) (CmdT := Cmd P) ""
                   (HasBoolOps.not (P := P) p) .empty] [lf]
      .ok ([(label, mainBlk), (tl, trueBridge), (fl, falseBridge)], taken)

/-- Convert a deterministic CFG over `CmdExt P` into a passification CFG,
    turning every branch guard into `assume`s on its edges. Fails on a residual
    `call`. Cycles are kept: `PassiveVCGen.defObligations` rejects them. -/
def convert [HasBool P] [HasBoolOps P]
    (cfg : CFG String (DetBlock String (CmdExt P) P)) : Except String (PCFG P) := do
  let mut taken : Std.HashSet String := Std.HashSet.ofList (cfg.blocks.map (·.1))
  let mut blocks : Array (String × PBlock P) := #[]
  for (l, b) in cfg.blocks do
    let (bs, taken') ← convertBlock taken l b
    taken := taken'
    blocks := blocks ++ bs.toArray
  return { entry := cfg.entry, blocks := blocks.toList }

end -- public section

end StructuredToPassiveCFG
end Imperative
