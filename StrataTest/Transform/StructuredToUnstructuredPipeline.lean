/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Transform.StructuredToUnstructuredPipeline
meta import Strata.Languages.Core.StatementSemantics
meta import Strata.Languages.Core.DDMTransform.Grammar
meta import Strata.Languages.Core.DDMTransform.Translate

meta section

open Imperative Core
open Lambda.LTy.Syntax
open Strata

/-! ## Structured-to-unstructured pipeline examples

Usage examples for the composed `s2uPipeline` and its three individual passes
(`Block.nondetElim`, `Block.hoistLoopPrefixInits`, `stmtsToCFG`), exercised on a
small structured program with a nondeterministic loop that carries a body-local
`init`.

The source programs are written in Strata's DDM concrete syntax (`#strata
program Core; … #end`) and translated to the Core AST.  The S2U passes operate on
the bare imperative layer `Stmt Expression (Cmd Expression)`, whereas a Core
procedure body is `List Core.Statement = List (Stmt Expression Core.Command)` with
`Core.Command = CmdExt Expression` wrapping each bare command; `unwrapBody` below
strips that wrapper on the call-free fragment these examples use. -/

section S2UPipelineExamples

/-- Extract the first procedure's structured body from a translated Core program. -/
def coreBody (p : StrataDDM.SourcedProgram) : List Core.Statement :=
  let corePgm : Core.Program := (TransM.run Inhabited.default (translateProgram p)).fst
  match corePgm.decls.findSome? Decl.getProc? with
  | some proc => match proc.body with
                 | .structured ss => ss
                 | .cfg _ => []
  | none => []

/-- Strip the `CmdExt` wrapper from a Core statement down to the bare imperative
`Stmt Expression (Cmd Expression)` the S2U pipeline consumes.  Total on the
call-free fragment (`init`/`set`/`havoc`/`assert`/`assume`/`cover` commands under
`block`/`ite`/`loop`/`exit`); `.call` and declaration statements are dropped, as
the pipeline examples contain none. -/
partial def unwrapStmt : Core.Statement → List (Stmt Expression (Cmd Expression))
  | .cmd (.cmd c) => [.cmd c]
  | .cmd (.call ..) => []
  | .block lbl ss md => [.block lbl (ss.flatMap unwrapStmt) md]
  | .ite g t e md => [.ite g (t.flatMap unwrapStmt) (e.flatMap unwrapStmt) md]
  | .loop g m inv body md => [.loop g m inv (body.flatMap unwrapStmt) md]
  | .exit lbl md => [.exit lbl md]
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []

/-- The bare imperative body of the first procedure of a `#strata` Core program,
with parser-attached metadata (source provenance) stripped so the examples format
deterministically. -/
def unwrapBody (p : StrataDDM.SourcedProgram) : List (Stmt Expression (Cmd Expression)) :=
  Block.stripMetaData ((coreBody p).flatMap unwrapStmt)

/-- A structured source program: a `while(*)` (nondeterministic-guard) loop whose
body initializes a local `x` and then updates a counter `i`.  This exercises all
three passes — the nondet guard for `nondetElim`, the body-local `init x` for
`hoistLoopPrefixInits`, and the loop control flow for `stmtsToCFG`. -/
def s2uSrc : List (Stmt Expression (Cmd Expression)) :=
  unwrapBody <|
#strata
program Core;
procedure loopWithBodyInit()
{
  var i : int := 0;
  while *
  {
    var x : int := 0;
    havoc i;
  }
};
#end

/-! ### Individual passes

Pass 1 — `nondetElim`: the source has a nondeterministic loop, and `nondetElim`
removes it (the output is `simpleShape`, i.e. has no nondeterministic control). -/
#guard Block.containsNondetLoop s2uSrc == true
#guard Block.containsNondetLoop (Block.nondetElim s2uSrc) == false
#guard Block.simpleShape (Block.nondetElim s2uSrc) == true

/-! Pass 2 — `hoistLoopPrefixInits`: the loop body still `init`s `x`; hoisting
lifts that prefix init out of the loop body, establishing `loopBodyNoInits`. -/
#guard Block.loopBodyNoInits (Block.nondetElim s2uSrc) == false
#guard Block.loopBodyNoInits (Block.hoistLoopPrefixInits (Block.nondetElim s2uSrc)) == true

/-! Pass 3 — `stmtsToCFG`: lowers the (now nondet-free, hoisted) structured
program to a CFG.  Applied to the hoisted output it yields the same CFG the full
pipeline produces. -/
#guard stmtsToCFG (Block.hoistLoopPrefixInits (Block.nondetElim s2uSrc))
         == s2uPipeline s2uSrc

/-! ### Composed pipeline `s2uPipeline`

`s2uPipeline = stmtsToCFG ∘ hoistLoopPrefixInits ∘ nondetElim`.  On the source it
produces a CFG entered at the pre-loop block with one block per control point. -/
#guard (s2uPipeline s2uSrc).entry == "before_loop$_3"
#guard (s2uPipeline s2uSrc).blocks.length == 4

/-! ### What the transformation actually produces

`nondetElim` rewrites the `while(*)` loop into a deterministic loop guarded by a
fresh boolean `$__ndelim_loop$_0` (havoc'd each iteration), and `stmtsToCFG` then
lowers the whole program to a labeled CFG with `condGoto`/`finish` transfers. -/

/-- info: {
  init (i : int) := 0
  init ($__ndelim_loop$_0 : bool)
  while
    $__ndelim_loop$_0
    (none)
    []
  {
    init (x : int) := 0
    havoc i
    havoc $__ndelim_loop$_0
  }
} -/
#guard_msgs in
open Std (format) in
#eval format (Block.nondetElim s2uSrc)

/-- info: Entry: before_loop$_3

before_loop$_3:
  init (i : int) := 0
  init ($__ndelim_loop$_0 : bool)
  init (x : int)
  condGoto true loop_entry$_1 loop_entry$_1
loop_entry$_1:
  condGoto $__ndelim_loop$_0 l$_2 end$_0
l$_2:
  x := 0
  havoc i
  havoc $__ndelim_loop$_0
  condGoto true loop_entry$_1 loop_entry$_1
end$_0:
  finish -/
#guard_msgs in
open Std (format) in
#eval format (s2uPipeline s2uSrc)

/-! ### Example 2 — nondeterministic `.ite` (no loop)

A program with a nondeterministic-guard `if`: `nondetElim` rewrites the nondet
branch into a deterministic guard on a fresh havoc'd variable, so the output is
`simpleShape` and free of nondet control.  There are no loop-body inits, so
`hoistLoopPrefixInits` is the identity here. -/
def iteSrc : List (Stmt Expression (Cmd Expression)) :=
  unwrapBody <|
#strata
program Core;
procedure nondetIte(out x : bool, out y : bool)
{
  if * {
    x := true;
  } else {
    y := false;
  }
};
#end

#guard Block.simpleShape iteSrc == false
#guard Block.simpleShape (Block.nondetElim iteSrc) == true
-- hoisting is a no-op on a loop-free program.
#guard Block.hoistLoopPrefixInits (Block.nondetElim iteSrc)
         == Block.nondetElim iteSrc
#guard (s2uPipeline iteSrc).blocks.length == 4

/-! `nondetElim` rewrites the nondeterministic `.ite` into a deterministic `if`
guarded by a fresh havoc'd boolean, and the pipeline then lowers it to a CFG
whose loop-free control flow is two `condGoto` branches joining at the exit. -/

/-- info: {
  init ($__ndelim_ite$_0 : bool)
  if $__ndelim_ite$_0 {
    x := true
  }
  else {
    y := false
  }
} -/
#guard_msgs in
open Std (format) in
#eval format (Block.nondetElim iteSrc)

/-- info: Entry: ite$_4

ite$_4:
  init ($__ndelim_ite$_0 : bool)
  condGoto $__ndelim_ite$_0 l$_2 l$_3
l$_2:
  x := true
  condGoto true end$_0 end$_0
l$_3:
  y := false
  condGoto true end$_0 end$_0
end$_0:
  finish -/
#guard_msgs in
open Std (format) in
#eval format (s2uPipeline iteSrc)

/-! ### Example 3 — already simple (deterministic guard, no body inits)

A deterministic `while` with no body-local `init`: `nondetElim` leaves it
unchanged (already nondet-free) and `hoistLoopPrefixInits` has nothing to lift,
so the pipeline reduces to `stmtsToCFG` alone. -/
def detSrc : List (Stmt Expression (Cmd Expression)) :=
  unwrapBody <|
#strata
program Core;
procedure detLoop(out i : int)
{
  while (true)
  {
    havoc i;
  }
};
#end

#guard Block.containsNondetLoop detSrc == false
#guard Block.nondetElim detSrc == detSrc
#guard Block.loopBodyNoInits detSrc == true
#guard s2uPipeline detSrc == stmtsToCFG detSrc

/-- info: Entry: loop_entry$_1

loop_entry$_1:
  condGoto true l$_2 end$_0
l$_2:
  havoc i
  condGoto true loop_entry$_1 loop_entry$_1
end$_0:
  finish -/
#guard_msgs in
open Std (format) in
#eval format (s2uPipeline detSrc)

/-! ### Example 4 — early `exit` from a labeled block

A labeled block containing an early `exit` out of itself, guarded by a
nondeterministic `if`.  This exercises the pipeline's exit-routing path (the
`h_covered : exitsCoveredByBlocks` obligation and `pipeline_sound`'s exiting
arm): `nondetElim` rewrites the nondet branch, and `stmtsToCFG` must lower the
`exit outer` to a `goto` targeting the block's continuation label. -/
def exitSrc : List (Stmt Expression (Cmd Expression)) :=
  unwrapBody <|
#strata
program Core;
procedure blockExit(out x : int)
{
  outer: {
    if * {
      exit outer;
    } else {
      havoc x;
    }
  }
};
#end

#guard Block.simpleShape exitSrc == false
#guard Block.simpleShape (Block.nondetElim exitSrc) == true
-- no loops, so hoisting is a no-op.
#guard Block.hoistLoopPrefixInits (Block.nondetElim exitSrc) == Block.nondetElim exitSrc

/-! `nondetElim` rewrites the nondeterministic `if` inside the block into a
deterministic guard on a fresh havoc'd boolean, and `stmtsToCFG` lowers the
`exit outer` to a `condGoto` into the block's continuation label `end$_0` (the
true-branch target), while the else-branch falls through to `havoc x`. -/

/-- info: {
  outer :
  {
    init ($__ndelim_ite$_0 : bool)
    if $__ndelim_ite$_0 {
      exit outer
    }
    else {
      havoc x
    }
  }
} -/
#guard_msgs in
open Std (format) in
#eval format (Block.nondetElim exitSrc)

/-- info: Entry: ite$_3

outer:
  condGoto true ite$_3 ite$_3
ite$_3:
  init ($__ndelim_ite$_0 : bool)
  condGoto $__ndelim_ite$_0 end$_0 l$_2
l$_2:
  havoc x
  condGoto true end$_0 end$_0
end$_0:
  finish -/
#guard_msgs in
open Std (format) in
#eval format (s2uPipeline exitSrc)

/-! ### Example 5 — empty statement list (boundary)

The recursive base case: an empty source program. `s2uPipeline []` produces a
single terminal block with no statements — the entry is the `finish` block
itself. This pins the base case of the recursive CFG construction. -/

#guard (s2uPipeline (P := Expression) []).blocks.length == 1
#guard (s2uPipeline (P := Expression) []).entry == "end$_0"

/-- info: Entry: end$_0

end$_0:
  finish -/
#guard_msgs in
open Std (format) in
#eval format (s2uPipeline (P := Expression) [])

/-! ### Example 6 — nested nondeterministic loops

Two `while(*)` loops, one nested inside the other, the inner body carrying a
body-local `init x`.  This exercises the recursive composition of all three
passes at once: `nondetElim` eliminates both nondet guards (generating two
distinct fresh `$__ndelim_loop$` names), `hoistLoopPrefixInits` lifts the inner
body-local `init` out to its enclosing loop prelude, and `stmtsToCFG` lowers the
two-level loop nest to a CFG with an entry block per loop. -/
def nestedSrc : List (Stmt Expression (Cmd Expression)) :=
  unwrapBody <|
#strata
program Core;
procedure nestedLoops(out i : int)
{
  while *
  {
    while *
    {
      var x : int := 0;
      havoc i;
    }
  }
};
#end

#guard Block.containsNondetLoop nestedSrc == true
#guard Block.containsNondetLoop (Block.nondetElim nestedSrc) == false
#guard Block.simpleShape (Block.nondetElim nestedSrc) == true
#guard Block.loopBodyNoInits (Block.hoistLoopPrefixInits (Block.nondetElim nestedSrc)) == true
#guard stmtsToCFG (Block.hoistLoopPrefixInits (Block.nondetElim nestedSrc))
         == s2uPipeline nestedSrc

/-- info: Entry: before_loop$_6

before_loop$_6:
  init ($__ndelim_loop$_0 : bool)
  init ($__ndelim_loop$_1 : bool)
  init (x : int)
  condGoto true loop_entry$_1 loop_entry$_1
loop_entry$_1:
  condGoto $__ndelim_loop$_0 before_loop$_5 end$_0
before_loop$_5:
  havoc $__ndelim_loop$_1
  havoc x
  condGoto true loop_entry$_3 loop_entry$_3
loop_entry$_3:
  condGoto $__ndelim_loop$_1 l$_4 l$_2
l$_4:
  x := 0
  havoc i
  havoc $__ndelim_loop$_1
  condGoto true loop_entry$_3 loop_entry$_3
l$_2:
  havoc $__ndelim_loop$_0
  condGoto true loop_entry$_1 loop_entry$_1
end$_0:
  finish -/
#guard_msgs in
open Std (format) in
#eval format (s2uPipeline nestedSrc)

end S2UPipelineExamples
end
