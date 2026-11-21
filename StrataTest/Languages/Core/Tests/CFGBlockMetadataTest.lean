/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.DDMTransform.ASTtoCST
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.Options
meta import Strata.Languages.Core
meta import Strata.Transform.CallElim
meta import Strata.Transform.BetaReduce
meta import StrataDDM
meta import StrataDDM.BuiltinDialects
meta import StrataTest.Languages.Core.Tests.CoreTextTestUtils
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # CFG block metadata

A `cfg` block may carry annotations, written before its label with the same
`@[key, key = "s", key = (e)]` syntax as statements. They are stored as the
block's metadata (`BasicBlock.md`), e.g. loop invariants on a loop-header block.

* Expression values are translated in the scope at the start of the block: they
  see the procedure's parameters and the locals of textually earlier blocks, but
  not the block's own locals.
* An unannotated block has empty metadata (no derived `provenance` entry).
* The formatter prints block annotations under the same `annFilter` as statement
  annotations, hidden by default and shown with `.all`, from which they re-parse
  to the same metadata; except `loopInvariant`, which is always printed, since it
  decides what CFG loop elimination checks.
* The metadata is carried through transforms that rebuild blocks (here, call
  elimination). A `loopInvariant` is read by CFG loop elimination, which
  rejects one on a block that is not a loop header (see `CFGLoopElimTest`);
  other keys do not affect verification.
* The CFG type checker checks expression-valued metadata; see `CFGTypeCheck`. -/

namespace Strata.Test.CFGBlockMetadata

open Strata
open Strata.CoreDDM

def annotatedPgm :=
#strata
program Core;
procedure Inc(x : int, out r : int)
spec { ensures [inc]: (r == int.add(x, 1)); }
{ r := int.add(x, 1); };
procedure NotALoop(n : int, out y : int)
spec { requires (int.ge(n, 0)); }
cfg entry {
  entry: {
    var k : int := 0;
    y := 0;
    goto loop;
  }
  @[loopInvariant = (int.le(y, n)), loopInvariant = (int.ge(y, k)), loopHeader, note = "count up"]
  loop: {
    branch (int.lt(y, n)) goto body else goto done;
  }
  @[note = "calls Inc"]
  body: {
    call Inc(y, out y);
    goto done;
  }
  done: {
    assert [fin]: (int.le(y, n));
    return;
  }
};
#end

/-- `annotatedPgm` with `body` looping back to `loop`, which makes `loop` a loop header,
    so the type checker accepts its `loopInvariant`s. -/
def annotatedLoopPgm :=
#strata
program Core;
procedure Inc(x : int, out r : int)
spec { ensures [inc]: (r == int.add(x, 1)); }
{ r := int.add(x, 1); };
procedure Counted(n : int, out y : int)
spec { requires (int.ge(n, 0)); }
cfg entry {
  entry: {
    var k : int := 0;
    y := 0;
    goto loop;
  }
  @[loopInvariant = (int.le(y, n)), loopInvariant = (int.ge(y, k)), loopHeader, note = "count up"]
  loop: {
    branch (int.lt(y, n)) goto body else goto done;
  }
  @[note = "calls Inc"]
  body: {
    call Inc(y, out y);
    goto loop;
  }
  done: {
    assert [fin]: (int.le(y, n));
    return;
  }
};
#end

private def translate (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- Each CFG block's label and metadata, in program order. -/
private def blockMds (p : Core.Program) : List (String × Imperative.MetaData Core.Expression) :=
  p.decls.flatMap fun d => match d with
    | .proc proc _ => match proc.body with
      | .cfg g _ => g.blocks.map fun (l, b) => (l, b.md)
      | _ => []
    | _ => []

private def printBlockMds (p : Core.Program) : IO Unit :=
  for (l, md) in blockMds p do
    IO.println s!"{l}: {Std.format md}"

/-- Block metadata with expression types erased. -/
private def typeErasedBlockMds (p : Core.Program) :
    List (String × Imperative.MetaData Core.Expression) :=
  (blockMds p).map fun (l, md) => (l, md.mapExprs (·.eraseTypes))

/-- Block metadata with expression types and source locations erased, for comparing
    two translations: a re-parsed expression has the location of its re-parsed text. -/
private def erasedBlockMds (p : Core.Program) :
    List (String × Imperative.MetaData Core.Expression) :=
  (blockMds p).map fun (l, md) => (l, md.mapExprs fun e =>
    e.eraseTypes.replaceMetadata (fun _ => (default : _root_.ExprSourceLoc)))

/-! ## Translation -/

/--
info: entry: ⏎
loop: #[<[loopInvariant]: int.le(y, n)>, <[loopInvariant]: int.ge(y, k)>, <[loopHeader]: true>, <[note]: count up>] ⏎
body: #[<[note]: calls Inc>] ⏎
done:
-/
#guard_msgs in
#eval printBlockMds (translate annotatedPgm.program)

/-! ## A block's own locals are not in scope of its annotations -/

/-- error: Unknown expr identifier z -/
#guard_msgs (error, drop info) in
def ownLocalPgm :=
#strata
program Core;
procedure P(out y : int)
cfg entry {
  @[note = (z)]
  entry: {
    var z : int := 0;
    y := z;
    return;
  }
};
#end

/-! ## Formatting and re-parsing -/

-- Hidden by the default filter, like statement annotations, except the loop invariants.
/--
info: program Core;

procedure NotALoop (n : int, out y : int)
spec {
  requires [NotALoop_requires_0]: int.ge(n, 0);
  } cfg entry {
  entry: {
    var k : int := 0;
    y := 0;
    goto loop;
  }
  @[loopInvariant = ((int.le(y, n))), loopInvariant = ((int.ge(y, k)))] loop: {
    branch (int.lt(y, n)) goto body else goto done;
  }
  body: {
    call Inc(y, out y);
    goto done;
  }
  done: {
    assert [fin]: int.le(y, n);
    return;
  }
};
-/
#guard_msgs in
#eval IO.println (Core.formatProgram
  { decls := (translate annotatedPgm.program).decls.drop 1 }).pretty

private def parseText (text : String) : IO StrataDDM.Program :=
  Strata.Core.TestUtils.parseCoreText "roundtrip" text.toUTF8

-- Shown with `.all`, and re-parsed to the same block metadata.
/--
info: @[loopInvariant = ((int.le(y, n))), loopInvariant = ((int.ge(y, k))), loopHeader, note = "count up"] loop: {
roundtrip preserves block metadata: true
-/
#guard_msgs in
#eval show IO Unit from do
  let ast := translate annotatedPgm.program
  let text := (Core.formatProgram ast (annFilter := .all)).pretty
  for line in text.splitOn "\n" do
    if (line.trimAscii.toString.startsWith "@[loopInvariant") then IO.println line.trimAscii
  let ast' := translate (← parseText text)
  IO.println s!"roundtrip preserves block metadata: {erasedBlockMds ast == erasedBlockMds ast'}"

/-! ## Transforms and verification -/

-- Call elimination rewrites `body`'s commands and adds declarations to `entry`,
-- and keeps every block's metadata, including that of `body`.
/-- info: (true, true) -/
#guard_msgs in
#eval
  let ast := translate annotatedPgm.program
  match Core.Transform.run ast Core.CallElim.callElim' with
  | .ok (_, ast') =>
    let rewritten := (blockMds ast').length == (blockMds ast).length &&
      ast'.decls.any fun d => match d with
        | .proc proc _ => match proc.body with
          | .cfg g _ => g.blocks.any fun (l, b) => l == "body" && b.md.size == 1 &&
              b.cmds.all fun c => match c with | .call .. => false | _ => true
          | _ => false
        | _ => false
    (rewritten, erasedBlockMds ast' == erasedBlockMds ast)
  | .error _ => (false, false)

-- `loop` is not a loop header (no edge into it comes from a block it
-- dominates), so its `loopInvariant`s are an error rather than ignored: the CFG type
-- checker, which runs first, reports it.
/--
error: ❌ Type checking error.
Procedure 'NotALoop': [NotALoop]: block "loop" has a `loopInvariant` but is not a loop header (the target of an edge from a block it dominates).
-/
#guard_msgs in
#eval Strata.Core.verify annotatedPgm
  (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

def inertPgm :=
#strata
program Core;
procedure Inert(n : int, out y : int)
spec { requires (int.ge(n, 0)); }
cfg entry {
  entry: {
    y := 0;
    goto loop;
  }
  @[loopHeader, note = "count up", bound = (int.add(n, 1))]
  loop: {
    branch (int.lt(y, n)) goto body else goto done;
  }
  body: {
    y := int.add(y, 1);
    goto done;
  }
  @[note = (false)]
  done: {
    assert [fin]: (int.le(y, n));
    assert [past_n]: (y == int.add(n, 1));
    return;
  }
};
#end

-- Other keys are inert: neither checked (`note = (false)` raises no failure)
-- nor assumed (it does not make `past_n` hold), so the results are those
-- without them. `fin` holds on both paths: `y` is `0 ≤ n` on the direct
-- exit, and `y + 1 ≤ n` after one increment.
/--
info:
Obligation: fin
Property: assert
Result: ✅ pass

Obligation: past_n
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Core.verify inertPgm
  (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## Annotations of a block that declares locals

The formatter prints a block's annotations in the scope at the start of the
block, before the block's own declarations, as the parser reads them. -/

def localsPgm :=
#strata
program Core;
procedure Q(n : int, out y : int)
cfg entry {
  entry: {
    var k : int := 0;
    y := 0;
    goto loop;
  }
  @[loopInvariant = (int.le(y, n)), other = (int.ge(k, 0))]
  loop: {
    var t : int := 1;
    var u : int := 2;
    branch (int.lt(y, n)) goto done else goto done;
  }
  done: {
    return;
  }
};
#end

/--
info: @[loopInvariant = ((int.le(y, n))), other = ((int.ge(k, 0)))] loop: {
roundtrip preserves block metadata: true
-/
#guard_msgs in
#eval show IO Unit from do
  let ast := translate localsPgm.program
  let text := (Core.formatProgram ast (annFilter := .all)).pretty
  for line in text.splitOn "\n" do
    if (line.trimAscii.toString.startsWith "@[loopInvariant") then IO.println line.trimAscii
  let ast' := translate (← parseText text)
  IO.println s!"roundtrip preserves block metadata: {erasedBlockMds ast == erasedBlockMds ast'}"


/-! ## Beta reduction and type erasure reach block metadata -/

/-- `p` with every block annotation's expression replaced by `f` of it. -/
private def mapBlockMds (f : Core.Expression.Expr → Core.Expression.Expr) (p : Core.Program) :
    Core.Program :=
  { decls := p.decls.map fun d => match d with
    | .proc q md => match q.body with
      | .cfg g o => .proc { q with body := .cfg { g with blocks := g.blocks.map fun (l, b) =>
          (l, { b with md := b.md.mapExprs f }) } o } md
      | _ => d
    | _ => d }

-- Each annotation of `annotatedPgm` becomes the redex `(λ x. x) e`, which beta
-- reduction undoes.
/-- info: true -/
#guard_msgs in
#eval
  let p := translate annotatedPgm.program
  let redex := mapBlockMds (fun e => .app default (.abs default "x" none (.bvar default 0)) e) p
  erasedBlockMds (Core.BetaReduce.betaReduceProgram redex) == erasedBlockMds p &&
    erasedBlockMds redex != erasedBlockMds p

-- Type checking annotates the annotations; erasing types removes the annotations
-- again.
/-- info: true -/
#guard_msgs in
#eval
  match Core.typeCheck Core.VerifyOptions.quiet (translate annotatedLoopPgm.program) with
  | .ok p =>
    let erased := blockMds p.eraseTypes
    erased == typeErasedBlockMds p && erased != blockMds p
  | .error _ => false

/-! ## An expression annotation on a statement is an error

An expression value (`@[key = (e)]`) is translated in the bindings at the start of
a CFG block, which a statement does not have, so it is reported with its position. -/

/-- info: #[4:11: annotation `note`: an expression value (`@[note = (e)]`) is supported only on a CFG block] -/
#guard_msgs in
#eval show IO Unit from do
  let text := "program Core;\nprocedure P(out y : int)\n{\n  @[note = (y)]\n  y := 1;\n};\n"
  let p ← parseText text
  let (_, errors) := TransM.run (Lean.Parser.mkInputContext text "annotated.core.st")
    (translateProgram p)
  IO.println errors

end Strata.Test.CFGBlockMetadata

end
