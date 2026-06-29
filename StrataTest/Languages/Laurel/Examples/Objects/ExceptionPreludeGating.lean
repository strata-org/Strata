/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Confirms the E1 *prelude gating* (see `docs/design/laurel_extensions.md`,
extension E1, and `Strata/Languages/Laurel/CoreDefinitionsForLaurel.lean`).

`BaseException` is a heap-participating composite, so injecting it into every
program would perturb SMT heap reasoning for programs that never throw. The
pipeline therefore prepends the exception prelude **only when the user program
references `BaseException`** (directly, or via a subtype whose `extends` chain
names it).

These tests lower each program to Core (translation only, no SMT) and check
whether `BaseException` appears in the result:

- a program that uses no exceptions must **not** pull it in (gating off);
- a program that references it must (gating on).
-/

/-- A program that does not mention exceptions at all. -/
private def noExceptionsBlock := #strata
program Laurel;

procedure noExceptions()
  opaque
{
  var x: int := 1;
  assert x == 1
};
#end

/-- A program that references the prelude root `BaseException`. -/
private def usesExceptionsBlock := #strata
program Laurel;

procedure usesExceptions()
  opaque
{
  var e: BaseException := new BaseException;
  e#message := "boom";
  assert e#message == "boom"
};
#end

/-- Lower a parsed snippet to Core and return the pretty-printed program text,
    throwing on a translation failure. The pipeline prepends the (gated)
    prelude, so the result reflects whether `BaseException` was injected. -/
private def loweredCoreText (block : StrataDDM.SourcedProgram) : IO String := do
  let user ← translateLaurel block.program
  let (coreOpt, diags) ← Strata.Laurel.translate {} user
  match coreOpt with
  | some core => return (Std.format core).pretty
  | none =>
    throw <| IO.userError s!"translation failed: {diags.map (·.message)}"

/-- True iff `BaseException` occurs anywhere in `text`. -/
private def mentionsBaseException (text : String) : Bool :=
  (text.splitOn "BaseException").length > 1

-- Gating OFF: a non-exception program must not carry `BaseException`.
#eval do
  let text ← loweredCoreText noExceptionsBlock
  if mentionsBaseException text then
    throw <| IO.userError
      "E1 gating: BaseException leaked into a program that does not use exceptions"
  IO.println "ok: no BaseException injected into a non-exception program"

-- Gating ON: a program referencing `BaseException` must carry it.
#eval do
  let text ← loweredCoreText usesExceptionsBlock
  unless mentionsBaseException text do
    throw <| IO.userError
      "E1 gating: BaseException missing from a program that references it"
  IO.println "ok: BaseException injected into a program that references it"
