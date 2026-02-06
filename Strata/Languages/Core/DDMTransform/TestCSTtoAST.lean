/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core.DDMTransform.TranslateAST

/-!
# Tests for Core CST → AST Translation

This file contains tests to ensure the translation from Core CST to
Core.Program AST works correctly by comparing with the old translator.
-/

namespace Strata.Test

open Strata.CoreDDM
open Core

def testProgram : Program :=
#strata
program Core;
// type T0;
// type T1 (a : Type);
// type T2 (a : Type, b : Type);
// type Byte := bv8;
// type Word := bv32;
// type IntMap := Map int int;
type IntAlphaMap (a : Type) := Map int a;
#end


---------------------------------------------------------------------
-- New Translator Tests (using programFromCST)
---------------------------------------------------------------------

open Strata (FromCSTContext programFromCST)

#eval do
  let ctx := FromCSTContext.empty
  let cmds := testProgram.commands.toList.map fun op =>
    dbg_trace f!"op: {repr op}\n"
    match Command.ofAst op with
    | .ok (cmd : Command SourceRange) => cmd
    | .error e => panic! s!"\nCommand.ofAst Error:\n {e}"
  dbg_trace f!"cmds: {repr cmds}"
  --let (newProg, newErrs) := programFromCST ctx cmds
  --let (oldProg, oldErrs) := TransM.run Inhabited.default
  --  (translateProgram testProgram)
  --IO.println (toString (Std.format newProg) == toString (Std.format oldProg)
  --  && newErrs.isEmpty && oldErrs.isEmpty)
