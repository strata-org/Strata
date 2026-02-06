/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.TranslateAST

/-!
# Roundtrip Tests for Core CST ↔ AST Conversion

This file tests bidirectional conversion: CST → AST → CST → AST
-/

namespace Strata.Test

open Strata.CoreDDM
open Strata
open Core

-- Test roundtrip: CST → AST → CST → AST
def testRoundtrip : Program :=
#strata
program Core;
type T0;
type T1 (a : Type);
type Byte := bv8;
type IntMap := Map int int;
#end

/--
info: true
-/
#guard_msgs in
#eval do
  let ctx := FromCSTContext.empty
  let cmds := testRoundtrip.commands.toList.map fun op =>
    match Command.ofAst op with
    | .ok (cmd : Command SourceRange) => cmd
    | .error e => panic! s!"Failed to convert: {e}"
  
  -- CST → AST
  let (prog, errs1) := programFromCST ctx cmds
  
  -- AST → CST
  let (cmds2, errs2) := programToCST ToCSTContext.empty prog
  
  -- CST → AST again
  let (prog2, errs3) := programFromCST ctx cmds2
  
  -- Check roundtrip
  IO.println (toString (Std.format prog) == toString (Std.format prog2)
    && errs1.isEmpty && errs2.isEmpty && errs3.isEmpty)

end Strata.Test
