/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Parse

/-!
# Tests for Core.Program → CST Conversion

This file tests one-direction conversion: AST → CST using the old
translator to obtain the AST.
-/

namespace Strata.Test

open Strata.CoreDDM
open Strata
open Core

def testProgram : Program :=
#strata
program Core;
type T0;
type T1 (x : Type);
type Byte := bv8;
type IntMap := Map int int;
const fooConst : int;
function id(x : int, y : int) : int { y }
#end

#print CoreDDM.Expr

#eval do
  -- Use old translator to get AST
  let (ast, errs) := TransM.run Inhabited.default (translateProgram testProgram)
  if !errs.isEmpty then
    IO.println f!"CST to AST Error: {errs}"

  -- Convert AST → CST
  let (cmds, errs) := programToCST (M := SourceRange) ToCSTContext.empty ast
  if !errs.isEmpty then
    IO.println "AST to CST Error: {errs}"

  -- Format with original global context
  let ctx := FormatContext.ofDialects testProgram.dialects
    testProgram.globalContext {}
  let state : FormatState := {
    openDialects := testProgram.dialects.toList.foldl (init := {})
      fun a (d : Dialect) => a.insert d.name
  }

  -- Display commands using mformat
  IO.println "Rendered Program:\n"
  for cmd in cmds do
    IO.print ((mformat (ArgF.op cmd.toAst) ctx state).format)

end Strata.Test
