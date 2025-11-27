/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Minimal Laurel dialect for AssertFalse example
import Strata

#dialect
dialect LaurelMinimal;

// Basic types
type bool;
type void;

// Boolean literals
fn boolTrue : bool => "true";
fn boolFalse : bool => "false";

// Statements
op assert (cond : bool) : Command => "assert " cond ";\n";
op assume (cond : bool) : Command => "assume " cond ";\n";
op block (stmts : Seq Command) : Command => "{\n" stmts "}\n";

// Procedure definition
op procedure (body : Command) : Command => "procedure() " body;
op valDecl (name : Ident, proc : Command) : Command => "val " name " = " proc "\n";

#end
