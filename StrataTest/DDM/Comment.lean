/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
This is a small example showing syntax overriding a comment.
-/
import Strata.DDM.Integration.Lean

#dialect
dialect Comment;

category Annotation;
op blockAnn (name : Ident) : Annotation => "/*@ " name " */ ";
// Inline annotations work, but there is currently no mechanism to require a newline.
op inlineAnn (name : Ident) : Annotation => "//@ " name:10 "\n";

op decl (name : Ident, ann : Option Annotation) : Command => ann:10 "decl " name ";\n";

#end

def example1 := #strata
program Comment;

decl foo;
/*@ annotation */ decl bar;
//@ inline
decl bar;
#end

/--
info: program Comment;
decl foo;
/*@ annotation */ decl bar;
//@ inline
decl bar;
-/
#guard_msgs in
#eval IO.println <| example1.format
