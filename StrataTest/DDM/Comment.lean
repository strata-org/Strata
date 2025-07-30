/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
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
info: decl foo;
/*@ annotation */ decl bar;
//@ inline
decl bar;
-/
#guard_msgs in
#eval IO.println <| example1.format
