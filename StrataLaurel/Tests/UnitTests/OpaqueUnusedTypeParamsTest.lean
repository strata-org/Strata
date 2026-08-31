/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.LaurelCompilationPipeline

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Lowers the program to Core and keeps the type and function declarations
    whose names start with `pfx`; prints `no Core program` and returns `none`
    if lowering fails. -/
private meta def lowerDecls (pfx : String) (program : StrataDDM.Program) :
    IO (Option Core.Program) := do
  let laurelProgram ← translateLaurel program
  let (core?, _, _, _) ← translateWithLaurel {} laurelProgram
  let some core := core? | IO.println "no Core program"; pure none
  let decls := core.decls.filter fun d =>
    d.name.name.startsWith pfx && (d matches .type .. || d matches .func ..)
  pure (some { core with decls })

/-- Lowers the program to Core and prints, as one Core program, the type and
    function declarations whose names start with `pfx`. -/
private meta def printDecls (pfx : String) (program : StrataDDM.Program) :
    IO Unit := do
  let some core ← lowerDecls pfx program | pure ()
  IO.println (Std.format core)

/-- Lowers the program to Core and prints each function's name and type
    parameters and each type's name, for the declarations whose names start
    with `pfx`. -/
private meta def printHeaders (pfx : String) (program : StrataDDM.Program) :
    IO Unit := do
  let some core ← lowerDecls pfx program | pure ()
  for d in core.decls do
    match d with
    | .func f _ =>
      IO.println s!"function {d.name.name}<{", ".intercalate f.typeArgs}>"
    | _ => IO.println s!"type {d.name.name}"

/-! ## A used and an unused type parameter

`T` occurs in the signature and stays a type parameter. `Q` occurs only in the
precondition, so the declared opaque type `mixed$Q$opaque` takes its place. -/

/--
info: program Core;

type mixed$Q$opaque;
function mixed$pre0<T> (t : T) : bool {
  forall x : mixed$Q$opaque :: x == x
}
function mixed$post0<T> (t : T, r$out : T) : bool {
  r$out == t
}
function mixed$asFunction<T> (t : T) : T;
-/
#guard_msgs in
#eval printDecls "mixed" <|
#strata
program Laurel;
procedure mixed<T, Q>(t: T) returns (r: T)
  requires forall(x: Q) => x == x
  opaque
  ensures r == t
{ r := t };
#end

/-! ## A type parameter named like a generated precondition

The opaque type for `pre0` gets a name distinct from the precondition function
`p$pre0`. -/

/--
info: program Core;

type p$pre0$opaque;
function p$pre0 (b : int) : bool {
  forall x : p$pre0$opaque :: x == x
}
function p$asFunction (b : int) : int;
-/
#guard_msgs in
#eval printDecls "p$" <|
#strata
program Laurel;
procedure p<pre0>(b: int) returns (r: int)
  requires forall(x: pre0) => x == x
  opaque;
#end

/-! ## A type parameter used only in the thrown type

`E` stays a type parameter of the derived functions and gets no opaque type. -/

/--
info: function thrower$post0<E>
function thrower$asFunction<E>
-/
#guard_msgs in
#eval printHeaders "thrower" <|
#strata
program Laurel;
procedure thrower<E>(x: int) returns (r: int)
  throws (e: E)
  opaque
  ensures r == x + 1
{ r := x + 1 };
#end

/-! ## A declared name equal to the opaque type's name

A procedure is already named `q$T$opaque`, so the opaque type for `T` takes
the next free name. -/

/--
info: program Core;

type q$T$opaque_1;
function q$pre0 (b : int) : bool {
  forall x : q$T$opaque_1 :: x == x
}
function q$T$opaque$asFunction () : bool;
function q$asFunction (b : int) : int;
-/
#guard_msgs in
#eval printDecls "q$" <|
#strata
program Laurel;
procedure q$T$opaque() opaque;
procedure q<T>(b: int) returns (r: int)
  requires forall(x: T) => x == x
  opaque;
#end

end Strata.Laurel
