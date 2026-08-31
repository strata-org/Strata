/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.PackageFunctionOutputs
import StrataLaurel.Implementation.FunctionalRewrite
import StrataLaurel.Implementation.EliminateReturnStatements
import StrataLaurel.Implementation.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Parse + resolve a program, lower its returns, then run the two packaging passes
    in pipeline order, printing the datatypes and function bodies before and after.

    The re-resolve `packageFunctionOutputsPass` requests is deliberately *not* run in
    between: this harness builds a bare `LaurelProgram` without the
    operator wrappers a real program carries, so a resolve here only reports those as
    undefined. `MultiOutputTransparentBody.lean` pins the whole pipeline instead. -/
private def printPackaged (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  let lowered := eliminateReturnStatements (.Unordered result.program)
  let loweredProcs := match lowered with
    | .Unordered p => p.staticProcedures
    | _ => []
  let uc : LaurelProgram :=
    { staticProcedures := [], staticFunctions := loweredProcs,
      staticFields := [], types := [], constants := [] }
  let printUc (u : LaurelProgram) : IO Unit := do
    -- Only the generated output datatypes are printed; the other `TypeDefinition`
    -- variants are not what this harness is about.
    for t in u.types do
      match t with
      | .Datatype dt =>
        IO.println (toString (Std.Format.pretty (Std.ToFormat.format dt)))
      | _ => pure ()
    for proc in u.staticFunctions do
      IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))
  let unordered (p : Program) : LaurelProgram :=
    match p with | .Unordered u => u | _ => uc
  IO.println "-- before --"
  printUc uc
  let (p1, d1, _) := packageFunctionOutputsPass.run {} (.Unordered uc) result.model
  let (p2, d2, _) := functionalRewritePass.run {} p1 result.model
  IO.println "-- after --"
  printUc (unordered p2)
  for d in d1 ++ d2 do
    IO.println s!"diagnostic[{d.kind}]: {d.message}"

/-! ## Two outputs become one datatype value -/

/--
info: -- before --
procedure divmod(a: int, b: int)
  returns (q: int, r: int)
{
  q := a / b;
  r := a - q * b
}$return;
-- after --
datatype $outputs_divmod { $mkOutputs_divmod(q: int, r: int) }
procedure $declHole_divmod_4(a: int, b: int): int
  opaque;
procedure $declHole_divmod_5(a: int, b: int): int
  opaque;
procedure divmod(a: int, b: int)
  returns ($packedOutputs: $outputs_divmod)
{
  var $declHoleVal_4: int := $declHole_divmod_4(a, b);
  {
    var $declHoleVal_5: int := $declHole_divmod_5(a, b);
    {
      var $v_4: int := $declHoleVal_4;
      {
        var $v_5: int := $declHoleVal_5;
        {
          var $v_4: int := a / b;
          {
            var $v_5: int := a - $v_4 * b;
            $mkOutputs_divmod($v_4, $v_5)
          }
        }
      }
    }
  }
};
-/
#guard_msgs in
#eval printPackaged <|
#strata
program Laurel;
procedure divmod(a: int, b: int) returns (q: int, r: int) {
  q := a / b;
  r := a - q * b
};
#end

/-! ## A call binding one target per output becomes a call plus projections -/

/--
info: -- before --
procedure pair()
  returns (x: int, y: int)
{
  x := 1;
  y := 2
}$return;
procedure usePair()
  returns (s: int)
{
  var p: int;
  var q: int;
  assign p, q := pair();
  {
    s := p + q;
    exit $return
  }
}$return;
-- after --
datatype $outputs_pair { $mkOutputs_pair(x: int, y: int) }
procedure $declHole_pair_3(): int
  opaque;
procedure $declHole_pair_4(): int
  opaque;
procedure $declHole_usePair_5(): int
  opaque;
procedure $declHole_usePair_6(): int
  opaque;
procedure $declHole_usePair_7(): int
  opaque;
procedure pair()
  returns ($packedOutputs: $outputs_pair)
{
  var $declHoleVal_3: int := $declHole_pair_3();
  {
    var $declHoleVal_4: int := $declHole_pair_4();
    {
      var $v_3: int := $declHoleVal_3;
      {
        var $v_4: int := $declHoleVal_4;
        {
          var $v_3: int := 1;
          {
            var $v_4: int := 2;
            $mkOutputs_pair($v_3, $v_4)
          }
        }
      }
    }
  }
};
procedure usePair()
  returns (s: int)
{
  var s: int := $declHole_usePair_5();
  {
    var $declHoleVal_6: int := $declHole_usePair_6();
    {
      var $declHoleVal_7: int := $declHole_usePair_7();
      {
        var $v_6: int := $declHoleVal_6;
        {
          var $v_7: int := $declHoleVal_7;
          {
            var $callOutputs_0 := pair();
            {
              var $v_6: int := $outputs_pair..x($callOutputs_0);
              {
                var $v_7: int := $outputs_pair..y($callOutputs_0);
                {
                  var s: int := $v_6 + $v_7;
                  s
                }
              }
            }
          }
        }
      }
    }
  }
};
-/
#guard_msgs in
#eval printPackaged <|
#strata
program Laurel;
procedure pair() returns (x: int, y: int) {
  x := 1;
  y := 2
};
procedure usePair() returns (s: int) {
  var p: int;
  var q: int;
  assign p, q := pair();
  return p + q
};
#end

/-! ## An inout output gets no declaration, and so no hole -/

/--
info: -- before --
procedure bumpAndDouble(x: int, y: int)
  returns (x: int, d: int)
{
  x := x + 1;
  d := y * 2
}$return;
-- after --
datatype $outputs_bumpAndDouble { $mkOutputs_bumpAndDouble(x: int, d: int) }
procedure $declHole_bumpAndDouble_4(x: int, y: int): int
  opaque;
procedure bumpAndDouble(x: int, y: int)
  returns ($packedOutputs: $outputs_bumpAndDouble)
{
  var $declHoleVal_4: int := $declHole_bumpAndDouble_4(x, y);
  {
    var $v_4: int := $declHoleVal_4;
    {
      var x: int := x + 1;
      {
        var $v_4: int := y * 2;
        $mkOutputs_bumpAndDouble(x, $v_4)
      }
    }
  }
};
-/
#guard_msgs in
#eval printPackaged <|
#strata
program Laurel;
procedure bumpAndDouble(x: int, y: int) returns (x: int, d: int) {
  x := x + 1;
  d := y * 2
};
#end

/-! ## An opaque function's signature is packaged, with no body to rewrite -/

/--
info: -- before --
procedure opaquePair()
  returns (a: int, b: int)
  opaque;
-- after --
datatype $outputs_opaquePair { $mkOutputs_opaquePair(a: int, b: int) }
procedure opaquePair()
  returns ($packedOutputs: $outputs_opaquePair)
  opaque;
-/
#guard_msgs in
#eval printPackaged <|
#strata
program Laurel;
procedure opaquePair() returns (a: int, b: int) opaque;
#end

/-! ## A polymorphic body with several outputs is packaged into a generic datatype

The datatype takes the procedure's own type parameters, so the single packed output is
typed at `$outputs_polyPair<T>` and each ex-output's hole is polymorphic too. -/

/--
info: -- before --
procedure polyPair<T>(a: T)
  returns (p: T, q: T)
{
  p := a;
  q := a
}$return;
-- after --
datatype $outputs_polyPair<T> { $mkOutputs_polyPair(p: T, q: T) }
procedure $declHole_polyPair_4<T>(a: T): T
  opaque;
procedure $declHole_polyPair_5<T>(a: T): T
  opaque;
procedure polyPair<T>(a: T)
  returns ($packedOutputs: ($outputs_polyPair<T>))
{
  var $declHoleVal_4: T := $declHole_polyPair_4(a);
  {
    var $declHoleVal_5: T := $declHole_polyPair_5(a);
    {
      var $v_4: T := $declHoleVal_4;
      {
        var $v_5: T := $declHoleVal_5;
        {
          var $v_4: T := a;
          {
            var $v_5: T := a;
            $mkOutputs_polyPair($v_4, $v_5)
          }
        }
      }
    }
  }
};
-/
#guard_msgs in
#eval printPackaged <|
#strata
program Laurel;
procedure polyPair<T>(a: T) returns (p: T, q: T) {
  p := a;
  q := a
};
#end

/-! ## A call to a polymorphic callee binds an UNANNOTATED temporary

This pass is syntactic and holds no call-site type substitution, so it cannot name the
callee's instantiation — `$outputs_polyPair<int>` here. It leaves the temporary's
annotation off instead, and the re-resolve it requests infers the type from the call.
That is why the printed temporary carries no type while a projection target does.
`MultiOutputTransparentBody.lean` pins that two different instantiations of one callee
both resolve. -/

/--
info: -- before --
procedure polyPair<T>(a: T)
  returns (p: T, q: T)
{
  p := a;
  q := a
}$return;
procedure usePolyPair()
  returns (s: int)
{
  var p: int;
  var q: int;
  assign p, q := polyPair(5);
  {
    s := p + q;
    exit $return
  }
}$return;
-- after --
datatype $outputs_polyPair<T> { $mkOutputs_polyPair(p: T, q: T) }
procedure $declHole_polyPair_5<T>(a: T): T
  opaque;
procedure $declHole_polyPair_6<T>(a: T): T
  opaque;
procedure $declHole_usePolyPair_7(): int
  opaque;
procedure $declHole_usePolyPair_8(): int
  opaque;
procedure $declHole_usePolyPair_9(): int
  opaque;
procedure polyPair<T>(a: T)
  returns ($packedOutputs: ($outputs_polyPair<T>))
{
  var $declHoleVal_5: T := $declHole_polyPair_5(a);
  {
    var $declHoleVal_6: T := $declHole_polyPair_6(a);
    {
      var $v_5: T := $declHoleVal_5;
      {
        var $v_6: T := $declHoleVal_6;
        {
          var $v_5: T := a;
          {
            var $v_6: T := a;
            $mkOutputs_polyPair($v_5, $v_6)
          }
        }
      }
    }
  }
};
procedure usePolyPair()
  returns (s: int)
{
  var s: int := $declHole_usePolyPair_7();
  {
    var $declHoleVal_8: int := $declHole_usePolyPair_8();
    {
      var $declHoleVal_9: int := $declHole_usePolyPair_9();
      {
        var $v_8: int := $declHoleVal_8;
        {
          var $v_9: int := $declHoleVal_9;
          {
            var $callOutputs_0 := polyPair(5);
            {
              var $v_8: int := $outputs_polyPair..p($callOutputs_0);
              {
                var $v_9: int := $outputs_polyPair..q($callOutputs_0);
                {
                  var s: int := $v_8 + $v_9;
                  s
                }
              }
            }
          }
        }
      }
    }
  }
};
-/
#guard_msgs in
#eval printPackaged <|
#strata
program Laurel;
procedure polyPair<T>(a: T) returns (p: T, q: T) {
  p := a;
  q := a
};
procedure usePolyPair() returns (s: int) {
  var p: int;
  var q: int;
  assign p, q := polyPair(5);
  return p + q
};
#end
