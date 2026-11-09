/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure foo()
  opaque
{
  <?>
//^^^ error: could not infer type
};
#end

-- A hole as an `if`'s then-branch is typed at the else-branch's `int`.
#eval testLaurelVerification <|
#strata
program Laurel;
procedure holeBranch(b: bool, x: int) opaque {
  assert (if b then <?> else x) == x
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### A hole argument of a generic call

A hole at a parameter that mentions a type parameter takes the parameter at the instantiation the
call records, as `select(m, <?>)` in `Execution/Types/Maps.lean` does: here an overloaded generic,
a constructor and an instance call, and a call in a generic procedure, whose hole's procedure takes
the inputs and so declares `A`. -/

#eval testLaurelVerification <|
#strata
program Laurel;
datatype Pair<A, B> { MkPair(b: B, a: A, a2: A) }
composite C { procedure gen<U>(self: C, x: U, y: U) returns (r: U) opaque; }
procedure pick(x: int) opaque;
procedure pick<T>(m: TotalMap T bool, k: T) opaque;
procedure atInstantiation(c: C, m: TotalMap int bool) opaque {
  pick(m, <?>);
  var p := MkPair(true, <?>, 5);
  assert Pair..a2!(p) == 5 && Pair..b!(p);
  var x: TotalMap int bool := c#gen(<?>, m)
};
procedure inGenericBody<A>(a: A, m: TotalMap int bool) opaque {
  var b: bool := select(m, <?>)
};
#end

/-! Not typed, and reported:
- where the call records no instantiation: `id`, whose `X` only the expected type gives;
- where a recorded type argument is no value type: a type variable of the caller's (`sameType` at
  `r: A`), `Unknown` (`MkQ`, whose `T` only the holes give), `void` or several outputs;
- where the parameter would mention a generic datatype's bare name, which a tester's parameter as
  the call's expected type and a destructor give. -/

#eval testLaurelVerification <|
#strata
program Laurel;
datatype Opt<T> { Som(value: T), Non() }
datatype Q<T> { MkQ(a: Set<T>, b: T) }
procedure id<X>(x: X) returns (r: X) opaque;
procedure sameType<T>(x: T, y: T) opaque;
procedure mk<X>() returns (r: X) opaque;
procedure returnsNothing() opaque;
procedure twoOutputs() returns (a: int, b: int) opaque;
procedure pickFromOpt<V>(o: Opt<V>) returns (r: V) opaque;
procedure atCallerTypeVariable<A>() returns (r: A) opaque {
  r := mk();
  sameType(r, <?>)
//            ^^^ error: could not infer type
};
procedure notTyped() opaque {
  var x: int := id(<?>);
//                 ^^^ error: could not infer type
  var q := MkQ(<?>, <?>);
//             ^^^ error: could not infer type
//                  ^^^ error: could not infer type
  sameType(returnsNothing(), <?>);
//                           ^^^ error: could not infer type
  sameType(twoOutputs(), <?>);
//                       ^^^ error: could not infer type
  assume Opt..isSom(select(<?>, 1));
//                         ^^^ error: could not infer type
  assume Opt..isSom(pickFromOpt(<?>));
//                              ^^^ error: could not infer type
  var y: int := Opt..value!(<?>)
//                          ^^^ error: could not infer type
};
#end

-- A type parameter that no input or output mentions is reported beside a hole too, as without it:
-- no call determines it.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure two<T, U>(x: T, y: T) opaque;
procedure u() opaque {
  two(1, <?>)
//^^^^^^^^^^^ error: cannot infer type argument 'U' of 'two': annotate the variable or output it is assigned to with a concrete type
};
#end
