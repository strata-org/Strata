/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the resolution pass detects kind mismatches — e.g. using a variable
where a type is expected, or calling a type as if it were a procedure.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Using a variable name where a type is expected -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var y: x := 2
//       ^ error: 'x' resolves to variable, but expected composite type, constrained type, datatype definition, type alias
};
#end

/-! ## Using a procedure name where a type is expected -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure bar() opaque { };
procedure foo() opaque {
  var y: bar := 1
//       ^^^ error: 'bar' resolves to static procedure, but expected composite type, constrained type, datatype definition, type alias
};
#end

/-! ## Calling a composite type as a static call -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Foo { }
procedure bar() opaque {
  var x: int := Foo()
//              ^^^^^ error: 'Foo' resolves to composite type, but expected parameter, static procedure, datatype constructor, datatype destructor, constant
};
#end

/-! ## Using a procedure name with `new` -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure bar() opaque { };
procedure foo() opaque {
  var x: int := new bar
//              ^^^^^^^ error: 'bar' resolves to static procedure, but expected composite type, datatype definition
};
#end

/-! ## Extending a non-composite type (e.g. a constrained type) -/

#eval testLaurelResolution <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
composite Foo extends nat { }
//                    ^^^ error: 'nat' resolves to constrained type, but expected composite type
#end

/-! ## Multi-output procedure used in expression position -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure multi(x: int) returns (a: int, b: int) opaque;
procedure test() opaque {
  assert multi(1) == 1
//       ^^^^^^^^ error: multi-output call cannot be used as a value here
};
#end

/-! ## Destructor result assigned to wrong type -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype IntList { Nil(), Cons(head: int, tail: IntList) }
procedure test() opaque {
  var xs: IntList := Cons(1, Nil());
  var x: bool := IntList..head!(xs)
//               ^^^^^^^^^^^^^^^^^^ error: expected 'bool', got 'int'
};
#end

/-! ## Duplicate type parameters on a datatype -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Foo<T, T> {
//       ^^^ error: duplicate type parameter(s): T
  Mk(x: T)
}
#end

/-! ## Undeclared type name in a datatype constructor argument -/

-- A name in a constructor arg that is neither a declared type nor one of the
-- datatype's type parameters must still be reported as undefined (not silently
-- treated as a type variable).
#eval testLaurelResolution <|
#strata
program Laurel;
datatype Box<T> {
  Mk(x: Undeclared)
//      ^^^^^^^^^^ error: Resolution failed: 'Undeclared' is not defined
}
#end

/-! ## Constrained (subset) type as a generic datatype type argument -/

-- A constrained (subset) type used as a *type argument* of a generic datatype is
-- rejected at resolution time, in any position. Subset types are not yet
-- supported under polymorphism: the argument lowers through `resolveBaseType`,
-- which over-approximates it to its base (`int32` -> `int`) and silently drops
-- the refinement, so a value outside the subset would verify clean. Rather than
-- accept that, resolution rejects it wherever it appears.

-- (1) In a variable's type — `resolveHighType`'s `.Applied` arm.
#eval testLaurelResolution <|
#strata
program Laurel;
constrained int32 = x: int where 0 <= x && x < 100 witness 0
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
procedure foo() opaque {
  var o: Option<int32> := Nothing()
//              ^^^^^ error: constrained (subset) type 'int32' is not yet supported as a generic datatype type argument
};
#end

-- (2) In a datatype constructor field's type (resolved via `resolveHighType`
--     with the datatype's type parameters in scope).
#eval testLaurelResolution <|
#strata
program Laurel;
constrained int32 = x: int where 0 <= x && x < 100 witness 0
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
datatype Wrap {
  W(inner: Option<int32>)
//                ^^^^^ error: constrained (subset) type 'int32' is not yet supported as a generic datatype type argument
}
#end

/-! ## Malformed generic datatype references and applications

These are detected and reported in Laurel resolution rather than deferred to
Core, so the user gets a diagnostic naming the type and the problem. -/

-- A bare (unapplied) reference to a generic datatype is rejected: its type
-- arguments would otherwise be inferred by first use elsewhere in the program,
-- which is order-dependent. The user must apply it (`Option<int>`).
#eval testLaurelResolution <|
#strata
program Laurel;
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
procedure foo() opaque {
  var o: Option := Nothing()
//       ^^^^^^ error: generic datatype 'Option' must be applied to 1 type argument(s)
};
#end

-- Too many type arguments: the application arity must match the datatype's
-- declared type-parameter count.
#eval testLaurelResolution <|
#strata
program Laurel;
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
procedure foo() opaque {
  var o: Option<int, string> := Nothing()
//       ^^^^^^^^^^^^^^^^^^^ error: generic datatype 'Option' expects 1 type argument(s) but 2 were provided
};
#end

-- Type arguments applied to a non-generic datatype.
#eval testLaurelResolution <|
#strata
program Laurel;
datatype Plain {
  MkPlain()
}
procedure foo() opaque {
  var p: Plain<int> := MkPlain()
//       ^^^^^^^^^^ error: type 'Plain' is not generic and cannot be applied to type arguments
};
#end

-- Type arguments applied to a non-generic *composite* type. The `appliedType`
-- grammar op accepts any identifier as a base, so `C<int>` parses; resolution
-- rejects it via the applied-type arity check (`C` has 0 declared params)
-- rather than letting it reach Core as an internal-error strata-bug.
#eval testLaurelResolution <|
#strata
program Laurel;
composite C { var v: int }
datatype Wrap {
  W(inner: C<int>)
//         ^^^^^^ error: 'C' expects 0 type argument(s) but 1 were provided
}
#end

-- Type arguments applied to a constrained (subset) type (`int32<int>`) — a
-- constrained base is never generic, so `checkTypeApplication` rejects it
-- (before the applied-type arity check the composite case hits).
#eval testLaurelResolution <|
#strata
program Laurel;
constrained int32 = x: int where 0 <= x && x < 100 witness 0
datatype Wrap {
  W(inner: int32<int>)
//         ^^^^^^^^^^ error: type 'int32' is not generic and cannot be applied to type arguments
}
#end

-- A datatype's own type parameter cannot itself be applied to type arguments
-- (`T<int>`): rejected during resolution rather than surfacing as a Core-level
-- strata-bug.
#eval testLaurelResolution <|
#strata
program Laurel;
datatype Bad<T> {
  MkB(x: T<int>)
//       ^^^^^^ error: type parameter 'T' cannot be applied to type arguments
}
#end

/-! ## A type parameter is scoped to its own datatype

A datatype's type parameter is in scope only while resolving that datatype's
constructor argument types — it is resolved through the normal scope, so it does
not leak into sibling declarations. Referencing `Option`'s parameter `T` from a
procedure signature is therefore an ordinary "not defined" error. -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
procedure foo(x: T) opaque { };
//               ^ error: Resolution failed: 'T' is not defined
#end

/-! ## A type parameter shadowing a same-named global constrained type

When a datatype's type parameter `T` shares a name with a global `constrained T`,
the field `x: T` is the type parameter (a polymorphic slot), not the subset type,
so a constructor argument of any type resolves cleanly — `Mk(true)` is accepted
even though the global `T`'s base is `int`. The polymorphic-slot check keys off
the datatype's own type parameters *before* unfolding; otherwise `unfold` (keyed
on type-name text via the global constrained/alias map) would rewrite the field's
`T` to `int` and spuriously reject the argument. Resolution only: the constrained
(subset) type *elimination* pass has its own text-keyed-unfold collision on the
shared name, which is out of scope here and tracked separately. -/

#eval testLaurelResolution <|
#strata
program Laurel;
constrained T = x: int where 0 <= x witness 0
datatype Foo<T> {
  Mk(x: T)
}
procedure useFoo() opaque {
  var f: Foo<bool> := Mk(true)
};
#end

/-! ## A container-typed field over a type parameter is a polymorphic slot

A field is a polymorphic slot when its declared type *mentions* a type parameter
anywhere, not only when it is one. `Map int T` is erased just like `T`, so a
concrete instantiation must be accepted: checking the argument against the
declared type would compare `Map int int` with the phantom `T` and reject every
construction site. -/
#eval testLaurelResolution <|
#strata
program Laurel;
datatype Foo<T> {
  Mk(m: Map int T)
}
procedure buildFoo(m0: Map int int) opaque {
  var f: Foo<int> := Mk(m0)
};
#end

-- Nested in a generic application: the field type `Option<T>` mentions the
-- parameter under an `.Applied`, so it is a slot too.
#eval testLaurelResolution <|
#strata
program Laurel;
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
datatype Wrapper<T> {
  WrapOpt(inner: Option<T>)
}
procedure buildWrapper(o: Option<int>) opaque {
  var w: Wrapper<int> := WrapOpt(o)
};
#end

/-! ## A constrained type under a container inside a type argument

The rejection of constrained types as type arguments inspects the whole argument,
not just its head: smuggling `int32` under a `Map` inside the argument reaches the
same refinement-dropping outcome (`resolveBaseType` over-approximates it and the
elimination pass finds no enforcement point for it), so it is rejected too. -/
#eval testLaurelResolution <|
#strata
program Laurel;
constrained int32 = x: int where 0 <= x && x < 100 witness 0
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
procedure nestedConstrainedArg() opaque {
  var o: Option<Map int int32> := Nothing()
//                      ^^^^^ error: constrained (subset) type 'int32' is not yet supported as a generic datatype type argument
};
#end

/-! ## A generic datatype instantiation as a composite field type

A generic datatype instantiation (`Option<int>`) as a composite field resolves
cleanly: `HeapParameterization` boxes it into a per-instantiation `Box` variant
(the `.Applied` boxing arm), so it does not abort the pipeline. -/
#eval testLaurelResolution <|
#strata
program Laurel;
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
composite Holder {
  var o: Option<int>
}
#end
