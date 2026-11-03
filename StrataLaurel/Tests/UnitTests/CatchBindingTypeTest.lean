/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
What `Check.tryCatch` types a `catch` binding as, pinned at the pass that decides it.

`EliminateExceptions` treats a binding typed `Unknown` as a handler that cannot fire
and DISCARDS the clause (`lowerTry`), so the binding's type is not a convenience — it
decides whether the handler survives into the verified program at all. A regression
here is therefore a silently weaker program three passes later, which is why this
pins the type where it is computed rather than reading the lowered output.

The fragile case is a thrown type with no name to key on. `thrownTypes` has to
carry a primitive `throws (e: int)` or a `throw 7` as a type, because neither names a
composite; if such a type fails to reach the binding, the binding is `Unknown` and the
handler is deleted silently. The primitive cases below are what hold that up.

The join is computed over TYPES (`TypeLattice.commonAncestorType`), by one path for
every shape: composites join at their least common ancestor through the `extending`
graph, and anything with no hierarchy (a primitive here) reaches the same walk's
`highEq` fallback and so joins only with itself. Both shapes are pinned below because
that single path is the only thing making them agree. A `try` that can throw two
unrelated types has no join at all and is a hard error, which keeps `Unknown` from
being reachable by accident.

Generic exceptions are pinned too: joining over types rather than over `extending`-graph
NAMES is what lets `Box<int>` stay `Box<int>` instead of erasing to the head `Box`, and
what makes `Box<int>` and `Box<bool>` have no join at all.
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.Resolution
import StrataLaurel.Implementation.MapStmtExpr

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- The `bindingType` of every `catch` clause in `proc`, in traversal order,
    rendered the way a diagnostic would render it. -/
private def catchBindingTypes (proc : Procedure) : List String :=
  match proc.body.implementation with
  | none => []
  | some impl =>
    (foldStmtExpr (fun e acc =>
      match e.val with
      | .Try _ catches _ =>
        acc ++ catches.map (fun c => toString (formatHighTypeVal c.bindingType.val))
      | _ => acc) [] impl)

/-- `withBuiltins`, because every operator in these snippets (`<`, `-`) is a call to a
    `$`-prefixed prelude wrapper; resolving a bare snippet would report each as
    undefined and bury the type being pinned. -/
private def report (src : String) : IO Unit := do
  let parsed ← (Strata.parseLaurelText "<catch-binding-type-test>" src : IO LaurelProgram)
  let resolved := resolve (withBuiltins parsed)
  for p in resolved.program.staticProcedures do
    let tys := catchBindingTypes p
    unless tys.isEmpty do
      IO.println s!"{p.name.text}: {", ".intercalate tys}"
  for d in resolved.errors do
    IO.println s!"{d.kind}: {d.message}"

/-! ## A primitive `throws` type reaches the binding -/

/-- The thrown type is carried by the callee's `throws` clause, which is a primitive.
    `int`, not `Unknown`: `Unknown` here is what made `EliminateExceptions` delete the
    handler. -/
private def primitiveFromCallee := r"
procedure risky(x: int) returns (r: int) throws (e: int) opaque {
  if x < 0 then { throw 7 };
  r := x
};
procedure demo(x: int) returns (r: int) opaque {
  var n: int := 0;
  try { n := risky(x) } catch c { n := 0 - c };
  r := n
};
"

/-- info: demo: int -/
#guard_msgs in
#eval report primitiveFromCallee

/-- A direct `throw` of an integer literal, with no `throws` clause in sight to carry
    the type: the operand itself is what types the binding. -/
private def primitiveFromLiteral := r"
procedure demo(x: int) returns (r: int) opaque {
  var n: int := 0;
  try { throw 7 } catch c { n := 0 - c };
  r := n
};
"

/-- info: demo: int -/
#guard_msgs in
#eval report primitiveFromLiteral

/-- A `throw` of a declared local reads the declaration's annotation, which the
    traversal threads through the enclosing block. Also a primitive, so it also has
    no name for the join to key on. -/
private def primitiveFromLocal := r"
procedure demo() returns (r: bool) opaque {
  var flag: bool := true;
  try { throw flag } catch c { r := c };
  r := false
};
"

/-- info: demo: bool -/
#guard_msgs in
#eval report primitiveFromLocal

/-! ## The composite path

A set of composites joins at its least common ancestor through the `extending` graph.
Pinned here so a change to the join cannot fix one kind of thrown type by breaking
this one. -/

/-- Two thrown composites join at their least common ancestor, not at either leaf. -/
private def compositeLub := r"
composite Err {}
composite ParseErr extends Err {}
composite ArithErr extends Err {}
procedure demo(x: int) returns (r: int) opaque {
  var p: ParseErr := new ParseErr;
  var a: ArithErr := new ArithErr;
  try {
    if x < 0 then { throw p } else { throw a }
  } catch c { r := 1 };
  r := 0
};
"

/-- info: demo: Err -/
#guard_msgs in
#eval report compositeLub

/-- An alias thrown first joins through its target; a binding at the alias itself keeps the
    alias's name. -/
private def aliasLub := r"
composite Err {}
composite ParseErr extends Err {}
type PE = ParseErr
procedure demo(x: int, p: PE, e: Err) returns (r: int) opaque {
  try { if x < 0 then { throw p } else { throw e } } catch c { r := 1 }
};
procedure alone(p: PE) returns (r: int) opaque {
  try { throw p } catch c { r := 1 }
};
"

/-- info: demo: Err
alone: PE -/
#guard_msgs in
#eval report aliasLub

/-! ## Generic exception types keep their type arguments

The join is stated over types, not over the `extending` graph's node names, because a
name cannot carry type arguments. These pin what that buys: the two routes by which a
generic exception reaches a binding agree on its shape, a subclass joins with an
instantiated parent at the instantiation, and two instantiations of one generic are
correctly unjoinable. -/

/-- The SAME generic exception reaching the binding by both routes: thrown directly as
    `new Box<int>` (typed from the allocation's type arguments) and declared in a
    callee's `throws (e: Box<int>)` (typed from the signature). Both carry the type
    argument, so the two agree and the binding is `Box<int>`. -/
private def genericNewAndCallee := r"
composite Box<T> { var v: T }
procedure thrower() returns (q: int) throws (e: Box<int>) opaque {
  var b: Box<int> := new Box<int>;
  throw b
};
procedure demo(pick: bool) returns (r: int) opaque {
  try {
    if pick then { throw new Box<int> } else { r := thrower() }
  } catch c { r := 1 };
  r := 0
};
"

/-- info: demo: Box<int> -/
#guard_msgs in
#eval report genericNewAndCallee

/-- A subclass of an INSTANTIATED generic joins with that instantiation, at the
    instantiation: `Box<int>`, with the type argument intact. The remap lives in
    `substitutedAncestors`, which is what gives `IntBox` the supertype `Box<int>`. -/
private def genericSubclassLub := r"
composite Box<T> { var v: T }
composite IntBox extends Box<int> { var w: int }
procedure demo(pick: bool) returns (r: int) opaque {
  try { if pick then { throw new Box<int> } else { throw new IntBox } } catch c { r := 1 };
  r := 0
};
"

/-- info: demo: Box<int> -/
#guard_msgs in
#eval report genericSubclassLub

/-- Two instantiations of one generic have NO join: type arguments are invariant, so no
    single binding type could receive both. Rejected during resolution, and named in the
    types the user wrote rather than their monomorphized spelling. -/
private def genericInvariantArgs := r"
composite Box<T> { var v: T }
procedure demo(pick: bool) returns (r: int) opaque {
  try { if pick then { throw new Box<int> } else { throw new Box<bool> } } catch c { r := 1 };
  r := 0
};
"

/-- info: demo: Unknown
userError: the exception types thrown in this `try` block (Box<int>, Box<bool>) have no common ancestor; a `catch` binding needs a single least-common-ancestor type -/
#guard_msgs in
#eval report genericInvariantArgs

/-! ## No join at all -/

/-- A primitive and a composite under one `try` have no common ancestor: no single
    binding type could receive both. This is a hard error rather than a silent
    `Unknown`, which is what keeps the handler-dropping path out of reach. -/
private def noJoin := r"
composite Err {}
procedure demo(x: int) returns (r: int) opaque {
  var e: Err := new Err;
  try {
    if x < 0 then { throw 7 } else { throw e }
  } catch c { r := 1 };
  r := 0
};
"

/-- info: demo: Unknown
userError: the exception types thrown in this `try` block (int, Err) have no common ancestor; a `catch` binding needs a single least-common-ancestor type -/
#guard_msgs in
#eval report noJoin

/-! ## Nothing determinable is thrown -/

/-- A body that throws nothing leaves the binding `Unknown` and the clause is
    discarded downstream — legal, but never silent: the warning is the whole point of
    the case. -/
private def nothingThrown := r"
procedure demo() returns (r: int) opaque {
  try { assert true } catch c { r := 1 };
  r := 0
};
"

/-- info: demo: Unknown
warning: the `catch` clause(s) of this `try` can never fire: no exception type could be determined for the `try` body, so they are discarded and the body is verified as if no handler were present -/
#guard_msgs in
#eval report nothingThrown

/-! ## A generic thrower throws at the call's instantiation

A generic thrower's `throws (e: S)` names its own `S`, which the handler cannot bind and which
would accept the binding as any type. Both routes read the instantiation the call records: the
callee's `throws`, and a thrown call's output. -/

private def genericThrower := r"
composite Cell { var v: int }
procedure thrS<S>(x: S) throws (e: S) opaque { throw x };
procedure idg<T>(x: T) returns (r: T) opaque { r := x };
procedure demo(c: Cell) returns (r: int) opaque {
  try { thrS(c) } catch e { r := 1 };
  try { throw idg(c) } catch e2 { r := 2 };
  r := 0
};
"

/-- info: demo: Cell, Cell -/
#guard_msgs in
#eval report genericThrower

/-- A generic composite's members are read at the receiver's type arguments: its method's
    `throws`, a thrown method result and a thrown field. -/
private def instanceThrower := r"
composite Err {}
composite Holder<T> {
  var item: T
  procedure raise(self: Holder<T>) throws (e: T) opaque { throw self#item };
  procedure get(self: Holder<T>) returns (r: T) opaque { r := self#item };
}
composite Plain {
  procedure fail(self: Plain) throws (e: Err) opaque { throw new Err };
}
procedure demo(h: Holder<Err>, p: Plain) returns (r: int) opaque {
  try { h#raise() } catch e { r := 1 };
  try { throw h#get() } catch e2 { r := 2 };
  try { throw h#item } catch e3 { r := 3 };
  try { p#fail() } catch e4 { r := 4 };
  r := 0
};
"

/-- info: demo: Err, Err, Err, Err -/
#guard_msgs in
#eval report instanceThrower

/-- A method's own type parameters are read at the call's instantiation, which its arguments or
    the type it is assigned at determine: its `throws`, and a thrown result. -/
private def methodTypeParamThrower := r"
composite Err {}
composite Plain {
  procedure raise<U>(self: Plain, x: U) throws (e: U) opaque { throw x };
  procedure idm<U>(self: Plain, x: U) returns (r: U) opaque { r := x };
  procedure mk<U>(self: Plain) returns (r: U) throws (e: U) opaque;
}
procedure demo(p: Plain, er: Err) returns (r: int) opaque {
  try { p#raise(er) } catch e { r := 1 };
  try { throw p#idm(er) } catch e2 { r := 2 };
  var x: Err := new Err;
  try { x := p#mk() } catch e3 { r := 3 };
  r := 0
};
"

/-- info: demo: Err, Err, Err -/
#guard_msgs in
#eval report methodTypeParamThrower

/-- A value of no known type thrown beside a concrete one gives the binding no type either: the
    concrete type alone would accept it as that type. -/
private def unknownBesideConcrete := r"
composite A {}
composite B {}
composite Plain {
  procedure get<U>(self: Plain, x: U) returns (r: U) throws (e: U) opaque { throw x };
}
procedure demo(p: Plain, k: bool) returns (r: int) opaque {
  var a: A := new A;
  try { if k then { a := p#get(<?>) } else { throw new B } } catch e { r := 1 };
  try { if k then { throw <?> } else { throw new B } } catch e2 { r := 2 };
  r := 0
};
"

/-- info: demo: Unknown, Unknown
userError: the `catch` binding of this `try` cannot be typed: the body throws a value of unknown type
userError: the `catch` binding of this `try` cannot be typed: the body throws a value of unknown type -/
#guard_msgs in
#eval report unknownBesideConcrete

/-- A caller's type variable that the receiver passes on is not the method's own, though spelled
    alike. -/
private def callerTypeVariable := r"
composite B {}
composite Holder<T> {
  var item: T
  procedure raise<U>(self: Holder<T>, x: U) throws (e: T) opaque { throw self#item };
  procedure get<U>(self: Holder<T>, x: U) returns (r: T) opaque { r := self#item };
}
procedure demo<U>(h: Holder<U>, b: B) returns (r: int) opaque {
  try { h#raise(b) } catch e { r := 1 };
  try { throw h#get(b) } catch e2 { r := 2 };
  r := 0
};
"

/-- info: demo: U, U -/
#guard_msgs in
#eval report callerTypeVariable

/-- An assignment throws its target's type, as resolution types it, a generic holder's field at
    the holder's type arguments. -/
private def assignThrower := r"
composite Base {}
composite A extends Base {}
composite Holder<T> { var item: T }
procedure demo(h: Holder<Base>) returns (r: int) opaque modifies * {
  var x: Base;
  var a: A := new A;
  try { throw (x := a) } catch e { r := 1 };
  try { throw (h#item := a) } catch e2 { r := 2 };
  r := 0
};
"

/-- info: demo: Base, Base -/
#guard_msgs in
#eval report assignThrower

/-- A method's own type parameter that the arguments leave unbound, or bind inconsistently, gives
    the binding no type, as does a generic composite's that the receiver does not supply. Where the
    call already reports that, the `try` adds no error of its own. -/
private def unboundMethodTypeParam := r"
composite A {}
composite B {}
composite Plain {
  procedure get<U>(self: Plain, x: U) returns (r: U) throws (e: U) opaque { throw x };
  procedure both<U>(self: Plain, x: U, y: U) throws (e: U) opaque { throw x };
}
composite Holder<T> {
  var item: T
  procedure raise(self: Holder<T>) throws (e: T) opaque { throw self#item };
}
procedure demo(p: Plain, h: Holder) returns (r: int) opaque {
  var a: A := new A;
  try { a := p#get(<?>) } catch e { r := 1 };
  try { p#both(new A, new B) } catch e2 { r := 2 };
  try { h#raise() } catch e3 { r := 3 };
  r := 0
};
"

/-- info: demo: Unknown, Unknown, Unknown
userError: the `catch` binding of this `try` cannot be typed: the body throws a value of unknown type
userError: cannot infer type argument 'U' of 'both': 'A' and 'B' disagree
userError: the `catch` binding of this `try` cannot be typed: the body throws a value of unknown type -/
#guard_msgs in
#eval report unboundMethodTypeParam

/-- A handler that can never fire throws nothing, though it rethrows its binding. -/
private def deadRethrow := r"
procedure demo() returns (r: int) opaque {
  try { try { r := 1 } catch c { throw c } } catch d { r := 2 };
  r := 0
};
"

/-- info: demo: Unknown, Unknown
warning: the `catch` clause(s) of this `try` can never fire: no exception type could be determined for the `try` body, so they are discarded and the body is verified as if no handler were present
warning: the `catch` clause(s) of this `try` can never fire: no exception type could be determined for the `try` body, so they are discarded and the body is verified as if no handler were present -/
#guard_msgs in
#eval report deadRethrow

/-- An overloaded thrower throws the `throws` of the overload the call binds. -/
private def overloadedThrower := r"
composite A {}
composite B {}
procedure t(x: int) throws (e: A) opaque { throw new A };
procedure t(x: bool) throws (e: B) opaque { throw new B };
procedure demo() returns (r: int) opaque {
  try { t(1) } catch e { r := 1 };
  r := 0
};
"

/-- info: demo: A -/
#guard_msgs in
#eval report overloadedThrower

/-! ## A type variable is a type, not a deferral

`T` is the procedure's own bound parameter, so a `try` whose body throws only `T` binds
at `T`. It is deliberately NOT set aside for `MonomorphizeComposites` to resolve later:
monomorphization specializes a program, it does not decide what the program means, and
cloning is driven by generic composites, so a `g<T>(x: T) throws (e: T)` is never cloned
at all. -/

/-- A poly callee called at the procedure's own `T`, and nothing else: the binding is that
    `T`. -/
private def polyOnly := r"
procedure g<T>(x: T) returns (r: int) throws (e: T) opaque { throw x };
procedure u<T>(x: T) returns (r: int) opaque {
  try { r := g(x) } catch c { r := 1 }
};
"

/-- info: u: T -/
#guard_msgs in
#eval report polyOnly

/-- A `T` alongside a concrete thrown type has no join: pre-monomorphization `T` could be
    instantiated at anything, so no single binding type is known to receive both. Binding
    at the concrete one would accept a handler declared `Err` that holds a `T` value. -/
private def polyAndConcrete := r"
composite Err {}
procedure g<T>(x: T) returns (r: int) throws (e: T) opaque { throw x };
procedure risky() returns (r: int) throws (e: Err) opaque { r := 0 };
procedure u<T>(x: T) returns (r: int) opaque {
  try { r := g(x); r := risky() } catch c { r := 1 }
};
"

/-- info: u: Unknown
userError: the exception types thrown in this `try` block (T, Err) have no common ancestor; a `catch` binding needs a single least-common-ancestor type -/
#guard_msgs in
#eval report polyAndConcrete

/-! ## A rethrow of the catch binding

A handler sees its own binding, so `catch c { throw c }` contributes the binding's type to
an enclosing `try`. -/

/-- The outer binding is typed from the inner handler's rethrow. -/
private def rethrowBinding := r"
procedure u() returns (r: int) opaque {
  try { try { throw 7 } catch c { throw c } } catch d { r := d };
  r := 0
};
"

/-- info: u: int, int -/
#guard_msgs in
#eval report rethrowBinding

/-! ## A rethrow inside a clause whose guard can never hold

A guarded clause that provably never runs contributes nothing outward, mirroring
`Check.tryCatch`, which discards such a body unresolved. Both directions are pinned,
because the skip is only sound when it is exactly as narrow as that pass's: skipping
too much loses a live rethrow and leaves the enclosing binding untyped, skipping too
little carries a type outward that no execution can produce. -/

/-- The inner clause guards on `Unrelated`, which an `A` can never be, so its
    `throw c` is dead and `A` must not reach the outer `try` — where it would meet
    the `bool` thrown after the inner `try` and report a spurious "no common
    ancestor". The outer binding is the `bool` that is genuinely thrown. -/
private def deadGuardRethrow := r"
composite A {}
composite Unrelated {}
procedure u() returns (r: int) opaque {
  try {
    try { throw new A } catch c when c is Unrelated { throw c } catch c3 { r := 1 };
    throw true
  } catch d { r := 2 };
  r := 0
};
"

/-- info: u: bool, A, A -/
#guard_msgs in
#eval report deadGuardRethrow

/-- The contrast: a guard that CAN hold leaves the rethrow live, so the binding type
    still travels outward and types the enclosing `catch`. Only a guard proved
    impossible by `TypeLattice.unrelatedToCatchBinding` is skipped. -/
private def liveGuardRethrow := r"
composite Err {}
composite Sub extends Err {}
procedure u() returns (r: int) opaque {
  try {
    try { throw new Sub } catch c when c is Sub { throw c } catch c2 { r := 1 }
  } catch d { r := 2 };
  r := 0
};
"

/-- info: u: Sub, Sub, Sub -/
#guard_msgs in
#eval report liveGuardRethrow

/-- A multi-catch clause sees its binding at its alternatives' join, so its rethrow
    types the enclosing `catch` at `Mid`, not at the inner `try`'s join `Top`. -/
private def multiCatchRethrow := r"
composite Top {}
composite Mid extends Top {}
composite A extends Mid {}
composite B extends Mid {}
composite C extends Top {}
procedure u(k: int) returns (r: int) opaque {
  try {
    try { if k > 0 then { throw new A } else { if k < 0 then { throw new B } else { throw new C } } }
    catch c when c is A || c is B { throw c } catch c2 { r := 1 }
  } catch d { r := 2 };
  r := 0
};
"

/-- info: u: Mid, Top, Top -/
#guard_msgs in
#eval report multiCatchRethrow

/-- A guard wider than the binding does not widen it: the rethrow types the enclosing
    `catch` at `A`, not `Base`. -/
private def widerGuardRethrow := r"
composite Base {}
composite A extends Base {}
procedure u() returns (r: int) opaque {
  try {
    try { throw new A } catch c when c is Base { throw c }
  } catch d { r := 2 };
  r := 0
};
"

/-- info: u: A, A -/
#guard_msgs in
#eval report widerGuardRethrow

end Strata.Laurel
