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

The fragile case is a thrown type with no name to key on. `collectThrownTypes` has to
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
  let parsed ← (Strata.parseLaurelText "<catch-binding-type-test>" src : IO Program)
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

/-! ## The composite path is unchanged

The hierarchy walk is the case that always worked; it is pinned here so a change to
the join cannot fix the primitive case by breaking this one. -/

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

end Strata.Laurel
