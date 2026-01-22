# Datatypes in Strata

This document describes the datatype system in Strata Core.
For DDM-specific documentation on datatype annotations and the function template system, see the [DDM Manual](verso/DDMDoc.lean) (Datatypes section).

## Overview

Strata supports algebraic datatypes (ADTs) similar to those found in functional programming languages. Datatypes allow one to define custom types with multiple constructors, each of which can have zero or more fields (constructor arguments).

Example in Strata Core syntax:
```boogie
datatype Option<T> () {
  None(),
  Some(val: T)
};
```

## Datatype Declaration Syntax

### Strata Core Dialect

Datatypes are declared using the `datatype` keyword:

```boogie
datatype <Name> (<TypeParams>) {
  <Constructor1>(<field1>: <type1>, ...),
  <Constructor2>(<field2>: <type2>, ...),
  ...
};
```

**Components:**
- `<Name>`: The name of the datatype (e.g., `Option`, `List`, `Tree`)
- `<TypeParams>`: Type parameters in parentheses (can be empty `()`)
- `<Constructor>`: Constructor names (e.g., `None`, `Some`, `Nil`, `Cons`)
- `<field>: <type>`: Field declarations with name and type

### Examples

**Simple enum (no fields):**
```boogie
datatype Color () {
  Red(),
  Green(),
  Blue()
};
```

**Option type (polymorphic):**
```boogie
datatype Option<T> () {
  None(),
  Some(val: T)
};
```

**Recursive list:**
```boogie
datatype List<T> () {
  Nil(),
  Cons(head: T, tail: List<T>)
};
```

**Binary tree:**
```boogie
datatype Tree<T> () {
  Leaf(),
  Node(value: T, left: Tree<T>, right: Tree<T>)
};
```

## Generated Functions

When a datatype is declared, Strata Core automatically generates several auxiliary functions:

### Constructors

Each constructor becomes a function that creates values of the datatype:
- `None() : Option<T>`
- `Some(val: T) : Option<T>`
- `Nil() : List<T>`
- `Cons(head: T, tail: List<T>) : List<T>`

### Tester Functions

For each constructor, a tester function is generated that returns `true` if a value was created with that constructor:
- `Option..isNone(x: Option<T>) : bool`
- `Option..isSome(x: Option<T>) : bool`
- `List..isNil(x: List<T>) : bool`
- `List..isCons(x: List<T>) : bool`

The naming pattern is `<Datatype>..is<Constructor>`.

### Field Accessors (Destructors)

For each field, an accessor function is generated:
- `val(x: Option<T>) : T` - extracts the value from a `Some`
- `head(x: List<T>) : T` - extracts the head from a `Cons`
- `tail(x: List<T>) : List<T>` - extracts the tail from a `Cons`

These functions all have the expected computational behavior for the partial
evaluator (e.g. `val (Some 1)` evaluates to `1`).

**Note:** Field accessors are partial functions - calling them on the wrong constructor variant is undefined behavior.

## SMT Encoding

Datatypes are encoded in SMT-LIB using the `declare-datatypes` command:

```smt2
(declare-datatypes ((Option 1)) (
  (par (T) (
    (None)
    (Some (val T))
  ))
))
```

The generated functions (constructors, testers, accessors) are
mapped to the generated SMT functions (e.g. `Option..isNone` is
automatically mapped to `is-None`).

This SMT encoding allows one to prove standard properties of the
generated datatypes automatically, including exhaustiveness, disjointness and
injectivity of constructors.

## Limitations

1. The DDM does not yet support polymorphic functions, including
datatype constructors. Polymorphism is supported at the AST level.
Example: `StrataTest/Languages/Core/DatatypeVerificationTests.lean`
2. Strata also generates eliminators per data type, allowing
the definition of terms defined by pattern matching and/or
recursion, with the correct computational behavior.
This is also not yet available at the DDM level.
Example: `StrataTest/DL/Lambda/TypeFactoryTests.lean`

## Test Examples

See the following test files for working examples:

- `StrataTest/Languages/Core/Examples/DatatypeEnum.lean` - Simple enums
- `StrataTest/Languages/Core/Examples/DatatypeOption.lean` - Option type
- `StrataTest/Languages/Core/Examples/DatatypeList.lean` - Recursive lists
- `StrataTest/Languages/Core/Examples/DatatypeTree.lean` - Binary trees
