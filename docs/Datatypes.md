# Datatypes in Strata

This document describes the datatype system in Strata, including how to declare datatypes, how the DDM processes them, and the differences between encoding strategies in different dialects.

## Overview

Strata supports algebraic datatypes (ADTs) similar to those found in functional programming languages. Datatypes allow you to define custom types with multiple constructors, each of which can have zero or more fields.

Example in Boogie syntax:
```boogie
datatype Option<T> () {
  None(),
  Some(val: T)
};
```

## Datatype Declaration Syntax

### Boogie Dialect

In the Boogie dialect, datatypes are declared using the `datatype` keyword:

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

When a datatype is declared, Strata automatically generates several auxiliary functions:

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

**Note:** Field accessors are partial functions - calling them on the wrong constructor variant is undefined behavior.

## Function Template System

The DDM uses a **function template system** to generate auxiliary functions. This system is configurable per-dialect, allowing different dialects to generate different sets of functions.

### Template Types

Templates are defined with three key properties:

1. **Iteration Scope**: Determines how many functions are generated
   - `perConstructor`: One function per constructor (e.g., testers)
   - `perField`: One function per unique field name (e.g., accessors)
   - `perConstructorField`: One function per (constructor, field) pair

2. **Name Pattern**: How to construct the function name
   - `.datatype` - The datatype name
   - `.constructor` - The constructor name
   - `.field` - The field name
   - `.literal "str"` - A literal string

3. **Type Specification**: Parameter and return types
   - `.datatype` - The datatype type
   - `.fieldType` - The type of the current field
   - `.builtin "bool"` - A built-in type

### Boogie Templates

The Boogie dialect uses two templates:

**Tester Template (perConstructor):**
- Name pattern: `[.datatype, .literal "..is", .constructor]`
- Parameters: `[.datatype]`
- Return type: `.builtin "bool"`
- Example: `Option..isNone : Option<T> -> bool`

**Accessor Template (perField):**
- Name pattern: `[.field]`
- Parameters: `[.datatype]`
- Return type: `.fieldType`
- Example: `val : Option<T> -> T`

### BoogieMinimal Templates

The BoogieMinimal dialect demonstrates an alternative encoding using indexers instead of boolean testers:

**Indexer Template (perConstructor):**
- Name pattern: `[.datatype, .literal "..idx", .constructor]`
- Parameters: `[.datatype]`
- Return type: `.builtin "int"`
- Example: `Option..idxNone : Option<T> -> int`

This shows how the template system allows different dialects to generate different auxiliary functions.

## Annotation-Based Constructor Extraction

The DDM uses annotations to identify constructor and field operations in a dialect-agnostic way:

- `@[constructor(name, fields)]` - Marks an operation as a constructor definition
- `@[field(name, tp)]` - Marks an operation as a field definition
- `@[constructorListAtom(c)]` - Single constructor in a list
- `@[constructorListPush(list, c)]` - Adds a constructor to a list
- `@[fieldListAtom(f)]` - Single field in a list
- `@[fieldListPush(list, f)]` - Adds a field to a list

These annotations allow the DDM to extract constructor information without knowing the specific operation names used by each dialect.

## SMT Encoding

Datatypes are encoded to SMT-LIB using the `declare-datatypes` command:

```smt2
(declare-datatypes ((Option 1)) (
  (par (T) (
    (None)
    (Some (val T))
  ))
))
```

The SMT encoding includes:
- The datatype declaration with type parameters
- Constructor definitions with field selectors
- Automatic generation of tester predicates (`is-None`, `is-Some`)

## Verification Properties

The SMT solver automatically provides several properties for datatypes:

1. **Exhaustiveness**: Every value matches exactly one constructor
2. **Distinctness**: Different constructors produce different values
3. **Injectivity**: Constructors are injective (equal outputs imply equal inputs)
4. **Accessor correctness**: Accessors return the correct field values

Example verification:
```boogie
procedure TestOption() {
  var x : Option<int>;
  havoc x;
  
  // Exhaustiveness: exactly one tester is true
  assert Option..isNone(x) || Option..isSome(x);
  
  // Mutual exclusion
  assert !(Option..isNone(x) && Option..isSome(x));
  
  // Accessor correctness
  x := Some(42);
  assert val(x) == 42;
}
```

## Implementation Files

Key files for the datatype implementation:

| Component | File |
|-----------|------|
| Template types | `Strata/DDM/AST/Datatype.lean` |
| AST integration | `Strata/DDM/AST.lean` |
| Boogie config | `Strata/Languages/Boogie/DDMTransform/DatatypeConfig.lean` |
| Boogie translation | `Strata/Languages/Boogie/DDMTransform/Translate.lean` |
| SMT encoding | `Strata/Languages/Boogie/SMTEncoder.lean` |
| DDM annotations | `Strata/DDM/BuiltinDialects/StrataDDL.lean` |

## Test Examples

See the following test files for working examples:

- `StrataTest/Languages/Boogie/Examples/DatatypeEnum.lean` - Simple enums
- `StrataTest/Languages/Boogie/Examples/DatatypeOption.lean` - Option type
- `StrataTest/Languages/Boogie/Examples/DatatypeList.lean` - Recursive lists
- `StrataTest/Languages/Boogie/Examples/DatatypeTree.lean` - Binary trees
- `StrataTest/Languages/BoogieMinimal/DatatypeTest.lean` - Alternative encoding
