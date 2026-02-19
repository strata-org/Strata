/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Strata DDM Manual" =>
%%%
authors := ["Joe Hendrix"]
shortTitle := "Strata DDM"
%%%

The Strata Dialect Definition Mechanism (DDM) is a set of tools for defining
intermediate representations (IRs) for a wide variety of languages.
The DDM combines features of a parser grammar and a datatype definition language
to let developers quickly define intermediate representations that are easy to work with
both programmatically and textually.  Additionally, the DDM can automatically
generate serialization and deserialization code for its dialects to enable
distributed analysis across language and system boundaries.

The Strata DDM is implemented in Lean.  Strata dialects and programs may be embedded
in Lean or in standalone dialect files.  In a future release, we will support working with
Strata from the command line as well as other languages such as .Net-based languages,
JVM-based languages, Rust, Python and JavaScript/TypeScript.

# Strata Dialect Definitions

Dialects are the core mechanism in Strata used to declare and extend program
intermediate representations.  A Strata dialect defines new syntactic categories,
operations, types, functions and metadata.  Strata dialects are composable and
can be used to define extensions that can be used in multiple languages.  There
is a builtin dialect, called `Init` that provides some basic declarations that
automatically are included in all other dialects.

## Strata Dialect Concepts

Each Strata dialect introduces declarations that ultimately define the IR.  There
are five basic types of declarations:

 * A {deftech}_Syntactic Category_ declaration represents a concept in a Strata dialect
   definition such as an expression, type, statement, or binding.  They are
   defined by operators.
 * A {deftech}_Operator_ declaration defines information that may be stored in a
   syntactic category, along with how it is textually presented.
   Operators have arguments that may reference categories or types, and
   use metadata to define how their arguments affect
   [type checking](#typechecking).
 * A {deftech}_Type_ declaration declares a new builtin type for the dialect
   that all programs in a dialect may refer to.  Type declarations do not introduce
   new syntactic categories, but rather extend the `Init.Type` category.
   This allows Strata to support type variables and polymorphism.
 * A {deftech}_Function_ declaration introduces a new function into Strata's
   builtin expression syntactic category `Init.Expr`.  Functions have a user-
   definable syntax like operators, but can be polymorphic and are type checked
   after parsing.
 * A {deftech}_Metadata_ declaration introduces a new attribute that may be attached
   to other Strata declarations.  There are builtin metadata attributes used to
   control parsing and type checking in dialects.  Dialects may introduce new metadata
   to provide a mechanism for associating properties with declarations.

## Strata Examples

As a simple example, we define a sequence of progressively more complex Strata
dialects with Boolean and arithmetic expressions as well as a simple assertion
language.  Each example provides just enough detail to help readers understand
the example code.  The [Dialect Language Reference](#reference)
contains additional detail on the commands.

```
dialect BoolDialect;
// Introduce Boolean type
type BoolType;

// Introduce literals as constants.
fn true_lit : BoolType => "true";
fn false_lit : BoolType => "false";

// Introduce basic Boolean operations.
fn not_expr (a : BoolType) : BoolType => "-" a;
fn and (a : BoolType, b : BoolType) : BoolType => @[prec(10), leftassoc] a " && " b;
fn or (a : BoolType, b : BoolType) : BoolType => @[prec(8), leftassoc] a " || " b;
fn imp (a : BoolType, b : BoolType) : BoolType => @[prec(8), leftassoc] a " ==> " b;

// Introduce equality operations that work for arbitrary types.
// The type is inferred.
fn equal (tp : Type, a : tp, b : tp) : BoolType => @[prec(15)] a " == " b;
fn not_equal (tp : Type, a : tp, b : tp) : BoolType => @[prec(15)] a " != " b;
```

We can then extend these operations with an Integer type and operations.
```
dialect Arith;
import BoolDialect;

type Int;
fn neg_expr (a : Int) : Int => "- " a;
fn add_expr (a : Int, b : Int) : Int => @[prec(25), leftassoc] a " + " b;
fn sub_expr (a : Int, b : Int) : Int => @[prec(25), leftassoc] a " - " b;
fn mul_expr (a : Int, b : Int) : Int => @[prec(30), leftassoc] a " * " b;
fn exp_expr (a : Int, b : Int) : Int => @[prec(32), rightassoc] a " ^ " b;

fn le (a : Int, b : Int) : BoolType => @[prec(15)] a " <= " b;
fn lt (a : Int, b : Int) : BoolType => @[prec(15)] a " < " b;
fn ge (a : Int, b : Int) : BoolType => @[prec(15)] a " >= " b;
fn gt (a : Int, b : Int) : BoolType => @[prec(15)] a " > " b;
```

By themselves, these dialects do not define a new language.  To define a
language, one needs to extend the builtin `Command` category with
new commands.  This is done with the following dialect that introduces
commands for assertions and defining functions:

```
dialect AssertLang;
import Arith; // Automatically imports BoolDialect dependency of Arith

// This introduces a new operator into the Command category.
op assert (b : BoolType) : Command => "assert " b ";";

// Introduce a category for arguments.
category ArgDecl;
@[declare(var, tp)]
op decl (var : Ident, tp : Type) : ArgDecl => var " : " tp;

category ArgDecls;
op decls (l : CommaSepBy ArgDecl) : ArgDecls => "(" l ")";

@[declareFn(name, args, tp)]
op defFun (name : Ident, args : ArgDecls, tp : Type, @[scope(args)] value : tp)
  : Command => "def " name args "=" value ";";

// Now that we have binders, introduce quantifiers
fn forall_expr (args : ArgDecls, @[scope(args)] b : BoolType) : BoolType =>
  "forall " args ", " b;
fn exists_expr (args : ArgDecls, @[scope(args)] b : BoolType) : BoolType =>
  "exists " args ", " b;
```

With these command extensions, we are now ready to use the dialects in programs:

```
program AssertLang;

assert forall (a : Int), exists (b : Int), b > a;
// Assert Fermat's last theorem
assert forall (a : Int, b : Int, c : Int, n : Int),
         a > 0 && b > 0 && c > 0 && n > 2 ==> a^n + b^n != c^n;

// Introduce function
def addMul(a : Int, b : Int, c : Int) = a * b + c;

assert forall (a : Int, b : Int, c : Int),
        b >= c ==> addMul(a, b, b) >= addMul(a, c, c);
```

# Dialect Language Reference
%%%
tag := "reference"
%%%

The Strata Dialect Definition Language is defined in the rest of this section.
The convention is to use `monospace` text for concrete syntax in the dialect definition
language and _italic_ for identifiers and other expressions introduced as part of a
specific dialect.

Each dialect definition must begin with `dialect` followed by the name of the dialect.

`dialect` _name_`;`.

Additional commands are defined in the following subsections.

## Importing dialects

Imports bring declarations of another dialect into the current dialect being
declared.  This includes transitive imports of the dialect being imported.

:::paragraph
`import` _ident_`;`

Imports the dialect _ident_.
:::

## Syntactic Categories

Syntactic categories are introduced by the `category` declaration:

:::paragraph
`category` _name_`;`

Declares a new syntactic category _name_.
:::

## Operators
%%%
tag := "operator"
%%%

Operators extend syntactic categories with additional constructors for data.  Each Strata
operator has a name that is distinct from other names in the dialect, a list of arguments
to the operator, the syntactic category being extended, and a syntax definition describing
how to pretty-print the operator.

:::paragraph
_md_ `op` _name_`(`_id1_ `:` _k1_`,` _id2_ `:` _k2_, _..._`) :` _cat_ `=>` _syntax_`;`

Declares a new operator _name_ where

* _md_ is optional metadata (see [Metadata](#metadata)).
* `(`_id1_ `:` _k1_`,` _id2_ `:` _k2_`,` _..._`)` are optional bindings and may
  be omitted if the operator takes no arguments.  Each identifier _idN_ is the name
  of an argument while the _kN_ annotation may refer to a syntax category or type.
* _cat_ is the syntax category that is extended by this operator.
* _syntax_ is the [syntax definition](#syntaxdef).
:::

### Examples

A simple operator is an assert operator that takes a Boolean expression and extends
a hypothetical `Statement` category.

```
op assert (b : BoolType) : Statement => "assert" b ";";
```

For expressions, Strata supports polymorphic types.  An example operator that uses
this is a polymorphic assignment operator in the Strata Core statement dialect.

```
op assign (tp : Type, v : Ident, e : tp) : Statement => v " := " e ";";
```

As an example, the following introduces an operator `const` that takes a single binding value
as an argument and produces a `Command`.  The `scope` and `prec` metadata attributes are
described in the [Metadata](#metadata).

```
@[scope(b)]
op const (b : Binding) : Command => @[prec(10)] "const " b ";";
```

## Types and Expressions
%%%
tag := "type_expression"
%%%

As mentioned, the builtin `Init.Type` and `Init.Expr` categories are not extended using
the `op` declaration.  Instead one introduces new types with the `type` declaration and
extends the expression language with new functions using the `fn` declaration.  The builtin
`Init.Type` and `Init.Expr` categories have some special support to simplify the
creation of typed IRs in Strata.

 * Strata supports polymorphic functions and operations and has support for
   type inference that allows it to automatically infer type arguments as long as
   an expression argument uses that type.
 * Unlike categories, user types may contain parameters and parameters may themselves
   be variables.  This allows more general functions than can be supported by operators
   such as a polymorphic length function over lists.
 * Types use a standardized syntax that does not require syntax definitions for each type.
 * After parsing, expressions are type checked to ensure that the syntax is well
   formed.

### Types

`type` _name_`(`_id1_ `:` `Type,` _id2_ `:` `Type,` _..._`);`

Declares a new type with optional parameters with names given by the identifiers
_id1_, _id2_, ...

The code below declares a type `BoolType` and a polymorphic Map type.
```
type BoolType;
type Map (dom : Type, range : Type);  -- Ex. Map Nat BoolType
```

### Expressions

_metadata_ `fn` _name_`(`_id1_ `:` _k1_`,` _id2_ `:` _k2_, _..._`) :` _type_ `=>` _syntax_`;`

This introduces a new function into the `Init.Expr` category.  Unlike `op`
declarations, functions can be polymorphic — type arguments (parameters of
kind `Type`) are automatically inferred from the types of other arguments.
Expressions built from functions are also type checked after parsing.

As an example, the code below introduces a polymorphic `if` expression.

```
fn if (tp : Type, c : BoolType, t : tp, f : tp) : tp =>
   "if " c " then " t "else " f;
```

## Metadata
%%%
tag := "metadata"
%%%

The Strata `Init` dialect provides a builtin `Init.Metadata` category that allows metadata
to be declared and attached to other declarations in dialects.  Predefined metadata attributes
are used for [precedence](#syntaxdef), [type checking](#typechecking), and
configuring [list categories](#init) (e.g., `@[nonempty]`).
Additional metadata attributes can be declared in dialects as a user-controllable extension
mechanism, allowing dialects to be repurposed to new use cases.

`metadata` _name_ `(`_id1_ `:` _tp1_`,` _id2_ `:` _tp2_`,` _..._ `);`

Declares a new metadata operation with the given name.

The type annotations in _tp1_ are currently restricted to `Ident`
(for referencing arguments), natural numbers (`Num`) and optional versions of
each (`Option Ident` and `Option Num`).  More general support for metadata will
be added in a future release.

## Syntax Definitions
%%%
tag := "syntaxdef"
%%%

How operations and functions are represented in Strata's textual format depends on
{deftech}_syntax definitions_.  Each syntax definition is a sequence of tokens that
describe the syntax of the operator or function.

* A string literal such as `"assert "` outputs the literal text as a token.
  Spacing should be used to ensure whitespace appears after a token.
* An argument name `arg` indicates the associated argument to the function
  or operator appears in output.  The precedence can be set with the syntax
  `arg:prec`.
* For multiline declarations, the function `indent(`_n_`,` _tokens_`)` may
  be used.  The _tokens_ will appear indented when they appear on new lines.

### Precedence

Precedence controls when parentheses are inserted during pretty-printing.
There are two precedence values at play:

* *Operator precedence* (`@[prec(p)]`): The precedence of the formatted
  result produced by this operator. When omitted, defaults to `maxPrec`.
  A higher value means the operator binds more tightly.

* *Argument precedence* (`arg:p`): The minimum precedence an argument must
  have to appear without parentheses. If the argument's operator precedence
  is ≤ `p`, it will be wrapped in parentheses. The special case `arg:0`
  disables parenthesization entirely for that argument position. When
  omitted, defaults are derived from the operator precedence as described
  below.

Atoms (identifiers, numeric literals, string literals) have precedence
`maxPrec + 1`, so they are never parenthesized.

*Single-token syntax.* When an operator or function has exactly one
argument and no other syntax tokens (e.g., `op foo (x : Cat) : Cat => x;`),
the formatted result inherits the argument's precedence directly, so
trivial wrapper operators do not introduce unnecessary parentheses. When
the syntax is a single string literal (e.g.,
`=> "keyword";`), the result gets precedence `maxPrec + 1`.

Three metadata annotations affect precedence:

```
metadata prec(p : Nat); -- Sets the operator precedence of the result
metadata leftassoc;     -- Left-associative: left arg binds tighter
metadata rightassoc;    -- Right-associative: right arg binds tighter
```

*Default argument precedences.* When `arg:p` is not written explicitly,
the argument precedence is derived from the operator precedence and
associativity:

* For a non-associative operator with precedence `p` and multiple arguments,
  the first and last arguments get precedence `p` and middle arguments get
  precedence `0`.
* For `leftassoc` with precedence `p`, the leftmost argument gets `p - 1`
  (allowing the same operator to nest on the left without parens) and the
  remaining arguments get `p`.
* For `rightassoc` with precedence `p`, the rightmost argument gets `p - 1`
  and the remaining arguments get `p`.

As an example, a right-associative implies operator can be defined with the
syntax:

```
fn implies (p : Pred, q : Pred) : Pred => @[prec(20), rightassoc] p " ==> " q;
```

Without the `rightassoc` annotation, this is equivalent to the definition:

```
fn implies (p : Pred, q : Pred) : Pred => @[prec(20)] p:20 " ==> " q:19;
```

Here `p:20` means the left argument needs precedence > 20 to avoid parens
(so a nested `implies` on the left *will* be parenthesized), while `q:19`
means the right argument needs precedence > 19 (so a nested `implies` on
the right will *not* be parenthesized, since `implies` itself has
precedence 20 > 19).


## Type Checking
%%%
tag := "typechecking"
%%%

Expressions composed from functions introduced by `fn` declarations are
type checked by the DDM after parsing.  This ensures that argument types
match, type variables are consistently instantiated, and polymorphic type
inference succeeds.  Type checking enables polymorphic functions whose type
arguments are inferred from the types of value arguments, so users can write
`a == b` rather than explicitly providing the type as in `equal(Int, a, b)`.

To support type checking, the DDM maintains a variable context during
parsing that tracks which bindings are in scope.  Operators can introduce
new bindings (e.g., a variable declaration) or evaluate arguments within
a particular scope.  The following metadata declarations control how the
variable context is built up during parsing.

```
-- Specify result scope of argument used to evaluate
-- argument or following code.
metadata scope(name : Ident);
-- Declares a new variable in the resulting scope.
metadata declare(name : Ident, type : TypeOrCat);
-- Declares a function in the resulting scope with name,
-- arguments, and return type determined by the given arguments.
metadata declareFn(name : Ident, args : Ident, type : Ident);
-- Marks a list argument as requiring at least one element.
metadata nonempty;
```

As an example, Strata Core's variable declaration syntax can be defined in Strata using the
following code:

```
category Decl;
-- Decl represents a single variable declaration that extends the context.
@[declare(v, tp)]
op var (v : Ident, tp : Type) : Decl => v ":" tp;

category DeclList;
@[scope(d)]
op declAtom (d : Decl) : DeclList => d;
@[scope(d)]
op declPush (dl : DeclList, @[scope(dl)] d : Decl) : DeclList => dl "," d;

category Statement;
@[scope(dl)]
op varStatement (dl : DeclList) : Statement => "var " dl ";";
```

### Polymorphic Type Variables

The `@[declareTVar]` annotation allows polymorphic function declarations
where type parameters (like `<a, b>`)
need to be in scope when parsing parameter types and return types.
For example, function declarations in Strata.Core are defined as
the following:

```
category TypeVar;
@[declareTVar(name)]
op type_var (name : Ident) : TypeVar => name;

category TypeArgs;
@[scope(args)]
op type_args (args : CommaSepBy TypeVar) : TypeArgs => "<" args ">";

@[declareFn(name, b, r)]
op command_fndecl (name : Ident,
                   typeArgs : Option TypeArgs,
                   @[scope(typeArgs)] b : Bindings,
                   @[scope(typeArgs)] r : Type) : Command =>
  "function " name typeArgs b ":" r ";";
```

This allows parsing declarations like `function identity<a>(x: a): a`.

## The `Init` dialect
%%%
tag := "init"
%%%

The `Init` dialect introduces a few syntactic categories that cannot currently
be defined in user definable dialects.

* `Init.Type` and `Init.Expr` represent types and expressions in Strata.  Unlike
  other categories, these are extended through the specialized `type` and
  `fn` commands rather than [`op`](#operator) declarations so that expressions
  can be type checked after parsing.  See [Types and Expressions](#type_expression) for
  more details.

* Syntactic categories in dialects other than `Init` currently cannot
  take additional parameters.  This support will be added in a future update, but
  to help users, `Init` declares a few builtin parametric categories:

  * `Init.Option c` denotes an optional value of `c`.  Syntactically, either
    `c` may be read in or the empty string.

  * `Init.Seq c` denotes a sequence of values with category `c`.  Each value of `c` is
    separated by whitespace. When formatted, values are concatenated with no separator.

  * `Init.CommaSepBy c` denotes a comma-separated list of values of type `c`. When formatted,
    values are separated by `, ` (comma followed by space).

  * `Init.SpaceSepBy c` denotes a space-separated list of values of type `c`. Parsing is
    identical to `Init.Seq`, but when formatted, values are separated by a single space.

  * `Init.SpacePrefixSepBy c` denotes a space-prefix-separated list of values of type `c`.
    Parsing is identical to `Init.Seq`, but when formatted, each value is prefixed with a space.

  All list categories (`CommaSepBy`, `SpaceSepBy`, `SpacePrefixSepBy`, `Seq`) can be marked
  with the `@[nonempty]` metadata attribute to require at least one element during parsing.
  For example: `@[nonempty] items : SpaceSepBy Item` will reject empty lists with a parse error.

* Parsing for primitive literals and identifiers cannot be expressed directly in syntax definitions.
  To accommodate this, the `Init` dialect introduces syntactic categories for them:

  * `Init.Ident` represents identifiers.  These are alphanumeric sequences that start with
    a letter that are not otherwise used as keywords in a dialect.

  * `Init.Str` represents string literals.  These are delimited by double quotes and use escaping
    for special characters.

  * `Init.Num` represents numeric natural number literals.

## Datatypes
%%%
tag := "datatypes"
%%%

The DDM has special support for defining dialects with algebraic datatypes
(ADTs) similar to those found in functional programming languages.
Datatypes allow one to define custom types with multiple constructors,
each of which can have zero or more fields (constructor arguments).

Datatypes differ from other language constructs (e.g. types, operators), since
they define several operations simultaneously. For example, an
SMT datatype declaration defines (in addition to the type itself and the
constructors) _tester_ functions to identify to which constructor an
instance belongs and _accessor_ functions to extract the fields of a
constructor.
Dafny datatypes additionally produce an ordering relation, while Lean inductive
types produce _eliminator_ instances defining induction principles. The DDM
enables automatic creation of (a subset of) these auxiliary functions via a
configurable {deftech}_function template_ system.

### Example

In the Strata Core dialect, the auxiliary functions are testers and accessors. That
is, one can define the following datatype in Strata Core:

```
datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
};
```

This declares a list type with two constructors (`Nil` and `Cons`) and two
fields (`head` and `tail`). The Core dialect automatically generates:

* Constructors: `Nil : IntList` and `Cons : int -> IntList -> IntList`
* Testers: `IntList..isNil : IntList -> bool` and `IntList..isCons : IntList -> bool`
* Accessors: `head : IntList -> int` and `tail : IntList -> IntList`

### Defining Datatype Syntax in a Dialect

To support datatypes in a dialect, you must define syntactic categories and
operators with appropriate annotations. The Core dialect provides a complete example.

#### Constructor Syntax

Constructors define the variants of a datatype. Constructor fields are specified
via Bindings like other function declarations.

```
category Constructor;
category ConstructorList;

@[constructor(name, fields)]
op constructor_mk (name : Ident, fields : Option (CommaSepBy Binding)) : Constructor =>
  name "(" fields ")";

@[constructorListAtom(c)]
op constructorListAtom (c : Constructor) : ConstructorList => c;

@[constructorListPush(cl, c)]
op constructorListPush (cl : ConstructorList, c : Constructor) : ConstructorList =>
  cl "," c;
```

The annotations:

* `@[constructor(name, fields)]` marks this operation as a constructor
definition, where `fields` is a `Bindings` argument containing the constructor
arguments
* `@[constructorListAtom(c)]` marks a single-element constructor list
* `@[constructorListPush(cl, c)]` marks an operation that extends a constructor list

#### Datatype Command

The main datatype declaration uses `@[declareDatatype]` to tie everything
together. It is best illustrated with an example (from the Core dialect):

```
@[declareDatatype(name, typeParams, constructors,
    perConstructor([.datatype, .literal "..is", .constructor], [.datatype], .builtin "bool"),
    perField([.field], [.datatype], .fieldType))]
op command_datatype (name : Ident,
                     typeParams : Option Bindings,
                     @[scopeDatatype(name, typeParams)] constructors : ConstructorList)
  : Command =>
  "datatype " name typeParams " {" constructors "}" ";\n";
```

`@[declareDatatype]` declares a datatype command operator given the datatype
name, the optional type parameters, the constructor list, and zero or more
[function templates](#datatypes-function-templates) to expand. Note that the `@[scopeDatatype]`
annotation brings the datatype name and type parameters into scope when
parsing the constructors, enabling recursive type references.

#### Function Templates
%%%
tag := "datatypes-function-templates"
%%%

Function templates specify patterns for generating auxiliary functions from datatype
declarations.
Currently there are two supported templates: `perConstructor` generates one
function per constructor, while `perField` generates one function per field
(note that the DDM enforces that fields are unique across all constructors in
a datatype).

:::paragraph
`perConstructor(`_namePattern_`,` _paramTypes_`,` _returnType_`)`

`perField(`_namePattern_`,` _paramTypes_`,` _returnType_`)`

Each template has three components:

* _namePattern_ is an array of name parts: `.datatype`, `.constructor`, or `.literal "str"`
* _paramTypes_ is an array of type references for parameters
* _returnType_ is a type reference for the return type
:::

Name patterns consist of the following components:

* `.datatype` - Expands to the datatype name
* `.constructor` - Expands to the constructor name in `perConstructor`
* `.field` - Expands to the field name in `perField`
* `.literal "str"` - A literal string

Type references consist of the following components:

* `.datatype` - The datatype type (e.g., `IntList`)
* `.fieldType` - The type of the current field in `perField`
* `.builtin "bool"` - A built-in type from the dialect

##### Example Templates

The Strata Core dialect uses two templates:

The tester template generates `IntList..isNil : IntList -> bool`:
```
perConstructor([.datatype, .literal "..is", .constructor], [.datatype], .builtin "bool")
```

The accessor template generates `head : IntList -> int`:
```
perField([.field], [.datatype], .fieldType)
```

An alternative indexer template could generate `IntList$idx$Nil : IntList -> int`:
```
perConstructor([.datatype, .literal "$idx$", .constructor], [.datatype], .builtin "int")
```

# Lean Integration
%%%
tag := "lean_integration"
%%%

Strata provides two complementary ways to work with dialect ASTs in Lean.
The _generic AST_ is a set of dialect-agnostic types that can represent
programs in any dialect.  It is used by the DDM's parser, pretty-printer,
serializer, and other infrastructure that must operate uniformly across
dialects.  The `#strata_gen` command takes the opposite approach: given a
specific dialect, it generates Lean inductive types with one constructor per
operator, enabling direct pattern matching and type-safe construction.
Conversion functions (`toAst`/`ofAst`) bridge the two representations.

## The Generic AST

The generic AST is defined in `Strata.DDM.AST`.  All types are parameterized
by an annotation type `α` (typically `SourceRange` for source locations).

The core types are listed below in the same order as the
[dialect concepts](#Strata-Dialect-Concepts) they represent:

* `SyntaxCatF α` — a reference to a syntactic category, identified by its
  qualified name.
* `OperationF α` — an application of a dialect operator.  Contains the
  operator's qualified name and an array of arguments.
* `ArgF α` — a single argument to an operation.  This is a sum type whose
  variants cover all the kinds of data an operator can receive: nested
  operations, expressions, types, identifiers, numeric literals, string
  literals, decimal literals, byte arrays, category references, optional
  values, and sequences.
* `TypeExprF α` — a type expression.  Variants cover dialect-defined types
  (`ident`), bound and polymorphic type variables (`bvar`, `tvar`), global
  type references (`fvar`), and function types (`arrow`).
* `ExprF α` — a typed expression.  Expressions are represented in curried
  form: a head (`fn` for a named dialect function, `bvar` for a bound
  variable, or `fvar` for a free variable) applied to arguments via `app`.
  Type arguments for bound and free variables are implicit and omitted.

For the common case where annotations are source locations, Strata defines
abbreviations:

```
abbrev SyntaxCat := SyntaxCatF SourceRange
abbrev Operation := OperationF SourceRange
abbrev Arg       := ArgF SourceRange
abbrev TypeExpr  := TypeExprF SourceRange
abbrev Expr      := ExprF SourceRange
```

### How DDM Concepts Map to the Generic AST

The following table summarizes how the DDM concepts described in earlier
sections are represented in the generic AST.

:::table +header
 *
   * DDM Concept
   * Generic AST Type
   * Notes
 *
   * Syntactic category
   * `SyntaxCatF`
   * Identified by qualified name (e.g. `Init.Expr`)
 *
   * Operator application
   * `OperationF`
   * Qualified name + array of `ArgF` arguments
 *
   * Type expression
   * `TypeExprF`
   * Concrete types, type variables, function types
 *
   * Expression
   * `ExprF`
   * Curried: head (`fn`/`bvar`/`fvar`) + `app` chain
 *
   * Identifier literal
   * `ArgF.ident`
   * e.g. variable names from `Ident` arguments
 *
   * Numeric literal
   * `ArgF.num`
   * From `Num` arguments
 *
   * String literal
   * `ArgF.strlit`
   * From `Str` arguments
 *
   * `CommaSepBy`/`Seq`
   * `ArgF.seq`
   * Array of `ArgF` with a separator format
 *
   * `Option`
   * `ArgF.option`
   * `Option (ArgF α)`
:::

The generic AST is dialect-agnostic: operators are identified by their
`QualifiedIdent` (a dialect name paired with an operator name) rather than
by distinct Lean constructors.  This uniformity makes it the natural
representation for DDM infrastructure such as the parser, formatter, and
serializer, but it means that working with a specific dialect requires
string-based matching on operator names.

## The `#strata_gen` Command
%%%
tag := "strata_gen"
%%%

The `#strata_gen` command bridges Strata dialect definitions and Lean by
automatically generating Lean inductive types and conversion functions from a
dialect definition.  This lets developers work with dialect ASTs as ordinary
Lean values — constructing, pattern matching, and transforming them — while
retaining the ability to convert back to the generic AST representation
for serialization, pretty-printing, and cross-dialect interoperability.

### Basic Syntax

```
import Strata.DDM.Integration.Lean

namespace MyDialect
#strata_gen MyDialect
end MyDialect
```

`#strata_gen` requires `import Strata.DDM.Integration.Lean` and takes a single
argument: the name of a dialect that has already been defined (via
`#dialect ... #end` or `#load_dialect`).  The command should typically be placed
inside a `namespace` block so that the generated types and functions are scoped
under that namespace.

#### Tracing

To see what `#strata_gen` generates, enable the `Strata.generator` trace
option immediately before the command:

```
set_option trace.Strata.generator true in
#strata_gen MyDialect
```

This prints each generated definition (inductives, `toAst`, `ofAst`) and the
dependency groups used to order them.  For example, running `#strata_gen` on the
AssertLang dialect defined [earlier in this manual](#reference) produces:

```
[Strata.generator] Generating AssertLangType
[Strata.generator] Generating AssertLangType.toAst
[Strata.generator] Generating AssertLangType.ofAst
[Strata.generator] Generating ArgDecl
[Strata.generator] Generating ArgDecl.toAst
[Strata.generator] Generating ArgDecl.ofAst
[Strata.generator] Generating ArgDecls
[Strata.generator] Generating ArgDecls.toAst
[Strata.generator] Generating ArgDecls.ofAst
[Strata.generator] Generating Expr
[Strata.generator] Generating Expr.toAst
[Strata.generator] Generating Expr.ofAst
[Strata.generator] Generating Command
[Strata.generator] Generating Command.toAst
[Strata.generator] Generating Command.ofAst
[Strata.generator] Declarations group: [Init.Type]
[Strata.generator] Declarations group: [AssertLang.ArgDecl]
[Strata.generator] Declarations group: [AssertLang.ArgDecls]
[Strata.generator] Declarations group: [Init.Expr]
[Strata.generator] Declarations group: [Init.Command]
```

Each category produces an inductive type, a `toAst` function, and an `ofAst`
function.  The "Declarations group" lines show the topologically sorted groups
in the order they are emitted to Lean.

### What Gets Generated

For each syntactic category used by a dialect, `#strata_gen` generates four
things:

1. An inductive type parameterized by an annotation type `α`.
2. An `Inhabited` instance (when possible).
3. A `toAst` function that converts from the generated type to Strata's
   generic AST representation (`ExprF`, `TypeExprF`, or `OperationF`).
4. An `ofAst` function that converts from the generic AST back to the
   generated type (returning `OfAstM`, an error monad).

Every generated constructor includes an `ann : α` field that carries
source-location or other annotation data through transformations.

#### Determining Which Categories Are Used

Not every category in a dialect's transitive imports needs code generated for
it.  `#strata_gen` computes the set of _used_ categories by starting from the
categories and types directly declared or referenced in the dialect and
following argument dependencies transitively.  For example, if a dialect
declares only `op assert (b : BoolType) : Command => ...`, the generator will
produce types for `Command`, `Expr` (since `BoolType` is a type in
`Init.Expr`), and `Type` — but not for categories like `Binding` that are never
referenced.

Primitive categories (`Init.Ident`, `Init.Num`, `Init.Str`, etc.) map
directly to Lean types (`String`, `Nat`, `String`, etc.) and do not produce
their own inductive definitions.

#### Handling Mutually Recursive Categories

Categories can be mutually recursive.  For example:

```
category MutA;
category MutB;
op opA (b : MutB) : MutA => "opA " b;
op opB (a : MutA) : MutB => "opB " a;
```

`#strata_gen` uses Tarjan's algorithm to identify strongly connected
components — groups of categories that reference each other.  Each group is
emitted as a Lean `mutual ... end` block so that the inductive types, `toAst`
functions, and `ofAst` functions can refer to one another.  Groups are
processed in topological order so that a group's dependencies are always
defined before the group itself.

### Example Walkthrough

Consider a small SQL dialect:

```
dialect SQL;

op create (name : Ident, c : CommaSepBy Ident) : Command =>
  "CREATE " name "(" c ")" ";\n";

op drop (name : Ident) : Command =>
  "DROP " name ";\n";

category Columns;
op colStar : Columns => "*";
op colList (c : CommaSepBy Ident) : Columns => c;

op select (col : Columns, table : Ident) : Command =>
  "SELECT " col " FROM " table ";\n";
```

After `#strata_gen SQL`, the generator produces two inductive types.

`Command` gets one constructor per operation that targets it:

```
inductive Command (α : Type) : Type where
  | create (ann : α) (name : Ann String α) (c : Ann (Array String) α) : Command α
  | drop   (ann : α) (name : Ann String α) : Command α
  | select (ann : α) (col : Columns α) (table : Ann String α) : Command α
  deriving Repr
```

`Columns` gets its own constructors:

```
inductive Columns (α : Type) : Type where
  | colStar (ann : α) : Columns α
  | colList (ann : α) (c : Ann (Array String) α) : Columns α
  deriving Repr
```

Notice that:

* `Ident` arguments become `Ann String α` (a `String` carrying an annotation).
* `CommaSepBy Ident` arguments become `Ann (Array String) α`.
* The custom category `Columns` appears directly as a type in `Command.select`.

The generated `toAst` function converts from the dialect-specific type to the
generic AST, and `ofAst` converts back:

```
-- Convert generated type → generic AST
Command.toAst : {α : Type} → [Inhabited α] → Command α → OperationF α

-- Convert generic AST → generated type
Command.ofAst : {α : Type} → [Inhabited α] → [Repr α]
  → OperationF α → OfAstM (Command α)
```

#### Expression and Type Categories

Dialects that declare types (via `type`) or functions (via `fn`) also get
generated `Expr` and `Type` inductives.  These include builtin constructors
in addition to dialect-defined ones.  For instance, the Arith dialect's
generated `Expr` type includes:

```
inductive Expr (α : Type) : Type where
  -- Builtin constructors (always present for Init.Expr)
  | fvar  (ann : α) (idx : Nat) : Expr α
  | bvar  (ann : α) (idx : Nat) : Expr α
  | app   (ann : α) (fn : Expr α) (arg : Expr α) : Expr α
  -- Dialect-defined constructors
  | btrue   (ann : α) : Expr α
  | bfalse  (ann : α) : Expr α
  | intLit  (ann : α) (n : Ann Nat α) : Expr α
  | add     (ann : α) (x : Expr α) (y : Expr α) : Expr α
  | mul     (ann : α) (x : Expr α) (y : Expr α) : Expr α
  -- ... (additional constructors omitted)
  deriving Repr
```

The `fvar`, `bvar`, and `app` constructors correspond to free variables, bound
variables (de Bruijn indices), and function application in Strata's core
expression model.

### Post-Generation Patterns

After running `#strata_gen`, there are several common patterns for working
with the generated types.

#### Deriving Typeclass Instances

Generated types automatically derive `Repr`.  Other instances can be derived
after generation:

```
deriving instance BEq for Command, Columns
```

For larger dialects with many categories, this can be done in bulk:

```
deriving instance BEq for
  SpecConstant, QualifiedIdent, Symbol,
  SMTSort, Term, Command
```

Support for automatically deriving additional instances during generation
will be added in a future release.

#### Verifying Generated Types

Use `#print` and `#check` to inspect what was generated:

```
#print Command    -- Shows inductive definition and constructors
#print Columns
#check Columns.colStar  -- Columns.colStar : {α : Type} → α → Columns α
```

#### Round-Trip Testing

A simple round-trip test can verify that `toAst` and `ofAst` are inverses:

```
def testRoundTrip (e : Expr Unit) : Bool :=
  match e |> Expr.toAst |> Expr.ofAst with
  | .error _ => false
  | .ok g => e == g

#guard testRoundTrip <| Expr.btrue ()
#guard testRoundTrip <| Expr.app () (.fvar () 0) (.btrue ())
```

#### Dependent Dialects

When a dialect imports another, `#strata_gen` automatically resolves the full
transitive closure of dependencies.  Each invocation generates its own set of
types — if ArithChecker imports Arith and uses `Init.Expr`, it will produce a
new `ArithChecker.Expr` that includes all of Arith's constructors.  The two
Expr types are isomorphic but distinct:

```
namespace Arith
#strata_gen Arith      -- Generates Arith.Expr, Arith.ArithType, ...
end Arith

namespace ArithChecker
#strata_gen ArithChecker  -- Generates ArithChecker.Expr, ArithChecker.Command, ...
end ArithChecker
-- ArithChecker.Expr is isomorphic to Arith.Expr (same constructors)
-- but they are separate types.
```

# Command Line Use
%%%
tag := "command_line"
%%%

This will be described once available.
