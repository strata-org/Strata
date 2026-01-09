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
Strata from the command line as well as other languages such as .Net-based language,
JVM-based languages, Rust, Python and JavaScript/TypeScript.

# Strata Dialect Definitions

Dialects are the core mechanism in Strata used to declare and extend program
intermediate representations.   A Strata dialect defines new syntactic categories,
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
   use metadata to define how their arguments affect Strata
   [typechecking](typechecking).
 * A {deftech}_Type_ declaration declares a new builtin type for the dialect
   that all programs in a dialect may refer to.  Types declarations do not introduce
   new syntactic categories in a dialect, but rather extend a dialect `Init.Type`
   with new types that may be refered to.  This allows Strata to support type variables
   and polymorphism.
 * A {deftech}_Function_ declaration introduces a new function into Strata's
   builtin expression syntactic category `Init.Expr`.  Functions have an user-
   defineable syntax like operators, but can be polymorphic and are type checked
   after parsing.
 * A {deftech}_Metadata_ declaration introduces a new attribute that may be attached
   to other Strata declarations.  There are builtin metadata attributes used to
   control parsing and typechecking in dialects.  Dialects may introduce new metadata
   to provide a mechanism for associating properties with declarations.

## Strata Examples

As a simple example, we define a sequence of progressively more complex Strata
dialects with Boolean and arithmetic expressions as well as a simple assertion
language.  Each example provides just enough detail to help readers understand
the example code.  The [Strata Dialect Language Reference](#reference)
contains additional detail on the commands.

```
dialect Bool;
// Introduce Boolean type
type Bool;

// Introduce literals as constants.
fn true_lit : Bool => "true";
fn false_lit : Bool => "false";

// Introduce basic Boolean operations.
fn not_expr (a : Bool) : Bool => "-" a;
fn and (a : Bool, b : Bool) : Bool => @[prec(10), leftassoc] a " && " b;
fn or (a : Bool, b : Bool) : Bool => @[prec(8), leftassoc] a " || " b;
fn imp (a : Bool, b : Bool) : Bool => @[prec(8), leftassoc] a " ==> " b;

// Introduce equality operations that work for arbitrary types.
// The type is inferred.
fn equal (tp : Type, a : tp, b : tp) : Bool => @[prec(15)] a " == " b;
fn not_equal (tp : Type, a : tp, b : tp) : Bool => @[prec(15)] a " != " b;
```

We can then extend thse operations with an Integer type and operations.
```
dialect Arith;
import Bool;

type Int;
fn neg_expr (a : Int) : Int => "- " a;
fn add_expr (a : Int, b : Int) : Int => @[prec(25), leftassoc] a " + " b;
fn sub_expr (a : Int, b : Int) : Int => @[prec(25), leftassoc] a " - " b;
fn mul_expr (a : Int, b : Int) : Int => @[prec(30), leftassoc] a " * " b;
fn exp_expr (a : Int, b : Int) : Int => @[prec(32), rightassoc] a " ^ " b;

fn le (a : Int, b : Int) : Bool => @[prec(15)] a " <= " b;
fn lt (a : Int, b : Int) : Bool => @[prec(15)] a " < " b;
fn ge (a : Int, b : Int) : Bool => @[prec(15)] a " >= " b;
fn gt (a : Int, b : Int) : Bool => @[prec(15)] a " > " b;
```

By itself, these dialects do not define a new language.  To define a
language, one needs to extends a builtin `Command` category with
new commands.  This is done with the following dialect that introduces
commands for assertions and defining functions:

```
dialect AssertLang;
import Arith; // Automatically imports Bool dependency of Arith

// This introduces a new operator into the Command category.
op assert (b : Bool) : Command => "assert " b ";";

// Introduce a category for arguments.
category ArgDecl;
@[declare(var, tp)]
op decl (var : Ident, tp : Type) : ArgDecl => var " : " tp;

category ArgDecls;
op decls (l : CommaSepBy ArgDecl) => "(" l ")";

@[declareFn(name, args, tp)]
op defFun (name : Ident, args : ArgDecls, tp : Type, @[scope(args)] value : tp)
  : Command => "def " name args "=" value ";";

// Now that we have binders, Introduce quantifiers
fn forall (args : ArgDecls, @[scope(args)] b : bool) : bool =>
  "forall " args ", " b;
fn exists (args : ArgDecls, @[scope(args)] b : bool) : bool =>
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

# Strata Dialect Language Reference
%%%
tag := "reference"
%%%

The Strata Dialect Definition Language is defined in the rest of this section.
The convention is to use `monospace` text for concrete syntax in the dialect definition
language and _italic_ for identifiers and other expressions introduced as part of a
specific dialect.

Each dialect definition must begin with the `dialect` followed by the name of the dialect.

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
  be omited if the operator takes no arguments.  Each identifier _idN_ is the name
  of an argument while the _kN_ annotation may refer to a syntax category or type.
* _cat_ is the syntax category that is extended by this operator.
* _syntax_ is the [syntax definition](#syntaxdef).
:::

### Examples

A simple operator is an assert operator that takes a Boolean expression and extends
a hypothetical `Statement` category.

```
op assert (b : Bool) : Statement => "assert" b ";";
```

For expressions, Strata supports polymorphic types.  An example operator that uses
this is a polymorphic assignment operator in the Boogie statement dialect.

```
op assign (tp : Type, v : Ident, e : tp) : Statement => v " := " e ";";
```

As an example, the following introduces an operator `const` that takes a single binding value
as argument and produce a `Command`.  The `scope` and `prec` metadata attributes are
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

 * Strata supports type polymorphic functions and operations and has a support for
   type inference that allows it to automatically infer type arguments as long as
   an expression argument uses that type.
 * Unlike categories, user types may contain parameters and parameters may themselves
   be variables.  This allows more general functions than can be supported by operators
   such as a polymorphic length function over lists.
 * Types use a standardized syntax that do not require syntax definitions for each type.
 * After parsing, expressions are type checked to ensure that the syntax is well
   formed.

### Types

`type` _name_`(`_id1_ `:` `Type,` _id2_ `:` `Type,` _..._`);`

Declares a new type with optional parameters with names given by the identifiers
_id1_, _id2_, ...

The code below declares a type `Bool` and a polymorphic Map type.
```
type Bool;
type Map (dom : Type, range : Type);  -- Ex. Map Nat Bool
```

### Expressions

_metadata_ `fn` _name_`(`_id1_ `:` _k1_`,` _id2_ `:` _k2_, _..._`) :` _type_ `=>` _syntax_`;`

This introduces a new function

As an example, the code below introduces a polymorphic `if` expression.

```
fn if (tp : Type, c : Bool, t : tp, f : tp) : tp =>
   "if " c " then " t "else " f;
```

## Metadata
%%%
tag := "metadata"
%%%

The Stata `Init` dialect provides a builtin `Init.Metadata` category that allows metadata
to be declared and attached to other declarations in dialects.  Predefined metadata attributes
are used in dialect definitions for
[defining precedence and type checking](#parsing_typechecking), but additional metadata
attributes can be declared in dialects to build new capabilities on top of Strata.  The goal
of this is to provide an user-controllable extension mechanism to Strata dialects so that
dialects themselves may be repurposed to new use cases.

`metadata` _name_ `(`_id1_ `:` _tp1_`,` _id2_ `:` _tp2_`,` _..._ `);`

Declares a new metadata operation with the given name.

The type annotations in _tp1_ are currently restricted to `Ident`
(for referencing arguments), natural numbers (`Num`) and optional versions of
each (`Option Ident` and `Option Num`).  More general support for metadata will
be added in a future relase.

### Syntax Definitions
%%%
tag := "syntaxdef"
%%%

How operations and functions are represented in Strata depends on  {deftech}_syntax definitions_.
Each syntax definition is a sequence of tokens that describe the syntax of the operator or function.

* A string literal such as `"assert "` outputs the literal text as a token.  Spacing should be used to ensure
  whitespace appears after a token.
* An argument name `arg` indicates the the associated argument to the function or operator appears in output.  The
  precedence can be set with the syntax `arg:prec`.
* For multiline declarations, the function `indent(`_n_`,` _tokens_`)` may be used.  The _tokens_ will appear
  indented when they appear on new lines.

There are three metadata annotations in the Strata dialect that may affect precedence in syntax definitions.

```
metadata prec(p : Nat); -- Controls the precedence of the outermost operator
metadata leftassoc; -- Indicates operator is left-associative
metadata rightassoc; -- Indicates operator is right associative.
```

As an example, a right associative implies operator can be defined with the syntax:

```
fn implies (p : Pred, q : Pred) : Pred => @[prec(20), rightassoc] p " ==> " q;
```

Without the rightassoc operator, this is equivalent to the definition:

```
fn implies (p : Pred, q : Pred) : Pred => @[prec(20)] p:20 " ==> " q:19;
```


## Parsing, Type Checking and Pretty Printings
%%%
tag := "parsing_typechecking"
%%%

When parsing an operation or expression from source, there is an implicit variable
context that contains bindings for variables in scope. Operators may transform this
context while expressions are evaluated within a context.
The changes to the context are controlled via metadata, and the Strata dialect makes
three declarations for affecting this.

```
-- Specify result scope of argument used to evaluate argument or following code.
metadata scope(name : Ident);
-- Declares a new variable in the resulting scope with no metadata
metadata declare(name : Ident, type : TypeOrCat);
-- Declares a new variable in the resulting scope with metadata determined
-- by an argument.
```

As an example, Boogie variable declaration syntax can be defined in Strata using the
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

* Syntactic categories that in dialects other than `Init` cannot currently cannot
  take additional parameters.  This support will be added in a future update, but
  to help users, the `Init` declares a few builtin parametric categories:

  * `Init.Option c` denotes an optional value of `c`.  Syntactically, either
    `c` may be read in or the empty string.

  * `Init.Seq c` denotes a sequence of values with category `c`.  Each value of `c` is
    separated by whitespace.

  * `Init.CommaSepBy c` denotes a comma-separated list of values of type `c`.

* Parsing for primitive literals and identifiers cannot be directly in syntax definitions.
  To accomodate this, the `Init` dialect introduces the syntactic categories for this:

  * `Init.Ident` represents identifiers.  These are alphanumeric sequences that start with
    a letter that are not otherwise used as keywords in a dialect.

  * `Init.Str` represents string literals.  These are delimited by double quotes and use escaping
    for special characters.

  * `Init.Num` represents numeric natural number literals.
  
## Datatypes
%%%
tag := "datatypes"
%%%

The DDM has special support for defining dialects with algebraic datatypes (ADTs) similar to those found in functional programming
languages. Datatypes allow one to define custom types with multiple constructors, each of
which can have zero or more fields (constructor arguments).

Datatypes differ from other language constructs (e.g. types, operators), since
they define several operations simultaneously. For example, an
SMT datatype declaration defines (in addition to the type itself and the
constructors) _tester_ functions to identify to which constructor an instance belongs and _accessor_ functions to extract the fields of a constructor.
Dafny datatypes additionally produce an ordering relation, while Lean inductive
types produce _eliminator_ instances defining induction principles. The DDM
enables automatic creation of (a subset of) these auxiliary functions via a
configurable {deftech}_function template_ system. 

### Example

In the Boogie dialect, the auxiliary functions are testers and accessors. That
is, one can define the following datatype in Strata.Boogie:

```
datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
};
```

This declares a list type with two constructors (`Nil` and `Cons`) and two fields (`head` and `tail`). The Boogie dialect automatically generates:

* Constructors: `Nil : IntList` and `Cons : int -> IntList -> IntList`
* Testers: `IntList..isNil : IntList -> bool` and `IntList..isCons : IntList -> bool`
* Accessors: `head : IntList -> int` and `tail : IntList -> IntList`

### Defining Datatype Syntax in a Dialect

To support datatypes in a dialect, you must define syntactic categories and
operators with appropriate annotations. The Boogie dialect provides a complete example.

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

The main datatype declaration uses `@[declareDatatype]` to tie everything together. It is best illustrated with an example (from the Boogie dialect):

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

The Boogie dialect uses two templates:

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

This will be described in a later release.


# Command Line Use
%%%
tag := "command_line"
%%%

This will be described once available.
