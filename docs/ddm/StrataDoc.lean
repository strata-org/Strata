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
shortTitle := "Strata"
%%%

The Strata Dialect Definition Mechanism (DDM) is a set of tools for defining
intermediate representations (IRs) for a wide variety of programming and
specification languages - including potentially all the top languages on Github.

Strata definitions combine features of a datatype or schema definition language with
those of a parser generator so that intermediate representations can have an
easy-to-read textual representation.  Strata supports serialization and will provide
code generation in a variety of target languages so that one can build tooling for
Strata analysis in your language of choice.

Strata dialect are declared in Strata dialect files or may be embedded in Lean
using the [`#dialect`](#lean_dialect) command.

language for defining
languages including its operations as well as a syntactic textual representation.
Progams may be mapped into Strata either by ensuring the syntax of the representation
matches the language or by letting users use an extensting parser and translating
its output into Strata terms.

# Stata Dialects Definitions

Dialects are the core mechanism in Strata used to declare and extend program
intermediata representations.   A Strata dialect defines new syntactic categories,
operations, types, functions and metadata.  Strata dialects may also extend one or
more existing dialect with new operations by importing them.

In this section, we show the concrete syntax for declarations in a dialect definition.
Our convention is to use `monospace` text for concrete syntax in the dialect definition
language and _italic_ for identifiers and other expressions introduced as part of a
specific dialect.

Each dialect definition must begin with the name of the dialect specified
via the command `dialect` _name_`;`.

## Importing dialects

Imports bring declarations of another dialect into the current dialect being
declared.  This includes transitive imports of the dialect being imported.

Each dialect implicitly imports the builtin `Init` dialect that includes some
primitive declarations such as support for numeric literals that cannot
currently be introduced in a Strata user dialect.

:::paragraph
Syntax: `import` _ident_`;`

Imports the dialect `_ident_`.
:::

## Syntactic Categories

Perhaps the most fundamental concept in a Strata dialects is a
{deftech}_Syntactic Category_.
These are typically used to represent core concepts in a language
such as statements, declarations, expressions, variables bindings and types.

:::paragraph
Syntax: `category` _name_`;`

Declares a new syntactic category `_name_`.
:::

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

  * `Init.Ident` represents to identifiers.  These are alphanumeric sequences that start with
    a letter that are not otherwise used as keywords in a dialect.

  * `Init.Str` represents string literals.  These are delimited by double quotes and use escaping
    for special characters.

  * `Init.Num` represents numeric natural number literals.

## Operators
%%%
tag := "operator"
%%%

Operators extend syntactic categories with additional constructors for data.  Each Strata
operator has a name that is distinct from other names in the dialect, a list of arguments
to the operator, the syntactic category being extended, and a syntax definition describing
how to pretty-print the operator.

:::paragraph
Syntax: _metadata_ `op` _name_`(`_id1_ `:` _k1_`,` _id2_ `:` _k2_, _..._`) :` _cat_ `=>` _syntax_`;`

Declares a new operator _name_ where

* _metadata_ is optional metadata (see [Metadata](#metadata)).
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
   by variables.  This allows more general functions than can be supported by operators
   such as a polymorphic length function over lists.
 * Types use a standardized syntax that do not require syntax definitions for each type.
 * After parsing, expressions are type checked to ensure that the syntax is well
   formed.

### Types

Syntax: `type` _name_`(`_id1_ `:` `Type,` _id2_ `:` `Type,` _..._`);`

Declares a new type with optional parameters with names given by the identifiers
_id1_, _id2_, ...

The code below declares a type `Bool` for Booleans and a.
```
type Bool;
type Map (dom : Type, range : Type);  -- Ex. Map Nat Bool
```

### Expressions

Syntax: _metadata_ `fn` _name_`(`_id1_ `:` _k1_`,` _id2_ `:` _k2_, _..._`) :` _type_ `=>` _syntax_`;`

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
to be declared, and attached to other declarations in dialects.  Predefined metadata attributes
are used in dialect definitions for
[defining precedence and type checking](#parsing_typechecking), but additional metadata
attributes can be declared in dialects to build new capabilities on top of Strata.  The goal
of this is to provide an user-controllable extension mechanism to Strata dialects so that
dialects themselves may be repurposed to new use cases.

Syntax: `metadata` _name_ `(`_id1_ `:` _tp1_`,` _id2_ `:` _tp2_`,` _..._ `);`

Declares a new metadata operation with the given name.

The type annotations are currently restricted to identifiers (for referencing arguments),
natural numbers and optional values.  More general support for metadata will be added
in a future relase.

## Parsing, Type Checking and Pretty Printings
%%%
tag := "parsing_typechecking"
%%%

Strata automatically generates a parser, type checker and pretty printer from
the {deftech}_syntax definitions_ and

 syntax definitions to de

### Syntax Definitions
%%%
tag := "syntaxdef"
%%%

A syntax definition is a sequence of tokens that describe the syntax of the operator or function.

* A string literal "text" outputs the literal text as a token.
* An identifier var controls where the associated argument to the function or operator appears in output. The precedence of var is inferred from the operator precedence, but may be directly specified with the syntax var:prec. where prec is a non-negative integer.
* There is an additional function `indent(`_n_`,` _tokens_`)` that causes the tokens argument to appear with additional whitespace added to increase indention by n characters.

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

Default Syntax.  Currently, syntax descriptions are required. We expect this to be changed in the future with a default syntax, and as part of this we plan to explore whether metadata annotations could be added to categories to allow per-category default syntax

Strata

TODO:

* Give examples showing the operations for declaring variables, functions, types, etc.

## Variable Scoping

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
metadata declareMD(name : Ident, type : TypeOrCat, metadata : Ident);
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

There is additionally a builtin parametric category Strata.CommaSepList and DeclList could be replaced by CommaSepList Decl.

# Lean Integration

TODO

# Embedded dialects
%%%
tag := "lean_dialect"
%%%

TODO
