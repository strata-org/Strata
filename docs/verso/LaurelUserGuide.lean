/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.ModifiesClauses
-- Provides `Strata.parseLaurelText`, used by the `laurel` code block below to
-- parse-check every example at doc-elaboration time.
import Strata.Languages.Laurel

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

-- panel with an "Example" header, so concrete examples stand out from the
-- surrounding explanatory prose. Authored via the `:::example` directive below.
block_extension Block.«example» (title : Option String) where
  data := Lean.toJson (title : Option String)
  traverse _ _ _ := pure none
  toHtml := some fun _goI goB _id data contents => open Verso.Output.Html in do
    let title : Option String :=
      match Lean.fromJson? (α := Option String) data with
      | .ok t => t
      | .error _ => none
    let label := title.getD "Example"
    pure {{
      <div class="laurel-example">
        <div class="laurel-example-header">{{ label }}</div>
        <div class="laurel-example-body">{{← contents.mapM goB}}</div>
      </div>
    }}
  extraCss := [
r#"
.laurel-example {
  border: 1px solid #98B2C0;
  border-left: 4px solid #4A90E2;
  border-radius: 0.4rem;
  background: #F5F9FF;
  margin-top: var(--verso--box-vertical-margin);
  margin-bottom: var(--verso--box-vertical-margin);
  overflow: hidden;
}
.laurel-example-header {
  font-family: var(--verso-structure-font-family);
  font-style: italic;
  font-size: 0.875rem;
  font-weight: bold;
  color: #2A5680;
  background: #E4EEF8;
  padding: 0.3rem var(--verso--box-padding);
}
.laurel-example-body {
  padding: 0.2rem var(--verso--box-padding);
}
"#
  ]
  toTeX := some fun _goI goB _id _data contents => open Verso.Output.TeX in open Verso.Doc.TeX in do
    pure <| .seq <| ← contents.mapM fun b => do
      pure <| .seq #[← goB b, .raw "\n"]

/-- Configuration for the `:::example` directive: an optional title shown in the
    box header (defaults to "Example"). -/
structure LaurelExampleConfig where
  title : Option String := none

open Verso.ArgParse in
instance : Verso.ArgParse.FromArgs LaurelExampleConfig Verso.Doc.Elab.DocElabM where
  fromArgs := LaurelExampleConfig.mk <$>
    ((positional' `title <&> some) <|> pure none)

/-- Sets its contents apart in a styled *example* box (see `Block.example`).
    Optionally takes a title: `:::example "Arithmetic join"` … `:::`. -/
@[directive]
def «example» : Verso.Doc.Elab.DirectiveExpanderOf LaurelExampleConfig
  | {title}, stxs => do
    let args ← stxs.mapM Verso.Doc.Elab.elabBlock
    ``(Verso.Doc.Block.other (Block.«example» $(Lean.quote title)) #[ $[ $args ],* ])

/-- Configuration for the `laurel` code block. The `+unchecked` flag opts a
    block out of parse checking — use it for illustrative or partial snippets
    that are not intended to parse as a complete Laurel program. -/
structure LaurelCodeConfig where
  unchecked : Bool := false

instance : Verso.ArgParse.FromArgs LaurelCodeConfig Verso.Doc.Elab.DocElabM where
  fromArgs := LaurelCodeConfig.mk <$> .flag `unchecked false

/-- A ````laurel```` code block. Renders like an ordinary code block, but also
    *parse-checks* its contents at doc-elaboration time so a syntax error in an
    example fails the documentation build.

    Only parsing and AST translation are run — not resolution or verification —
    so examples that deliberately illustrate a verification *failure* (a failing
    `assert`, a violated precondition, …) still pass, since they are
    syntactically valid. A snippet that is not a complete program (it omits the
    `program Laurel;` header) is wrapped before checking. Pass `+unchecked` to
    skip checking entirely. -/
@[code_block]
def laurel : Verso.Doc.Elab.CodeBlockExpanderOf LaurelCodeConfig
  | config, str => do
    -- `parseLaurelText` parses a bare sequence of declarations (the `.laurel.st`
    -- file form), and the `program Laurel;` header is an artifact of the embedded
    -- style that readers shouldn't see. Strip an optional leading `program …;`
    -- header line so it is neither checked against nor rendered.
    let content := str.getString
    let source :=
      if content.startsWith "program" then
        match content.splitOn "\n" with
        | _header :: rest => "\n".intercalate rest
        | [] => content
      else content
    unless config.unchecked do
      try
        let _ ← (Strata.parseLaurelText "<LaurelUserGuide>" source : IO Strata.Laurel.Program)
      catch e =>
        throwErrorAt str m!"Laurel example failed to parse:\n{e.toMessageData}"
    ``(Verso.Doc.Block.code $(Lean.quote source))

#doc (Manual) "The Laurel User Guide" =>
%%%
shortTitle := "Laurel User Guide"
%%%

# Summary

Laurel is an intermediate analysis language. Its purpose is to reduce the cost of analysing code for
popular languages. Currently Laurel is focused on enabling analysis of Java, Python, and JavaScript,
but this list will grow and you can already use it for other languages as well.

Laurel is a good target when your source language has mutation and a function-like construct. Some
source-language features must be compiled away before or during translation, because Laurel does not
model them directly:
- metaprogramming (macros, reflection, runtime code generation);
- type-system features that do not fit Laurel's type system, which is close to C#'s (for example
  higher-kinded types or advanced generics);
- pointers and pointer arithmetic (Laurel does not yet model these).

Laurel is *not* a good target for languages that use none of its features — typically languages with
no procedure-like construct, such as assembly, or inputs that are not programming languages at all.
A stack-based language like JVM bytecode still benefits from targeting Laurel.

You use Laurel by building a compiler from your source language to Laurel. This guide will help you
understand Laurel and thus help build such compilers.

Laurel supports several types of analysis and some of these require additional information besides
the implementation code. You can enable your users to provide this information through annotations
in the source program, and those annotations should then be used in the compilation to Laurel, where
the analysis specific information lives in first class language constructs.

Using just the Strata CLI — without writing any Strata extensions — a Laurel program can be put
through these kinds of analysis. Laurel does not implement them itself; it lowers to Strata Core,
which performs the analysis:
- Property-based testing (planned)
- Bounded verification
- Unbounded verification

Front-end compilers targeting Laurel can recover from some errors in user code rather than abort:
when a side-effect-free sub-expression cannot be translated, emit a diagnostic and put a *hole*
(`<?>`) in its place. The program still compiles and the analyses still run, so users see your
diagnostic plus any further genuine errors instead of a cascade caused by the first one. Holes
stand for an unknown value only — they do not model mutation — so replacing code that may have side
effects with a hole silently drops those effects and can make an analysis prove properties the
original program does not have. For untranslatable constructs that may have effects, and for
unrecoverable errors (for example resolution failures), abort with a diagnostic instead.

## How this guide is organised

The three Laurel guides are aimed at different readers, and this one is for the person
*writing* Laurel — typically inside a front-end compiler:

- this *User Guide* describes what you can write and what it means;
- the *Designer Guide* records why the language is shaped the way it is, and what is planned;
- the *Implementor Guide* describes the compilation pipeline and how Laurel lowers to Core.

Within this guide, {ref "syntax"}[*Syntax*] is the grammar: lexical rules, precedence, and the
surface productions. {ref "execution"}[*Execution*] covers the features whose meaning does not
depend on verification — the ones a reader with an ordinary programming background will
recognise, and the ones that behave identically when a program is concretely interpreted. The
{ref "verification-fundamentals"}[*Verification*] sections cover features whose whole purpose is
analysis: they may be erased or approximated when the program runs, and they are introduced in
order of increasing difficulty — first the ones that do not involve the heap
({ref "verification-fundamentals"}[*Fundamentals*]), then the heap-specific ones
({ref "verification-objects"}[*Objects*]), then contracts on the exits and suspensions that
exceptions and coroutines introduce ({ref "verification-continued"}[*Continued*]), then proof
debugging.

A feature that has both an execution and a verification side appears in both places rather than
in a section of its own. Exceptions and coroutines are the two: `throw` / `try` / `catch` and
`coroutine` / `yield` / `resume` are described where the other execution features are, while
`throwsOn` and `relies` / `guarantees` are described with the other contracts.

## A first program

A Laurel program is a sequence of declarations. The most important one is the
*procedure*. A procedure has input parameters, optional output parameters
introduced with `returns`, an optional contract, and a body enclosed in braces.
Statements inside the body are separated by semicolons.

The procedure below computes integer division the hard way: it repeatedly
subtracts the divisor from the dividend, counting how many times it can do so.
The `ensures` clause then confirms the hand-rolled result against Laurel's
built-in `/` operator, so the two must agree for the procedure to verify. The
loop carries an *invariant* that ties the running quotient and remainder back to
the original dividend — this is the fact the verifier needs to discharge the
postcondition.

```laurel
program Laurel;
procedure divide(dividend: int, divisor: int) returns (quotient: int)
  requires dividend >= 0
  requires divisor > 0
  opaque
  ensures quotient == dividend / divisor
{
  var remainder: int := dividend;
  quotient := 0;
  while (remainder >= divisor)
    invariant remainder >= 0
    invariant dividend == quotient * divisor + remainder
  {
    remainder := remainder - divisor;
    quotient := quotient + 1
  };
  assert 0 <= remainder && remainder < divisor
};
```

## Internal constructors and properties
Some constructors and properties in the Laurel AST are marked for internal usage and should not be
needed by Laurel users. Having these internal properties and constructors allows us to define an
incremental translation to Core which improves maintainability.

# Syntax
%%%
tag := "syntax"
%%%

Laurel's concrete syntax is defined by a StrataDDM dialect, `LaurelGrammar.st`. That file is the
authority — a grammar production and its precedence are read from it directly, and everything
below is a readable transcription of it. What each form *means* is in
{ref "execution"}[*Execution*] and the `Verification` sections.

## At a glance

Several spellings differ from the mainstream languages Laurel is a target for. They are worth
skimming once, because they are the most common source of a first parse error.

:::table +header
 *
   * Intent
   * Laurel syntax
 *
   * Field read or write
   * `obj#field`, `obj#field := value`
 *
   * Instance procedure call
   * `obj#method(args)`
 *
   * Assignment
   * `x := value`
 *
   * String concatenation
   * `a ^ b`
 *
   * Eager Boolean and/or
   * `a & b`, `a | b`
 *
   * Short-circuit and/or
   * `a && b`, `a || b`
 *
   * Implication
   * `a ==> b`
 *
   * Euclidean integer division/remainder
   * `a / b`, `a % b`
 *
   * Truncating integer division/remainder
   * `a /t b`, `a %t b`
 *
   * Deterministic unknown
   * `<?>`
 *
   * Nondeterministic unknown
   * `<??>`
 *
   * Label and jump
   * `{ ... } label`, `exit label`
:::

Note that `^` is concatenation — not exponentiation, and not exclusive or. Fields use the `#`
selector rather than the `.` most languages use, because `.` is an identifier character in Laurel
and not a selector.

Three structural rules cover most of the rest:

1. A Laurel source file (`.lr.st` or `.laurel.st`) is a bare sequence of declarations. The
   `program Laurel;` header belongs only to `#strata` blocks embedded in Lean, so a standalone
   file must not carry it. Examples in this guide are shown without it.
2. Statements inside a block are separated by `;`, and the final one may omit it. A
   *procedure* declaration itself always ends in `;`; a `composite`, `datatype`, `constrained`,
   `type`, or `opaque` declaration does not.
3. Tabs are rejected as inter-token whitespace.

## Comments and whitespace

Outside tokens, spaces and newlines are insignificant except as separators. Both comment forms
are supported:

```laurel +unchecked
// line comment

/* block
   comment */
```

Block comments end at the first `*/`; they do not nest. A tab encountered as inter-token
whitespace is a parse error. CRLF line endings are accepted between tokens, but an isolated
carriage return there is not. Characters inside a string, a comment, or a pipe-quoted identifier
are token content and are not subject to this whitespace check.

## Identifiers

A regular identifier starts with a Unicode alphabetic character, `_`, or `$`, and continues with
alphanumeric characters or any of `_`, `'`, `.`, `?`, `!`, `$`, `@`. So these are all one
identifier each:

```
x
_temporary
Option..value!
module.name
```

The `.` being an identifier character rather than a selector is why field access uses `#`, and
why a generated name like `Option..value` is a single token rather than a projection.

Most names that are not regular identifiers can be *pipe-quoted*:

```
|name with spaces|
|123-leading-digit|
|name\|with\|pipes|
|path\\segment|
```

Inside a pipe-quoted identifier `\|` denotes `|` and `\\` denotes `\`; other backslash pairs are
accepted and keep the backslash literally. Pipe quoting is also the escape hatch for a name that
collides with a Laurel keyword. Because the lexer must still distinguish the `|` and `||`
operators, an empty pipe identifier — or one whose first character is whitespace — does not
parse.

## Reserved names
%%%
tag := "reserved-names"
%%%

A *leading* `$` is reserved for compiler-generated names, and this is enforced across a whole
program: a declaration whose name begins with `$` — a type, procedure, parameter, field, local,
bound variable, constructor or block label — is rejected with a diagnostic on the declaration
itself. A `$` anywhere else in a name is an ordinary identifier character, so `total$1` is legal
and needs no avoidance.

The sole exception is `$result`, the name the short `procedure f(…): T` return form gives a
procedure's single output. You may spell it out in an explicit `returns ($result: T)` clause and
refer to it in contracts, but you may not use it for anything else.

The always-on prelude also occupies a handful of unprefixed names, because they are the built-in
types and operations: `TotalMap`, `Map`, `Set`, `Sequence`, `select`, `update`, `mapConst`,
`mapEmpty`, `mapContains`, `mapGet`, `mapSet`, `mapRemove`, and the `set*` and `seq*` families.
A program using composites also has compiler-generated helper names in scope. Redeclaring any of
these is accepted by the parser and then fails during resolution.

## Literals

```laurel +unchecked
true
false
0
42
1_000
0b1010
0o755
0xCAFE
-42                  // unary minus applied to 42
3.1415               // exact mathematical real
6.02e23              // exact decimal with an exponent
"hello\nworld"
255 bv 8             // bitvector value 255, width 8
<?>                  // deterministic unknown
<??>                 // nondeterministic unknown
```

Natural tokens may be decimal, binary (`0b`/`0B`), octal (`0o`/`0O`), or hexadecimal
(`0x`/`0X`). Underscores may separate digits, and every underscore run must be followed by a
valid digit. Integer syntax is nonnegative: a negative value is unary `-` applied to a natural.

A decimal token must contain a decimal point or an `e`/`E` exponent. Forms such as `1.`, `1.25`,
`1e6`, and `1.25e-3` denote exact mathematical `real` values — not `float64`.

String literals use double quotes. The implemented escapes are `\\`, `\"`, `\'`, `\r`, `\n`,
`\t`, `\xHH`, and `\uHHHH`. A backslash followed by a newline and further non-newline whitespace
is a *string gap* and contributes no character. Other characters, including an unescaped
newline, are kept literally; an unknown or incomplete escape is a parse error.

## Operator precedence

Higher rows bind more tightly.

:::table +header
 *
   * Precedence
   * Operators and forms
   * Associativity
 *
   * 1000
   * `{ ... }`, `{ ... } label`
   * atomic
 *
   * 95
   * call `f(...)`, field `x#f`
   * left, chaining
 *
   * 90
   * postfix `x++`, `x--`
   * postfix
 *
   * 80
   * `!x`, `-x`, `++x`, `--x`, `new C`
   * prefix
 *
   * 70
   * `*`, `/`, `%`, `/t`, `%t`
   * left
 *
   * 60
   * `+`, `-`, `^`
   * left
 *
   * 40
   * `==`, `!=`, `<`, `<=`, `>`, `>=`, `is`, `as`
   * non-associative
 *
   * 30
   * eager `&`, short-circuit `&&`
   * left
 *
   * 20
   * eager `|`, short-circuit `||`, `if`
   * left
 *
   * 15
   * `==>`
   * right
 *
   * 10
   * `:=`, `+=`, `-=`, `*=`, `/=`, `%=`, `^=`
   * compound forms right-associate
:::

Because `if` sits at precedence 20, an `if` used as an operand of a comparison or an arithmetic
operator needs parentheses: write `(if c then 1 else 2) == y`. Parenthesise freely when mixing
comparison, type-test, implication, and assignment forms.

## Surface grammar

The transcription below normalises the layout directives in `LaurelGrammar.st`. `{ X }` means
zero or more, `[ X ]` optional, and `X , ...` a comma-separated list. A file is a sequence of
declarations with no separator between them; each declaration's own terminator (`;` for a
procedure, the closing brace or the next leading keyword otherwise) delimits it.

```
program             = { declaration } ;

declaration         = procedure-declaration
                    | coroutine-declaration
                    | composite-declaration
                    | datatype-declaration
                    | constrained-type-declaration
                    | type-alias-declaration
                    | opaque-type-declaration
                    | global-variable-declaration ;

(* Types *)

type                = "int" | "bool" | "real" | "float64" | "string"
                    | "bv" natural
                    | "TotalMap" type type
                    | "Core" identifier
                    | identifier
                    | identifier "<" type , ... ">"
                    | "(" type ")" ;

type-parameters     = "<" identifier , ... ">" ;

(* Type, alias, and global declarations *)

datatype-declaration
                    = "datatype" identifier [ type-parameters ]
                      "{" [ constructor , ... ] "}" ;
constructor         = identifier | identifier "(" [ argument , ... ] ")" ;
argument            = identifier ":" type ;

constrained-type-declaration
                    = "constrained" identifier "=" identifier ":" type
                      "where" expression "witness" expression ;

type-alias-declaration
                    = "type" identifier [ type-parameters ] "=" type ;

opaque-type-declaration
                    = "opaque" identifier [ type-parameters ] ;

global-variable-declaration
                    = "var" identifier ":" type [ ":=" expression ] ;

(* Composites *)

composite-declaration
                    = "composite" identifier [ type-parameters ]
                      [ "extends" type , ... ]
                      "{" { field-declaration } { procedure-declaration } "}" ;
field-declaration   = [ "var" ] identifier ":" type ;

(* Procedures: the clause order below is significant *)

procedure-declaration
                    = "procedure" identifier [ type-parameters ]
                      "(" [ parameter , ... ] ")"
                      [ ":" type ]
                      [ "returns" "(" [ parameter , ... ] ")" ]
                      [ "throws" "(" identifier ":" type ")" ]
                      { requires-clause }
                      [ "invokeOn" expression ]
                      [ "entry" ]
                      [ opaque-specification ]
                      [ body | "external" ]
                      ";" ;

parameter           = identifier ":" type ;
body                = expression ;

requires-clause     = [ "free" | "checked" ] "requires" expression
                      [ "summary" string-literal ] ;

opaque-specification
                    = "opaque"
                      { ensures-clause }
                      { modifies-clause }
                      { throws-on-clause }
                      { "reads" identifier , ... }
                      { "writes" identifier , ... } ;

ensures-clause      = [ "free" | "checked" ] "ensures" expression
                      [ "summary" string-literal ] ;
modifies-clause     = "modifies" "*" | "modifies" expression , ... ;

throws-on-clause    = "throwsOn" expression "{" { throws-on-spec } "}" ;
throws-on-spec      = "ensures" expression [ "summary" string-literal ]
                    | "modifies" expression , ... ;

(* Coroutines *)

coroutine-declaration
                    = "coroutine" identifier "(" [ parameter , ... ] ")"
                      [ "yields" "(" [ parameter , ... ] ")" ]
                      [ "resumes" "(" [ parameter , ... ] ")" ]
                      { requires-clause } { ensures-clause }
                      { relies-clause } { guarantees-clause }
                      { modifies-clause }
                      [ body | "external" ]
                      ";" ;
relies-clause       = "relies" expression [ "summary" string-literal ] ;
guarantees-clause   = "guarantees" expression [ "summary" string-literal ] ;

(* Unified statements and expressions *)

expression          = literal
                    | identifier
                    | "(" expression ")"
                    | variable-declaration
                    | expression "(" [ expression , ... ] ")"
                    | "new" identifier [ "<" type , ... ">" ]
                    | expression "#" identifier
                    | assignment
                    | compound-assignment
                    | multi-assignment
                    | increment-expression
                    | unary-expression
                    | binary-expression
                    | quantifier
                    | "old" "(" expression ")"
                    | "oldGuarantee" "(" expression ")"
                    | "oldRelies" "(" expression ")"
                    | if-expression
                    | "assert" expression [ "summary" string-literal ]
                    | "assume" expression
                    | "throw" expression
                    | "return" [ expression ]
                    | "yield"
                    | block
                    | block identifier
                    | "exit" identifier
                    | try-expression
                    | while-loop
                    | for-loop
                    | do-while-loop
                    | expression "is" type
                    | expression "as" type ;

literal             = "true" | "false" | natural | decimal | string-literal
                    | natural "bv" natural
                    | "<?>" | "<??>" ;

variable-declaration
                    = "var" identifier [ ":" type ] [ ":=" expression ] ;

assignment          = expression ":=" expression ;
compound-assignment = expression compound-operator expression ;
compound-operator   = "+=" | "-=" | "*=" | "/=" | "%=" | "^=" ;

multi-assignment    = "assign" assignment-target , ... ":=" expression ;
assignment-target   = "var" identifier [ ":" type ]
                    | identifier
                    | field-path "#" identifier ;
field-path          = identifier | field-path "#" identifier ;

increment-expression
                    = "++" expression | "--" expression
                    | expression "++" | expression "--" ;

unary-expression    = "!" expression | "-" expression ;

binary-expression   = expression binary-operator expression ;
binary-operator     = "+" | "-" | "*" | "/" | "%" | "/t" | "%t"
                    | "==" | "!=" | "<" | "<=" | ">" | ">="
                    | "&" | "|" | "&&" | "||" | "==>"
                    | "^" ;

quantifier          = ( "forall" | "exists" ) "(" identifier ":" type ")"
                      [ "{" expression "}" ] "=>" expression ;

if-expression       = "if" expression "then" expression
                      [ "else" expression ] ;

block               = "{" [ expression { ";" expression } ] "}" ;

try-expression      = "try" expression { catch-clause } [ finally-clause ] ;
catch-clause        = "catch" identifier [ "when" expression ] expression ;
finally-clause      = "finally" expression ;

while-loop          = "while" "(" expression ")" { invariant-clause }
                      expression ;
for-loop            = "for" "(" expression ";" expression ";" expression ")"
                      { invariant-clause } expression ;
do-while-loop       = "do" expression "while" "(" expression ")"
                      { invariant-clause } ;
invariant-clause    = "invariant" expression ;
```

A few points the productions alone do not make obvious:

- A single anonymous output (`: T`) and named outputs (`returns (...)`) are separate optional
  slots, but they are *alternative* user forms. Do not write both.
- Fields must precede procedures inside a composite.
- A procedure body is one expression. Most imperative procedures use a block, which is also an
  expression.
- A `return` carries no semicolon of its own; semicolons only separate it from neighbouring
  expressions in a block.
- A datatype constructor with no arguments may be written `Nil` or `Nil()`.
- A multi-assignment field target is a plain identifier/field chain, not an arbitrary
  expression.
- A local variable's `: type` annotation is grammatically optional, but an unannotated `var`
  with no initializer cannot be given a type and is diagnosed. Write the annotation, or use
  `var x := e` and let the initializer supply it.
- `yield`, `yields`, `resumes`, `relies`, `guarantees`, `oldGuarantee`, and `oldRelies` are
  coroutine-only; see {ref "coroutines"}[*Coroutines*].

# Resolution

Right now, Laurel reserves identifier names that start with `$` for use in its compilation passes.
In the future we may improve the passes so that this restriction can be dropped.

## Resolution in practice

The rest of this section states the typing rules precisely. In everyday use they come down to a
short list, and a front end that respects these will rarely be surprised:

- literals synthesize their primitive type; a local synthesizes its declared type;
- a field synthesizes its declared type after looking the receiver up by its *static* type;
- an assignment checks its right-hand side against the target's type, and yields that type;
- a declaration extends only the enclosing block's scope;
- a call checks arguments against the declared inputs and synthesizes the output type;
- a multi-output call has an internal multi-value type and must be unpacked with `assign`;
- an `if` checks both branches against the expected type when there is one, and otherwise joins
  the two synthesized branch types;
- a block's last item carries the block's value;
- loop conditions, invariants, and contract clauses check against `bool`;
- arithmetic needs operands of one compatible numeric type — there are no implicit numeric
  promotions;
- equality needs consistent operand types; `is` and `as` need related types;
- `return e` checks `e` against the sole declared output;
- names and types are pre-registered, so declaration order does not matter.

When a rule fails, resolution substitutes an internal unresolved or `Unknown` node so that one
mistake does not cascade into a list of derived errors. Compilation stops before any analysis
runs if a real diagnostic remains.

## Bidirectional type checking

There are two operations on expressions, written here in standard
bidirectional notation:

```
Γ ⊢ e ⇒ A            -- "e synthesizes A"     (Synth.resolveStmtExpr)
Γ ⊢ e ⇐ A            -- "e checks against A"  (Check.resolveStmtExpr)
```

Synthesis returns a type inferred from the expression itself; checking
verifies that the expression has a given expected type. Each construct
picks a mode based on whether its type is determined locally (synth) or
by context (check). The two judgments are connected by a single
change-of-direction rule, *subsumption*:

$$`\frac{\Gamma \vdash e \Rightarrow A \quad A <: B}{\Gamma \vdash e \Leftarrow B} \quad \text{([⇐] Sub)}`

The two judgments are implemented as
{name Strata.Laurel.Resolution.Synth.resolveStmtExpr}`Synth.resolveStmtExpr` and
{name Strata.Laurel.Resolution.Check.resolveStmtExpr}`Check.resolveStmtExpr`:

{docstring Strata.Laurel.Resolution.Synth.resolveStmtExpr}

{docstring Strata.Laurel.Resolution.Check.resolveStmtExpr}

## Gradual typing

The relation `<:` (used in \[⇐\] Sub) is built from three Lean functions —
{name Strata.Laurel.isSubtype}`isSubtype`, {name Strata.Laurel.isConsistent}`isConsistent`,
and {name Strata.Laurel.isConsistentSubtype}`isConsistentSubtype`:

{docstring Strata.Laurel.isSubtype}

{docstring Strata.Laurel.isConsistent}

{docstring Strata.Laurel.isConsistentSubtype}

## Typing rules

Each construct is given as a derivation. `Γ` is the current lexical scope (see
{name Strata.Laurel.ResolveState}`ResolveState`'s `scope`); it threads identically through
every premise and conclusion unless a rule explicitly extends it (written `Γ, x : T`).

Each rule is tagged with `[⇒]` (synthesis) or `[⇐]` (checking) to make the
direction explicit. The {ref "rules-procedure"}[*Procedure*] rule is the one
exception: it is a top-level well-formedness judgment and carries no direction
tag.

The following notation recurs throughout the rules:

- $`A <: B` — subtyping ({name Strata.Laurel.isSubtype}`isSubtype`); see
  *Gradual typing* above. In a *checking* premise or side condition (e.g.
  \[⇐\] Sub, \[⇐\] If-NoElse, \[⇐\] Assign, the check-mode operator rules, and
  \[⇐\] Hole-Some) the boundary check is the gradual consistent-subtype
  relation $`<:_\sim` below — the implementation routes every such check
  through {name Strata.Laurel.isConsistentSubtype}`isConsistentSubtype`, never
  bare $`<:` — so $`\mathsf{Unknown}` is admitted on either side.
- $`A \sim B` — the *consistency* relation
  {name Strata.Laurel.isConsistent}`isConsistent`: symmetric, with
  $`\mathsf{Unknown}` acting as a wildcard.
- $`A <:_\sim B` — the *consistent-subtype* relation
  {name Strata.Laurel.isConsistentSubtype}`isConsistentSubtype`, the gradual
  combination of the two above.
- $`\mathsf{Numeric}\;T` — a predicate holding when $`T` is consistent with one
  of $`\mathsf{TInt}`, $`\mathsf{TReal}`, $`\mathsf{TFloat64}`, or
  $`\mathsf{TBv}_w` (a bitvector of any width $`w`), with $`\mathsf{Unknown}`
  admitted as the gradual escape hatch.
- $`\dashv \Gamma'` — a rule's *output scope*: the judgment threads $`\Gamma` in
  and produces $`\Gamma'` out. Only the declaring rules extend the scope —
  \[⇒\] Var-Declare / Var-Declare-Infer, the Decl-Synth pair, and
  \[⇒\]/\[⇐\] Assign when a target is a `Declare`; the
  block rules thread it statement-to-statement (the $`\Gamma_{i-1} \to
  \Gamma_i` chain in \[⇐\] Block / \[⇒\] Block-Synth).
- $`\rightsquigarrow \text{error: …}` — the rule emits an error and aborts; no
  type is produced.
- $`[\text{emits …}]` — the rule produces its type but also emits a diagnostic.
- $`\mapsto` — elaboration: the construct is rewritten to the form on the right.

The Index below links to each construct's subsection.

### Index

- {ref "rules-subsumption"}[*Subsumption*] — \[⇐\] Sub
- {ref "rules-literals"}[*Literals*] — \[⇒\] Lit-Int, \[⇒\] Lit-Bool, \[⇒\] Lit-String, \[⇒\] Lit-Decimal
- {ref "rules-variables"}[*Variables*] — \[⇒\] Var-Local, \[⇒\] Var-Field,
  \[⇒\] Var-Declare, \[⇒\] Var-Declare-Infer
- {ref "rules-control-flow"}[*Control flow*] — \[⇐\] If, \[⇐\] If-NoElse,
  \[⇒\] If-Synth, \[⇒\] If-Synth-NoElse;
  \[⇐\] Block, \[⇒\] Block-Synth, \[⋄\] Synth-Discard,
  \[⇒\] Empty-Block; \[⇒\] Exit;
  \[⇒\] Return-None-Void, \[⇒\] Return-None-Single, \[⇒\] Return-None-Multi,
  \[⇒\] Return-Some, \[⇒\] Return-Void-Error,
  \[⇒\] Return-Multi-Error; \[⇒\] While
- {ref "rules-verification-statements"}[*Verification statements*] — \[⇒\] Assert, \[⇒\] Assume
- {ref "rules-assignment"}[*Assignment*] — \[⇒\] Assign, \[⇐\] Assign,
  \[⇒\] Decl-Synth, \[⇐\] Decl-Synth
- {ref "rules-calls"}[*Calls*] — \[⇒\] Static-Call, \[⇒\] Static-Call-Multi,
  \[⇒\] Instance-Call, \[⇒\] Instance-Call-Multi
- {ref "rules-primitive-operations"}[*Operators*] — no operator-specific rules:
  operators are calls, typed by \[⇒\] Static-Call. Equality is the one
  special case: \[⇒\] Op-Eq
- {ref "rules-object-forms"}[*Object forms*] — \[⇒\] New-Ok, \[⇒\] New-Fallback; \[⇒\] AsType; \[⇒\] IsType;
  \[⇒\] RefEq; \[⇒\] PureFieldUpdate
- {ref "rules-verification-expressions"}[*Verification expressions*] — \[⇒\] Quantifier, \[⇒\] Assigned, \[⇐\] Old,
  \[⇒\] Old-Synth, \[⇒\] Fresh, \[⇐\] ProveBy, \[⇒\] ProveBy-Synth
- {ref "rules-self-reference"}[*Self reference*] — \[⇒\] This-Inside, \[⇒\] This-Outside
- {ref "rules-untyped-forms"}[*Untyped forms*] — \[⇒\] Abstract / All
- {ref "rules-contract-of"}[*ContractOf*] — \[⇒\] ContractOf-Bool, \[⇒\] ContractOf-Set, \[⇒\] ContractOf-Error
- {ref "rules-holes"}[*Holes*] — \[⇐\] Hole-Some, \[⇐\] Hole-None, \[⇒\] Hole-Synth-None, \[⇒\] Hole-Synth-Some
- {ref "rules-procedure"}[*Procedure*] — Procedure

### Subsumption
%%%
tag := "rules-subsumption"
%%%

$$`\frac{\Gamma \vdash e \Rightarrow A \quad A <: B}{\Gamma \vdash e \Leftarrow B} \quad \text{([⇐] Sub)}`

Fallback in {name Strata.Laurel.Resolution.Check.resolveStmtExpr}`Check.resolveStmtExpr` whenever no
bespoke check rule applies.

### Literals
%%%
tag := "rules-literals"
%%%

$$`\frac{}{\Gamma \vdash \mathsf{LiteralInt}\;n \Rightarrow \mathsf{TInt}} \quad \text{([⇒] Lit-Int)}`

{docstring Strata.Laurel.Resolution.Synth.litInt}

$$`\frac{}{\Gamma \vdash \mathsf{LiteralBool}\;b \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Lit-Bool)}`

{docstring Strata.Laurel.Resolution.Synth.litBool}

$$`\frac{}{\Gamma \vdash \mathsf{LiteralString}\;s \Rightarrow \mathsf{TString}} \quad \text{([⇒] Lit-String)}`

{docstring Strata.Laurel.Resolution.Synth.litString}

$$`\frac{}{\Gamma \vdash \mathsf{LiteralDecimal}\;d \Rightarrow \mathsf{TReal}} \quad \text{([⇒] Lit-Decimal)}`

{docstring Strata.Laurel.Resolution.Synth.litDecimal}

### Variables
%%%
tag := "rules-variables"
%%%

$$`\frac{\Gamma(x) = T}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Local}\;x) \Rightarrow T} \quad \text{([⇒] Var-Local)}`

{docstring Strata.Laurel.Resolution.Synth.varLocal}

$$`\frac{\Gamma \vdash e \Rightarrow \_ \quad \Gamma(f) = T_f}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Field}\;e\;f) \Rightarrow T_f} \quad \text{([⇒] Var-Field)}`

{docstring Strata.Laurel.Resolution.Synth.varField}

$$`\frac{x \notin \mathrm{dom}(\Gamma)}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Declare}\;\langle x, \mathsf{some}\;T_x\rangle) \Rightarrow \mathsf{TVoid} \quad \dashv \quad \Gamma, x : T_x} \quad \text{([⇒] Var-Declare)}`

$$`\frac{x \notin \mathrm{dom}(\Gamma)}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Declare}\;\langle x, \mathsf{none}\rangle) \Rightarrow \mathsf{TVoid} \quad [\text{emits “cannot infer a type …”}] \quad \dashv \quad \Gamma, x : \mathsf{Unknown}} \quad \text{([⇒] Var-Declare-Infer)}`

The type annotation is optional in the AST (`type : Option`). A bare
`var x` (annotation `none`) has *neither* an annotation *nor* an
initializer to read a type from, so \[⇒\] Var-Declare-Infer diagnoses it
and binds $`x : \mathsf{Unknown}` so later uses of $`x` don't cascade
further type errors. An unannotated declaration *with* an initializer
(`var x := e`) never reaches these rules: it parses as an `Assign` with a
sole `Declare` target and is handled by the \[⇒\]/\[⇐\] Decl-Synth rules
(see {ref "rules-assignment"}[*Assignment*]), which recover the
binding's type from the initializer. Either way the node is rewritten to a
fully-annotated `Declare x (some T)`, so no `none` annotation survives
resolution.

$`x \notin \mathrm{dom}(\Gamma)` is a soft side condition rather than a
hard premise: when $`x` is already bound in the current scope the rule still
fires, $`[\text{emits “Duplicate definition …”}]`, and extends the scope —
but with an *unresolved* placeholder instead of $`x : T_x`, so later uses of
$`x` don't cascade further type errors.

{docstring Strata.Laurel.Resolution.Check.varDeclare}

### Control flow
%%%
tag := "rules-control-flow"
%%%

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Leftarrow T \quad \Gamma \vdash \mathit{elseBr} \Leftarrow T}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;(\mathsf{some}\;\mathit{elseBr}) \Leftarrow T} \quad \text{([⇐] If)}`

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Leftarrow T \quad \mathsf{TVoid} <: T}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;\mathsf{none} \Leftarrow T} \quad \text{([⇐] If-NoElse)}`

{docstring Strata.Laurel.Resolution.Check.ifThenElse}

When an `if` appears in *operand* position — where no expected type is
available to push down (e.g. as an operand of $`==` / $`<` / $`+\!+`,
whose operands are synthesized) — the synth counterpart fires instead.
With an `else`, both branches are synthesized and their types must be
mutually consistent ($`\sim`, the symmetric gradual relation);
inconsistent branches $`[\text{emits “'if' branches have incompatible
types X and Y”}]` and synthesize $`\mathsf{Unknown}`. The result is the
join $`T_t \sqcup T_e` of the two branch types, so when one branch is a
hole ($`\mathsf{Unknown}`) the join promotes to the other branch's
concrete type, and the synthesized type is independent of branch order.
Without an `else`, the missing branch cannot produce a value, so the `if`
synthesizes $`\mathsf{TVoid}`.

:::example "`if` in operand position"
- `(if c then 1 else 2) == y` — both branches $`\mathsf{TInt}`, so the `if` synthesizes $`\mathsf{TInt}`
- `if c then 1 else <?>` — the hole branch promotes; synthesizes $`\mathsf{TInt}`
- `if c then 1 else "x"` — incompatible branches: *'if' branches have incompatible types 'int' and 'string'*, synthesizes $`\mathsf{Unknown}`
- `if c then 1` (no `else`) — synthesizes $`\mathsf{TVoid}`
:::

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Rightarrow T_t \quad \Gamma \vdash \mathit{elseBr} \Rightarrow T_e \quad T_t \sim T_e}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;(\mathsf{some}\;\mathit{elseBr}) \Rightarrow T_t \sqcup T_e} \quad \text{([⇒] If-Synth)}`

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Rightarrow \_}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] If-Synth-NoElse)}`

{docstring Strata.Laurel.Resolution.Synth.ifThenElse}

A non-empty block is typed by splitting its statement list into the
*last* statement and the statements before it. The last statement
carries the block's value and inherits the surrounding expected type;
each earlier statement runs only for its effect — written
$`\Gamma \vdash s\;\diamond` (*effect position*: the statement's value
is discarded). The check and synth rules share this shape, differing
only in how the last statement is treated:

$$`\frac{\Gamma_0 = \Gamma \quad \Gamma_{i-1} \vdash s_i \;\diamond \;\dashv\; \Gamma_i \;\;(1 \le i \le n) \quad \Gamma_n \vdash \mathit{last} \Leftarrow T}{\Gamma \vdash \mathsf{Block}\;[s_1; \ldots; s_n; \mathit{last}]\;\mathit{label} \Leftarrow T} \quad \text{([⇐] Block)}`

$$`\frac{\Gamma_0 = \Gamma \quad \Gamma_{i-1} \vdash s_i \;\diamond \;\dashv\; \Gamma_i \;\;(1 \le i \le n) \quad \Gamma_n \vdash \mathit{last} \Rightarrow T}{\Gamma \vdash \mathsf{Block}\;[s_1; \ldots; s_n; \mathit{last}]\;\mathit{label} \Rightarrow T} \quad \text{([⇒] Block-Synth)}`

\[⇐\] Block fires whenever an expected type $`T` is supplied (procedure
bodies, branches, loop bodies, assignment RHS, call arguments);
\[⇒\] Block-Synth fires in operand position, where no expected type is
available (e.g. $`\{\,x := 1;\; x\,\} == y`), synthesizing the last
statement's type as the block's value type.

When the block itself sits in statement position ($`T = \mathsf{TVoid}`)
the last statement is in effect position too: its premise becomes
$`\mathit{last}\;\diamond` rather than $`\mathit{last} \Leftarrow
\mathsf{TVoid}`, so a trailing call discards its result and
$`\{\ldots;\,\mathit{foo}()\}` type-checks as a statement even when
`foo` returns a non-void type.

The effect-position judgment $`\Gamma \vdash s\;\diamond` synthesizes
the statement and discards the result:

$$`\frac{\Gamma \vdash s \Rightarrow \_ \;\dashv\; \Gamma'}{\Gamma \vdash s \;\diamond \;\dashv\; \Gamma'} \quad \text{([⋄] Synth-Discard)}`

Every expression in statement position is synthesized and its type
discarded. Statement-shaped forms (`Var-Declare`, `Assign`, `Assert`,
`Assume`, `While`, `Exit`, `Return`) synthesize $`\mathsf{TVoid}`;
value-producing forms (calls, `IncrDecr`, literals, etc.) synthesize
their natural type, which is then discarded. This means any expression
is accepted in statement position — the `f(x);` idiom works regardless
of `f`'s return type, and `x++;` is admitted even though `++`
synthesizes the target's type.

Only declarations actually extend the scope $`\Gamma_i` — `Var (.Declare …)`
and `Assign` statements with `Declare` targets (`var x := e`,
`assign var x, y := call()`); every other statement leaves it unchanged. The block opens a fresh nested
scope, so declarations made inside don't leak out — once the block ends,
the surrounding $`\Gamma` is restored. It also emits a
`"dead code after '<terminator>'"` diagnostic when an `Exit` or
`Return` is followed by further statements in the same block.

Pushing $`T` into the last statement (rather than synthesizing the whole
block and applying \[⇐\] Sub at the boundary) means a type mismatch is
reported at the offending subexpression's source location, and the
expectation keeps propagating through nested `Block` / `IfThenElse` /
`Hole` / `Quantifier` constructs that have their own check rules.

$$`\frac{}{\Gamma \vdash \mathsf{Block}\;[]\;\mathit{label} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Empty-Block)}`

The empty block has a fixed type and is the only block-level rule that
synthesizes unconditionally. \[⇐\] Block and \[⇒\] Block-Synth always
split off a *last* statement, so they never reach an empty list; the
empty case is hit only when the block is literally empty at the dispatch
site. When an empty block appears in check position with
`expected ≠ TVoid`, the standard \[⇐\] Sub rule fires at the boundary
(`Check.resolveStmtExpr`'s subsumption-fallback wildcard arm, requiring
$`\mathsf{TVoid} <: \mathit{expected}`).

{docstring Strata.Laurel.Resolution.Synth.emptyBlock}

{docstring Strata.Laurel.Resolution.Synth.block}

{docstring Strata.Laurel.Resolution.Check.block}

The $`\Gamma \vdash s\;\diamond` judgment — the \[⋄\] Synth-Discard
rule above — is the single definition of what counts as a statement in
effect position, factored out into
{name Strata.Laurel.Resolution.Check.statement}`Check.statement`:

{docstring Strata.Laurel.Resolution.Check.statement}

$$`\frac{l \in \Gamma_{\mathrm{lbl}}}{\Gamma \vdash \mathsf{Exit}\;l \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Exit)}`

`exit` is an unconditional jump out of the enclosing labeled block.
It synthesizes $`\mathsf{TVoid}` unconditionally. Labels live in their
own namespace $`\Gamma_{\mathrm{lbl}}`, populated by the surrounding
`Block` rule when its $`\mathit{label}` is `some l`. An
$`\mathsf{Exit}\;l` targeting a label not in $`\Gamma_{\mathrm{lbl}}`
is rejected.

{docstring Strata.Laurel.Resolution.Check.exit}

In the Return rules below, $`\overline{T_o}` denotes the declared
output-parameter type list of the enclosing procedure (an implicit
parameter of the rules — the procedure binds it once on entry).

$$`\frac{\overline{T_o} = []}{\Gamma \vdash \mathsf{Return}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-None-Void)}`

$$`\frac{\overline{T_o} = [T]}{\Gamma \vdash \mathsf{Return}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-None-Single)}`

$$`\frac{\overline{T_o} = [T_1; \ldots; T_n] \quad (n \ge 2)}{\Gamma \vdash \mathsf{Return}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-None-Multi)}`

$$`\frac{\overline{T_o} = [T] \quad \Gamma \vdash e \Leftarrow T}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-Some)}`

$$`\frac{\overline{T_o} = []}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \rightsquigarrow \text{error: “void procedure cannot return a value”}} \quad \text{([⇒] Return-Void-Error)}`

$$`\frac{\overline{T_o} = [T_1; \ldots; T_n] \quad (n \ge 2)}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \rightsquigarrow \text{error: “multi-output procedure cannot use 'return e'; assign to named outputs instead”}} \quad \text{([⇒] Return-Multi-Error)}`

`return` is the only rule whose premises depend on the enclosing
procedure's declared outputs. The rule synthesizes $`\mathsf{TVoid}`
because `return` is a control-flow terminator: it never falls through
and produces no value for the surrounding context. The returned value
(if any) is checked against the procedure's declared output. The error
arms fire when $`\overline{T_o}`'s arity does not match the syntactic
shape of `return e`.

Regardless of which arm fires, $`e` is always elaborated — it is
checked against the declared output in the single-output case,
otherwise synthesized — so any errors inside $`e` are reported in
addition to the arity diagnostic.

The three Return-None rules all accept `return;` unconditionally.
Void-output procedures accept it naturally (Return-None-Void);
single-output procedures accept it without a subtype check
(Return-None-Single); multi-output procedures accept it as an
early-exit shorthand that leaves the named outputs at whatever they
were last assigned to (Return-None-Multi).

When the surrounding context has no enclosing procedure body (e.g.
inside a constant initializer), `answerType = none` and all Return
checks are skipped; well-formed input never produces this case.

{docstring Strata.Laurel.Resolution.Check.return}

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{invs}_i \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{decreases} \Rightarrow U \quad \mathsf{Numeric}\;U \quad \Gamma \vdash \mathit{body} \Leftarrow \mathsf{Unknown}}{\Gamma \vdash \mathsf{While}\;\mathit{cond}\;\mathit{invs}\;\mathit{decreases}\;\mathit{body} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] While)}`

The body is checked at $`\mathsf{Unknown}`: control either re-enters
the loop or falls through, so the body's value type is never observed
by the surrounding context. A loop is a statement and yields no value,
so the rule synthesizes $`\mathsf{TVoid}`.

The optional $`\mathit{decreases}` clause is synthesized and required
to have a numeric type via the same $`\mathsf{Numeric}` predicate
used by the arithmetic primitive operations. $`\mathsf{Numeric}` is
a predicate (it admits $`\mathsf{TInt}`, $`\mathsf{TReal}`,
$`\mathsf{TFloat64}`, $`\mathsf{TBv}_w` (a bitvector of any width), and
$`\mathsf{Unknown}` as the gradual escape hatch), not a single type, so
the clause runs in synth mode rather than check mode.

{docstring Strata.Laurel.Resolution.Check.while}

### Verification statements
%%%
tag := "rules-verification-statements"
%%%

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Assert}\;\mathit{cond} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Assert)}`

{docstring Strata.Laurel.Resolution.Check.assert}

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Assume}\;\mathit{cond} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Assume)}`

{docstring Strata.Laurel.Resolution.Check.assume}

### Assignment
%%%
tag := "rules-assignment"
%%%

$$`\frac{\Gamma \vdash \mathit{targets}_i \Rightarrow T_i \quad \Gamma \vdash e \Leftarrow \mathit{ExpectedTy}}{\Gamma \vdash \mathsf{Assign}\;\mathit{targets}\;e \Rightarrow \mathit{ExpectedTy}} \quad \text{([⇒] Assign)}`

where `ExpectedTy = T_1` if `|targets| = 1` and `MultiValuedExpr [T_1; …; T_n]` otherwise.
The target's declared type `T_i` comes from the variable's scope entry (for
{name Strata.Laurel.Variable.Local}`Local` and {name Strata.Laurel.Variable.Field}`Field`)
or from the {name Strata.Laurel.Variable.Declare}`Declare`-bound parameter type. The
RHS receives `ExpectedTy` via `Check.resolveStmtExpr`, so bidirectional rules in the
RHS propagate the assignment's type into nested constructs. The
assignment synthesizes `ExpectedTy` — populating the surrounding
context with the target's type while the RHS is checked against it.

{docstring Strata.Laurel.Resolution.Synth.assign}

$$`\frac{\Gamma \vdash \mathsf{Assign}\;\mathit{targets}\;e \Rightarrow \mathit{ExpectedTy} \quad T = \mathsf{TVoid} \lor \mathit{ExpectedTy} <: T}{\Gamma \vdash \mathsf{Assign}\;\mathit{targets}\;e \Leftarrow T} \quad \text{([⇐] Assign)}`

The check rule synthesizes the assignment's type via \[⇒\] Assign
and then runs the standard \[⇐\] Sub boundary check `ExpectedTy <: T`
— *unless* `T = TVoid`, the marker for statement position. Pushing
`TVoid` through subsumption would only succeed when the LHS is itself
void, which would reject every non-void assignment used as a
statement, so the subsumption is skipped and the synthesized value is
discarded.

{docstring Strata.Laurel.Resolution.Check.assign}

An *unannotated* declaring assignment — `var x := e`, i.e. an `Assign`
whose sole target is `Declare x none` — is dispatched to a dedicated
rule pair *before* \[⇒\]/\[⇐\] Assign. The target has no declared type
to push into the RHS, so the direction flips: the initializer is
*synthesized* and the binding adopts its type.

$$`\frac{x \notin \mathrm{dom}(\Gamma) \quad \Gamma \vdash e \Rightarrow T}{\Gamma \vdash \mathsf{Assign}\;[\mathsf{.Declare}\;\langle x, \mathsf{none}\rangle]\;e \Rightarrow T \quad \dashv \quad \Gamma, x : T} \quad \text{([⇒] Decl-Synth)}`

$$`\frac{x \notin \mathrm{dom}(\Gamma) \quad \Gamma \vdash e \Rightarrow T \quad T' = \mathsf{TVoid} \lor T <:_\sim T'}{\Gamma \vdash \mathsf{Assign}\;[\mathsf{.Declare}\;\langle x, \mathsf{none}\rangle]\;e \Leftarrow T' \quad \dashv \quad \Gamma, x : T} \quad \text{([⇐] Decl-Synth)}`

The adopted type $`T` must be a *value* type: a $`\mathsf{TVoid}`
initializer (a void call, a `while`, …) or a
$`\mathsf{MultiValuedExpr}` (a multi-output call)
$`[\text{emits “cannot infer a type …”}]` and binds
$`x : \mathsf{Unknown}` instead, suppressing cascades on later uses.
As in \[⇒\] Var-Declare, the node is rewritten to carry
$`\mathsf{some}\;T`, so no `none` annotation survives resolution.
Unannotated declared targets of a *multi-target*
`assign var x, y := call()` don't take this rule; they are recovered
component-wise from the synthesized RHS tuple inside
\[⇒\]/\[⇐\] Assign (see the docstrings above).

{docstring Strata.Laurel.Resolution.Synth.declInfer}

{docstring Strata.Laurel.Resolution.Check.declInfer}

### Calls
%%%
tag := "rules-calls"
%%%

$$`\frac{\Gamma(\mathit{callee}) = \text{static-procedure with inputs } Ts \text{ and output } [T'] \text{ (single output)} \quad \Gamma \vdash \mathit{args}_i \Leftarrow Ts_i \text{ (pairwise)}}{\Gamma \vdash \mathsf{StaticCall}\;\mathit{callee}\;\mathit{args} \Rightarrow T'} \quad \text{([⇒] Static-Call)}`

$$`\frac{\Gamma(\mathit{callee}) = \text{static-procedure with inputs } Ts \text{ and outputs } [T_1; \ldots; T_n],\; n \ge 2 \quad \Gamma \vdash \mathit{args}_i \Leftarrow Ts_i \text{ (pairwise)}}{\Gamma \vdash \mathsf{StaticCall}\;\mathit{callee}\;\mathit{args} \Rightarrow \mathsf{MultiValuedExpr}\;[T_1; \ldots; T_n]} \quad \text{([⇒] Static-Call-Multi)}`

{docstring Strata.Laurel.Resolution.Synth.staticCall}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_ \quad \Gamma(\mathit{callee}) = \text{instance- or static-procedure with inputs } [\mathit{self}; Ts] \text{ and output } [T'] \text{ (single output)} \quad \Gamma \vdash \mathit{args}_i \Leftarrow Ts_i \text{ (pairwise; self dropped)}}{\Gamma \vdash \mathsf{InstanceCall}\;\mathit{target}\;\mathit{callee}\;\mathit{args} \Rightarrow T'} \quad \text{([⇒] Instance-Call)}`

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_ \quad \Gamma(\mathit{callee}) = \text{instance- or static-procedure with inputs } [\mathit{self}; Ts] \text{ and outputs } [T_1; \ldots; T_n],\; n \ge 2 \quad \Gamma \vdash \mathit{args}_i \Leftarrow Ts_i \text{ (pairwise; self dropped)}}{\Gamma \vdash \mathsf{InstanceCall}\;\mathit{target}\;\mathit{callee}\;\mathit{args} \Rightarrow \mathsf{MultiValuedExpr}\;[T_1; \ldots; T_n]} \quad \text{([⇒] Instance-Call-Multi)}`

The callee is resolved against either an instance procedure or a
static procedure (the latter handles uniformly-dispatched call syntax
where the receiver is forwarded as `self`). Output arity is forwarded
identically to
{name Strata.Laurel.Resolution.Synth.staticCall}`Synth.staticCall`'s
single-vs-multi split. In both call families the single- and multi-output
rules differ only in the *output* arity; argument checking is the same, and
surplus arguments (beyond the declared parameters, or when the callee is
unresolved) are checked against $`\mathsf{Unknown}` rather than flagged as an
arity error. A zero-output ($`n = 0`) procedure call is the third case in the
arity split: it synthesizes $`\mathsf{TVoid}` rather than a
$`\mathsf{MultiValuedExpr}`.

{docstring Strata.Laurel.Resolution.Synth.instanceCall}

### Operators
%%%
tag := "rules-primitive-operations"
%%%

Operators are *not* a distinct kind of expression, and there are no
operator-specific typing rules. `x + y` parses as
$`\mathsf{StaticCall}\;\$\mathsf{add}\;[x; y]`, a call to an overloaded
built-in wrapper procedure declared in `CoreDefinitionsForLaurel` and
prepended to every program, so operators are typed entirely by
\[⇒\] Static-Call above. What used to be an operator's admissible
operand types is now just the set of declared overloads:

```
procedure $add(x: int, y: int) : int    return intAdd(x, y);
procedure $add(x: real, y: real) : real return realAdd(x, y);
```

Each wrapper is a thin transparent procedure delegating to a
type-specific external (`intAdd`, `realAdd`, …) that
`LaurelToCoreSchemaPass` recognizes and lowers to the corresponding
Core operator. The wrappers of one operator must all share a name —
the parser cannot know which overload a `+` denotes — while the
externals they delegate to do not.

Two consequences of typing operators as calls:

: Operand admissibility is overload selection

  There is no `Numeric` side-condition. `1 + 2.0` is rejected not
  because a rule demands equal operand types, but because neither the
  `int` nor the `real` overload of `$add` accepts an
  $`(\mathsf{TInt}, \mathsf{TReal})` pair — reported as *no overload of
  '$add' matches the argument types*. Likewise `<` on bitvectors
  resolves only at the widths Core provides operators for
  (1, 8, 16, 32, 64), rather than silently mistranslating other widths.

: Preconditions come from the wrapper

  Because a wrapper is an ordinary procedure it can carry a contract.
  `$div` declares `requires y != 0` and delegates to Core's *safe*
  division, so a possible division by zero surfaces as a failed
  precondition on the call.

The gradual $`\mathsf{Unknown}` still flows freely: it is a consistent
subtype of every parameter type, so it never rules an overload out. An
$`\mathsf{Unknown}` argument therefore cannot *discriminate* between
overloads, but the other arguments still can — selection runs on the
informative arguments alone, and only an unresolved result caused by an
$`\mathsf{Unknown}` argument is passed over silently (the argument's own
error already covers it) instead of being reported as a no-match or an
ambiguity.

:::example "Operator overload selection"
- `1 + 2` selects the `int` overload and synthesizes $`\mathsf{TInt}`
- `1.5 + 2.5` selects the `real` overload and synthesizes $`\mathsf{TReal}`
- `<?> + 1` selects the `int` overload — the informative operand decides
- `<?> + <?>` is unresolved and synthesizes $`\mathsf{Unknown}`; no error is reported
- `1 + 2.0` is rejected: *no overload of '$add' matches the argument types*
:::

Equality is the one operator that is *not* a transparent wrapper.
`$eq` / `$neq` are declared `external`, because equality is polymorphic
and Laurel has no polymorphic types: a wrapper body would carry a
placeholder $`\mathsf{int} \to \mathsf{int} \to \mathsf{bool}`
signature into Core and fail to unify against a composite, a datatype,
or a bool. `Synth.staticCall` special-cases these two names to require
only that the operands be consistent ($`T_l \sim T_r`), and
`LaurelToCoreSchemaPass` lowers them straight to Core's polymorphic
equality.

$$`\frac{\Gamma \vdash \mathit{lhs} \Rightarrow T_l \quad \Gamma \vdash \mathit{rhs} \Rightarrow T_r \quad T_l \sim T_r \quad T_l \neq \mathsf{TVoid} \quad T_r \neq \mathsf{TVoid} \quad \mathit{callee} \in \{\$\mathsf{eq}, \$\mathsf{neq}\}}{\Gamma \vdash \mathsf{StaticCall}\;\mathit{callee}\;[\mathit{lhs}; \mathit{rhs}] \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Eq)}`

The $`\neq \mathsf{TVoid}` premises reject void operands even though
$`\mathsf{TVoid} \sim \mathsf{TVoid}` holds: a void expression carries no
value to compare.

Since an operator is a call, the check-mode rule for one is
\[⇐\] Sub applied to \[⇒\] Static-Call: the call's synthesized
result type is compared against the expected type. There is no separate
operand-pushing rule, so a mixed-type operator expression reports one
overload-resolution failure over the whole call rather than a mismatch
against an individual operand.

### Object forms
%%%
tag := "rules-object-forms"
%%%

$$`\frac{\mathit{ref} \text{ is a composite or datatype, or is unresolved, or is absent from } \Gamma}{\Gamma \vdash \mathsf{New}\;\mathit{ref} \Rightarrow \mathsf{UserDefined}\;\mathit{ref}} \quad \text{([⇒] New-Ok)}`

$$`\frac{\mathit{ref} \text{ resolves to a non-type kind}}{\Gamma \vdash \mathsf{New}\;\mathit{ref} \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] New-Fallback)}`

The $`\mathsf{Unknown}` fallback fires *only* when $`\mathit{ref}` resolves to
a present definition whose kind is neither composite nor datatype. An
unresolved or out-of-scope $`\mathit{ref}` takes the New-Ok branch instead, so
the kind diagnostic that `resolveRef` already emitted is not duplicated.

{docstring Strata.Laurel.Resolution.Synth.new}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow U \quad U \sim T \lor U <: T \lor T <: U}{\Gamma \vdash \mathsf{AsType}\;\mathit{target}\;T \Rightarrow T} \quad \text{([⇒] AsType)}`

{docstring Strata.Laurel.Resolution.Synth.asType}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow U \quad U \sim T \lor U <: T \lor T <: U}{\Gamma \vdash \mathsf{IsType}\;\mathit{target}\;T \Rightarrow \mathsf{TBool}} \quad \text{([⇒] IsType)}`

{docstring Strata.Laurel.Resolution.Synth.isType}

$$`\frac{\Gamma \vdash \mathit{lhs} \Rightarrow T_l \quad \Gamma \vdash \mathit{rhs} \Rightarrow T_r \quad \mathsf{isReference}\;T_l \quad \mathsf{isReference}\;T_r \quad T_l \sim T_r}{\Gamma \vdash \mathsf{ReferenceEquals}\;\mathit{lhs}\;\mathit{rhs} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] RefEq)}`

`isReference T` holds when `T` is a {name Strata.Laurel.HighType.UserDefined}`UserDefined`
or {name Strata.Laurel.HighType.Unknown}`Unknown` type. `~` is the consistency relation
{name Strata.Laurel.isConsistent}`isConsistent` — symmetric, with the
{name Strata.Laurel.HighType.Unknown}`Unknown` wildcard.

{docstring Strata.Laurel.Resolution.Synth.refEq}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow T_t \quad \Gamma(f) = T_f \quad \Gamma \vdash \mathit{newVal} \Leftarrow T_f}{\Gamma \vdash \mathsf{PureFieldUpdate}\;\mathit{target}\;f\;\mathit{newVal} \Rightarrow T_t} \quad \text{([⇒] PureFieldUpdate)}`

{docstring Strata.Laurel.Resolution.Synth.pureFieldUpdate}

### Verification expressions
%%%
tag := "rules-verification-expressions"
%%%

$$`\frac{\Gamma, x : T \vdash \mathit{body} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Quantifier}\;\mathit{mode}\;\langle x, T\rangle\;\mathit{trig}\;\mathit{body} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Quantifier)}`

{docstring Strata.Laurel.Resolution.Synth.quantifier}

$$`\frac{\Gamma \vdash \mathit{name} \Rightarrow \_}{\Gamma \vdash \mathsf{Assigned}\;\mathit{name} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Assigned)}`

{docstring Strata.Laurel.Resolution.Synth.assigned}

$$`\frac{\Gamma \vdash v \Leftarrow T}{\Gamma \vdash \mathsf{Old}\;v \Leftarrow T} \quad \text{([⇐] Old)}`

{docstring Strata.Laurel.Resolution.Check.old}

`old` is type-transparent, so it also synthesizes: in operand position
(e.g. the postcondition pattern `ensures counter.value == old(counter.value) + 1`,
where $`==` synthesizes its operands) $`v` is synthesized and its type
returned unchanged.

$$`\frac{\Gamma \vdash v \Rightarrow T}{\Gamma \vdash \mathsf{Old}\;v \Rightarrow T} \quad \text{([⇒] Old-Synth)}`

{docstring Strata.Laurel.Resolution.Synth.old}

$$`\frac{\Gamma \vdash v \Rightarrow T \quad \mathsf{isReference}\;T}{\Gamma \vdash \mathsf{Fresh}\;v \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Fresh)}`

{docstring Strata.Laurel.Resolution.Synth.fresh}

$$`\frac{\Gamma \vdash v \Leftarrow T \quad \Gamma \vdash \mathit{proof} \Rightarrow \_}{\Gamma \vdash \mathsf{ProveBy}\;v\;\mathit{proof} \Leftarrow T} \quad \text{([⇐] ProveBy)}`

{docstring Strata.Laurel.Resolution.Check.proveBy}

Like `old`, `ProveBy` is type-transparent in `v`, so it also
synthesizes: in operand position $`v` is synthesized for its type $`T`,
$`\mathit{proof}` is synthesized only for its name-resolution side
effects (its type discarded), and $`T` is returned.

$$`\frac{\Gamma \vdash v \Rightarrow T \quad \Gamma \vdash \mathit{proof} \Rightarrow \_}{\Gamma \vdash \mathsf{ProveBy}\;v\;\mathit{proof} \Rightarrow T} \quad \text{([⇒] ProveBy-Synth)}`

{docstring Strata.Laurel.Resolution.Synth.proveBy}

### Self reference
%%%
tag := "rules-self-reference"
%%%

$$`\frac{\Gamma.\mathit{instanceTypeName} = \mathsf{some}\;T}{\Gamma \vdash \mathsf{This} \Rightarrow \mathsf{UserDefined}\;T} \quad \text{([⇒] This-Inside)}`

$$`\frac{\Gamma.\mathit{instanceTypeName} = \mathsf{none}}{\Gamma \vdash \mathsf{This} \Rightarrow \mathsf{Unknown} \quad [\text{emits “‘this’ is not allowed outside instance methods”}]} \quad \text{([⇒] This-Outside)}`

{docstring Strata.Laurel.Resolution.Synth.this}

### Untyped forms
%%%
tag := "rules-untyped-forms"
%%%

$$`\frac{}{\Gamma \vdash \mathsf{Abstract}\,/\,\mathsf{All}\;\ldots \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] Abstract / All)}`

{docstring Strata.Laurel.Resolution.Synth.abstract}

{docstring Strata.Laurel.Resolution.Synth.all}

### ContractOf
%%%
tag := "rules-contract-of"
%%%

$$`\frac{\mathit{fn} = \mathsf{Var}\;(\mathsf{.Local}\;\mathit{id}) \quad \Gamma(\mathit{id}) \in \{\mathit{staticProcedure}, \mathit{instanceProcedure}, \mathit{unresolved}\}}{\Gamma \vdash \mathsf{ContractOf}\;\mathsf{Precondition}\;\mathit{fn} \Rightarrow \mathsf{TBool} \qquad \Gamma \vdash \mathsf{ContractOf}\;\mathsf{PostCondition}\;\mathit{fn} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] ContractOf-Bool)}`

$$`\frac{\mathit{fn} = \mathsf{Var}\;(\mathsf{.Local}\;\mathit{id}) \quad \Gamma(\mathit{id}) \in \{\mathit{staticProcedure}, \mathit{instanceProcedure}, \mathit{unresolved}\}}{\Gamma \vdash \mathsf{ContractOf}\;\mathsf{Reads}\;\mathit{fn} \Rightarrow \mathsf{TSet}\;\mathsf{Unknown} \qquad \Gamma \vdash \mathsf{ContractOf}\;\mathsf{Modifies}\;\mathit{fn} \Rightarrow \mathsf{TSet}\;\mathsf{Unknown}} \quad \text{([⇒] ContractOf-Set)}`

$$`\frac{\mathit{fn} \text{ is not a } \mathsf{Var}\;(\mathsf{.Local}) \text{ resolving to a procedure or unresolved name}}{\Gamma \vdash \mathsf{ContractOf}\;\ldots\;\mathit{fn} \rightsquigarrow \text{error: “‘contractOf’ expected a procedure reference”}} \quad \text{([⇒] ContractOf-Error)}`

The $`\mathit{unresolved}` kind is admitted so an already-reported
name-resolution error is not duplicated; ContractOf-Error fires only when
$`\mathit{fn}` resolves to a *present* non-procedure definition (or is not a
local reference at all).

{docstring Strata.Laurel.Resolution.Synth.contractOf}

### Holes
%%%
tag := "rules-holes"
%%%

$$`\frac{T_h <: T}{\Gamma \vdash \mathsf{Hole}\;d\;(\mathsf{some}\;T_h) \Leftarrow T} \quad \text{([⇐] Hole-Some)}`

{docstring Strata.Laurel.Resolution.Check.holeSome}

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;\mathsf{none} \Leftarrow T \quad \mapsto \quad \mathsf{Hole}\;d\;(\mathsf{some}\;T)} \quad \text{([⇐] Hole-None)}`

{docstring Strata.Laurel.Resolution.Check.holeNone}

In synth position no expected type is available to push into the hole, so
an unannotated hole synthesizes the gradual $`\mathsf{Unknown}` while an
annotated hole synthesizes its annotation $`T_h` (this is what lets
`<?> + 1` synthesize $`\mathsf{TInt}`).

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;\mathsf{none} \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] Hole-Synth-None)}`

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;(\mathsf{some}\;T_h) \Rightarrow T_h} \quad \text{([⇒] Hole-Synth-Some)}`

### Procedure
%%%
tag := "rules-procedure"
%%%

A procedure body is synthesized (not checked against a computed
expected type) and is resolved under a scope that includes the
procedure's input and output parameters. The Return rules above refer
to the same output list $`\overline{T_o}` that the procedure binds
here.

$$`\frac{\overline{T_o} = \mathit{proc}.\mathit{outputs}.\mathit{types} \quad \Gamma_\mathit{global},\,\mathit{params}(\mathit{proc}) \vdash \mathit{proc}.\mathit{body} \Rightarrow \_}{\Gamma_\mathit{global} \vdash \mathsf{Procedure}\;\mathit{proc}} \quad \text{(Procedure)}`

The body is synthesized and its type is discarded — there is no
constraint from the output list pushed into the body. Outputs are
matched only via `return e` (checked against $`\overline{T_o}` by
{name Strata.Laurel.Resolution.Check.return}`Check.return`) or via
named-output assignment.

{docstring Strata.Laurel.resolveProcedure}

{docstring Strata.Laurel.resolveInstanceProcedure}

# Execution
%%%
tag := "execution"
%%%

The execution features are types, values, expressions, statements, procedures, and objects.

## Types

Laurel's types come in two groups: those a user can write — primitives,
collections, and user-defined types — and a few internal constructors the
implementation introduces that have no surface syntax.

The {name Strata.Laurel.HighType}`HighType` type enumerates every type Laurel
tracks. Alongside the user-writable types it also includes internal constructors
(such as `Unknown` and `MultiValuedExpr`) that the compiler introduces
during resolution and later passes; these have no surface syntax.

{docstring Strata.Laurel.HighType}

### User-Defined Types

User-defined types come in two categories: composite types and constrained types.

Composite types have fields and procedures, and may extend other composite types. Fields
declare whether they are mutable and specify their type.

{docstring Strata.Laurel.CompositeType}

{docstring Strata.Laurel.Field}

Constrained types are defined by a base type and a constraint over the values of the base
type. Algebraic datatypes can be encoded using composite and constrained types.

{docstring Strata.Laurel.ConstrainedType}

{docstring Strata.Laurel.TypeDefinition}

### Primitive types

Laurel provides unbounded mathematical `int` and `real` types, a `bool` type,
`string`, and fixed-width bitvectors `bv N`. Because `int` is unbounded, arithmetic in
specifications behaves like ordinary mathematics: there is no overflow to reason
around when you are stating what a procedure computes. Likewise `real` is an exact
mathematical real, not a floating-point approximation — a decimal literal such as `3.1415`
denotes exactly that rational value.

There is no writable `void` type; a procedure with no outputs is void. `float64` is accepted by
the parser as a statement of intent, but is not implemented, so it cannot be used in a program
that has to be analysed.

### Collections

Laurel has four built-in collection types. They are declared in the always-on prelude rather than
built into the grammar, so their operations are ordinary procedure calls and they can be used
wherever a value can. None of them has literal syntax: build a collection from its empty value.

`Map<K, V>` is a *partial* map — a key may be absent — and is the one to reach for when modelling
a source-language dictionary:

```laurel
procedure mapDemo()
  opaque
{
  var m: Map<int, bool> := mapEmpty();
  m := mapSet(m, 1, true);
  assert mapContains(m, 1);
  assert mapGet(m, 1);
  m := mapRemove(m, 1);
  assert !mapContains(m, 1)
};
```

`mapGet` is total but unconstrained on an absent key, so it returns *some* value of the right
type rather than failing. Test with `mapContains` when absence matters.

`Set<T>` is an immutable set, and `Sequence<T>` an immutable sequence:

```laurel
procedure setDemo()
  opaque
{
  var s: Set<int> := setEmpty();
  s := setInsert(s, 3);
  assert setContains(s, 3);
  assert !setContains(setRemove(s, 3), 3)
};

procedure seqDemo()
  opaque
{
  var xs: Sequence<int> := seqEmpty();
  xs := seqBuild(xs, 7);
  assert seqLength(xs) == 1;
  assert seqSelect(xs, 0) == 7
};
```

`seqSelect`, `seqUpdate`, `seqTake`, and `seqDrop` carry bounds preconditions, so an in-range
index is a proof obligation at the call site rather than an unchecked read.

Underneath all of these is `TotalMap K V`, a *total* map in which every key has a value. It is
the low-level building block, and it is available directly when a producer wants exactly that:

```laurel
procedure totalMapDemo()
  opaque
{
  var t: TotalMap int bool := mapConst(false);
  t := update(t, 1, true);
  assert select(t, 1);
  assert !select(t, 0)
};
```

Its three primitives are `select(m, k)`, `update(m, k, v)`, and `mapConst(v)`, and they satisfy
the expected law, `select(update(m, k, v), k) == v`.

Prefer the partial `Map<K, V>` in ordinary code: `TotalMap` cannot express absence, so a front
end modelling a dictionary would have to encode key presence separately, which is exactly what
`Map<K, V>` already does.

`mapConst`, `mapEmpty`, `setEmpty`, and `seqEmpty` take no argument that fixes their type, so
their result type is read from the declared type of the binding they initialize. Always annotate
that binding — every argument-less empty constructor needs it.

### Named and generic types

A bare identifier names a composite, a datatype, a constrained type, an opaque type, or a type
alias. Generic types are applied with angle brackets:

```laurel
datatype Option<T> {
  Nothing(),
  Some(value: T)
}

composite Box<T> {
  var item: T
}

procedure boxDemo()
  opaque
{
  var b: Box<int> := new Box<int>;
  b#item := 3;
  assert b#item == 3
};
```

Type parameters are first-order: a parameter cannot itself be applied to arguments, so there are
no higher-kinded types. The resolver checks that the base is generic and that the number of
arguments is exact.

Two further declarations name a type without giving it structure. A *type alias* introduces a
second spelling for an existing type, and is expanded early, so it is interchangeable with its
target:

```laurel
type Ints = Map<int, int>
```

An *opaque type* introduces a named type with no constructors: its values can be passed, stored,
and compared, but not taken apart. The operations come from procedures declared over it. This is
how `Set` and `Sequence` themselves are declared, and it is the right tool for modelling a
source-language type whose representation should stay hidden:

```laurel
opaque Handle
```

### Subtyping and gradual typing

Composite inheritance defines nominal subtyping, so that `Cat` below is a subtype of `Animal`:

```laurel
composite Animal {}
composite Cat extends Animal {}
```

A constrained type unfolds to its base type for subtyping purposes. There are no implicit
numeric promotions of any kind: keep the operands of an arithmetic operator at a single concrete
type.

Subtyping does *not* yet extend through a generic type's arguments. Generic types are invariant,
so a `Sequence<Circle>` is not accepted where a `Sequence<Shape>` is expected even when `Circle`
extends `Shape`, and the same applies to a `Map`, a `Set`, and a generic composite or datatype —
both as a call argument and as a field. Variance is intended and not yet supported, so a front end
for a language with covariant collections has to erase to a common element type, or convert
element by element, for now.

Alongside these, resolution has an internal `Unknown` type. It is what an unannotated hole gets,
and what a failed rule substitutes so that one error does not cascade. `Unknown` is *consistent*
with every type, which is what makes it a gradual escape hatch, but it is not writable as a
source type, and a program that still contains one cannot be analysed. Its rules are in
{ref "rules-holes"}[*Holes*] and *Gradual typing* above.

## Algebraic datatypes

A `datatype` declares a value built from a fixed set of constructors. Laurel generates a
constructor, a tester, and one selector per field:

:::table +header
 *
   * Source declaration
   * Generated operation
 *
   * `Some(value: T)`
   * constructor `Some(v)`
 *
   * `Some(...)`
   * tester `Option..isSome(x)`
 *
   * field `value`
   * checked selector `Option..value(x)`
 *
   * field `value`
   * unchecked selector `Option..value!(x)`
:::

The checked selector carries a precondition that the value really was built with a constructor
containing that field, so reading it is a proof obligation. The unchecked `!` variant skips that
obligation; use the checked one unless the constructor is already established.

```laurel
datatype Option<T> {
  Nothing(),
  Some(value: T)
}

procedure unwrapOr(o: Option<int>, fallback: int): int
{
  return if Option..isSome(o)
    then Option..value(o)
    else fallback
};
```

Datatypes have *structural* equality — two values are equal when they have the same constructor
and equal arguments — which is what distinguishes them from composites. Recursive and mutually
recursive datatypes are supported.

Two naming rules are easy to trip over. Constructor names are program-global, so they must not
collide across datatypes. And field names must be unique across all constructors of one
datatype, because every field generates one datatype-wide selector `<Datatype>..<field>`: a
declaration `Left(value: T), Right(value: T)` is rejected, because both fields would define
`Datatype..value`. Use distinct names such as `leftValue` and `rightValue`.

Laurel has no pattern-matching syntax. Testers and selectors, combined with `if`, are how a
datatype is taken apart.

## Statements are expressions

Laurel has one syntactic category for statements and expressions. In practice:

- a block evaluates its items left to right;
- every item but the last is evaluated for its effect and its value discarded;
- the block's value is the value of its last item;
- an assignment evaluates to the assigned value;
- an `if` with an `else` can produce a value; without one, the missing branch produces nothing,
  so the form is only usable where its value is discarded.

```laurel
procedure example(flag: bool): int
{
  var x: int := 0;
  return {
    x := 10;
    if flag
      then { x := x + 1; x }
      else { x := x + 2; x }
  }
};
```

The nested block evaluates to `11` or `12`.

A local declaration is lexically scoped to its block and does not escape it. A declaration
without an initializer introduces an *arbitrary* value of its type — not a null, and not an
"unbound" marker, so a front end for a language with unbound locals must encode that state
separately.

```laurel
procedure declarations()
  opaque
{
  var x: int;        // arbitrary int
  var y: int := 4;   // exactly 4
  assert y == 4
};
```

One current restriction is worth knowing: a block used *as a value* should not contain a
non-final loop, `return`, or `exit`. Keep control-flow constructs in blocks that are used in
statement position.

### Evaluation order

Because an operand may itself assign or call, the order operands run in is observable, so it is
fixed: evaluation is *left to right* everywhere. That covers the items of a block and the
arguments of a call — if one argument mutates state that a later one reads, the later one sees the
mutation, and an earlier one does not.

Three constructs deliberately do not evaluate all of their operands:

- `&&` and `||` evaluate their right operand only when the left one does not already decide the
  result, and `a ==> b` evaluates `b` only when `a` holds;
- `if` evaluates only the branch it takes.

That is the whole of it — there is no other laziness, and nothing is reordered or evaluated more
than once, with one exception: an update operator applied to a *field* evaluates the receiver
twice, so keep the receiver side-effect-free (see
{ref "assignment-and-update-operators"}[*Assignment and update operators*]).

The eager `&` and `|` exist precisely so that the choice is yours: they evaluate both operands
whatever the left one says. Where the operands are pure the two spellings agree, and the
short-circuiting pair is the one to reach for when the right operand may fail an obligation —
`x != 0 && 10 / x > 1` is well-formed, while `x != 0 & 10 / x > 1` is not.

## Assignment and update operators
%%%
tag := "assignment-and-update-operators"
%%%

Assignment targets a local or a field. A multi-assignment unpacks a call with several outputs;
its right-hand side must be such a call, and its targets are positional. A target introduced
with `var` declares a new local, and a bare target updates an existing one.

```laurel
procedure triple() returns (a: int, b: int, c: int)
  opaque
{
  a := 1; b := 2; c := 3
};

composite Holder { var field: int }

procedure assignments()
  opaque
{
  var x: int := 3;
  var obj: Holder := new Holder;
  obj#field := 4;
  assign var p: int, x, var r: int := triple();
  assert p == 1
};
```

The Java-style increment and compound-assignment forms are also available. The prefix forms
yield the new value and the postfix forms the old one:

```laurel
procedure updateOperators()
  opaque
{
  var x: int := 0;
  ++x;
  x++;
  --x;
  x--;
  x += 2;
  var s: string := "pre";
  s ^= "suffix";
  assert x == 2
};
```

Each compound form means what it looks like: `x op= y` is `x := x op y`. Increment and decrement
are currently restricted to `int` and to constrained types over `int`. Both families accept a
field lvalue, but an update operator on a field duplicates the receiver expression, so keep the
receiver side-effect-free — bind it to a local first if it is not.

## Operators

### Arithmetic

`+`, `-`, `*`, unary `-`, `/`, `%`, `/t`, and `%t` operate on numeric values, and both operands
must have the same numeric type. For integers there are two division/remainder pairs, and the
difference only shows up on negative operands:

- `/` and `%` are Euclidean: the remainder is never negative;
- `/t` truncates the quotient toward zero, and `%t` is `a - b * (a /t b)`.

```laurel
procedure divisionFacts()
  opaque
{
  assert -7 / 3 == -3;
  assert -7 % 3 == 2;
  assert -7 /t 3 == -2;
  assert -7 %t 3 == -1
};
```

All four forms generate a nonzero-divisor proof obligation, so a possible division by zero shows
up as a failed precondition at the offending operator rather than as undefined behaviour. There
is no source syntax for skipping that check.

Operators are not a separate kind of expression: each is a call to an overloaded built-in
procedure, which is why operand admissibility is overload selection and why `/` can carry a
precondition at all. That mechanism is described under {ref "rules-primitive-operations"}[*Operators*].

### Boolean operators

```laurel
procedure booleans(a: bool, b: bool)
  opaque
{
  assert (a & b) == (b & a);      // eager: both sides evaluated
  assert (a | b) == (b | a);      // eager
  assert (a && b) == (b && a);    // b evaluated only when a is true
  assert (a || b) == (b || a);    // b evaluated only when a is false
  assert (a ==> b) == (!a || b);  // b evaluated only when a is true
  assert !(!a) == a
};
```

The eager and short-circuiting pairs differ only when the right-hand side has an effect, which in
Laurel it may: operands can contain assignments and calls. The short-circuit forms mean exactly
what the corresponding conditional means — `a && b` is `if a then b else false`, `a || b` is
`if a then true else b`, and `a ==> b` is `if a then b else true`.

One caveat: if the right-hand side contains an `assert` or `assume` and nothing else effectful,
write the conditional explicitly rather than relying on the short-circuit form, because the proof
statement can currently escape its guard.

### Equality, ordering, and strings

```laurel
procedure comparisons(x: int, y: int, l: string, r: string)
  opaque
{
  assert (x == y) == !(x != y);
  assert (x < y) ==> (x <= y);
  assert (x > y) ==> (x >= y);
  assert (l ^ r) == (l ^ r)
};
```

Equality requires operands of consistent types and is available at every type. Ordering requires
numeric operands. `^` concatenates two strings.

Equality means different things at different types, and the difference matters: on a datatype it
is structural, and on a composite it is reference identity. See
{ref "aliasing-and-separation"}[*Aliasing and separation*].

## Conditionals

An `if` is usable both as a statement and as an expression:

```laurel
procedure conditionals(x: int) returns (y: int)
  opaque
{
  if x > 0
  then {
    y := 1
  }
  else {
    y := 2
  };
  var sign: int :=
    if x > 0 then 1 else if x == 0 then 0 else -1;
  y := y + sign
};
```

With an `else`, both branches must agree with the expected type, or synthesize compatible types.
Without one, the `if` produces nothing and can only be used where its value is discarded.
Because `if` binds loosely, parenthesise it when it is an operand: `(if c then 1 else 2) == y`.

## Loops and labelled exits

### While

```laurel
procedure whileLoop(n: int) returns (i: int)
  opaque
  ensures i >= 0
{
  i := 0;
  while (i < n)
    invariant 0 <= i
  {
    i := i + 1
  }
};
```

Invariants are optional as far as the grammar is concerned; they are what verification needs, and
are covered under {ref "loop-invariants"}[*Loop invariants*].

Keep the loop condition pure. An effectful condition is currently evaluated once before the loop
rather than at every iteration, so hoist the effect yourself and update a plain variable in the
body.

### For

```laurel
procedure forLoop(n: int) returns (sum: int)
  opaque
{
  sum := 0;
  for (var i: int := 0; i < n; i := i + 1)
    invariant 0 <= i
  {
    sum := sum + i
  }
};
```

A `for` is desugared immediately into its initializer followed by a `while` whose body ends with
the step, so everything true of `while` is true of it.

### Do-while

```laurel
procedure doWhileLoop() returns (x: int)
  opaque
{
  x := 0;
  do {
    x := x + 1
  } while (x < 3)
    invariant 0 <= x
};
```

The body runs at least once. Invariants are still checked at the loop head, including before the
first execution of the body.

### Labels and exits

A block may carry a label, and `exit` jumps to the end of the enclosing block with that label.
The label must be in lexical scope.

```laurel
procedure labelledExit(done: bool) returns (x: int)
  opaque
{
  x := 1;
  {
    if done then { exit finished };
    x := 2
  } finished
};
```

Laurel has no `break` or `continue` keyword: a labelled block plus `exit` is how a front end
builds them — `break` exits a block wrapped around the loop, `continue` exits a block wrapped
around the loop *body*. Code following an unconditional `return` or `exit` in the same block is
reported as dead.

## Procedures, outputs, and calls

A procedure has three output styles. It may have none, one anonymous output, or named outputs:

```laurel
procedure log(x: int) { assert x == x };

procedure addOne(x: int): int
{
  return x + 1
};

procedure quotientAndRemainder(a: int, b: int)
  returns (q: int, r: int)
  requires b != 0
  opaque
  ensures a == q * b + r
{
  q := a / b;
  r := a % b
};
```

The short `: T` form names the output `$result`, which is the one exception to the reserved
leading `$` (see {ref "reserved-names"}[*Reserved names*]): you may write
`returns ($result: T)` explicitly and refer to it in a contract. Prefer `returns (r: T)` with a
name of your own whenever a contract needs the result. `return e` is valid only when
there is exactly one output; a multi-output procedure assigns its named outputs and uses a bare
`return` for an early exit, which leaves the outputs at whatever they were last assigned.

An input and an output that share a name form an *inout* parameter — the standard way to model a
procedure that updates its argument:

```laurel
procedure bump(x: int) returns (x: int)
  opaque
  ensures x == old(x) + 1
{
  x := x + 1
};
```

Top-level procedures may share a name when their parameter signatures do not overlap; resolution
picks the unique overload the argument types accept, and both no match and several matches are
errors. `external` procedures cannot be overloaded.

### Bodiless and external procedures

A procedure may be declared without a body, in which case its contract is all there is. This is
the right way to model an operation whose implementation is outside the program — a boundary
call, or a stub standing in for code not yet translated. Its outputs are arbitrary subject to its
postconditions:

```laurel
procedure boundary(x: int) returns (r: int)
  opaque
  ensures r >= x;
```

`external` is different: it declares an operation supplied by the Core environment itself. The
declaration exists so Laurel can resolve calls to it, and is then dropped, with each call
becoming an application of a Core operator. Use exactly one output.

```laurel
procedure hostPrimitive(x: int): int external;
```

Do not reach for `external` when what you want is an unconstrained value — that is a bodiless
`opaque` procedure. The distinction between a *transparent* procedure, whose body callers may
reason through, and an `opaque` one, whose contract is all callers see, is a verification concern
and is covered under {ref "postconditions"}[*Postconditions*].

## Composites and objects

Laurel models objects with *composite* types. A composite declares fields and may declare
*instance procedures* (methods). Fields are read and written with the `#` selector, instances are
created with `new`, and a method is invoked with the same `#` syntax.

```laurel
composite Counter {
  var count: int
  procedure reset(self: Counter)
    opaque
    ensures self#count == 0
    modifies self
  {
    self#count := 0
  };
}

procedure useCounter()
  opaque
{
  var c: Counter := new Counter;
  c#reset();
  assert c#count == 0
};
```

An instance procedure takes its receiver as an explicit `self` parameter and refers to fields
through it. The contract of a method uses the same `requires` / `ensures` / `modifies` clauses as
any other procedure; here `ensures self#count == 0` is what lets the caller conclude
`c#count == 0` after `c#reset()`.

Field selection and method calls chain, so you can reach through one object to another:
`o#inner#x` reads field `x` of the object stored in `o`'s `inner` field, and `o#inner#isOne()`
calls a method on it.

```laurel
composite Inner { var x: int }
composite Outer { var inner: Inner }

procedure useOuter()
  opaque
{
  var o: Outer := new Outer;
  var v: int := o#inner#x
};
```

Two things about `new` regularly surprise newcomers. It allocates identity but runs no
constructor, so the fields of a fresh object are *unconstrained* until assigned — a freshly
allocated `int` field is an arbitrary integer, not zero. And a variable of composite type holds a
*reference*, so assigning it copies the reference and not the object; that is the subject of
{ref "aliasing-and-separation"}[*Aliasing and separation*].

A field may be declared with or without the `var` marker, which records whether it is mutable.
Only mutable fields are implemented: every field is currently compiled as mutable, so leaving
`var` off records the intent but does not prevent writes, and nothing yet relies on it. Genuinely
immutable fields are planned — they make verification easier, because a value read once stays
valid — along with non-reference composites, which will only be allowed immutable fields. Until
then, do not treat a missing `var` as a guarantee.

### Inheritance and runtime type tests

A composite may extend one or more parents, which gives nominal subtyping and inherits their
fields. `x is T` tests an object's runtime type and `x as T` narrows a reference to a subtype:

```laurel
composite Shape {}
composite Colored {}
composite Circle extends Shape, Colored {}

procedure classify(s: Shape): bool
{
  return s is Circle
};
```

`x as T` behaves like a checked narrowing — it asserts `x is T` and then has static type `T`, so
a cast that cannot be justified is a verification failure rather than a runtime one.

Fields are inherited through the declared parent graph. If the same field name reaches a child
along two different paths, accessing it is rejected as ambiguous unless the child declares its
own field with that name.

### Overriding and dynamic dispatch

When a composite declares a method that an ancestor also declares, it *overrides* it, and a call
through the ancestor's type runs the override that matches the receiver's *runtime* type — the
same semantics Java and C# have. So a parent may declare a method with a contract and no body and
let each child supply the implementation:

```laurel
composite Shape {
  procedure area(self: Shape): int
    opaque
    ensures area >= 0;
}

composite Square extends Shape {
  var side: int
  procedure area(self: Square): int
    opaque
    ensures area >= 0
  {
    return self#side * self#side
  };
}

procedure describe(s: Shape): int
  opaque
{
  return s#area()
};
```

`describe` sees only `Shape`'s contract, and the call dispatches to whichever override the
receiver's runtime type selects. A method that nothing overrides is dispatched statically, so
inheritance-free code pays nothing for this.

What makes it sound is that an override may not weaken the contract callers were promised. Laurel
checks *behavioural subtyping* at the point of declaration: the override may not demand more of
its callers than the parent's precondition did, must deliver at least the parent's postcondition,
and may not widen the parent's `modifies` frame. An override that breaks one of these is reported
against the override itself, not at some call site.

Four shapes are rejected rather than dispatched, each with a diagnostic:

- the methods in a family disagreeing about whether they `throw`;
- an overrider that renames its type parameters instead of reusing the base's names
  (`SBox<T> extends Box<T>` is fine, a renamed one is not);
- an incompatible output signature — a different number of outputs, or a return type that is
  neither the base's nor a subtype of it. A *covariant* return type is accepted;
- an `external` body anywhere in the family, since a dispatch branch needs a real implementation
  to call.

Note that changing the non-`self` parameter types does not produce an override at all: that is an
overload, and the two methods stay independent.

Dispatch is on the runtime type tag, so this is not Python's MRO. A front end whose dispatch rules
differ from single-inheritance-style tag dispatch — Python's method resolution order, or dispatch
on something other than the receiver's type — still has to emit that itself, as explicit control
flow over type tests.

## Holes and nondeterminism

Two literals stand for a value the program does not determine. They differ in whether repeated
evaluation agrees, and choosing the wrong one is a common source of confusion.

A *deterministic* hole `<?>` denotes one unknown-but-fixed value. Each hole site is a function
of the enclosing procedure's inputs, so the same site reached with the same inputs yields the
same value, while two different sites need not agree.

```laurel
procedure unknownScore(x: int): int
{
  return <?>
};
```

This is what a front end should emit when it cannot translate a side-effect-free
sub-expression: the analysis still runs, and the user sees your diagnostic rather than a cascade.
Because a hole stands for a *value*, replacing an effectful expression with one silently drops
the effect and can make an analysis prove something the original program does not satisfy.

A *nondeterministic* hole `<??>` takes a fresh unconstrained value at every evaluation, so
distinct evaluations are independent:

```laurel
procedure nondeterminism()
  opaque
{
  var x: int := <??>;
  var y: int := <??>;
  assert x == y      // not provable: the two are independent
};
```

## Exceptions

Mainstream languages use exceptions to signal that an operation cannot complete
normally, and to transfer control from the point of failure to the code prepared to
handle it. Laurel models this directly: a procedure declares what it may throw with
`throws`, a `throw` statement raises a value, and `try` / `catch` / `finally`
handles it. Modelling exceptions here means each frontend does not have to
re-implement them.

Laurel imposes no root exception type, and does not require a thrown value to belong
to any particular hierarchy — a procedure may declare `throws int` and `throw 3`.
What Laurel provides instead is subtype-aware typing of the `catch` binding, so each
frontend uses its own hierarchy directly: Java's `Throwable`, Python's
`BaseException`, or JavaScript's convention of throwing an `Error`.

What a throwing procedure *promises* its callers — which inputs force a throw, and what may
change on the way out — is a contract, and is covered under
{ref "verification-continued"}[*Verification - Continued*].

### Declaring and throwing

`throws T` in a procedure's signature says the procedure may finish by throwing a
`T`. In the body, `throw e` raises `e` and abandons the rest of the procedure.

```laurel
composite Exception {}
composite ArithmeticException extends Exception {}

procedure div(a: int, b: int) returns (r: int)
  throws (e: Exception)
  opaque
{
  if b == 0 then {
    var ae: ArithmeticException := new ArithmeticException;
    throw ae
  };
  r := a / b
};
```

`throws` is part of the signature — it changes what callers have to deal with — so
it sits with `returns`, before `opaque`.

### Catch or declare

Laurel enforces *catch-or-declare*, the discipline Java applies to its checked
exceptions. A procedure that declares no `throws` may not let an exception escape,
whether thrown directly or propagated from a callee, and a procedure declaring
`throws T` may only let exceptions escape whose type is a subtype of `T`.

```laurel
composite ArithError {}
composite ParseError {}

procedure wrongThrows()
  throws (e: ArithError)
  opaque
{
  var e: ParseError := new ParseError;
  throw e
  // error: procedure 'wrongThrows' may throw 'ParseError', which is not a
  // subtype of its declared `throws` type 'ArithError'
};
```

The check is about the program as you wrote it rather than about how it lowers, so
it runs during resolution and reports at the offending `throw` or call. Whether the
*source* language requires catch-or-declare is a separate question: procedures
coming from Python or JavaScript carry a `throws` clause too, even though neither
language has that surface construct.

### Handling: try, catch, finally

`catch` dispatches on a *predicate* rather than on a type, written
`catch e when <condition on e>`. Type-based dispatch is one such predicate:
`catch e when e is NotFound`. Clauses are ordered and first-match-wins, and a clause
with no `when` guard is a catch-all. `finally` runs on the way out of the `try`.

```laurel
composite Exception {}
composite NotFound extends Exception {}
composite Invalid extends Exception {}

procedure handle(fail: int) returns (r: int)
  opaque
{
  r := 0;
  try {
    if fail == 1 then {
      var e: NotFound := new NotFound;
      throw e
    };
    if fail == 2 then {
      var i: Invalid := new Invalid;
      throw i
    }
  } catch e when e is NotFound {
    r := 1
  } catch e {
    r := 2
  } finally {
    assert r >= 0
  }
};
```

`finally` runs after a normal completion, after a caught exception, on the way out
with an uncaught one, and when a handler itself throws or returns. A `return` or an
`exit` that leaves the `try` runs it too, and nested `finally` arms chain outward.

One rule decides the rest: if the `finally` arm itself completes abruptly — it
returns, throws, or exits — that completion wins, and whatever was pending is
discarded. This is Java's rule (JLS 14.20.2), so `try { throw e } finally { return }`
returns normally and the exception is gone.

### The type of a catch binding

A `catch` binding is typed at the *least common ancestor* of the exception types
that can reach it: the types thrown directly in the `try` body, and the declared
`throws` types of the procedures the body calls. When those share a common ancestor
`T`, the binding has type `T`, and reading a field of `e` needs no downcast.

```laurel
composite Exception {
  var message: string
}
composite NotFound extends Exception {}
composite Invalid extends Exception {}

procedure logFailure(which: int) returns (out: string)
  opaque
{
  out := "";
  try {
    if which == 1 then {
      var f: NotFound := new NotFound;
      f#message := "missing";
      throw f
    };
    var i: Invalid := new Invalid;
    i#message := "invalid";
    throw i
  } catch e {
    // `NotFound` and `Invalid` join at `Exception`, so `e` is an `Exception` and
    // the inherited field is readable without a cast.
    out := e#message
  }
};
```

If the types reaching a `catch` share no common ancestor, Laurel reports an error
rather than leaving the binding untyped. If the body throws nothing determinable,
no exception can reach the clauses, and they are dropped as unreachable.

A frontend that needs to catch values with no useful common ancestor — unrelated
types, or JavaScript's arbitrary thrown values — can *box* them: wrap the value in a
composite field when throwing, and unwrap it in the handler.

### Not yet supported

Two shapes are rejected during resolution with a *not yet supported* diagnostic
rather than lowered, because the alternatives would be an internal error or a silent
miscompile:

- a call to a procedure that `throws` in a nested expression position. Only a whole
  statement or a whole assignment right-hand side is handled, so `s := f()` is fine
  while `s := 1 + f()` is rejected;
- a `catch` handler that re-declares its own exception binding, because the
  substitution that rewrites the binding matches by name and is not scope-aware.

## Coroutines
%%%
tag := "coroutines"
%%%

Laurel models cooperative concurrency with *coroutines*: procedures that can voluntarily
suspend themselves with `yield`, handing control back to their caller, and can later be
resumed with `resume`. This closely matches Python generators and JavaScript coroutines,
where `yield` suspends execution and `next(...)` resumes it.

What a coroutine may assume, and must establish, at each suspension is a contract, and is
covered under {ref "verification-continued"}[*Verification - Continued*].

### Declaring a coroutine

A resumable procedure (or coroutine) is declared with the `coroutine` keyword, and its
body may contain `yield`. Two optional channel clauses declare the values that flow
across a suspension:
`yields (x: T)` is the outgoing channel (the value handed out at a `yield`), and
`resumes (y: U)` is the incoming channel (the value sent back in on the next resume).
To yield a value, assign it to the `yields` binding and then `yield`; `yield` itself
is nullary.

```laurel
coroutine counter(n: int) yields (x: int)
{
  var i: int := 0;
  while (i < n)
  {
    x := i;   // put the value on the outgoing channel
    yield;    // suspend; the caller sees x
    i := i + 1
  }
};
```

### Driving a coroutine: `resume` and `has_next`

A caller spawns a coroutine by calling its name, then advances it one suspension at a
time with `resume`. In expression position, `resume(co)` evaluates to the value the
coroutine just put on its `yields` channel; `resume(co, v)` additionally sends `v` in
on the `resumes` channel. `has_next(co)` reports whether the coroutine has more steps
to run, so a driver loop reads:

```laurel
procedure drive()
  opaque
{
  var co: counter := counter();
  while (has_next(co))
  {
    resume(co)
  }
};
```

### Planned: `async` / `await`

The examples above are supported today. The `async`/`await` surface syntax that source
languages use is planned, and desugars onto the same coroutine primitives: `await g(y)`
drives `g` to completion and takes its result. The Python program

```
# Python
async def fetch_page(cursor):
    await asyncio.sleep(0.1)
    if cursor >= 3:
        return None
    return cursor + 1

async def download_all():
    cursor = 0
    while cursor is not None:
        cursor = await fetch_page(cursor)
```

is intended to be written with coroutine `return` values and `await` as below. This
does not compile yet: a coroutine `return` value and the `await` sugar are planned (see
the Designer Guide's concurrency section). The block is shown to illustrate the
mapping, not as working syntax.

```laurel +unchecked
coroutine fetch_page(cursor: int): int
{
  yield;                          // models `await asyncio.sleep(0.1)`
  if cursor >= 3 then {
    return -1                     // models `return None`
  } else {
    return cursor + 1
  }
};

coroutine download_all(): int
{
  var cursor: int := 0;
  while (cursor >= 0) {
    cursor := await fetch_page(cursor)   // drives fetch_page to completion
  };
  return cursor
};
```

## AST reference

The remaining subsections document the Laurel abstract syntax tree itself, generated from the
implementation. They are the reference for a producer building the AST directly — through the
Lean API or Ion — rather than emitting Laurel text.

## Expressions and Statements

Laurel uses a unified `StmtExpr` type that contains both expression-like and statement-like
constructs. This avoids duplication of shared concepts such as conditionals and variable
declarations.

### Operations

{docstring Strata.Laurel.Operation}

### The StmtExpr Type

{docstring Strata.Laurel.StmtExpr}

## Sources

All AST nodes can carry a source location via the `AstNode` wrapper.

{docstring Strata.Laurel.AstNode}

## Procedures

Procedures are the main unit of specification and verification in Laurel.

{docstring Strata.Laurel.Procedure}

{docstring Strata.Laurel.Parameter}

{docstring Strata.Laurel.Body}

## Programs

A Laurel program consists of procedures, global variables, type definitions, and constants.

{docstring Strata.Laurel.Program}

### File-scope globals

A program-level `var counter: int` defines shared mutable state. Laurel lowers
direct and transitive global effects to hidden parameters in declaration order;
initial values come from the caller or runtime.

*Supported:* reads and writes in procedure bodies (including instance and
transitive calls), current global values in contracts, and multiple globals
alongside heap state.

*Not yet supported* (reported with source diagnostics):
- Global-dependent `old(...)` expressions.
- Globals in entry procedures, constants, or constrained-type predicates and witnesses.
- Explicit inout/global interactions and global-writing `invokeOn` procedures.
- Writes in restricted expressions, ambiguous bodiless postconditions, and
  unsupported multi-output call shapes.

A leading `$` is reserved for compiler-generated names; see
{ref "reserved-names"}[*Reserved names*].

# Verification - Fundamentals
%%%
tag := "verification-fundamentals"
%%%

A verification feature may be erased or approximated when a program is run concretely: `assume`
is a no-op in the interpreter, and a contract on a bodiless procedure has no runtime meaning at
all. Its behaviour under verification is therefore the behaviour that matters.

This section covers the features that do not involve the heap, which are enough to specify code
over plain values.

## Assertions

An `assert` states a fact that Laurel must prove holds at that point in the
program. If the solver cannot prove it, verification fails and the failing
`assert` is reported.

```laurel
procedure checkPositive(x: int)
  requires x > 0
  opaque
{
  assert x > 0;
  assert x >= 1
};
```

The dual of `assert` is `assume`. An `assume` introduces a fact without proof:
from that point on, Laurel reasons as if the assumed expression is true. Assuming
something false makes everything afterwards trivially provable, which is
occasionally useful but should be used with care.

```laurel
procedure assumeThenProve()
  opaque
{
  assume false;
  assert false  // provable: we assumed a contradiction
};
```

Assertions are the building block behind every other verification feature in
this guide. Preconditions, postconditions, and loop invariants are all
ultimately checked by turning them into assertions at the right program points.

## Erased code

To be designed..

## Loop invariants
%%%
tag := "loop-invariants"
%%%

Laurel cannot know in advance how many times a loop runs, so it reasons about
loops through a *loop invariant*: a condition that holds every time the loop
guard is evaluated — on first entry and after each execution of the body.

A loop invariant serves two purposes. Inside the loop it tells Laurel what is
true, which is what lets it prove that operations in the body are safe. After the
loop it combines with the negated guard to describe the state on exit.

```laurel
procedure countUp()
  opaque
{
  var n: int := 5;
  var i: int := 0;
  while (i < n)
    invariant i >= 0
    invariant i <= n
  {
    i := i + 1
  };
  assert i == n
};
```

The two invariants together establish `i == n` after the loop: the loop exits
when `i < n` is false, so `i >= n`, and the second invariant gives `i <= n`.

A loop invariant must hold *on entry* and be *preserved* by the body. If it fails
on entry, Laurel reports the error at the offending invariant. For example,
initializing `i` to `-1` above would break `invariant i >= 0` before the loop
even starts, and that specific invariant is flagged.

## Preconditions

A *precondition*, written with `requires`, states what must be true when a
procedure is called. It has two effects. It restricts callers: every call site
must prove the precondition holds for the arguments it passes. And it gives the
body an assumption to work from when proving its own obligations.

```laurel
procedure halve(x: int) returns (r: int)
  requires x > 0
  opaque
  ensures r >= 0
{
  r := x / 2
};

procedure caller()
  opaque
{
  var a: int := halve(10);   // ok: 10 > 0
  var b: int := halve(0)     // error: precondition does not hold
};
```

A procedure may have several `requires` clauses; they are conjoined. A call must
satisfy all of them.

```laurel
procedure addBoth(x: int, y: int) returns (r: int)
  requires x > 0
  requires y > 0
  opaque
  ensures r > 0
{
  r := x + y
};
```

A clause is itself checked, and the order of the clauses matters when it is. That is the
subject of {ref "contract-well-formedness"}[*Contract well-formedness*] below.

## Postconditions
%%%
tag := "postconditions"
%%%

A postcondition for a procedure is a condition that is guaranteed to hold after the procedure
executes. Sometimes, we can capture the entire desired behavior of a procedure with a postcondition
that is simpler than the procedure's implementation. A typical example of sorting a list of numbers:
the end result, that the list is sorted, is simpler to describe than the algorithm to do the
sorting.

When a postcondition can capture the entire desired behavior of a procedure, and is simpler than the
body, then adding it allows improving the correctness guarantee of your program, since only the
simpler postcondition needs to be reviewed for correctness. Also, when postconditions are added to a
procedure, callers will only be able to use the postconditions to reason about the call, and not the
body. This simplifies reasoning at the call-site, improving verification results.

In Laurel, to be explicit, a procedure with postconditions must be marked as `opaque`, indicating
that its body is not visible to callers. A procedure without postconditions can also be marked
`opaque`, although then callers will know nothing about the result of the call. By default Laurel
procedures have a transparent body, meaning that callers can use the callee's body for reasoning
about the call's result.

```laurel
procedure max(x: int, y: int) returns (r: int)
  opaque
  ensures r >= x
  ensures r >= y
  ensures r == x || r == y
{
  if x > y then { r := x }
  else { r := y }
};
```

At a call site, the postcondition is all the caller knows about the result:

```laurel
procedure useMax()
  opaque
{
  var m: int := max(3, 7);
  assert m >= 3;
  assert m >= 7
  // we cannot assert m == 7 here: the contract only promises r >= x, r >= y,
  // and r == x || r == y, which does not pin m to 7.
};
```

Postconditions and preconditions work together. It is common to need a
precondition in order to be able to prove a postcondition, and adding that
precondition simultaneously rules out the calls for which the procedure would not
behave as specified.

## Contract modes: `free` and `checked`

Every plain contract clause has two sides: it is *asserted* at one end and *assumed* at the
other. A `requires` is proved by the caller and assumed by the body; an `ensures` is proved by the
body and assumed by the caller. The `free` and `checked` modifiers keep only one of those sides.

:::table +header
 *
   * Clause
   * Asserted
   * Assumed
 *
   * `requires P`
   * yes, at every call site
   * yes, in the body
 *
   * `free requires P`
   * no
   * yes, in the body
 *
   * `checked requires P`
   * yes, at every call site
   * no
 *
   * `ensures P`
   * yes, at every exit of the body
   * yes, after every call
 *
   * `free ensures P`
   * no
   * yes, after every call
 *
   * `checked ensures P`
   * yes, at every exit of the body
   * no
:::

So `free` is *trusted* information: it is believed without proof, and it is the right tool for an
assumption that comes from outside the program — a fact about a boundary the analysis cannot see.
Because nothing checks it, a wrong `free` clause can make the analysis prove things the program
does not satisfy; treat each one as an axiom you are adding.

`checked` is the opposite: the property is proved but deliberately not handed to the other side.
It is useful for a property you want enforced without letting callers depend on it, so that it
stays free to change.

```laurel
procedure boundaryRead(handle: int) returns (r: int)
  free requires handle > 0
  opaque
  ensures r >= 0
  checked ensures r != 42;
```

## Contract well-formedness
%%%
tag := "contract-well-formedness"
%%%

An assertion inside a contract must be proven, and that includes the *implicit* assertions — the
ones you did not write, such as the precondition of a call the clause makes. A contract clause is
an expression, so it carries the obligations of every operation it names, exactly as the same
expression would in a procedure body.

Two kinds of obligation come up. A *partial* operation raises the one it always raises: division
needs a nonzero divisor, a sequence index needs to be in bounds. And a *call* must satisfy the
callee's preconditions.

The clause's mode does not change any of this. `free` and `checked` choose where the clause's own
condition is asserted and assumed; neither suppresses the obligations of the expression that
states it. A failure is reported at the clause, and the procedure whose contract it is must
discharge it — not the caller.

### Order matters

A clause may rely on the clauses written before it to discharge its obligations, so where a guard
sits decides whether the clause that needs it is well-formed. Division requires a nonzero divisor,
so the second clause below is fine only because the first has already ruled out `x == 0`:

```laurel
procedure scaleDown(x: int) returns (r: int)
  requires x != 0
  requires 10 / x > 1
  opaque
{
  r := x
};
```

Written the other way round, the division comes before anything constrains `x`, so the divisor may
be zero and Laurel reports `precondition does not hold` on `10 / x`:

```laurel
procedure scaleDownBadOrder(x: int) returns (r: int)
  requires 10 / x > 1
  requires x != 0
  opaque
{
  r := x
};
```

An `ensures` may additionally rely on the procedure's preconditions, whatever their mode. Since
the `requires` clauses are conjoined, order changes nothing about what a *caller* must prove; it
changes only which facts are in scope while Laurel checks a clause's own obligations.

### A call in a clause

The same rule covers a call, whose precondition has to be established at the clause just as it
would at any other call site. Here the procedure's own `requires` is what discharges it:

```laurel
procedure needsBig(x: int) returns (s: int)
  requires x > 100
  opaque
  ensures s == x + 1
{
  s := x + 1
};

procedure callsItSafely(x: int) returns (r: int)
  requires x > 100
  opaque
  free ensures r == needsBig(x)
{
  r := x + 1
};
```

Drop that `requires` and the call is no longer justified, so the clause fails even though it is
`free` — the mode waives proving the *condition*, not the obligations inside it:

```laurel
procedure needsBigAgain(x: int) returns (s: int)
  requires x > 100
  opaque
  ensures s == x + 1
{
  s := x + 1
};

procedure callsItUnsafely(x: int) returns (r: int)
  opaque
  free ensures r == needsBigAgain(x)
{
  r := x + 1
};
```

## Naming a failure with `summary`

An `assert`, a `requires`, or an `ensures` may carry `summary "..."`, which is attached to the
diagnostic reported when that obligation fails. It is the difference between a failure that
identifies itself and one the reader has to decode from a line number, so it is worth writing on
any clause a front end generates on a user's behalf — the summary can name the *source-language*
reason rather than the Laurel one.

```laurel
procedure indexed(xs: Sequence<int>, i: int): int
  requires 0 <= i summary "index must not be negative"
  requires i < seqLength(xs) summary "index must be within bounds"
{
  return seqSelect(xs, i)
};
```

## Quantifier

For specifications that range over many values, Laurel provides *quantifiers*.
A `forall` states that its body holds for every value of the bound variables; an
`exists` states that there is at least one value for which the body holds. Both
take one or more typed binders and a body introduced with `=>`.

```laurel
procedure quantifiers()
  opaque
{
  assert forall(x: int) => x + 0 == x;
  assert exists(x: int) => x == 42
};
```

The implication operator `==>` is frequently used inside quantifiers to restrict
the range of interest — for instance, to say something about every index of an
array within bounds:

```laurel
procedure inContract(n: int)
  requires n > 0
  opaque
  ensures forall(i: int) => i >= 0 ==> i < n ==> i < n + 1
{
};
```

Because a `forall` over an infinite domain (such as all integers) cannot be
checked by enumeration, the solver reasons about it logically. To control how it
instantiates a quantifier, you can attach a *trigger* — a pattern in braces that
tells the solver which terms should cause the quantified fact to fire:

```laurel
procedure P(x: int): int;
procedure withTrigger()
  opaque
{
  assume forall(i: int) { P(i) } => P(i) == i + 1;
  assert P(1) == 2   // the term P(1) matches the trigger, so the fact fires
};
```

Use a trigger only when you know which instantiation pattern you want. A trigger that is too
narrow makes the fact fire too rarely and the goal unprovable; one that is too broad makes it fire
constantly and the query slow. When in doubt, leave it off and let the solver choose.

## Lemmas with `invokeOn`

Sometimes the fact you need is not a property of one call but a general rule: for every input,
this holds. `invokeOn` turns a procedure's postconditions into a universally quantified fact over
its inputs, using the given expression as the trigger. It declares a *lemma*, not something that
runs.

```laurel
procedure P(x: int): bool;

procedure pLemma(x: int)
  invokeOn P(x)
  opaque
  ensures P(x) ==> x >= 0;
```

That declares, once and for all, that `P(x) ==> x >= 0` for every `x`, and arranges for the fact
to fire whenever the term `P(x)` appears. Nothing calls `pLemma`.

An `invokeOn` procedure may not declare outputs, because an output would be unbound in the
resulting quantified fact.

## Termination checking

To be designed..

## Constrained types

A *constrained type* (a refinement type) is a base type narrowed by a
predicate. It is introduced with the `constrained` keyword and has four parts: a
name, a value binder together with its base type, a `where` predicate that
values of the type must satisfy, and a `witness` value that proves the type is
inhabited.

```laurel
constrained nat = x: int where x >= 0 witness 0
```

This declares `nat` as the integers that are at least zero. The binder `x`
ranges over the base type `int`, `x >= 0` is the constraint, and `0` is the
witness — a concrete value Laurel checks against the predicate to be sure the
type is not empty. A witness that fails its own predicate is rejected:

```laurel
constrained bad = x: int where x > 0 witness -1
// error: the witness -1 does not satisfy x > 0
```

A constrained type is checked at every point where a value *acquires* the type,
and it is available as an assumption at every point where a value is *known* to
have the type. The rest of this section walks through those points.

### Inputs

A parameter of constrained type contributes a precondition. Callers must prove
the argument satisfies the constraint, and in exchange the body may assume it.

```laurel
constrained nat = x: int where x >= 0 witness 0

procedure inputAssumed(n: nat)
  opaque
{
  assert n >= 0   // holds: the nat constraint is assumed for inputs
};
```

Passing an argument that cannot be shown to satisfy the constraint fails at the
call site, exactly like any other {ref "rules-verification-statements"}[precondition].

### Outputs

An output of constrained type contributes a postcondition. The procedure must
establish the constraint on its result, and callers may then assume it.

```laurel
constrained nat = x: int where x >= 0 witness 0

procedure outputValid() returns (r: nat)
  opaque
{
  r := 3          // ok: 3 satisfies x >= 0
};
```

Returning a value that violates the constraint fails as a postcondition:

```laurel
constrained nat = x: int where x >= 0 witness 0

procedure outputInvalid() returns (r: nat)
  opaque
{
  r := -1         // error: postcondition does not hold (-1 is not a nat)
};
```

Because the constraint travels with the output, a caller of an `opaque`
procedure learns it from the contract alone, without seeing the body:

```laurel
constrained nat = x: int where x >= 0 witness 0

procedure opaqueNat() returns (r: nat)
  opaque;

procedure callerAssumes()
  opaque
{
  var v: int := opaqueNat();
  assert v >= 0   // holds: opaqueNat's result is a nat
};
```

### Local variables

Initializing or assigning to a constrained-typed local asserts the constraint
on the assigned value. Both the initial value and every later reassignment are
checked.

```laurel
constrained nat = x: int where x >= 0 witness 0

procedure assignLocal()
  opaque
{
  var y: nat := 5;   // ok
  y := -1            // error: assignment violates the nat constraint
};
```

A constrained-typed local that is *declared without an initializer* is treated
as an arbitrary value that satisfies the constraint: the constraint is assumed,
but nothing more. In particular you cannot assume it holds the witness value.

```laurel
constrained nat = x: int where x >= 0 witness 0

procedure uninitialized()
  opaque
{
  var y: nat;
  assert y >= 0   // holds: the constraint is assumed
};
```

### Quantifiers

When a quantifier binds a variable of constrained type, the constraint is
injected into the body so the bound variable ranges only over values of the
type. For `forall` the constraint becomes an antecedent; for `exists` it becomes
a conjunct.

```laurel
constrained nat = x: int where x >= 0 witness 0

procedure quantifiedNat()
  opaque
{
  // provable only because n >= 0 is injected: false over all integers
  assert forall(n: nat) => n + 1 > 0;
  // 42 witnesses the existential and satisfies n >= 0
  assert exists(n: nat) => n == 42
};
```

### Nested constrained types

A constrained type may refine another constrained type. The constraints then
compose: a value of the inner type must satisfy its own predicate *and* every
predicate up the chain.

```laurel
constrained even = x: int where x % 2 == 0 witness 0
constrained evenpos = x: even where x > 0 witness 2

procedure nested(x: evenpos)
  opaque
{
  assert x > 0;      // evenpos's own constraint
  assert x % 2 == 0  // inherited from even
};
```

Because algebraic datatypes can be encoded as constrained types over a base
type, this composition is what lets a value carry several layers of invariant at
once.

# Verification - Objects
%%%
tag := "verification-objects"
%%%

## Modifies clauses

As previously mentioned, Laurel procedures have a transparent body by default, so callers can reason
about the callee's body. This works also when the callee mutates the heap in its body. However, when
we make a heap-mutating procedure `opaque`, and the body is no longer available for reasoning, then
the caller must accept the possibility that the entire heap was mutated, meaning that nothing can be
proven about the heap any more. This is sound but imprecise, and it makes reasoning about callers of
such procedures difficult. To enable heap reasoning after calling opaque heap-mutating procedures,
Laurel has modifies clauses.

A modifies clause specifies the heap references that may have been modified by the procedure.
Example:

```laurel
composite Container {
  var value: int
}

procedure bump(c: Container)
  opaque
  modifies c
{
  c#value := c#value + 1
};

procedure caller()
  opaque
{
  var a: Container := new Container;
  var b: Container := new Container;
  var x: int := a#value;
  var y: int := b#value;
  bump(b);
  assert x == a#value;  // holds: only b is in bump's modifies clause
  assert y == b#value   // fails: b is in bump's modifies clause
};
```

An opaque procedure that writes to an object it has not listed in the modifies clause is rejected,
also when this write is done through another procedure call. You can list several references by
repeating the clause (`modifies c; modifies d`), and the wildcard `modifies *` permits modifying any
object — at the cost of telling callers that nothing on the heap is preserved.

Objects allocated with `new` *inside* the procedure body are exempt: a freshly
allocated object may be modified freely without appearing in the `modifies`
clause, because no caller could hold any prior knowledge about it.

```laurel
composite Container { var value: int }

procedure makeOne()
  opaque
{
  var c: Container := new Container;
  c#value := 1   // allowed: c is freshly allocated here
};
```

A `modifies` clause frames the *normal* return only. A procedure that can also finish
by throwing frames that exit separately, with a `throwsOn` case's `modifies` — see
{ref "verification-continued"}[*Verification - Continued*].

### Frame granularity

A frame entry may name a whole object or a single field, and several entries may be given in one
clause, separated by commas:

:::table +header
 *
   * Form
   * Meaning
 *
   * `modifies o`
   * any field of the object `o` may change
 *
   * `modifies o#f`
   * only the `f` field of `o` may change
 *
   * `modifies first, second#field`
   * several entries in one clause
 *
   * `modifies *`
   * no frame restriction at all
:::

Naming the field rather than the object is the more informative choice when a procedure only
touches one field, because a caller then keeps its knowledge about the object's other fields.

An entry must denote a composite reference or a composite field. A primitive entry — `modifies x`
where `x: int` — is an error: an `int` parameter is passed by value, so there is no heap location
for the frame to name. Use an inout parameter instead.

An implemented procedure must *honour* its frame — writing outside it is rejected, including
through a further call — while a bodiless one merely *declares* it, and callers rely on the
declaration.

## Aliasing and separation
%%%
tag := "aliasing-and-separation"
%%%

A variable of composite type holds a *reference*, not an inline copy of the object's fields.
Assigning one such variable to another therefore copies the reference, and both names then denote
the same object:

```laurel
composite Cell {
  var value: int
}

procedure aliasDemo()
  opaque
{
  var x: Cell := new Cell;
  x#value := 0;
  var y: Cell := x;

  assert x == y;
  y#value := 7;
  assert x#value == 7;

  var z: Cell := new Cell;
  assert z != x
};
```

The write through `y` is visible through `x` because both refer to the same object. Note what `==`
means here: on a composite it is *reference identity*, not field-by-field comparison. Two
separately allocated objects with identical fields are not equal, and two `new` expressions always
produce distinct references. (On a datatype, by contrast, equality is structural.)

A field that stores a composite likewise stores a reference. Reading the field copies the current
reference out; assigning a new reference to the field changes the object's field, and does *not*
retarget a local that read the old value earlier:

```laurel
composite Child { var n: int }
composite Owner { var child: Child }

procedure fieldReferences(owner: Owner, replacement: Child)
  opaque
  modifies owner#child
{
  var saved: Child := owner#child;
  owner#child := replacement;
  assert owner#child == replacement
  // `saved` still denotes the original child
};
```

### Separation is shallow

This is the point that most often causes a proof to fail unexpectedly. Reference inequality is
only *root* separation: from `left != right` Laurel does not conclude anything about the objects
reachable from their fields. Two distinct objects may perfectly well share a child, and the
following two facts are consistent:

```laurel +unchecked
requires left != right
requires left#next == right#next
```

Frame clauses are identity-based in the same shallow way. `modifies x` permits every field of the
object identified by `x`; it does not permit mutating an object stored *in* one of those fields. A
reachable child has to be named separately. And because frames name objects by identity, aliasing
interacts with them the way you would hope: if `x == y`, a write through `y` is a write to the
object named by `x`, so naming `x` in the frame suffices.

```laurel
composite Cell2 { var value: int }

procedure writeAlias(x: Cell2, y: Cell2)
  requires x == y
  opaque
  modifies x#value
{
  y#value := 1
};
```

Laurel has no native separation logic: there is no separating conjunction, no ownership or
permission system, no heaplets, no built-in reachability relation, and no automatic footprint
computation. Deep separation has to be stated as an ordinary first-order property. If a front end
supplies maps representing two object footprints, disjointness takes this shape:

```laurel +unchecked
forall(r: Node) =>
  !(mapContains(leftFootprint, r) && mapContains(rightFootprint, r))
```

The front end must also supply the contracts or axioms that connect those maps to the fields they
are meant to describe. A finite, fixed object shape can use an explicitly enumerated footprint; a
recursive structure needs a generated inductive summary, an axiomatised reachability relation, a
bounded approximation, or a proof strategy that avoids materialising reachability at all.

### Encoding an analysis's alias facts

A front end that has alias information from its own analysis should map it onto Laurel
constraints rather than onto source-language equality — in particular, do not use the source
language's `==` to state identity unless that operator *is* object identity. For a source type
modelled as a datatype over composite variants, write an identity helper that reaches through the
variants and compares the underlying references.

:::table +header
 *
   * Abstract alias fact
   * Laurel constraint
 *
   * must alias
   * `sameRef(x, y)`
 *
   * definitely separate
   * `!sameRef(x, y)`
 *
   * may alias
   * no constraint either way
 *
   * points-to allocation site
   * a separate tag or set-membership constraint, not identity
:::

A may-alias edge records *uncertainty*, so it must not be turned into an equality; conversely, the
*absence* of a may-alias edge justifies `!sameRef(x, y)` only if the analysis defines absence as
proved non-aliasing. Allocation-site tags are abstractions, not identities: two objects allocated
by different iterations of the same loop share a site tag while having different references.

## Reads clauses

To be designed..

Reads clauses can only be specified for deterministic procedures

## Old

In a postcondition you often want to relate the state when the procedure returns
to the state when it was entered. Wrapping an expression in `old(...)` evaluates
that expression in the *pre-state* — the heap as it was on entry. This is the
standard way to specify a procedure that mutates its arguments.

```laurel
composite Cell {
  var value: int
}

procedure bumpCell(c: Cell)
  opaque
  ensures c#value == old(c#value) + 1
  modifies c
{
  c#value := c#value + 1
};
```

Here `c#value` denotes the value on return and `old(c#value)` the value on entry,
so the postcondition says the field grew by exactly one. Without `old`, the
clause would read `c#value == c#value + 1`, which no implementation can satisfy.

`old` distributes through the structure of an expression, so you can wrap a whole
sub-expression: `old(2 * c#value + 3)` means the same as `2 * old(c#value) + 3`.
It may also appear inside quantifiers and conditionals in a postcondition:

```laurel
composite Cell { var value: int }

procedure strictBump(c: Cell)
  opaque
  ensures forall(other: Cell) => other == c ==> other#value > old(other#value)
  modifies c
{
  c#value := c#value + 1
};
```

A caller can reproduce the two-state reasoning by snapshotting the pre-state into
a local variable before the call and asserting against it afterwards:

```laurel
program Laurel;
composite Cell { var value: int }

procedure bumpCell(c: Cell)
  opaque
  ensures c#value == old(c#value) + 1
  modifies c
{
  c#value := c#value + 1
};

procedure bumpCellCaller()
  opaque
{
  var c: Cell := new Cell;
  var pre: int := c#value;
  bumpCell(c);
  assert c#value == pre + 1
};
```

An `old(...)` that mentions nothing from the heap has no effect and Laurel warns
about it, since it cannot relate two states. The same warning is issued for a
redundant `old(old(...))`, whose inner `old` is dropped.

## Allocated and fresh

`fresh(e)` is a predicate that holds when the reference `e` was newly allocated by the current
procedure — it did not exist in the heap on entry. It is the standard way to tell a caller that a
returned reference cannot alias any object that already existed, which is what rules out aliasing
between the result and the caller's pre-existing objects.

```laurel
composite Node { var next: Node }

procedure allocate() returns (r: Node)
  opaque
  ensures fresh(r)
{
  r := new Node
};
```

`fresh(e)` may only target reference (composite) types. Its planned dual, `allocated(e)` — asserting
that a reference already existed in the current state — has not been implemented yet. See the
Aliasing helpers section of the Laurel Design Guide for the underlying model of allocation and how
these two notions relate.

## Immutable fields

To be designed..

## Type invariants

To be designed..

# Verification - Continued
%%%
tag := "verification-continued"
%%%

The two remaining specification features each attach a contract to something other than a
procedure's normal return: an exceptional exit, and a coroutine's suspension points. Both
build on everything above — {ref "postconditions"}[postconditions] for what a contract is,
and {ref "verification-objects"}[frames] for what may change — so they come last.

The constructs themselves are execution features, described under
{ref "execution"}[*Execution*]: `throws` / `throw` / `try` / `catch` / `finally` under
*Exceptions*, and `coroutine` / `yield` / `resume` under {ref "coroutines"}[*Coroutines*].

## Exceptional contracts

`requires` and `ensures` describe the entry condition and the normal return. A
procedure that can throw has a second exit, described by one or more `throwsOn`
*behavior cases*. They follow `opaque`, alongside `ensures` and `modifies`, because
they constrain an exit rather than form part of the signature.

A case pairs a pre-state guard with the contract for the throwing path it selects:

```laurel
composite Exception {}
composite ArithmeticException extends Exception {}

procedure div(a: int, b: int) returns (r: int)
  throws (e: Exception)
  opaque
  throwsOn b == 0 {
    ensures e is ArithmeticException
  }
{
  if b == 0 then {
    var ae: ArithmeticException := new ArithmeticException;
    throw ae
  };
  r := a / b
};
```

The guard *forces* the throw. If `b == 0` holds on entry the procedure is guaranteed
to exit by throwing, and the thrown value satisfies the case's `ensures` clauses. So a
caller can prove ahead of time that a given input will fail, and knows what it will get.

`throws (e: T)` names the thrown value as well as its type, and scopes that name over
every case's `ensures`. There is one spelling, always binding: a procedure that says
nothing about its exception today would otherwise have to change its signature the moment
it wants to. `e` is deliberately *not* in scope in a `requires`, in a top-level `ensures`,
or in a guard — all three are evaluated where no exception exists.

The declaration already tells callers what was thrown. `throws (e: T)` on its own
guarantees

    it threw  ==>  e is T

on *every* throwing path, so a case never has to restate the declared type. That is why
the example above says `ensures e is ArithmeticException` and not `ensures e is Exception`:
a case's type test earns its place only when it *narrows* the declaration to a subtype for
that particular path. Restating the declared type would in fact say less, since the case's
`ensures` holds only when that case's guard held, while the declaration holds always.

A case with nothing left to say may therefore be empty, and is still meaningful — its
guard alone forces the throw:

```laurel
composite Exception {}

procedure mustThrow(a: int, b: int) returns (r: int)
  throws (e: Exception)
  opaque
  throwsOn b == 0 {
  };
```

A caller passing `b == 0` learns that the call throws, and learns from the declaration
that what it gets is an `Exception`.

Stating cases also settles the converse. Because a guard forces its throw, writing any
case is a claim to have enumerated them, so the verifier checks

    it threw  ==>  one of the guards held

A caller that can refute every guard therefore learns the call cannot have thrown. Two
consequences worth knowing: a throwing path that matches no guard is reported rather
than quietly accepted, and the two boundary cases read as you would hope —
`throwsOn true { … }` means the procedure always throws, and `throwsOn false { }` means
it never does.

None of this is documentation only. For a procedure with a body the verifier proves the
body honours the cases; at a call site they are assumed, so a caller can reason about a
throwing procedure without seeing its code.

### What a case may contain

A case takes `ensures` and `modifies`, mirroring their normal-exit counterparts but scoped
to the path its guard selects. An `ensures` inside a case also takes `summary "…"`, exactly
as a top-level one does, so a failing exceptional postcondition can report in your words:

```
  throwsOn b == 0 {
    ensures e is ArithmeticException summary "dividing by zero throws"
  }
```

Two forms that exist on the normal exit are deliberately absent inside a case, so a parse
error there is the surface telling you to write something else:

* No `free` or `checked` variant of a case's `ensures`. This is a deferral rather than a
  rule about exceptions; until it lands, a case's `ensures` is always both checked against
  the body and assumed by callers.
* No `modifies *`. It would say nothing new: a case that names no `modifies` already leaves
  its throwing path unframed, which is exactly what the wildcard means on the normal exit.
  Write `throwsOn C { }` — or omit the `modifies` and keep the `ensures` — instead.

The reasoning behind both is in the exceptions section of the Laurel Designer Guide.

### Stating no case

Cases are optional, and omitting them is not the same as `throwsOn false`. A procedure
with no case makes no claim about its throwing paths at all:

```laurel
composite Err {}

procedure thrower(x: int) returns (r: int)
  throws (e: Err)
  opaque
{
  if x < 0 then {
    var e: Err := new Err;
    throw e
  };
  r := x
};
```

A caller of `thrower` learns exactly one thing about the throwing exit — that what comes
out is an `Err`, from the declaration. It cannot tell *when* the call throws, so it must
allow for both exits; and because no case names a frame, it must also assume the heap may
have changed. Nothing is checked against the body either: with no guards to enumerate,
the `it threw ==> one of the guards held` obligation is not emitted.

That is weaker than stating a case, but it is weak in the safe direction — the contract
claims nothing, so nothing it claims can be wrong. The dangerous shape is *partial*
enumeration, cases with a gap between them, and that is what the check above catches.

Saying nothing is the right choice when the throwing condition is not expressible in the
procedure's own pre-state. The clearest example is a procedure that propagates a callee's
exception: it throws exactly when the callee does, and the callee's contract need not say
when that is. Where the condition *is* available — as `x < 0` is to `thrower` — stating a
case is strictly more informative, and worth doing.

## Exceptional frames

`modifies` at the top level frames the normal return. A `modifies` inside a case frames
that case's throwing path: it names the locations that may change when the procedure
throws for that reason.

```laurel
composite Cell {
  value: int
}
composite Err {}

procedure doWork(c: Cell, logCell: Cell, fail: bool) returns (r: int)
  throws (e: Err)
  opaque
  modifies c
  throwsOn fail {
    modifies logCell
  }
{
  if fail then {
    logCell#value := 1;
    var e: Err := new Err;
    throw e
  };
  c#value := 42;
  r := 0
};
```

Only `c` may change on the normal path, and only `logCell` when it throws because
`fail`. All frames are checked against the body and assumed at call sites, a case's
`modifies` accepts the same targets the top-level one does including field-granular ones
(`modifies logCell#value`), and an object allocated inside the body is exempt from all of
them.

Because each case carries its own frame, a procedure that writes different locations for
different reasons can say so — one case each — rather than declaring only their union.
A caller that rules out one case can then conclude the others' targets are unchanged.

Two things to keep in mind. Guards are not checked for overlap: if two can hold at once
both frames apply, and a caller gets only their intersection, which is rarely what was
meant. And framing a throwing path means naming its condition, so a procedure whose
throwing condition cannot be stated — one that propagates a callee's exception, say —
has to leave that path unframed by stating no case.

## Coroutine rely/guarantee contracts

Because a coroutine is suspended across a `yield`, the environment may act in between.
The `relies` and `guarantees` clauses specify that boundary, and are checked at every
`yield`:

- A `guarantees G` clause states a property the coroutine establishes at each `yield`
  (and when it halts). It is asserted there.
- A `relies R` clause states a property the coroutine may assume the environment
  maintained across the suspension. It is assumed on entry and after each `yield`.

Both may be two-state: `old(e)` inside a clause refers to the state at the start of
the coroutine's current step. The example below verifies: the coroutine relies on the
environment never decreasing the shared counter, and guarantees that its own step
strictly increases it.

:::example "A monotonically increasing counter"
```laurel
composite Cell { var x: int }

coroutine incMonotonic(s: Cell)
  requires s#x == 0
  relies old(s#x) <= s#x
  guarantees old(s#x) < s#x
  modifies s
{
  while (true)
      invariant oldGuarantee(s#x) <= s#x
  {
    s#x := s#x + 1;
    yield
  }
};
```
:::

Inside a loop that contains a `yield`, the per-yield guarantee is not threaded through
the loop head automatically: write the loop invariant explicitly using
`oldGuarantee(e)`, which refers to the state at the start of the current step (as
`old(e)` does inside a `guarantees` clause). The invariant above restates the
guarantee's baseline so the next iteration's `yield` can discharge it.

# Verification - Proof hints
%%%
tag := "proof-hints"
%%%

To be designed..

# Debugging and tooling
%%%
tag := "debugging"
%%%

A verification failure has more possible causes than a compile error: the program may be wrong,
the specification may be wrong, or the specification may be right but out of the solver's reach.
This section is about telling those apart.

## Running a program

The Laurel commands live in the `strata` CLI, from the `StrataCLI` package. The three that matter
for everyday work take a textual Laurel file and go progressively further:

```
lake exe strata -- laurelParse file.lr.st
lake exe strata -- laurelToCore file.lr.st
lake exe strata -- laurelAnalyze file.lr.st
```

`laurelParse` only parses and builds the AST, so it separates a syntax problem from everything
else. `laurelToCore` additionally resolves and lowers, printing translation diagnostics and the
resulting Core program — this is where a resolution or lowering complaint surfaces.
`laurelAnalyze` goes all the way: it generates verification conditions, solves them, and prints
an `==== ERRORS ====` section for translation problems followed by `==== RESULTS ====` for each
obligation.

The remaining commands are for producers rather than for reading Laurel text.
`laurelAnalyzeBinary` and `laurelInterpretBinary` read Ion from stdin; `laurelInterpret` reads an
Ion *file* and concretely executes it; `laurelPrint` renders Ion back as Laurel text; and
`laurelAnalyzeToGoto` emits a goto program. To produce Ion from text, convert it first:

```
lake exe strata -- toIon file.lr.st file.laurel.st.ion
lake exe strata -- laurelInterpret file.laurel.st.ion
```

## Seeing what the compiler did

The single most useful flag is `--keep-all-files`, which writes every intermediate Laurel and
Core program to a directory:

```
lake exe strata -- laurelAnalyze file.lr.st --keep-all-files lowering
```

The files are numbered in pipeline order, `lowering/file.0.Initial.laurel.st` onwards, ending in
the final Core program. When a construct behaves unexpectedly, find the first stage where it
stopped looking the way you meant, and you have localised the problem to one pass.

To inspect the SMT-LIB that the solver actually receives, keep the verification conditions and
skip solving:

```
lake exe strata -- laurelAnalyze file.lr.st --vc-directory vcs --no-solve
```

`--no-solve` requires `--vc-directory`. Reach for this only once the final Core program looks
right — an SMT query derived from wrong Core is rarely informative.

## Useful verification flags

`laurelAnalyze` and `laurelAnalyzeBinary` share the verification flag set. `strata laurelAnalyze
--help` is the authoritative list; the ones that come up most are:

:::table +header
 *
   * Flag
   * Effect
 *
   * `--keep-all-files DIR`
   * Write every Laurel and Core pipeline stage under `DIR`.
 *
   * `--vc-directory DIR`
   * Keep the generated SMT-LIB files in `DIR`.
 *
   * `--no-solve`
   * Generate SMT-LIB without invoking a solver. Requires `--vc-directory`.
 *
   * `--solver NAME`
   * Choose the solver executable. Defaults to cvc5.
 *
   * `--solver-timeout SECONDS`
   * Per-invocation solver timeout. Defaults to 10.
 *
   * `--stop-on-first-error`
   * Stop after the first failing obligation instead of reporting all of them.
 *
   * `--profile`
   * Print elapsed time per pipeline step — the first thing to try when a run is slow.
 *
   * `--check-mode MODE`
   * `deductive` (default), `bugFinding`, or `bugFindingAssumingCompleteSpec`.
 *
   * `--check-level LEVEL`
   * `minimal` (default), `minimalVerbose`, or `full`; controls how many checks are emitted.
 *
   * `--overflow-checks LIST`
   * Comma-separated `signed`, `unsigned`, `float64`, `all`, `none`.
 *
   * `--parallel N`
   * Run `N` solver workers concurrently.
 *
   * `--set-option NAME=VALUE`
   * Pass a solver-specific SMT option through verbatim. Repeatable.
:::

Note that supplying `--overflow-checks` starts from *all checks disabled* and then applies the
listed tokens left to right, so `--overflow-checks unsigned` turns the default signed check off.

The interpreter commands deliberately accept none of these — they never invoke a solver — and
take only `--fuel N` (a step limit), `--entry PROC` (run one named procedure instead of the ones
marked `entry`), and `--keep-all-files`.

## A debugging order

When something fails, working outward in this order avoids most wasted effort:

1. `laurelParse` — is it a syntax problem?
2. `laurelToCore` — is it a resolution or lowering problem?
3. `laurelAnalyze --keep-all-files out` — did a pass transform the construct in a way you did not
   expect?
4. Read the final Core program before looking at any SMT.
5. Only then, `--vc-directory vcs --no-solve` to inspect the query.

For a failing obligation specifically, the usual moves are to weaken the goal until it passes —
which tells you which conjunct is at fault — and to add `assert`s at intermediate points, since a
proof that fails at the end often fails because a fact you assumed was available never was. When
an obligation times out rather than fails, suspect a quantifier: check whether a `forall` needs a
trigger, or whether one it has is firing far too often.

## Exit statuses

The `strata` CLI shares one exit-status contract. Codes 1 and 2 mean *you* have something to fix;
3 and 4 mean the tool does.

:::table +header
 *
   * Code
   * Meaning
 *
   * 0
   * Success, an inconclusive result, or a solver timeout
 *
   * 1
   * Bad arguments or input, or command setup failure
 *
   * 2
   * Analysis failures were found
 *
   * 3
   * Internal error — report it
 *
   * 4
   * A known limitation was hit — an intentionally unsupported construct
:::

A `0` from `laurelAnalyze` does not on its own mean verification succeeded, because inconclusive
results and timeouts also exit `0`. Parse the printed `==== RESULTS ====` section rather than
trusting the status alone. The same applies to `laurelInterpret`, which reports assertion failures
in its diagnostics block while still exiting `0`.

## The Lean API

A tool that embeds Laurel rather than shelling out to the CLI uses the `Strata.Languages.Laurel`
facade. `parseLaurelText` and `readLaurelTextFile` produce a `Laurel.Program`; `readLaurelIonFiles`
and `readLaurelIonProgram` do the same from Ion; `laurelToCore` lowers one; and
`Laurel.verifyProgram` translates and verifies in one step.

```
import Strata.Languages.Laurel

open Strata

def lower (path : System.FilePath) : IO Unit := do
  let source ← readLaurelTextFile path
  let (core?, diagnostics) ← Laurel.translate {} source
  diagnostics.forM (fun d => IO.println d.message)
  match core? with
  | some core => IO.println (Std.format core).pretty
  | none => throw (IO.userError "Laurel translation failed")
```

Prefer `Laurel.translate` over `laurelToCore` in tooling: it preserves the structured
diagnostics instead of flattening them to strings, which is what you need to report a problem at
a source location. `translateWithLaurel` additionally hands back the post-pass Laurel program.

# Current limitations

Two kinds of gap are worth knowing about before designing a front end around Laurel: features
the language deliberately does not have, and features it accepts today but does not yet fully
support. The first list is stable, and a front end must plan around it. The second changes as the
implementation advances, so check it against the version you are building on rather than treating
it as permanent.

## Features Laurel does not have

Laurel does not model these at all, so a front end must compile them away before or during
translation:

- metaprogramming: macros, reflection, runtime code generation;
- pattern-matching syntax — use datatype testers and selectors;
- literal syntax for collections;
- first-class or higher-order procedure values;
- modules and imports;
- dedicated `break` and `continue` — build them from labelled blocks and `exit`;
- Python-style MRO, or dispatch on anything other than the receiver's runtime type — dispatch on
  an overridden method *is* supported, so only rules that differ from it need emitting explicitly;
- variance through a generic type's arguments — generic types are invariant for now;
- native separation logic: no separating conjunction, ownership, permissions, heaplets, or
  reachability;
- pointers and pointer arithmetic;
- garbage-collection observability, object deallocation, field deletion, or dynamic field lookup;
- preemptive concurrency. Cooperative coroutines *are* supported; see
  {ref "coroutines"}[*Coroutines*].

Laurel's type system is roughly at the level of C#'s, so source type-system features beyond it —
higher-kinded types, or advanced generics — also have to be erased or encoded before translation.

## Accepted today, but limited

These parse and resolve, so nothing warns you early, and they fail or misbehave later:

- `float64` parses and resolves, but is not implemented, so it cannot reach an analysis.
- Bitvector literals, storage, equality, and comparisons work, and comparisons are *signed*.
  General bitvector arithmetic does not yet select the bitvector operator family, and
  comparisons exist only at widths 1, 8, 16, 32, and 64.
- For `real`, the implemented operators are `+`, `-`, `*`, `/`, unary `-`, and the orderings.
  `%`, `/t`, and `%t` are admitted by resolution but are not correctly implemented.
- A composite field declared without `var` is not protected from writes.
- `new` should be used only with composites, even though the resolver also accepts datatypes.
- A composite field whose type is a generic datatype instantiation is rejected, because the heap
  representation cannot distinguish instantiations.
- A transparent procedure's body is turned into a function only for supported control and effect
  shapes; `opaque` is the robust choice for imperative code.
- Passing too *few* arguments to a procedure is not currently diagnosed, while passing too many
  is. Always pass exactly the declared number.
- Effects in a loop condition, control flow in a block used as a value, and `assert`/`assume` in
  the right-hand side of a short-circuit operator all misbehave; each is described where the
  construct itself is, under {ref "execution"}[*Execution*].
- Do not shadow a procedure input or output name inside a contract quantifier: the passes that
  rewrite `old` and outputs match on identifier text, so shadowing can silently change the
  formula.
- Pipe-quoted identifiers parse and lower, but the Core formatter does not re-quote every
  reference, so retained Core text containing them may not re-parse. Prefer regular identifiers
  when the output must be read back.

The Designer Guide's *Planned features* section records what is intended for the gaps above and
for the `To be designed..` sections in this guide.
