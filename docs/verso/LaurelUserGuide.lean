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
but this list will grow and you can already use it for other languages as well. We recommend
targeting Laurel when trying to analyse any programming language using Strata.

Laurel is a good target when your source language has a procedure-like construct and its features
map onto Laurel's. Some source-language features must be compiled away before or during translation,
because Laurel does not model them directly:
- metaprogramming (macros, reflection, runtime code generation);
- type-system features that do not fit Laurel's type system, which is close to C#'s (for example
  higher-kinded types or advanced generics);
- pointers and pointer arithmetic (Laurel does not yet model these).

Laurel is *not* a good target for languages that use none of its features — typically languages with
no procedure-like construct, such as assembly, or inputs that are not programming languages at all.
For those, target Strata Core directly. A stack-based language like JVM bytecode still benefits from
targeting Laurel.

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

# Resolution

Right now, Laurel reserves identifier names that start with `$` for use in its compilation passes.
In the future we may improve the passes so that this restriction can be dropped.

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
  and produces $`\Gamma'` out. Only \[⇐\] Var-Declare extends the scope; the
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
- {ref "rules-variables"}[*Variables*] — \[⇒\] Var-Local, \[⇒\] Var-Field, \[⇒\] Var-Declare
- {ref "rules-control-flow"}[*Control flow*] — \[⇐\] If, \[⇐\] If-NoElse,
  \[⇒\] If-Synth, \[⇒\] If-Synth-NoElse;
  \[⇐\] Block, \[⇒\] Block-Synth, \[⋄\] Synth-Discard,
  \[⇒\] Empty-Block; \[⇒\] Exit;
  \[⇒\] Return-None-Void, \[⇒\] Return-None-Single, \[⇒\] Return-None-Multi,
  \[⇒\] Return-Some, \[⇒\] Return-Void-Error,
  \[⇒\] Return-Multi-Error; \[⇒\] While
- {ref "rules-verification-statements"}[*Verification statements*] — \[⇒\] Assert, \[⇒\] Assume
- {ref "rules-assignment"}[*Assignment*] — \[⇒\] Assign, \[⇐\] Assign
- {ref "rules-calls"}[*Calls*] — \[⇒\] Static-Call, \[⇒\] Static-Call-Multi,
  \[⇒\] Instance-Call, \[⇒\] Instance-Call-Multi
- {ref "rules-primitive-operations"}[*Primitive operations*] — \[⇒\] Op-Bool, \[⇒\] Op-Cmp, \[⇒\] Op-Eq,
  \[⇒\] Op-Arith, \[⇒\] Op-Concat; \[⇐\] Op-Arith, \[⇐\] Op-Bool
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

$$`\frac{x \notin \mathrm{dom}(\Gamma)}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Declare}\;\langle x, T_x\rangle) \Rightarrow \mathsf{TVoid} \quad \dashv \quad \Gamma, x : T_x} \quad \text{([⇒] Var-Declare)}`

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

Only `Var (.Declare …)` actually extends the scope $`\Gamma_i`; every
other statement leaves it unchanged. The block opens a fresh nested
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

### Primitive operations
%%%
tag := "rules-primitive-operations"
%%%

`Numeric` abbreviates "consistent with one of {name Strata.Laurel.HighType.TInt}`TInt`,
{name Strata.Laurel.HighType.TReal}`TReal`,
{name Strata.Laurel.HighType.TFloat64}`TFloat64`, or
{name Strata.Laurel.HighType.TBv}`TBv` (a bitvector of any width)", with
`Unknown` admitted as the gradual escape hatch.

$$`\frac{\Gamma \vdash \mathit{args}_i \Rightarrow U_i \quad U_i <: \mathsf{TBool} \quad \mathit{op} \in \{\mathsf{And}, \mathsf{Or}, \mathsf{AndThen}, \mathsf{OrElse}, \mathsf{Not}, \mathsf{Implies}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Bool)}`

$$`\frac{\Gamma \vdash \mathit{args}_i \Rightarrow U_i \quad \mathsf{Numeric}\;U_i \quad \mathit{op} \in \{\mathsf{Lt}, \mathsf{Leq}, \mathsf{Gt}, \mathsf{Geq}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Cmp)}`

$$`\frac{\Gamma \vdash \mathit{lhs} \Rightarrow T_l \quad \Gamma \vdash \mathit{rhs} \Rightarrow T_r \quad T_l \sim T_r \quad \mathit{op} \in \{\mathsf{Eq}, \mathsf{Neq}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;[\mathit{lhs}; \mathit{rhs}] \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Eq)}`

$$`\frac{\Gamma \vdash \mathit{args}_i \Rightarrow U_i \quad \mathsf{Numeric}\;U_i \quad T = \bigsqcup_i U_i \text{ (consistency join)} \quad \mathit{op} \in \{\mathsf{Neg}, \mathsf{Add}, \mathsf{Sub}, \mathsf{Mul}, \mathsf{Div}, \mathsf{Mod}, \mathsf{DivT}, \mathsf{ModT}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow T} \quad \text{([⇒] Op-Arith)}`

The arithmetic synth rule mirrors $`[⇒]\,\text{Op-Eq}` but generalised
to $`n` operands. Each operand is synthesized and required to be
$`\mathsf{Numeric}` (i.e. $`\mathsf{TInt}`, $`\mathsf{TReal}`,
$`\mathsf{TFloat64}`, $`\mathsf{TBv}_w` (a bitvector of any width), or
the gradual $`\mathsf{Unknown}`). The
result type is the *consistency join* $`\bigsqcup_i U_i` — a fold of
the operand types under
{name Strata.Laurel.isConsistent}`isConsistent`'s flat lattice:
$`\mathsf{Unknown} \sqcup T = T`, $`T \sqcup T = T`, and any other
combination is rejected. The fold runs via `join`, a pure function, so
the search has no diagnostic side-effects.

:::example "Arithmetic operand join"
- `1 + 2` synthesizes $`\mathsf{TInt}`
- `1.5 + 2.5` synthesizes $`\mathsf{TReal}`
- `<?> + 1` synthesizes $`\mathsf{TInt}` — the $`\mathsf{Unknown}` operand promotes to its neighbour
- `<?> + <?>` synthesizes $`\mathsf{Unknown}`
- `1 + 2.0` is rejected: *cannot apply '+' to operands of types 'int', 'real'*
:::

$$`\frac{\Gamma \vdash \mathit{args}_i \Rightarrow U_i \quad U_i <: \mathsf{TString} \quad \mathit{op} = \mathsf{StrConcat}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TString}} \quad \text{([⇒] Op-Concat)}`

{docstring Strata.Laurel.Resolution.Synth.primitiveOp}

The arithmetic and boolean families also have a check-mode rule, used
when the surrounding context provides an `expected` type. The rule
pushes the operand type into each operand via
`Check.resolveStmtExpr`, replacing the synth-then-`checkSubtype`
discipline with bidirectional check.

$$`\frac{\mathsf{Numeric}\;T \quad \Gamma \vdash \mathit{args}_i \Leftarrow T \quad \mathit{op} \in \{\mathsf{Neg}, \mathsf{Add}, \mathsf{Sub}, \mathsf{Mul}, \mathsf{Div}, \mathsf{Mod}, \mathsf{DivT}, \mathsf{ModT}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Leftarrow T} \quad \text{([⇐] Op-Arith)}`

$$`\frac{\mathsf{TBool} <: T \quad \Gamma \vdash \mathit{args}_i \Leftarrow \mathsf{TBool} \quad \mathit{op} \in \{\mathsf{And}, \mathsf{Or}, \mathsf{AndThen}, \mathsf{OrElse}, \mathsf{Not}, \mathsf{Implies}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Leftarrow T} \quad \text{([⇐] Op-Bool)}`

{docstring Strata.Laurel.Resolution.Check.primitiveOp}

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

### Primitive types

Laurel provides unbounded mathematical `int` and `real` types, a `bool` type,
`string`, and fixed-width bitvectors. Because `int` is unbounded, arithmetic in
specifications behaves like ordinary mathematics: there is no overflow to reason
around when you are stating what a procedure computes.

### Composites

Laurel models objects with *composite* types. A composite declares mutable
fields and may declare *instance procedures* (methods). Fields are read and
written with the `#` selector, instances are created with `new`, and a method is
invoked with the same `#` syntax.

```laurel
program Laurel;
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

An instance procedure takes its receiver as an explicit `self` parameter and
refers to fields through it. The contract of a method uses the same `requires` /
`ensures` / `modifies` clauses as any other procedure; here `ensures self#count
== 0` is what lets the caller conclude `c#count == 0` after `c#reset()`.

Field selection and method calls chain, so you can reach through one object to
another: `o#inner#x` reads field `x` of the object stored in `o`'s `inner` field,
and `o#inner#isOne()` calls a method on it.

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

# Verification - Fundamentals

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

## Postconditions

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

## Concurrency

To be designed..

# Verification - Proof hints

To be designed..
