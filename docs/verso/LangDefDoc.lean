/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Lambda.LExpr
open Imperative
open Lambda

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Strata Language Definition" =>
%%%
authors := ["Aaron Tomb", "TODO"]
shortTitle := "Strata Language"
%%%

TODO: below is an example of what including Lean code defining the semantics of
Strata might look like.

```lean
namespace Imperative

```
# Small-Step Operational Semantics for Statements

Here we define small-step operational semantics for the
`Imperative` dialect's statement constructs.

First, we define the notion of a configuration, representing the
current execution state. A configuration consists of:
- The current statement or statements being executed
- The current store (for current variable values)
- The initial store (for evaluating Boogie's `old` operator)

```lean
inductive Config (P : PureExpr) : Type where
  | stmt :
      Stmt P (Cmd P) →
      SemanticStore P →
      SemanticStore P →
      Config P
  | stmts :
      List (Stmt P (Cmd P)) →
      SemanticStore P →
      SemanticStore P →
      Config P
  | terminal : SemanticStore P → SemanticStore P → Config P
```
