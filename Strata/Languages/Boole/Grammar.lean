/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.Grammar

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------
---------------------------------------------------------------------

/- DDM support for parsing and pretty-printing Boole -/
-- Extended version with support for:
-- ✓ Multiple invariants
-- ✓ For loops down to
-- Division operator `/`
-- ✓ Array assignment syntax
-- ✓ Quantifier syntax (forall, exists)
-- Simple procedure calls
-- Summation expressions
-- Structures and records (basic support)

#dialect
dialect Boole;

import Core;

// Boole retains global variable declarations and modifies clauses in its
// concrete syntax. During translation to Core, these are converted into
// additional input/output parameters on procedure headers.
@[scope(b)]
op command_var (b : Bind) : Command =>
  @[prec(10)] "var " b ";\n";

op modifies_spec (nms : CommaSepBy Ident) : SpecElt => "modifies " nms ";\n";

// Unicode quantifier aliases use the same `::` separator as the ASCII forms.
// The legacy dotted separator is normalized earlier in `Strata.DDM.Elab`.
fn forall_unicode (d : DeclList, @[scope(d)] b : bool) : bool =>
  "∀ " d " :: " b:3;
fn exists_unicode (d : DeclList, @[scope(d)] b : bool) : bool =>
  "∃ " d " :: " b:3;
fn forall_unicodeT (d : DeclList, @[scope(d)] triggers : Triggers, @[scope(d)] b : bool) : bool =>
  "∀ " d " :: " triggers indent(2, b:3);
fn exists_unicodeT (d : DeclList, @[scope(d)] triggers : Triggers, @[scope(d)] b : bool) : bool =>
  "∃ " d " :: " triggers indent(2, b:3);

category Step;
op step(e: Expr) : Step =>
  " by " e;

op for_statement (v : MonoBind, init : Expr,
  @[scope(v)] guard : bool, @[scope(v)] step : Expr,
  @[scope(v)] invs : Invariants, @[scope(v)] body : Block) : Statement =>
  "for " "(" v " := " init "; " guard "; " step ")" invs body;

op for_to_by_statement (v : MonoBind, init : Expr, limit : Expr,
  @[scope(v)] step : Option Step, @[scope(v)] invs : Invariants,
  @[scope(v)] body : Block) : Statement =>
  "for " v " := " init " to " limit step invs body;

op for_down_to_by_statement (v : MonoBind, init : Expr, limit : Expr,
  @[scope(v)] step : Option Step, @[scope(v)] invs : Invariants,
  @[scope(v)] body : Block) : Statement =>
  "for " v " := " init " downto " limit step invs body;

category Program;
op prog (commands : SpacePrefixSepBy Command) : Program =>
  commands;

#end

---------------------------------------------------------------------

end Strata
