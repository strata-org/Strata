/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.DDMTransform.Grammar
meta import Strata.DDM.Integration.Lean

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

// Boole's global variables declarations and modifies clauses are converted into
// inout parameters in Core.
@[scope(b)]
op command_var (b : Bind) : Command =>
  @[prec(10)] "var " b ";\n";

op modifies_spec (nms : CommaSepBy Ident) : SpecElt => "modifies " nms ";\n";

// Boole keeps the `returns` syntax for procedure declarations, while Core
// uses `out`/`inout` parameter modifiers.
op boole_procedure (name : Ident,
                    typeArgs : Option TypeArgs,
                    @[scope(typeArgs)] b : Bindings,
                    @[scope(b)] ret : Option MonoDeclList,
                    @[scope(ret)] s: Option Spec,
                    @[scope(ret)] body : Option Block) :
  Command =>
  @[prec(10)] "procedure " name typeArgs b " returns " "(" ret ")\n"
              s body ";\n";

// Boole keeps the `call lhs := f(args)` syntax for calls with outputs.
// Unit calls (no outputs) use Core's `call_statement` with `callArgExpr` args.
op boole_call_statement (vs : CommaSepBy Ident, f : Ident, expr : CommaSepBy Expr) : Statement =>
   "call " vs " := " f "(" expr ")" ";\n";

fn ext_equal (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a " =~= " b;

// Unicode dotted quantifiers are normalized earlier in `Strata.DDM.Elab`.
// This keeps modern surface syntax such as `∀ x . P` working while the DDM
// grammar continues to elaborate through the legacy `::` separator.
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
