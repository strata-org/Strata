/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import StrataDDM.Util.IO
meta import Strata.Languages.Laurel.Grammar.LaurelGrammar
meta import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
meta import Strata.Languages.Laurel.LaurelCompilationPipeline
meta import all StrataTest.Util.LaurelCorpusHarness

/-!
# Polymorphic function tests

End-to-end polymorphic *functions* (Core HM instantiation) and reference-kinded `T` through a function.
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-! ## End-to-end: a genuinely polymorphic function

The first program that exercises the full tyvar substrate: a polymorphic
`function id<T>(x: T): T` declared with a `<T>` binder (grammar), `T` resolved
to `.TVar` in scope (resolution), lowered to a Core `ftvar` and instantiated by
Core's HM at the `id(5)` call site (translation + Core). If this verifies, the
substrate works end-to-end — not just compiles. -/
def polyIdProgram := r"
function id<T>(x: T): T
{
    x
};

procedure useIt()
  opaque
{
    var a: int := id(5);
    assert a == 5
};"

def runPolyIdTest : IO Unit := do
  let m ← corpusMetricsOf "poly_id" polyIdProgram
  unless m.translated do
    throw (IO.userError "poly_id: a polymorphic function failed to translate to Core")
  unless m.numFailures == 0 do
    throw (IO.userError s!"poly_id: expected all-verified, got numFailures={m.numFailures}")

#guard_msgs (drop info, error) in
#eval runPolyIdTest

/-! ## Reference-kinded T through a function: already works (no erasure pass needed)

Empirically established (this commit): a polymorphic `function id<T>` applied to a
**composite (reference) argument** verifies, because every composite lowers to the
single `tcons "Composite"` type and Core's HM unifies `ftvar T` with `Composite`
exactly as it does with `int`. The pass-through path is therefore *kind-agnostic*
— there is NO separate "erase reference T to Composite" pass to write for
functions. (Reference T only needs special handling where it would reach machinery
that can't represent a type variable: a composite FIELD of type T → monomorphization;
a polymorphic procedure → per-call-site freshening. Neither is an erasure pass.) -/
def polyRefFunctionProgram := r"
composite Cir { var r: int }

function idc<T>(x: T): T { x };

procedure useRef()
  opaque
{
    var c: Cir := new Cir;
    c#r := 7;
    var d: Cir := idc(c);
    assert d#r == 7
};"

def runPolyRefFunctionTest : IO Unit := do
  let m ← corpusMetricsOf "poly_ref_fn" polyRefFunctionProgram
  unless m.translated do
    throw (IO.userError "poly_ref_fn: a polymorphic function over a REFERENCE arg failed to translate — the ftvar/Composite unification regressed")
  unless m.numFailures == 0 do
    throw (IO.userError s!"poly_ref_fn: expected all-verified, got numFailures={m.numFailures}")

#guard_msgs (drop info, error) in
#eval runPolyRefFunctionTest

end Strata.Laurel
