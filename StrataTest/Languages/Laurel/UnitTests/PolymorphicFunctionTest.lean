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
`procedure id<T>(x: T): T` declared with a `<T>` binder (grammar), `T` resolved
to `.TVar` in scope (resolution), lowered to a Core `ftvar` and instantiated by
Core's HM at the `id(5)` call site (translation + Core). If this verifies, the
substrate works end-to-end — not just compiles. -/
private def polyIdProgram := r"
procedure id<T>(x: T): T
{
    return x
};

procedure useIt()
  opaque
{
    var a: int := id(5);
    assert a == 5
};"

/-! ## Reference-kinded T through a function: already works (no erasure pass needed)

Empirically established: a polymorphic `procedure id<T>` applied to a
**composite (reference) argument** verifies, because every composite lowers to the
single `tcons "Composite"` type and Core's HM unifies `ftvar T` with `Composite`
exactly as it does with `int`. The pass-through path is therefore *kind-agnostic*
— there is NO separate "erase reference T to Composite" pass to write for
functions. (Reference T only needs special handling where it would reach machinery
that can't represent a type variable: a composite FIELD of type T → monomorphization;
a polymorphic procedure → per-call-site freshening. Neither is an erasure pass.) -/
private def polyRefFunctionProgram := r"
composite Cir { var r: int }

procedure idc<T>(x: T): T { return x };

procedure useRef()
  opaque
{
    var c: Cir := new Cir;
    c#r := 7;
    var d: Cir := idc(c);
    assert d#r == 7
};"

-- Must-fail twins: a wrong expectation on the instantiated result must be reported, proving the
-- verifying cases are non-vacuous — the return value actually flows through the ftvar/Core-HM
-- instantiation rather than the assertion being trivially discharged.
private def polyIdProgramWrong := r"
procedure id<T>(x: T): T
{
    return x
};

procedure useIt()
  opaque
{
    var a: int := id(5);
    assert a == 6
};"

private def polyRefFunctionProgramWrong := r"
composite Cir { var r: int }

procedure idc<T>(x: T): T { return x };

procedure useRef()
  opaque
{
    var c: Cir := new Cir;
    c#r := 7;
    var d: Cir := idc(c);
    assert d#r == 8
};"

private def polymorphicFunctionCorpus : List Case := [
  { name := "poly_id", outcome := .verifies,
    why := "poly `id<T>(x:T):T` instantiated at `id(5)` verifies end-to-end (grammar → resolution → ftvar → Core HM)"
    src := polyIdProgram },
  { name := "poly_id_wrong", outcome := .failsExactly 1,
    why := "`id(5)` returns 5, so `assert a == 6` must fail exactly once — pins that the ftvar return value flows (poly_id is non-vacuous)"
    src := polyIdProgramWrong },
  { name := "poly_ref_fn", outcome := .verifies,
    why := "poly `id<T>` over a REFERENCE (composite) arg verifies — ftvar/Composite HM-unification regression pin"
    src := polyRefFunctionProgram },
  { name := "poly_ref_fn_wrong", outcome := .failsExactly 1,
    why := "`idc(c)` returns `c` with `c#r == 7`, so `assert d#r == 8` must fail — pins Composite value pass-through (poly_ref_fn is non-vacuous)"
    src := polyRefFunctionProgramWrong } ]

private def runPolymorphicFunctionTests : IO Unit := checkCases polymorphicFunctionCorpus

#guard_msgs (drop info, error) in
#eval runPolymorphicFunctionTests

end Strata.Laurel
