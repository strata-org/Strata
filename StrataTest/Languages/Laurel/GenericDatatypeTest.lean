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
# Generic datatype tests

Generic datatypes: native Core parametric datatypes.
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-! ## Generic datatypes verify end-to-end (native Core parametric datatypes)

Unlike generic composites (which are monomorphized to a concrete type per instantiation),
generic datatypes map to NATIVE Core parametric datatypes (`declare-datatypes` with sort
params) — a pass-through, no monomorphization. Front-end plumbing: `datatype Bx<T> { … }` grammar
binder → `DatatypeDefinition.typeArgs` → resolution scopes `T` as `.TVar` → `translateType`
lowers `Bx<int>` to `.tcons "Bx" [int]`.

NB: avoid the type name `Box` here — it collides with the internal heap boxed-value
datatype from `HeapParameterization` (a pre-existing name clash, not a generics issue),
so these use `Bx`/`Lst`/`Pr`. -/
def genericDatatypeCorpus : List Case := [
  { name := "generic_datatype_construct_eq", outcome := .verifies,
    why := "a generic datatype `Bx<int>` constructed + compared verifies (native Core parametric datatype)"
    src := r"
datatype Bx<T> { MkBx(v: T) }
procedure u() opaque { var b1: Bx<int> := MkBx(5); var b2: Bx<int> := MkBx(5); assert b1 == b2 };"},

  { name := "generic_datatype_construct_eq_wrong", outcome := .failsExactly 1,
    why := "distinct `Bx<int>` values must NOT be equal — datatype eq is real, not vacuous"
    src := r"
datatype Bx<T> { MkBx(v: T) }
procedure u() opaque { var b1: Bx<int> := MkBx(5); var b2: Bx<int> := MkBx(6); assert b1 == b2 };"},
  -- Native parametric datatype = ONE declaration shared by both instances (no per-inst
  -- clone). Reads each value back so it proves distinct correct values, not just translation.
  { name := "generic_datatype_multi_instantiation", outcome := .verifies,
    why := "`Bx<int>` AND `Bx<bool>` in one program each hold their value (one shared datatype)"
    src := r"
datatype Bx<T> { MkBx(v: T) }
procedure u() opaque { var bi: Bx<int> := MkBx(5); var bb: Bx<bool> := MkBx(true); assert bi == MkBx(5) && bb == MkBx(true) };"},

  { name := "generic_datatype_recursive", outcome := .verifies,
    why := "recursive generic datatype `Lst<int>` (Cons/Nil) round-trips — value observed via equality, not just constructed"
    src := r"
datatype Lst<T> { Nil(), Cons(head: T, tail: Lst<T>) }
procedure u() opaque { var xs: Lst<int> := Cons(1, Nil()); assert xs == Cons(1, Nil()) };"},

  { name := "generic_datatype_recursive_wrong", outcome := .failsExactly 1,
    why := "a wrong-value equality on the recursive `Lst<int>` must FAIL — the recursive lowering is sound, not degenerate"
    src := r"
datatype Lst<T> { Nil(), Cons(head: T, tail: Lst<T>) }
procedure u() opaque { var xs: Lst<int> := Cons(1, Nil()); assert xs == Cons(2, Nil()) };"},

  { name := "generic_datatype_monomorphic_unaffected", outcome := .verifies,
    why := "a datatype with NO type params still works after the grammar gained Option TypeParams"
    src := r"
datatype Pr { MkPr(a: int, b: int) }
procedure u() opaque { var p1: Pr := MkPr(1, 2); var p2: Pr := MkPr(1, 2); assert p1 == p2 };"},
  -- CROSS-INSTANTIATION DISTINCTNESS: `Bx<int>` and `Bx<bool>` are DISTINCT Core sorts, not
  -- erased to a single sort — so assigning one to the other is rejected.
  { name := "generic_datatype_cross_instantiation_rejected", outcome := .rejected,
    why := "assigning `Bx<int>` to a `Bx<bool>` var must be REJECTED (distinct sorts; cross-inst confusion = unsound)"
    src := r"
datatype Bx<T> { MkBx(v: T) }
procedure u() opaque { var bi: Bx<int> := MkBx(5); var bb: Bx<bool> := bi; assert 1 == 1 };"},
  -- HEAP-STORED COMPOSITE FIELD: a generic datatype as a composite field routes through
  -- HeapParameterization's box wrapper (the `.Applied` arm — one box variant per inst).
  { name := "generic_datatype_composite_field", outcome := .verifies,
    why := "`Bx<int>` as a composite field, written + read back, verifies (heap-box `.Applied` arm)"
    src := r"
datatype Bx<T> { MkBx(v: T) }
composite Holder { var b: Bx<int> }
procedure u() opaque { var h: Holder := new Holder; var x: Bx<int> := MkBx(9); h#b := x; var y: Bx<int> := h#b; assert y == x };"},

  { name := "generic_datatype_composite_field_wrong", outcome := .failsExactly 1,
    why := "a FALSE read-back of a generic-datatype field must FAIL — heap-box round-trip is sound, not vacuous"
    src := r"
datatype Bx<T> { MkBx(v: T) }
composite Holder { var b: Bx<int> }
procedure u() opaque { var h: Holder := new Holder; var x: Bx<int> := MkBx(9); var z: Bx<int> := MkBx(8); h#b := x; var y: Bx<int> := h#b; assert y == z };"},

  { name := "generic_datatype_composite_two_insts", outcome := .verifies,
    why := "`Bx<int>` and `Bx<bool>` as separate composite fields each get a distinct heap-box variant"
    src := r"
datatype Bx<T> { MkBx(v: T) }
composite Holder { var bi: Bx<int> var bb: Bx<bool> }
procedure u() opaque { var h: Holder := new Holder; h#bi := MkBx(1); h#bb := MkBx(true); var yi: Bx<int> := h#bi; assert yi == MkBx(1) };"} ]

/-- Generic DATATYPES. Unlike generic composites (which are monomorphized to a concrete
    type per instantiation), generic datatypes map to NATIVE Core parametric datatypes
    (`declare-datatypes` with sort params) — a pass-through, no monomorphization. -/
def runGenericDatatypeTest : IO Unit := checkCases genericDatatypeCorpus

#guard_msgs (drop info, error) in
#eval runGenericDatatypeTest

end Strata.Laurel
