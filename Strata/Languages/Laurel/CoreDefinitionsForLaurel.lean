/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.AST
public import StrataDDM.Integration.Lean.HashCommands -- shake: keep
public import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Grammar.LaurelGrammar

namespace Strata.Laurel

public section

/--
Core built-in definitions expressed in Laurel syntax.

Includes:
- Map primitives (`select`, `update`, `mapConst`) — polymorphic map operations.
- Type-specific external operators (`intAdd`, `realAdd`, etc.) — the Core primitives.
- Overloaded transparent wrappers (`add`, `sub`, etc.) — dispatching to the
  type-specific externals. The parser emits `StaticCall "add"` and resolution
  picks the right overload based on argument types.

The map primitives and the equality wrappers carry generic signatures
(`select<K,V>(map: Map K V, key: K) : V`). Resolution instantiates them per call site
from the actual argument types (`callSiteTypeSubst`), so `select` on a `Map int bool`
reports `bool`. A bare `.TVar` there would be a gradual wildcard under `isConsistent`,
leaving every use of the result unchecked.

The generic `Result` datatype that the exceptional-channel lowering targets is
*not* part of this always-on prelude: it is injected by `EliminateExceptions`
only when a program actually uses exceptions (see `resultDefinitions`), so a
program that never throws does not carry it.
-/
def coreDefinitionsForLaurelDDM :=
#strata
program Laurel;

datatype LaurelResolutionErrorPlaceholder {}
datatype Float64IsNotSupportedYet {}
datatype LaurelUnit { MkLaurelUnit() }

// These are internal stand-ins for Core's native, already-polymorphic map primitives
// (the real signatures live in Core.Factory). Declared `external`, they are filtered out
// before Core translation and never reach Core; calls resolve to the Core primitives by
// name. Nothing observes these signatures at translation time, but resolution does: the generic
// form lets a call site infer `K`/`V` from its actual arguments (`callSiteTypeSubst`) and report
// a concrete result type. The polymorphism callers ultimately rely on is the Core primitives' own.
procedure select<K, V>(map: Map K V, key: K) : V
  external;

procedure update<K, V>(map: Map K V, key: K, value: V) : Map K V
  external;

// `K` is not determined by the single value argument; `LaurelToCoreSchemaPass` recovers it
// from the binding's declared type (`expectedType`), defaulting to `TypeTag`.
procedure mapConst<K, V>(value: V) : Map K V
  external;

// --- Type-specific external operators (Core primitives) ---

// Integer arithmetic
procedure $intAdd(x: int, y: int) : int external;
procedure $intSub(x: int, y: int) : int external;
procedure $intMul(x: int, y: int) : int external;
procedure $intDiv(x: int, y: int) : int external;
procedure $intSafeDiv(x: int, y: int) : int external;
procedure $intMod(x: int, y: int) : int external;
procedure $intSafeMod(x: int, y: int) : int external;
procedure $intDivT(x: int, y: int) : int external;
procedure $intSafeDivT(x: int, y: int) : int external;
procedure $intModT(x: int, y: int) : int external;
procedure $intSafeModT(x: int, y: int) : int external;
procedure $intNeg(x: int) : int external;

// Integer comparisons
procedure $intLt(x: int, y: int) : bool external;
procedure $intLe(x: int, y: int) : bool external;
procedure $intGt(x: int, y: int) : bool external;
procedure $intGe(x: int, y: int) : bool external;

// Real arithmetic
procedure $realAdd(x: real, y: real) : real external;
procedure $realSub(x: real, y: real) : real external;
procedure $realMul(x: real, y: real) : real external;
procedure $realDiv(x: real, y: real) : real external;
procedure $realNeg(x: real) : real external;

// Real comparisons
procedure $realLt(x: real, y: real) : bool external;
procedure $realLe(x: real, y: real) : bool external;
procedure $realGt(x: real, y: real) : bool external;
procedure $realGe(x: real, y: real) : bool external;

// Bitvector comparisons, per width.
//
// Bitvector types are width-parameterized, so unlike `int`/`real` they cannot be
// covered by a single overload. Core generates its bitvector operators per width
// (`Bv32.SLt`, …) for widths 1, 8, 16, 32, 64 and 128 (see `Factory.lean`'s
// `DefBVOpFuncExprs`); the wrappers below cover 1 through 64, so a comparison at
// any other width — including the 128 that Core does support — reports "no overload
// matches" rather than silently mistranslating.
//
// These are the *signed* comparisons, which preserves the previous behaviour:
// before operators became procedure calls, a bitvector comparison was lowered to
// the *integer* operator (`intLt`), i.e. signed. Laurel's `bv n` carries no
// signedness, so an unsigned comparison is not currently expressible.
procedure $bv1SLt(x: bv 1, y: bv 1) : bool external;
procedure $bv1SLe(x: bv 1, y: bv 1) : bool external;
procedure $bv1SGt(x: bv 1, y: bv 1) : bool external;
procedure $bv1SGe(x: bv 1, y: bv 1) : bool external;
procedure $bv8SLt(x: bv 8, y: bv 8) : bool external;
procedure $bv8SLe(x: bv 8, y: bv 8) : bool external;
procedure $bv8SGt(x: bv 8, y: bv 8) : bool external;
procedure $bv8SGe(x: bv 8, y: bv 8) : bool external;
procedure $bv16SLt(x: bv 16, y: bv 16) : bool external;
procedure $bv16SLe(x: bv 16, y: bv 16) : bool external;
procedure $bv16SGt(x: bv 16, y: bv 16) : bool external;
procedure $bv16SGe(x: bv 16, y: bv 16) : bool external;
procedure $bv32SLt(x: bv 32, y: bv 32) : bool external;
procedure $bv32SLe(x: bv 32, y: bv 32) : bool external;
procedure $bv32SGt(x: bv 32, y: bv 32) : bool external;
procedure $bv32SGe(x: bv 32, y: bv 32) : bool external;
procedure $bv64SLt(x: bv 64, y: bv 64) : bool external;
procedure $bv64SLe(x: bv 64, y: bv 64) : bool external;
procedure $bv64SGt(x: bv 64, y: bv 64) : bool external;
procedure $bv64SGe(x: bv 64, y: bv 64) : bool external;

// Boolean operations
procedure $boolNot(x: bool) : bool external;
procedure $boolAnd(x: bool, y: bool) : bool external;
procedure $boolOr(x: bool, y: bool) : bool external;
procedure $boolImplies(x: bool, y: bool) : bool external;

// Short-circuit boolean operations, string concatenation and equality have no
// separate delegate: the operator wrapper's own reserved name (`$andThen`,
// `$orElse`, `$strConcat`, `$eq`, `$neq`) is already the name
// `LaurelToCoreSchemaPass` recognizes, so they are declared `external` at the
// wrapper site below rather than delegated to a second procedure.

// --- Overloaded operator wrappers ($ prefix = reserved namespace) ---
// The parser emits StaticCall "$add" for "+", etc. Resolution picks the overload.

// Arithmetic (int overload)
procedure $add(x: int, y: int) : int
  return $intAdd(x, y);
procedure $sub(x: int, y: int) : int
  return $intSub(x, y);
procedure $mul(x: int, y: int) : int
  return $intMul(x, y);
procedure $div(x: int, y: int) : int
  requires y != 0
  return $intSafeDiv(x, y);
procedure $mod(x: int, y: int) : int
  requires y != 0
  return $intSafeMod(x, y);
procedure $divT(x: int, y: int) : int
  requires y != 0
  return $intSafeDivT(x, y);
procedure $modT(x: int, y: int) : int
  requires y != 0
  return $intSafeModT(x, y);
procedure $neg(x: int) : int
  return $intNeg(x);

// Arithmetic (real overload)
procedure $add(x: real, y: real) : real
  return $realAdd(x, y);
procedure $sub(x: real, y: real) : real
  return $realSub(x, y);
procedure $mul(x: real, y: real) : real
  return $realMul(x, y);
procedure $div(x: real, y: real) : real
  return $realDiv(x, y);
procedure $neg(x: real) : real
  return $realNeg(x);

// Comparisons (int overload)
procedure $lt(x: int, y: int) : bool
  return $intLt(x, y);
procedure $le(x: int, y: int) : bool
  return $intLe(x, y);
procedure $gt(x: int, y: int) : bool
  return $intGt(x, y);
procedure $ge(x: int, y: int) : bool
  return $intGe(x, y);

// Comparisons (real overload)
procedure $lt(x: real, y: real) : bool
  return $realLt(x, y);
procedure $le(x: real, y: real) : bool
  return $realLe(x, y);
procedure $gt(x: real, y: real) : bool
  return $realGt(x, y);
procedure $ge(x: real, y: real) : bool
  return $realGe(x, y);

// Comparisons (bitvector overloads, one per Core-supported width — see the
// `bv*S*` externals above for why these are per-width and signed).
procedure $lt(x: bv 1, y: bv 1) : bool
  return $bv1SLt(x, y);
procedure $le(x: bv 1, y: bv 1) : bool
  return $bv1SLe(x, y);
procedure $gt(x: bv 1, y: bv 1) : bool
  return $bv1SGt(x, y);
procedure $ge(x: bv 1, y: bv 1) : bool
  return $bv1SGe(x, y);
procedure $lt(x: bv 8, y: bv 8) : bool
  return $bv8SLt(x, y);
procedure $le(x: bv 8, y: bv 8) : bool
  return $bv8SLe(x, y);
procedure $gt(x: bv 8, y: bv 8) : bool
  return $bv8SGt(x, y);
procedure $ge(x: bv 8, y: bv 8) : bool
  return $bv8SGe(x, y);
procedure $lt(x: bv 16, y: bv 16) : bool
  return $bv16SLt(x, y);
procedure $le(x: bv 16, y: bv 16) : bool
  return $bv16SLe(x, y);
procedure $gt(x: bv 16, y: bv 16) : bool
  return $bv16SGt(x, y);
procedure $ge(x: bv 16, y: bv 16) : bool
  return $bv16SGe(x, y);
procedure $lt(x: bv 32, y: bv 32) : bool
  return $bv32SLt(x, y);
procedure $le(x: bv 32, y: bv 32) : bool
  return $bv32SLe(x, y);
procedure $gt(x: bv 32, y: bv 32) : bool
  return $bv32SGt(x, y);
procedure $ge(x: bv 32, y: bv 32) : bool
  return $bv32SGe(x, y);
procedure $lt(x: bv 64, y: bv 64) : bool
  return $bv64SLt(x, y);
procedure $le(x: bv 64, y: bv 64) : bool
  return $bv64SLe(x, y);
procedure $gt(x: bv 64, y: bv 64) : bool
  return $bv64SGt(x, y);
procedure $ge(x: bv 64, y: bv 64) : bool
  return $bv64SGe(x, y);

// Boolean
procedure $not(x: bool) : bool
  return $boolNot(x);
procedure $and(x: bool, y: bool) : bool
  return $boolAnd(x, y);
procedure $or(x: bool, y: bool) : bool
  return $boolOr(x, y);
procedure $implies(x: bool, y: bool) : bool
  return $boolImplies(x, y);
procedure $andThen(x: bool, y: bool) : bool external;
procedure $orElse(x: bool, y: bool) : bool external;

// Equality. `T` binds from the operands at each call site, so `1 == true` is a type error.
// These stay `external`: a transparent body would carry this signature into Core and fail to
// unify against `Composite`, `$Box`, `bool`, … , whereas `LaurelToCoreSchemaPass` lowers the
// wrapper straight to Core's polymorphic equality, which is what holds at every type. The
// generic signature is a resolution-time device and gives no such single definition —
// composites monomorphize per instantiation, poly type variables freshen per call site.
// `Synth.staticCall` additionally guards the operand SHAPES (`MultiValuedExpr`, `TVoid`) and
// phrases a type-argument conflict as `==`/`!=`, neither of which a signature can state.
procedure $eq<T>(x: T, y: T) : bool external;
procedure $neq<T>(x: T, y: T) : bool external;

// String
procedure $strConcat(x: string, y: string) : string external;

// Havoc the entire heap: a bodiless `opaque modifies *` procedure whose
// `modifies *` lets the heap change arbitrarily while its monotonic-counter
// postcondition still holds across the change. Emitted to model an arbitrary
// environment step on the heap.
procedure $havocHeap()
  opaque
  modifies *;

#end

/--
The core map operation definitions as a `Laurel.Program`, parsed at compile time.
-/
def coreDefinitionsForLaurel : Program :=
  match TransM.run
      (.file "Strata/Languages/Laurel/CoreDefinitionsForLaurel.lean")
      (parseProgram coreDefinitionsForLaurelDDM) (synthesized := true) with
  | .ok program => program
  | .error e => dbg_trace s!"BUG: CoreDefinitionsForLaurel parse error: {e}"; default

/--
The generic `Result<Val, Err>` datatype that the exceptional-channel lowering
targets. `EliminateExceptions` injects it into a program's types *only* when the
program uses exceptions (a `throws` procedure, a `throw`, or a call to a throwing
procedure), so a program that never throws does not carry it. It is a plain
datatype (free for SMT), so it does not perturb heap reasoning.
-/
def resultDefinitionsDDM :=
#strata
program Laurel;

datatype Result<Val, Err> {
  Good(value: Val),
  Bad(err: Err)
}

#end

/-- The `Result` datatype definition as a `Laurel.Program`, parsed at compile time. -/
def resultDefinitions : Program :=
  match TransM.run
      (.file "Strata/Languages/Laurel/CoreDefinitionsForLaurel.lean")
      (parseProgram resultDefinitionsDDM) (synthesized := true) with
  | .ok program => program
  | .error e => dbg_trace s!"BUG: resultDefinitions parse error: {e}"; default

/-- Whether the shared names in `LaurelAST` (`exnResultDatatypeName` and friends)
    still describe the datatype defined above.

    The definition is DDM source, so it cannot be built from those names; this
    checks the other direction instead. `EliminateExceptions` builds the encoding
    and `ModifiesClauses` consumes it, both through the shared names, so a rename
    in the source above that is not mirrored there would desync them — with no
    build failure, since every spelling is just a string.

    Pinned by a `#guard` in `StrataTest/.../UnitTests/ExceptionResultNamesTest.lean`
    rather than here: this module cannot evaluate it at elaboration time, because
    `resultDefinitions` runs the DDM parser, whose IR is not available to the
    interpreter while this library is still being compiled. -/
def resultDefinitionsMatchSharedNames : Bool :=
  match resultDefinitions.types.filterMap
      (fun t => match t with | .Datatype dt => some dt | _ => none) with
  | [dt] =>
      dt.name.text == exnResultDatatypeName
        && dt.constructors.map (fun c => c.name.text)
             == [exnResultGoodCtor, exnResultBadCtor]
        && dt.constructors.flatMap (fun c => c.args.map (fun a => a.name.text))
             == [exnResultValueField, exnResultErrField]
        -- The member names the passes use must be the ones resolution will
        -- generate for this datatype's own constructors and fields.
        && dt.constructors.map dt.testerName == [exnResultIsGood, exnResultIsBad]
        && dt.constructors.flatMap (fun c => c.args.map dt.destructorName)
             == [exnResultValue, exnResultErr]
  | _ => false

/-- The datatype's *own* names, labelled and in the order
    `resultDefinitionsMatchSharedNames` compares them.

    Exposed so a test can pin the concrete strings rather than only a single boolean.
    When a rename desyncs the DDM source above from the shared names in `LaurelAST`,
    a golden over this list names the aspect that moved; `#guard` on the boolean can
    only report that something did. -/
def resultDefinitionNames : List (String × String) :=
  match resultDefinitions.types.filterMap
      (fun t => match t with | .Datatype dt => some dt | _ => none) with
  | [dt] =>
      [ ("datatype",     dt.name.text),
        ("constructors", ", ".intercalate (dt.constructors.map (fun c => c.name.text))),
        ("fields",       ", ".intercalate
                           (dt.constructors.flatMap (fun c => c.args.map (fun a => a.name.text)))),
        ("testers",      ", ".intercalate (dt.constructors.map dt.testerName)),
        ("destructors",  ", ".intercalate
                           (dt.constructors.flatMap (fun c => c.args.map dt.destructorName))) ]
  | _ => [("error", "expected exactly one datatype in resultDefinitions")]

end -- public section

end Strata.Laurel
