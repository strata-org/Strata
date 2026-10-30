// Driver for the wire round trips in
// StrataTestExtra/Languages/Go/TestGen.lean. It constructs one value per case,
// marshals it with the generated runtime and writes `<label>.ion` into the
// directory named by argv[1]; the Lean side then decodes each file with
// `getIonDeserializer%` and compares against the Lean value it was built from.
//
// This is deliberately `package main` in a DIFFERENT Go package from the
// generated one: every type, field and helper it touches has to be exported for
// this file to compile, which is the reason the generator PascalCases
// everything. An in-package test could not establish that.
//
// The labels must match `roundTripChecks` in TestGen.lean. A label with no
// matching file is reported as a failure, so a typo cannot silently skip a case.
package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"math"
	"math/big"
	"os"
	"path/filepath"
	"strings"

	g "advtest/gotest"
)

var outDir string

// n is the integer constructor for every `Int`/`Nat` field below. Lean's `Int`
// and `Nat` are arbitrary precision, so the generated Go type is a *big.Int and
// not a machine integer; `IntLit` is the runtime's
// convenience wrapper for the overwhelmingly common small-literal case, and the
// point of having it is that these call sites read like literals.
func n(v int64) *big.Int { return g.IntLit(v) }

// bigLit is the runtime's ParseIntLit with the ok discarded, for literals this
// file knows are well formed. A front-end reading an integer out of source text
// holds a string, and a value past uint64 has no machine type to route through,
// so this is the only way to reach one.
func bigLit(s string) *big.Int {
	v, ok := g.ParseIntLit(s)
	if !ok {
		fmt.Fprintf(os.Stderr, "bad integer literal %q\n", s)
		os.Exit(1)
	}
	return v
}

// pow2 is 2^k, and neg flips a sign. Both exist so the "huge" case below can be
// written without a sixty-digit literal.
func pow2(k uint) *big.Int    { return new(big.Int).Lsh(big.NewInt(1), k) }
func neg(v *big.Int) *big.Int { return new(big.Int).Neg(v) }

// emit marshals v and writes it to <outDir>/<label>.ion.
func emit(label string, v g.ToIon) {
	b, err := g.MarshalBinary(v)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%s: MarshalBinary: %v\n", label, err)
		os.Exit(1)
	}
	if err := os.WriteFile(filepath.Join(outDir, label+".ion"), b, 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "%s: write: %v\n", label, err)
		os.Exit(1)
	}
}

func expectMarshalError(label string, v g.ToIon, want ...string) {
	defer func() {
		if recovered := recover(); recovered != nil {
			fmt.Fprintf(os.Stderr, "%s: MarshalBinary panicked: %v\n", label, recovered)
			os.Exit(1)
		}
	}()
	_, err := g.MarshalBinary(v)
	if err == nil {
		fmt.Fprintf(os.Stderr, "%s: MarshalBinary unexpectedly succeeded\n", label)
		os.Exit(1)
	}
	for _, part := range want {
		if !strings.Contains(err.Error(), part) {
			fmt.Fprintf(os.Stderr, "%s: error %q does not contain %q\n", label, err, part)
			os.Exit(1)
		}
	}
}

func checkGeneratedMarker() {
	f, err := parser.ParseFile(token.NewFileSet(), filepath.Join("gotest", "Leaves.go"), nil,
		parser.ParseComments)
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse generated file: %v\n", err)
		os.Exit(1)
	}
	if !ast.IsGenerated(f) {
		fmt.Fprintln(os.Stderr, "Go tooling did not recognize Leaves.go as generated")
		os.Exit(1)
	}
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: driver <output-dir>")
		os.Exit(2)
	}
	outDir = os.Args[1]
	checkGeneratedMarker()

	expectMarshalError("negative-nat", g.Leaves{
		Nat: n(-5), Int: n(0), Dec: g.Decimal{Mantissa: n(0)},
	}, "ion at nat", "negative Nat value -5")
	expectMarshalError("nil-interface-field", g.Nilable{},
		"ion at value", "cannot marshal a nil value")
	expectMarshalError("nil-interface-list-element", g.Nilable{
		Value: g.MExprLit{N: n(0)},
		Items: []g.MExpr{nil},
	}, "ion at items[0]", "cannot marshal a nil value")
	expectMarshalError("nil-interface-option-target", g.Nilable{
		Value: g.MExprLit{N: n(0)},
		Maybe: g.Opt[g.MExpr](nil),
	}, "ion at maybe", "cannot marshal a nil value")
	expectMarshalError("nil-type-parameter", g.Box[g.MExpr]{Value: nil},
		"ion at value", "cannot marshal a nil value")
	// No Lean type generates `Box[*Point]` (an `Option` type argument is refused),
	// but Go code can still spell it; a nil there is refused rather than encoded.
	expectMarshalError("nil-typed-pointer", g.Box[*g.Point]{Value: nil},
		"ion at value", "cannot marshal a nil value")

	// Ion keys `type`, `2x`, `a?b`, `ab`, `a"b`, `?`, `??` against the Go
	// identifiers the escape rules produced for them.
	emit("fields", g.Fields{Type: n(1), X2x: n(2), Ab: n(3), Ab_: n(4), Ab_2: n(5),
		Field: n(6), Field_: n(7)})
	// Every field explicitly zero: the zero VALUE of the struct is a nil *big.Int
	// in each slot, which MarshalBinary reports as an error rather than encoding
	// as 0. That is deliberate — an unset field is a bug, not a zero.
	emit("fields-zero", g.Fields{Type: n(0), X2x: n(0), Ab: n(0), Ab_: n(0),
		Ab_2: n(0), Field: n(0), Field_: n(0)})

	// Types escaped away from runtime names still carry their Lean field keys.
	emit("reserved", g.ReservedRoot{
		A: g.Decimal_{Dv: n(1)},
		B: g.Opt_{Ov: n(2)},
		C: g.MarshalBinary_{Mv: n(3)},
		D: g.ToIon_{Tv: n(4)},
		E: g.Type{Kv: n(5)},
		F: g.String{Sv: n(6)},
		G: g.Error{Ev: n(7)},
		H: g.Len{Lv: n(8)},
	})

	// A constructor struct renamed to dodge the runtime's IonWriter must still
	// emit the Lean tag `writer`.
	emit("ion-writer", g.IonWriter_{X: n(42)})
	emit("ion-other", g.IonOther{Y: n(7)})

	// Two Lean constructors folding to one Go name keep distinct Ion tags.
	emit("ctor-mycase", g.CollidingCtorsMyCase{X: n(1)})
	emit("ctor-my-case", g.CollidingCtorsMyCase_{Y: n(2)})

	// Container nesting, populated at every level.
	emit("nest-full", g.Nest{
		MaybeEach: []*string{g.Opt("a"), nil, g.Opt("")},
		DeepMix:   g.Opt([]*[]*big.Int{nil, g.Opt([]*big.Int{n(1), n(2)}), g.Opt([]*big.Int{})}),
		OptOpt:    g.Opt(g.Opt("x")),
		ListList:  [][]*big.Int{{n(1), n(-2)}, {}},
	})
	// `some none` versus `none`. These two differ in exactly one field and are
	// what an Option-guard variable that shadows its parent collapses together.
	emit("nest-some-none", g.Nest{OptOpt: g.Opt[*string](nil)})
	emit("nest-empty", g.Nest{})

	// Mutual recursion, traversed in both directions.
	emit("mexpr", g.MExprNeg{E: g.MExprFromStmt{S: g.MStmtSeq{L: []g.MStmt{
		g.MStmtExprStmt{E: g.MExprLit{N: n(-5)}},
		g.MStmtSeq{L: []g.MStmt{}},
	}}}})

	// Leaf boundaries at the 64-bit edges: uint64 max, int64 min, an astral-plane
	// codepoint and an embedded NUL, and a decimal whose exponent crosses the
	// VarInt 13-bit group. `UintLit` is what reaches math.MaxUint64 — it does not
	// fit in an int64, and it is exactly the bound a Go front-end needs in order
	// to describe Go's own uint64.
	emit("leaves-max", g.Leaves{
		Nat:  g.UintLit(math.MaxUint64),
		Int:  n(math.MinInt64),
		Flt:  0.5,
		Str:  "é\U0001d11e\x00z",
		Bool: true,
		Dec:  g.Decimal{Mantissa: big.NewInt(math.MinInt64), Exponent: -8192},
	})
	emit("leaves-zero", g.Leaves{
		Nat: n(0), Int: n(0), Dec: g.Decimal{Mantissa: big.NewInt(0), Exponent: 0},
	})

	// PAST the 64-bit edges. 2^64 and -(2^64) are the first values the old
	// uint64/int64 mapping could not express at all, and 2^200 is past any
	// machine width; Lean's Nat and Int are unbounded, so both are ordinary
	// values of the type being mirrored.
	emit("leaves-beyond-64", g.Leaves{
		Nat:  bigLit("18446744073709551616"),
		Int:  bigLit("-18446744073709551616"),
		Flt:  1.5,
		Str:  "beyond",
		Bool: false,
		Dec:  g.Decimal{Mantissa: bigLit("18446744073709551616"), Exponent: 3},
	})
	emit("leaves-huge", g.Leaves{
		Nat:  pow2(200),
		Int:  neg(pow2(200)),
		Flt:  -0.25,
		Str:  "huge",
		Bool: true,
		Dec:  g.Decimal{Mantissa: neg(pow2(200)), Exponent: -1},
	})

	// Positional `_0`/`_1`/`_2` keys rather than field names.
	emit("wrapper", g.Wrapper{Value: n(-1), Label: "hi", Flag: true})

	// A generic instantiation must be indistinguishable on the wire from the
	// equivalent monomorphic structure.
	emit("boxroot", g.BoxRoot{
		B:  g.Box[g.Point]{Value: g.Point{X: n(1), Y: n(2)}},
		Ob: g.Opt(g.Box[g.Point]{Value: g.Point{X: n(3), Y: n(4)}}),
		Lb: []g.Box[g.Point]{{Value: g.Point{X: n(5), Y: n(6)}}},
	})
	emit("boxroot-none", g.BoxRoot{B: g.Box[g.Point]{Value: g.Point{X: n(0), Y: n(0)}}})

	// A Lean field with a default value is an ordinary field in Go.
	emit("withdefault", g.WithDefault{Count: n(99), Label: "zz"})
}
