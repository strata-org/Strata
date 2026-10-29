// Driver for the Laurel end-to-end case: a Go program that builds a non-trivial
// `Laurel.LaurelProgram` with the generated types, marshals it to Ion, and leaves it
// for Lean's `readLaurelIonProgram` to decode and verify.
//
// This is the point of the whole Go backend, so it is written the way a real Go
// front-end would have to write it: `package main` importing the generated
// package, touching only exported names, with no access to the generator.
//
// It writes two programs into argv[1]:
//
//	laurel-good.ion    verifies cleanly
//	laurel-bad.ion     the same procedure with an unprovable assert
//	laurel-bigint.ion  the same procedure asserting over integer literals that
//	                   fit in no machine integer type
//
// The Laurel source both are meant to be equal to is in TestGen.lean, which
// parses it and compares the concrete syntax of the two ASTs. Keep the two in
// step: a change here without the matching change there is a test failure, which
// is the intended coupling.
package main

import (
	"fmt"
	"os"
	"path/filepath"

	l "e2e/laurel"
)

// badAssertStart and badAssertStop are the source range stamped on the failing
// assert in laurel-bad.ion. The Lean side requires the diagnostic to be reported
// at that position; distinctive offsets that appear nowhere else make that
// checkable, and they prove source provenance survives Go -> Ion -> Lean rather
// than being re-derived on the Lean side.
const (
	badAssertStart = 4242
	badAssertStop  = 4250
)

// goSourceURI is what the diagnostics should attribute the program to: the Go
// program is the producer, so it names itself.
const goSourceURI = "<go-front-end>"

// A Lean `Nat`/`Int` field is a *big.Int, because Lean's integers are arbitrary
// precision. `UintLit` and `IntLit` are the runtime's
// convenience constructors for values that do fit in a machine integer, which is
// every byte offset and nearly every literal a front-end emits.
func rangeAt(start, stop uint64) l.FileRange {
	return l.FileRange{
		File: l.Uri{Path: goSourceURI},
		Range: l.SourceRange{
			Start: l.Raw{ByteIdx: l.UintLit(start)},
			Stop:  l.Raw{ByteIdx: l.UintLit(stop)},
		},
	}
}

func fr() l.FileRange { return rangeAt(0, 0) }

func id(name string) l.Identifier { return l.Identifier{Text: name, Source: fr()} }

func ex(x l.StmtExpr) l.AstNode[l.StmtExpr] {
	return l.AstNode[l.StmtExpr]{Val: x, Source: fr()}
}

func exAt(x l.StmtExpr, start, stop uint64) l.AstNode[l.StmtExpr] {
	return l.AstNode[l.StmtExpr]{Val: x, Source: rangeAt(start, stop)}
}

func ty(x l.HighType) l.AstNode[l.HighType] {
	return l.AstNode[l.HighType]{Val: x, Source: fr()}
}

func vr(x l.Variable) l.AstNode[l.Variable] {
	return l.AstNode[l.Variable]{Val: x, Source: fr()}
}

// local reads a local variable; lit is an integer literal.
func local(name string) l.StmtExpr { return l.StmtExprVar{Var: l.VariableLocal{Name: id(name)}} }
func lit(n int64) l.StmtExpr       { return l.StmtExprLiteralInt{Value: l.IntLit(n)} }

// bigLit is an integer literal that fits in no machine integer type, which is
// the reason `StmtExprLiteralInt.Value` is a *big.Int: `LiteralInt` carries a
// Lean `Int`, and a front-end that cannot write 18446744073709551615 cannot
// state the upper bound of a constrained type for Go's own uint64.
func bigLit(s string) l.StmtExpr {
	v, ok := l.ParseIntLit(s)
	if !ok {
		fmt.Fprintf(os.Stderr, "bad integer literal %q\n", s)
		os.Exit(1)
	}
	return l.StmtExprLiteralInt{Value: v}
}

// op builds one of Laurel's built-in operator wrappers. Laurel has no separate
// binary-operator node: `x + y` is a StaticCall to `$add` (Operation.procName),
// and the pretty-printer turns it back into infix syntax.
func op(wrapper string, args ...l.AstNode[l.StmtExpr]) l.StmtExpr {
	return l.StmtExprStaticCall{Callee: id(wrapper), Arguments: args}
}

// sumTo builds
//
//	procedure sumTo(n: int): int
//	  requires n >= 0
//	{
//	  var i: int := 0;
//	  while (i < n) invariant i <= n { i := i + 1 };
//	  <finalAssert>;
//	  return i
//	}
//
// `$result` is the output name the short `: T` return form mints
// (`Laurel.resultOutputName`), so a hand-built AST has to use it too.
func sumTo(finalAssert l.AstNode[l.StmtExpr]) l.Procedure {
	tInt := ty(l.HighTypeTInt{})

	declareI := ex(l.StmtExprAssign{
		Targets: []l.AstNode[l.Variable]{vr(l.VariableDeclare{
			Parameter: l.ParameterOpt{Name: id("i"), Type: l.Opt(tInt)},
		})},
		Value: ex(lit(0)),
	})

	loop := ex(l.StmtExprWhile{
		Cond:       ex(op("$lt", ex(local("i")), ex(local("n")))),
		Invariants: []l.AstNode[l.StmtExpr]{ex(op("$le", ex(local("i")), ex(local("n"))))},
		Body: ex(l.StmtExprBlock{Statements: []l.AstNode[l.StmtExpr]{
			ex(l.StmtExprAssign{
				Targets: []l.AstNode[l.Variable]{vr(l.VariableLocal{Name: id("i")})},
				Value:   ex(op("$add", ex(local("i")), ex(lit(1)))),
			}),
		}}),
	})

	return l.Procedure{
		Name:    id("sumTo"),
		Inputs:  []l.Parameter{{Name: id("n"), Type: tInt}},
		Outputs: []l.Parameter{{Name: id("$result"), Type: tInt}},
		Preconditions: []l.Condition{{
			Condition: ex(op("$ge", ex(local("n")), ex(lit(0)))),
			Mode:      l.ConditionModeBoth{},
		}},
		Contracts: l.CoroutineContractsRegular{},
		// Opaque, not transparent: Laurel rejects a loop in a transparent body
		// ("loops are not YET supported in transparent bodies or contracts"), so a
		// `while` can only be reached through `Body.Opaque`. A hand-built AST has
		// to know that; it is not discoverable from the Go types.
		Body: l.BodyOpaque{Implementation: l.Opt(ex(l.StmtExprBlock{
			Statements: []l.AstNode[l.StmtExpr]{
				declareI,
				loop,
				finalAssert,
				ex(l.StmtExprReturn{Value: l.Opt(ex(local("i")))}),
			},
		}))},
	}
}

func emit(dir, name string, p l.LaurelProgram) {
	b, err := l.MarshalBinary(p)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%s: MarshalBinary: %v\n", name, err)
		os.Exit(1)
	}
	if err := os.WriteFile(filepath.Join(dir, name), b, 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "%s: write: %v\n", name, err)
		os.Exit(1)
	}
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: laurel-driver <output-dir>")
		os.Exit(2)
	}
	dir := os.Args[1]

	// `assert i == n` follows from the invariant `i <= n` plus the negated loop
	// condition `i >= n`, so this verifies.
	good := ex(l.StmtExprAssert{
		Condition: ex(op("$eq", ex(local("i")), ex(local("n")))),
	})

	// `assert i == n + 1` does not, and the diagnostic must land on the range
	// stamped here rather than on the enclosing block or on nothing.
	bad := exAt(l.StmtExprAssert{
		Condition: ex(op("$eq", ex(local("i")),
			ex(op("$add", ex(local("n")), ex(lit(1)))))),
	}, badAssertStart, badAssertStop)

	// `assert 18446744073709551615 <= 18446744073709551616`: math.MaxUint64 — the
	// bound a Go front-end needs for Go's own uint64 — against 2^64, which does
	// not even fit there. Neither was expressible when `Int` mapped to int64, so
	// this is the case the *big.Int mapping exists for. Lean decodes it; the
	// numerals have to come back out of `readLaurelIonProgram` intact.
	bigAssert := ex(l.StmtExprAssert{
		Condition: ex(op("$le",
			ex(bigLit("18446744073709551615")),
			ex(bigLit("18446744073709551616")))),
	})

	emit(dir, "laurel-good.ion", l.LaurelProgram{StaticProcedures: []l.Procedure{sumTo(good)}})
	emit(dir, "laurel-bad.ion", l.LaurelProgram{StaticProcedures: []l.Procedure{sumTo(bad)}})
	emit(dir, "laurel-bigint.ion",
		l.LaurelProgram{StaticProcedures: []l.Procedure{sumTo(bigAssert)}})
}
