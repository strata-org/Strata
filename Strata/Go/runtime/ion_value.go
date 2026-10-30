package ___placeholder___

import (
	"fmt"
	"math"
	"math/big"
	"unicode/utf8"

	ion "github.com/amazon-ion/ion-go/ion"
)

// IonWriter is the ion-go writer used by generated MarshalIon methods.
type IonWriter = ion.Writer

// ToIon is kept as the generated type-parameter constraint and public adapter
// name. It is exactly ion.Marshaler, so generated values can also be passed
// directly to ion-go APIs.
type ToIon = ion.Marshaler

// Decimal mirrors StrataDDM.Decimal within ion-go's supported exponent range.
// Mantissa remains arbitrary precision; ion-go represents decimal exponents as
// int32.
type Decimal struct {
	Mantissa *big.Int
	Exponent int32
}

// IntLit returns v as an arbitrary-precision integer suitable for an Int or Nat
// field.
func IntLit(v int64) *big.Int {
	return big.NewInt(v)
}

// UintLit returns v as an arbitrary-precision integer suitable for an Int or
// Nat field.
func UintLit(v uint64) *big.Int {
	return new(big.Int).SetUint64(v)
}

// ParseIntLit parses a base-ten arbitrary-precision integer.
func ParseIntLit(s string) (*big.Int, bool) {
	return new(big.Int).SetString(s, 10)
}

func writeBigInt(w IonWriter, v *big.Int) error {
	if v == nil {
		return fmt.Errorf("nil *big.Int")
	}
	return w.WriteBigInt(v)
}

func writeNat(w IonWriter, v *big.Int) error {
	if v == nil {
		return fmt.Errorf("nil *big.Int")
	}
	if v.Sign() < 0 {
		return fmt.Errorf("negative Nat value %s", v)
	}
	return w.WriteBigInt(v)
}

func writeString(w IonWriter, v string) error {
	if !utf8.ValidString(v) {
		return fmt.Errorf("invalid UTF-8 string")
	}
	return w.WriteString(v)
}

func writeDecimal(w IonWriter, v Decimal) error {
	if v.Mantissa == nil {
		return fmt.Errorf("nil decimal mantissa")
	}
	// ion.NewDecimal stores -Exponent in an int32. MinInt32 cannot be negated
	// in that representation and would silently wrap.
	if v.Exponent == math.MinInt32 {
		return fmt.Errorf("decimal exponent %d is unsupported by ion-go", v.Exponent)
	}
	return w.WriteDecimal(ion.NewDecimal(v.Mantissa, v.Exponent, false))
}

func fieldName(w IonWriter, name string) error {
	if !utf8.ValidString(name) {
		return fmt.Errorf("invalid UTF-8 field name")
	}
	return w.FieldName(ion.NewSymbolTokenFromString(name))
}

func writeSymbol(w IonWriter, symbol string) error {
	if !utf8.ValidString(symbol) {
		return fmt.Errorf("invalid UTF-8 symbol")
	}
	return w.WriteSymbolFromString(symbol)
}

func atPath(err error, path string) error {
	if err == nil {
		return nil
	}
	if path == "" {
		return err
	}
	return fmt.Errorf("ion at %s: %w", path, err)
}

func indexPath(path string, index int) string {
	return fmt.Sprintf("%s[%d]", path, index)
}

func sexpPath(name string, index int) string {
	return fmt.Sprintf("%s(%d)", name, index)
}
