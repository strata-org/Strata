package ___placeholder___

import (
	"bytes"
	"errors"
	"reflect"

	ion "github.com/amazon-ion/ion-go/ion"
)

var errNilValue = errors.New("cannot marshal a nil value")

func isNilIonMarshaler(v ToIon) bool {
	if v == nil {
		return true
	}
	rv := reflect.ValueOf(v)
	switch rv.Kind() {
	case reflect.Chan, reflect.Func, reflect.Interface, reflect.Map, reflect.Ptr, reflect.Slice:
		return rv.IsNil()
	default:
		return false
	}
}

// MarshalBinary serializes v as an Ion binary datagram using ion-go.
func MarshalBinary(v ToIon) ([]byte, error) {
	if isNilIonMarshaler(v) {
		return nil, errNilValue
	}

	var out bytes.Buffer
	w := ion.NewBinaryWriter(&out)
	if err := v.MarshalIon(w); err != nil {
		return nil, err
	}
	if err := w.Finish(); err != nil {
		return nil, err
	}
	return out.Bytes(), nil
}
