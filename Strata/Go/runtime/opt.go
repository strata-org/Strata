package ___placeholder___

// Opt returns a pointer to v.
//
// Generated code represents a Lean Option field as a Go pointer. Go cannot
// take the address of a literal or function result, so Opt(expr) keeps
// construction sites concise.
func Opt[T any](v T) *T {
	return &v
}
