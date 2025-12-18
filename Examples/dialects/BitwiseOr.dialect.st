dialect BitwiseOr;

// Dialect that uses | as a bitwise OR operator
// This tests that pipe-delimited identifiers still work when | is an operator

category Expression;

op var (name : Ident) : Expression => name;
op intLit (n : Num) : Expression => n;

// Single | as bitwise OR operator
op bitwiseOr (a : Expression, b : Expression) : Expression => @[prec(5), leftassoc] a " | " b;

// Assignment
op assign (lhs : Ident, rhs : Expression) : Command => lhs " := " rhs ";";
