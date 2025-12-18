dialect PipeIdent;

// Test dialect for pipe-delimited identifiers (SMT-LIB/Boogie syntax)

category Expression;

// Variable reference using pipe-delimited identifiers
op var (name : Ident) : Expression => name;

// Assignment statement
op assign (lhs : Ident, rhs : Expression) : Command => lhs " := " rhs ";";

// Binary operations
op add (a : Expression, b : Expression) : Expression => @[prec(10), leftassoc] a " + " b;
op or (a : Expression, b : Expression) : Expression => @[prec(5), leftassoc] a " || " b;
op bitwiseOr (a : Expression, b : Expression) : Expression => @[prec(6), leftassoc] a " | " b;

// Integer literal
op intLit (n : Num) : Expression => n;
