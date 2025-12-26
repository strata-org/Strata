dialect Bool;

// BoolType for use in function signatures
type BoolType;

// Function to lift Init.Bool literals to expressions
fn boolLit (b : Bool) : BoolType => b;

// Introduce basic Boolean operations.
fn not_expr (tp : Type, a : tp) : tp => "-" a;
fn and (a : BoolType, b : BoolType) : BoolType => @[prec(10), leftassoc] a " && " b;
fn or (a : BoolType, b : BoolType) : BoolType => @[prec(8), leftassoc] a " || " b;
fn imp (a : BoolType, b : BoolType) : BoolType => @[prec(8), leftassoc] a " ==> " b;

// Introduce equality operations that work for arbitrary types.
// The type is inferred.
fn equal (tp : Type, a : tp, b : tp) : BoolType => @[prec(15)] a " == " b;
fn not_equal (tp : Type, a : tp, b : tp) : BoolType => @[prec(15)] a " != " b;
