dialect Bool;

// BoolType for the type-level Bool
type BoolType;

// BoolLit category with a single operator that takes a Bool value
category BoolLit;
op boolLit (b : Bool) : BoolLit => b;

// Introduce basic Boolean operations.
fn not_expr (tp : Type, a : tp) : tp => "-" a;
fn and (a : BoolType, b : BoolType) : BoolType => @[prec(10), leftassoc] a " && " b;
fn or (a : BoolType, b : BoolType) : BoolType => @[prec(8), leftassoc] a " || " b;
fn imp (a : BoolType, b : BoolType) : BoolType => @[prec(8), leftassoc] a " ==> " b;

// Introduce equality operations that work for arbitrary types.
// The type is inferred.
fn equal (tp : Type, a : tp, b : tp) : BoolType => @[prec(15)] a " == " b;
fn not_equal (tp : Type, a : tp, b : tp) : BoolType => @[prec(15)] a " != " b;
