dialect Bool;

// Bool type for use in function signatures
type Bool;

// BoolLit category with two operators (for parsing true/false literals)
category BoolLit;
op boolTrue : BoolLit => "true";
op boolFalse : BoolLit => "false";

// Introduce basic Boolean operations.
fn not_expr (tp : Type, a : tp) : tp => "-" a;
fn and (a : Bool, b : Bool) : Bool => @[prec(10), leftassoc] a " && " b;
fn or (a : Bool, b : Bool) : Bool => @[prec(8), leftassoc] a " || " b;
fn imp (a : Bool, b : Bool) : Bool => @[prec(8), leftassoc] a " ==> " b;

// Introduce equality operations that work for arbitrary types.
// The type is inferred.
fn equal (tp : Type, a : tp, b : tp) : Bool => @[prec(15)] a " == " b;
fn not_equal (tp : Type, a : tp, b : tp) : Bool => @[prec(15)] a " != " b;
