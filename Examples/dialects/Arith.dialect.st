dialect Arith;
import Bool;

type Int;
fn neg_expr (a : Int) : Int => "- " a;
fn add_expr (a : Int, b : Int) : Int => @[prec(25), leftassoc] a " + " b;
fn sub_expr (a : Int, b : Int) : Int => @[prec(25), leftassoc] a " - " b;
fn mul_expr (a : Int, b : Int) : Int => @[prec(30), leftassoc] a " * " b;
fn exp_expr (a : Int, b : Int) : Int => @[prec(32), rightassoc] a " ^ " b;

fn le (a : Int, b : Int) : Bool => @[prec(15)] a " <= " b;
fn lt (a : Int, b : Int) : Bool => @[prec(15)] a " < " b;
fn ge (a : Int, b : Int) : Bool => @[prec(15)] a " >= " b;
fn gt (a : Int, b : Int) : Bool => @[prec(15)] a " > " b;
