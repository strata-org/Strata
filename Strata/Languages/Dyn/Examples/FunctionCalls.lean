/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def FunctionCallsPgm :=
#strata
program Dyn;

def test_fun (dummy : Any) -> Any
{
  return int_to_Any(0);
}

def test_fun_as_val (dummy : Any) -> Any
{
  var my_fun : Any;

  return call(my_fun, int_to_Any(20));
}

def apply_twice(f: Any, arg: Any) -> Any
{
  return call(f, call(f, arg));
}

def test_apply_twice(dummy : Any) -> Any
{
  var x : Any;
  x = int_to_Any(0);
  return call(fun_to_Any(apply_twice), test_fun, x);
}

#end

/--
info: #[{ name := { dialect := "Dyn", name := "function_def" },
    args :=
      ((((Array.mkEmpty 4).push (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                (Arg.ident "test_fun")).push
            (Arg.op
              { name := { dialect := "Dyn", name := "mkParams" },
                args :=
                  (Array.mkEmpty 1).push
                    (Arg.commaSepList
                      ((Array.mkEmpty 1).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "mkParam" },
                            args :=
                              ((Array.mkEmpty 2).push (Arg.ident "dummy")).push
                                (Arg.type
                                  (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0))) }))) })).push
        (Arg.op
          { name := { dialect := "Dyn", name := "block" },
            args :=
              (Array.mkEmpty 1).push
                (Arg.seq
                  ((Array.mkEmpty 1).push
                    (Arg.op
                      { name := { dialect := "Dyn", name := "return_stmt" },
                        args :=
                          ((Array.mkEmpty 2).push
                                (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                            (Arg.expr
                              ((Expr.fn { dialect := "Dyn", name := "int_to_Any" }).app
                                (Arg.expr
                                  ((Expr.fn { dialect := "Dyn", name := "to_int" }).app (Arg.num 0))))) }))) }) },
  { name := { dialect := "Dyn", name := "function_def" },
    args :=
      ((((Array.mkEmpty 4).push (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                (Arg.ident "test_fun_as_val")).push
            (Arg.op
              { name := { dialect := "Dyn", name := "mkParams" },
                args :=
                  (Array.mkEmpty 1).push
                    (Arg.commaSepList
                      ((Array.mkEmpty 1).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "mkParam" },
                            args :=
                              ((Array.mkEmpty 2).push (Arg.ident "dummy")).push
                                (Arg.type
                                  (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0))) }))) })).push
        (Arg.op
          { name := { dialect := "Dyn", name := "block" },
            args :=
              (Array.mkEmpty 1).push
                (Arg.seq
                  (((Array.mkEmpty 2).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "var_decl" },
                            args :=
                              ((Array.mkEmpty 2).push (Arg.ident "my_fun")).push
                                (Arg.type
                                  (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0))) })).push
                    (Arg.op
                      { name := { dialect := "Dyn", name := "return_stmt" },
                        args :=
                          ((Array.mkEmpty 2).push
                                (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                            (Arg.expr
                              (((Expr.fn { dialect := "Dyn", name := "func_call" }).app (Arg.expr (Expr.bvar 0))).app
                                (Arg.commaSepList
                                  ((Array.mkEmpty 1).push
                                    (Arg.expr
                                      ((Expr.fn { dialect := "Dyn", name := "int_to_Any" }).app
                                        (Arg.expr
                                          ((Expr.fn { dialect := "Dyn", name := "to_int" }).app
                                            (Arg.num 20))))))))) }))) }) },
  { name := { dialect := "Dyn", name := "function_def" },
    args :=
      ((((Array.mkEmpty 4).push (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                (Arg.ident "apply_twice")).push
            (Arg.op
              { name := { dialect := "Dyn", name := "mkParams" },
                args :=
                  (Array.mkEmpty 1).push
                    (Arg.commaSepList
                      (((Array.mkEmpty 2).push
                            (Arg.op
                              { name := { dialect := "Dyn", name := "mkParam" },
                                args :=
                                  ((Array.mkEmpty 2).push (Arg.ident "f")).push
                                    (Arg.type
                                      (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0))) })).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "mkParam" },
                            args :=
                              ((Array.mkEmpty 2).push (Arg.ident "arg")).push
                                (Arg.type
                                  (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0))) }))) })).push
        (Arg.op
          { name := { dialect := "Dyn", name := "block" },
            args :=
              (Array.mkEmpty 1).push
                (Arg.seq
                  ((Array.mkEmpty 1).push
                    (Arg.op
                      { name := { dialect := "Dyn", name := "return_stmt" },
                        args :=
                          ((Array.mkEmpty 2).push
                                (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                            (Arg.expr
                              (((Expr.fn { dialect := "Dyn", name := "func_call" }).app (Arg.expr (Expr.bvar 1))).app
                                (Arg.commaSepList
                                  ((Array.mkEmpty 1).push
                                    (Arg.expr
                                      (((Expr.fn { dialect := "Dyn", name := "func_call" }).app
                                            (Arg.expr (Expr.bvar 1))).app
                                        (Arg.commaSepList
                                          ((Array.mkEmpty 1).push (Arg.expr (Expr.bvar 0)))))))))) }))) }) },
  { name := { dialect := "Dyn", name := "function_def" },
    args :=
      ((((Array.mkEmpty 4).push (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                (Arg.ident "test_apply_twice")).push
            (Arg.op
              { name := { dialect := "Dyn", name := "mkParams" },
                args :=
                  (Array.mkEmpty 1).push
                    (Arg.commaSepList
                      ((Array.mkEmpty 1).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "mkParam" },
                            args :=
                              ((Array.mkEmpty 2).push (Arg.ident "dummy")).push
                                (Arg.type
                                  (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0))) }))) })).push
        (Arg.op
          { name := { dialect := "Dyn", name := "block" },
            args :=
              (Array.mkEmpty 1).push
                (Arg.seq
                  ((((Array.mkEmpty 3).push
                            (Arg.op
                              { name := { dialect := "Dyn", name := "var_decl" },
                                args :=
                                  ((Array.mkEmpty 2).push (Arg.ident "x")).push
                                    (Arg.type
                                      (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0))) })).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "assign" },
                            args :=
                              (((Array.mkEmpty 3).push
                                        (Arg.type
                                          (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                                    (Arg.ident "x")).push
                                (Arg.expr
                                  ((Expr.fn { dialect := "Dyn", name := "int_to_Any" }).app
                                    (Arg.expr
                                      ((Expr.fn { dialect := "Dyn", name := "to_int" }).app (Arg.num 0))))) })).push
                    (Arg.op
                      { name := { dialect := "Dyn", name := "return_stmt" },
                        args :=
                          ((Array.mkEmpty 2).push
                                (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                            (Arg.expr
                              (((Expr.fn { dialect := "Dyn", name := "func_call" }).app
                                    (Arg.expr
                                      ((Expr.fn { dialect := "Dyn", name := "fun_to_Any" }).app
                                        (Arg.expr (Expr.fvar 2))))).app
                                (Arg.commaSepList
                                  (((Array.mkEmpty 2).push (Arg.expr (Expr.fvar 0))).push
                                    (Arg.expr (Expr.bvar 0)))))) }))) }) }]
-/
#guard_msgs in
#eval FunctionCallsPgm.commands

end Dyn
end Strata

-- my_fun = test_fun;
