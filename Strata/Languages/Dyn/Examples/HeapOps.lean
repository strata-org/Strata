/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def HeapOpsPgm :=
#strata
program Dyn;

def test_heap_ops (dummy : Any) -> Any
{
  var p : Any;
  p = alloc();
  var success : Any;
  success = write(p, int_to_Any(5));
  var x : Any;
  x = read(p);
  success = free(p);
  return success and bool_to_Any((x == int_to_Any(5)));
}

#end

/--
info: #[{ name := { dialect := "Dyn", name := "function_def" },
    args :=
      ((((Array.mkEmpty 4).push (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                (Arg.ident "test_heap_ops")).push
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
                  (((((((((Array.mkEmpty 8).push
                                                (Arg.op
                                                  { name := { dialect := "Dyn", name := "var_decl" },
                                                    args :=
                                                      ((Array.mkEmpty 2).push (Arg.ident "p")).push
                                                        (Arg.type
                                                          (TypeExpr.ident { dialect := "Dyn", name := "Any" }
                                                            (Array.mkEmpty 0))) })).push
                                            (Arg.op
                                              { name := { dialect := "Dyn", name := "assign" },
                                                args :=
                                                  (((Array.mkEmpty 3).push
                                                            (Arg.type
                                                              (TypeExpr.ident { dialect := "Dyn", name := "Any" }
                                                                (Array.mkEmpty 0)))).push
                                                        (Arg.ident "p")).push
                                                    (Arg.expr
                                                      (Expr.fn { dialect := "Dyn", name := "heap_alloc" })) })).push
                                        (Arg.op
                                          { name := { dialect := "Dyn", name := "var_decl" },
                                            args :=
                                              ((Array.mkEmpty 2).push (Arg.ident "success")).push
                                                (Arg.type
                                                  (TypeExpr.ident { dialect := "Dyn", name := "Any" }
                                                    (Array.mkEmpty 0))) })).push
                                    (Arg.op
                                      { name := { dialect := "Dyn", name := "assign" },
                                        args :=
                                          (((Array.mkEmpty 3).push
                                                    (Arg.type
                                                      (TypeExpr.ident { dialect := "Dyn", name := "Any" }
                                                        (Array.mkEmpty 0)))).push
                                                (Arg.ident "success")).push
                                            (Arg.expr
                                              (((Expr.fn { dialect := "Dyn", name := "heap_write" }).app
                                                    (Arg.expr (Expr.bvar 1))).app
                                                (Arg.expr
                                                  ((Expr.fn { dialect := "Dyn", name := "int_to_Any" }).app
                                                    (Arg.expr
                                                      ((Expr.fn { dialect := "Dyn", name := "to_int" }).app
                                                        (Arg.num 5))))))) })).push
                                (Arg.op
                                  { name := { dialect := "Dyn", name := "var_decl" },
                                    args :=
                                      ((Array.mkEmpty 2).push (Arg.ident "x")).push
                                        (Arg.type
                                          (TypeExpr.ident { dialect := "Dyn", name := "Any" }
                                            (Array.mkEmpty 0))) })).push
                            (Arg.op
                              { name := { dialect := "Dyn", name := "assign" },
                                args :=
                                  (((Array.mkEmpty 3).push
                                            (Arg.type
                                              (TypeExpr.ident { dialect := "Dyn", name := "Any" }
                                                (Array.mkEmpty 0)))).push
                                        (Arg.ident "x")).push
                                    (Arg.expr
                                      ((Expr.fn { dialect := "Dyn", name := "heap_read" }).app
                                        (Arg.expr (Expr.bvar 2)))) })).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "assign" },
                            args :=
                              (((Array.mkEmpty 3).push
                                        (Arg.type
                                          (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                                    (Arg.ident "success")).push
                                (Arg.expr
                                  ((Expr.fn { dialect := "Dyn", name := "heap_free" }).app
                                    (Arg.expr (Expr.bvar 2)))) })).push
                    (Arg.op
                      { name := { dialect := "Dyn", name := "return_stmt" },
                        args :=
                          ((Array.mkEmpty 2).push
                                (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                            (Arg.expr
                              (((Expr.fn { dialect := "Dyn", name := "and" }).app (Arg.expr (Expr.bvar 1))).app
                                (Arg.expr
                                  ((Expr.fn { dialect := "Dyn", name := "bool_to_Any" }).app
                                    (Arg.expr
                                      (((Expr.fn { dialect := "Dyn", name := "eq" }).app (Arg.expr (Expr.bvar 0))).app
                                        (Arg.expr
                                          ((Expr.fn { dialect := "Dyn", name := "int_to_Any" }).app
                                            (Arg.expr
                                              ((Expr.fn { dialect := "Dyn", name := "to_int" }).app
                                                (Arg.num 5))))))))))) }))) }) }]
-/
#guard_msgs in
#eval HeapOpsPgm.commands

end Dyn
end Strata
