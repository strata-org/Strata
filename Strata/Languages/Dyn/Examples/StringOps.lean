/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def StringOpsPgm :=
#strata
program Dyn;

def test_strings (dummy : Any) -> Any
{
  var greeting : Any;
  greeting = str_to_Any("Hello");
  return greeting;
}

#end

/--
info: #[{ name := { dialect := "Dyn", name := "function_def" },
    args :=
      ((((Array.mkEmpty 4).push (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                (Arg.ident "test_strings")).push
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
                                  ((Array.mkEmpty 2).push (Arg.ident "greeting")).push
                                    (Arg.type
                                      (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0))) })).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "assign" },
                            args :=
                              (((Array.mkEmpty 3).push
                                        (Arg.type
                                          (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                                    (Arg.ident "greeting")).push
                                (Arg.expr
                                  ((Expr.fn { dialect := "Dyn", name := "str_to_Any" }).app
                                    (Arg.expr
                                      ((Expr.fn { dialect := "Dyn", name := "strLit" }).app
                                        (Arg.strlit "Hello"))))) })).push
                    (Arg.op
                      { name := { dialect := "Dyn", name := "return_stmt" },
                        args :=
                          ((Array.mkEmpty 2).push
                                (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                            (Arg.expr (Expr.bvar 0)) }))) }) }]
-/
#guard_msgs in
#eval StringOpsPgm.commands

end Dyn
end Strata
