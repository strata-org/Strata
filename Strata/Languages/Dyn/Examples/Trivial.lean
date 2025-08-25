/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn
import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def TrivialPgm :=
#strata
program Dyn;

def trivial (x : Any) -> Any
{
  return int_to_Any(0);
}

#end

/--
info: #[{ name := { dialect := "Dyn", name := "function_def" },
    args :=
      ((((Array.mkEmpty 4).push (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                (Arg.ident "trivial")).push
            (Arg.op
              { name := { dialect := "Dyn", name := "mkParams" },
                args :=
                  (Array.mkEmpty 1).push
                    (Arg.commaSepList
                      ((Array.mkEmpty 1).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "mkParam" },
                            args :=
                              ((Array.mkEmpty 2).push (Arg.ident "x")).push
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
                                  ((Expr.fn { dialect := "Dyn", name := "to_int" }).app (Arg.num 0))))) }))) }) }]
-/
#guard_msgs in
#eval TrivialPgm.commands

end Dyn
end Strata
