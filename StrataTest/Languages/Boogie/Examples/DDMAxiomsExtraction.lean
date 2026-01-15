/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

-- Example Boogie program with axioms
def examplePgm :=
#strata
program Core;
type k;
type v;
axiom [updateSelect]: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv;
axiom [updatePreserves]: forall m: Map k v, okk: k, kk: k, vv: v :: m[kk := vv][okk] == m[okk];
#end

/--
  This function extracts the Boogie.Decl in the given program that are axiom declarations
-/
def extractAxiomsDecl (prg: Core.Program) : (List Core.Decl) :=
  let rec loop (acc: List Core.Decl) (l: List Core.Decl): List Core.Decl :=
    match l with
      | [] => acc
      | hd :: tl =>
          match hd with
          | .ax _ _ => loop (acc ++ [hd]) tl
          | _ => loop acc tl
  loop [] prg.decls

/--
  Extract the body LExpr from the axiom declaration
-/
def extractExpr (axDecl: Core.Decl): Core.Expression.Expr :=
  match axDecl with
    | .ax a _ => a.e
    | _ => panic "Can be called only on axiom declaration"

/--
  Transform the given type into "ftvar name"
  - if it is of form LMonoTy.tcons name []
  - AND if name is in to_replace
-/
def transformSimpleTypeToFreeVariable (ty: Lambda.LMonoTy) (to_replace: List String): Lambda.LMonoTy :=
  match ty with
    | (.tcons name []) =>
      if name ∈ to_replace
      then
        .ftvar name
      else
        ty
    | .tcons name args => .tcons name (args.map (fun ar => transformSimpleTypeToFreeVariable ar to_replace))
    | _ => ty

/--
  Transform all occurences of types of the form LMonoTy.tcons name [] into ftvar name, if name is in to_replace
  in the given expression
-/
def replaceTypesByFTV (expr: Core.Expression.Expr) (to_replace: List String): Core.Expression.Expr :=
  match expr with
    | .const m c => .const m c
    | .op m o oty => .op m o (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace))
    | .fvar m name oty => .fvar m name (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace))
    | .bvar m i => .bvar m i
    | .abs m oty e => .abs m (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace)) (replaceTypesByFTV e to_replace)
    | .quant m k oty tr e => .quant m k (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace)) (replaceTypesByFTV tr to_replace) (replaceTypesByFTV e to_replace)
    | .app m fn e => .app m (replaceTypesByFTV fn to_replace) (replaceTypesByFTV e to_replace)
    | .ite m c t e => .ite m (replaceTypesByFTV c to_replace) (replaceTypesByFTV t to_replace) (replaceTypesByFTV e to_replace)
    | .eq m e1 e2 => .eq m (replaceTypesByFTV e1 to_replace) (replaceTypesByFTV e2 to_replace)

/--
  Extract all axioms from the given environment by first translating it into a Boogie Program.
  It then extracts LExpr body from the axioms, and replace all occurences of the typeArgs by a ftvar with the same name
-/
def extractAxiomsWithFreeTypeVars (pgm: Program) (typeArgs: List String): (List Core.Expression.Expr) :=
  let prg: Core.Program := (TransM.run Inhabited.default (translateProgram pgm)).fst
  let axiomsDecls := extractAxiomsDecl prg
  let axioms := axiomsDecls.map extractExpr
  axioms.map (fun a => replaceTypesByFTV a typeArgs)

/--
info: program Core;
type k;
type v;
axiom [updateSelect]:forall(((m):(Map v k)),((kk):(k))),((vv):(v))::((m)[kk:=vv])[kk]==vv;
axiom [updatePreserves]:forall((((m):(Map v k)),((okk):(k))),((kk):(k))),((vv):(v))::((m)[kk:=vv])[okk]==(m)[okk];
-/
#guard_msgs in
#eval IO.println examplePgm.format.render

/--
info: #[{ ann := { start := { byteIdx := 293 }, stop := { byteIdx := 300 } },
    name := { dialect := "Core", name := "command_typedecl" },
    args :=
      ((Array.mkEmpty 2).push (ArgF.ident { start := { byteIdx := 298 }, stop := { byteIdx := 299 } } "k")).push
        (ArgF.option { start := { byteIdx := 299 }, stop := { byteIdx := 299 } } none) },
  { ann := { start := { byteIdx := 301 }, stop := { byteIdx := 308 } },
    name := { dialect := "Core", name := "command_typedecl" },
    args :=
      ((Array.mkEmpty 2).push (ArgF.ident { start := { byteIdx := 306 }, stop := { byteIdx := 307 } } "v")).push
        (ArgF.option { start := { byteIdx := 307 }, stop := { byteIdx := 307 } } none) },
  { ann := { start := { byteIdx := 309 }, stop := { byteIdx := 388 } },
    name := { dialect := "Core", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (ArgF.option { start := { byteIdx := 315 }, stop := { byteIdx := 330 } }
              (some
                (ArgF.op
                  { ann := { start := { byteIdx := 315 }, stop := { byteIdx := 330 } },
                    name := { dialect := "Core", name := "label" },
                    args :=
                      (Array.mkEmpty 1).push
                        (ArgF.ident { start := { byteIdx := 316 }, stop := { byteIdx := 328 } }
                          "updateSelect") })))).push
        (ArgF.expr
          (ExprF.app { start := { byteIdx := 331 }, stop := { byteIdx := 387 } }
            (ExprF.app { start := { byteIdx := 331 }, stop := { byteIdx := 387 } }
              (ExprF.fn { start := { byteIdx := 331 }, stop := { byteIdx := 387 } }
                { dialect := "Core", name := "forall" })
              (ArgF.op
                { ann := { start := { byteIdx := 338 }, stop := { byteIdx := 362 } },
                  name := { dialect := "Core", name := "declPush" },
                  args :=
                    ((Array.mkEmpty 2).push
                          (ArgF.op
                            { ann := { start := { byteIdx := 338 }, stop := { byteIdx := 355 } },
                              name := { dialect := "Core", name := "declPush" },
                              args :=
                                ((Array.mkEmpty 2).push
                                      (ArgF.op
                                        { ann := { start := { byteIdx := 338 }, stop := { byteIdx := 348 } },
                                          name := { dialect := "Core", name := "declAtom" },
                                          args :=
                                            (Array.mkEmpty 1).push
                                              (ArgF.op
                                                { ann := { start := { byteIdx := 338 }, stop := { byteIdx := 348 } },
                                                  name := { dialect := "Core", name := "bind_mk" },
                                                  args :=
                                                    (((Array.mkEmpty 3).push
                                                              (ArgF.ident
                                                                { start := { byteIdx := 338 },
                                                                  stop := { byteIdx := 339 } }
                                                                "m")).push
                                                          (ArgF.option
                                                            { start := { byteIdx := 341 }, stop := { byteIdx := 341 } }
                                                            none)).push
                                                      (ArgF.type
                                                        (TypeExprF.ident
                                                          { start := { byteIdx := 341 }, stop := { byteIdx := 344 } }
                                                          { dialect := "Core", name := "Map" }
                                                          (((Array.mkEmpty 2).push
                                                                (TypeExprF.fvar
                                                                  { start := { byteIdx := 347 },
                                                                    stop := { byteIdx := 348 } }
                                                                  1 (Array.mkEmpty 0))).push
                                                            (TypeExprF.fvar
                                                              { start := { byteIdx := 345 },
                                                                stop := { byteIdx := 346 } }
                                                              0 (Array.mkEmpty 0))))) }) })).push
                                  (ArgF.op
                                    { ann := { start := { byteIdx := 350 }, stop := { byteIdx := 355 } },
                                      name := { dialect := "Core", name := "bind_mk" },
                                      args :=
                                        (((Array.mkEmpty 3).push
                                                  (ArgF.ident
                                                    { start := { byteIdx := 350 }, stop := { byteIdx := 352 } }
                                                    "kk")).push
                                              (ArgF.option { start := { byteIdx := 354 }, stop := { byteIdx := 354 } }
                                                none)).push
                                          (ArgF.type
                                            (TypeExprF.fvar { start := { byteIdx := 354 }, stop := { byteIdx := 355 } }
                                              0 (Array.mkEmpty 0))) }) })).push
                      (ArgF.op
                        { ann := { start := { byteIdx := 357 }, stop := { byteIdx := 362 } },
                          name := { dialect := "Core", name := "bind_mk" },
                          args :=
                            (((Array.mkEmpty 3).push
                                      (ArgF.ident { start := { byteIdx := 357 }, stop := { byteIdx := 359 } }
                                        "vv")).push
                                  (ArgF.option { start := { byteIdx := 361 }, stop := { byteIdx := 361 } } none)).push
                              (ArgF.type
                                (TypeExprF.fvar { start := { byteIdx := 361 }, stop := { byteIdx := 362 } } 1
                                  (Array.mkEmpty 0))) }) }))
            (ArgF.expr
              (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 387 } }
                (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 387 } }
                  (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 387 } }
                    (ExprF.fn { start := { byteIdx := 366 }, stop := { byteIdx := 387 } }
                      { dialect := "Core", name := "equal" })
                    (ArgF.type
                      (TypeExprF.fvar { start := { byteIdx := 347 }, stop := { byteIdx := 348 } } 1 (Array.mkEmpty 0))))
                  (ArgF.expr
                    (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 381 } }
                      (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 381 } }
                        (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 381 } }
                          (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 381 } }
                            (ExprF.fn { start := { byteIdx := 366 }, stop := { byteIdx := 381 } }
                              { dialect := "Core", name := "map_get" })
                            (ArgF.type
                              (TypeExprF.fvar { start := { byteIdx := 345 }, stop := { byteIdx := 346 } } 0
                                (Array.mkEmpty 0))))
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 347 }, stop := { byteIdx := 348 } } 1
                              (Array.mkEmpty 0))))
                        (ArgF.expr
                          (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 377 } }
                            (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 377 } }
                              (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 377 } }
                                (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 377 } }
                                  (ExprF.app { start := { byteIdx := 366 }, stop := { byteIdx := 377 } }
                                    (ExprF.fn { start := { byteIdx := 366 }, stop := { byteIdx := 377 } }
                                      { dialect := "Core", name := "map_set" })
                                    (ArgF.type
                                      (TypeExprF.fvar { start := { byteIdx := 345 }, stop := { byteIdx := 346 } } 0
                                        (Array.mkEmpty 0))))
                                  (ArgF.type
                                    (TypeExprF.fvar { start := { byteIdx := 347 }, stop := { byteIdx := 348 } } 1
                                      (Array.mkEmpty 0))))
                                (ArgF.expr (ExprF.bvar { start := { byteIdx := 366 }, stop := { byteIdx := 367 } } 2)))
                              (ArgF.expr (ExprF.bvar { start := { byteIdx := 368 }, stop := { byteIdx := 370 } } 1)))
                            (ArgF.expr (ExprF.bvar { start := { byteIdx := 374 }, stop := { byteIdx := 376 } } 0)))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 378 }, stop := { byteIdx := 380 } } 1)))))
                (ArgF.expr (ExprF.bvar { start := { byteIdx := 385 }, stop := { byteIdx := 387 } } 0)))))) },
  { ann := { start := { byteIdx := 389 }, stop := { byteIdx := 484 } },
    name := { dialect := "Core", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (ArgF.option { start := { byteIdx := 395 }, stop := { byteIdx := 413 } }
              (some
                (ArgF.op
                  { ann := { start := { byteIdx := 395 }, stop := { byteIdx := 413 } },
                    name := { dialect := "Core", name := "label" },
                    args :=
                      (Array.mkEmpty 1).push
                        (ArgF.ident { start := { byteIdx := 396 }, stop := { byteIdx := 411 } }
                          "updatePreserves") })))).push
        (ArgF.expr
          (ExprF.app { start := { byteIdx := 414 }, stop := { byteIdx := 483 } }
            (ExprF.app { start := { byteIdx := 414 }, stop := { byteIdx := 483 } }
              (ExprF.fn { start := { byteIdx := 414 }, stop := { byteIdx := 483 } }
                { dialect := "Core", name := "forall" })
              (ArgF.op
                { ann := { start := { byteIdx := 421 }, stop := { byteIdx := 453 } },
                  name := { dialect := "Core", name := "declPush" },
                  args :=
                    ((Array.mkEmpty 2).push
                          (ArgF.op
                            { ann := { start := { byteIdx := 421 }, stop := { byteIdx := 446 } },
                              name := { dialect := "Core", name := "declPush" },
                              args :=
                                ((Array.mkEmpty 2).push
                                      (ArgF.op
                                        { ann := { start := { byteIdx := 421 }, stop := { byteIdx := 439 } },
                                          name := { dialect := "Core", name := "declPush" },
                                          args :=
                                            ((Array.mkEmpty 2).push
                                                  (ArgF.op
                                                    {
                                                      ann :=
                                                        { start := { byteIdx := 421 }, stop := { byteIdx := 431 } },
                                                      name := { dialect := "Core", name := "declAtom" },
                                                      args :=
                                                        (Array.mkEmpty 1).push
                                                          (ArgF.op
                                                            {
                                                              ann :=
                                                                { start := { byteIdx := 421 },
                                                                  stop := { byteIdx := 431 } },
                                                              name := { dialect := "Core", name := "bind_mk" },
                                                              args :=
                                                                (((Array.mkEmpty 3).push
                                                                          (ArgF.ident
                                                                            { start := { byteIdx := 421 },
                                                                              stop := { byteIdx := 422 } }
                                                                            "m")).push
                                                                      (ArgF.option
                                                                        { start := { byteIdx := 424 },
                                                                          stop := { byteIdx := 424 } }
                                                                        none)).push
                                                                  (ArgF.type
                                                                    (TypeExprF.ident
                                                                      { start := { byteIdx := 424 },
                                                                        stop := { byteIdx := 427 } }
                                                                      { dialect := "Core", name := "Map" }
                                                                      (((Array.mkEmpty 2).push
                                                                            (TypeExprF.fvar
                                                                              { start := { byteIdx := 430 },
                                                                                stop := { byteIdx := 431 } }
                                                                              1 (Array.mkEmpty 0))).push
                                                                        (TypeExprF.fvar
                                                                          { start := { byteIdx := 428 },
                                                                            stop := { byteIdx := 429 } }
                                                                          0 (Array.mkEmpty 0))))) }) })).push
                                              (ArgF.op
                                                { ann := { start := { byteIdx := 433 }, stop := { byteIdx := 439 } },
                                                  name := { dialect := "Core", name := "bind_mk" },
                                                  args :=
                                                    (((Array.mkEmpty 3).push
                                                              (ArgF.ident
                                                                { start := { byteIdx := 433 },
                                                                  stop := { byteIdx := 436 } }
                                                                "okk")).push
                                                          (ArgF.option
                                                            { start := { byteIdx := 438 }, stop := { byteIdx := 438 } }
                                                            none)).push
                                                      (ArgF.type
                                                        (TypeExprF.fvar
                                                          { start := { byteIdx := 438 }, stop := { byteIdx := 439 } } 0
                                                          (Array.mkEmpty 0))) }) })).push
                                  (ArgF.op
                                    { ann := { start := { byteIdx := 441 }, stop := { byteIdx := 446 } },
                                      name := { dialect := "Core", name := "bind_mk" },
                                      args :=
                                        (((Array.mkEmpty 3).push
                                                  (ArgF.ident
                                                    { start := { byteIdx := 441 }, stop := { byteIdx := 443 } }
                                                    "kk")).push
                                              (ArgF.option { start := { byteIdx := 445 }, stop := { byteIdx := 445 } }
                                                none)).push
                                          (ArgF.type
                                            (TypeExprF.fvar { start := { byteIdx := 445 }, stop := { byteIdx := 446 } }
                                              0 (Array.mkEmpty 0))) }) })).push
                      (ArgF.op
                        { ann := { start := { byteIdx := 448 }, stop := { byteIdx := 453 } },
                          name := { dialect := "Core", name := "bind_mk" },
                          args :=
                            (((Array.mkEmpty 3).push
                                      (ArgF.ident { start := { byteIdx := 448 }, stop := { byteIdx := 450 } }
                                        "vv")).push
                                  (ArgF.option { start := { byteIdx := 452 }, stop := { byteIdx := 452 } } none)).push
                              (ArgF.type
                                (TypeExprF.fvar { start := { byteIdx := 452 }, stop := { byteIdx := 453 } } 1
                                  (Array.mkEmpty 0))) }) }))
            (ArgF.expr
              (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 483 } }
                (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 483 } }
                  (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 483 } }
                    (ExprF.fn { start := { byteIdx := 457 }, stop := { byteIdx := 483 } }
                      { dialect := "Core", name := "equal" })
                    (ArgF.type
                      (TypeExprF.fvar { start := { byteIdx := 430 }, stop := { byteIdx := 431 } } 1 (Array.mkEmpty 0))))
                  (ArgF.expr
                    (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 473 } }
                      (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 473 } }
                        (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 473 } }
                          (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 473 } }
                            (ExprF.fn { start := { byteIdx := 457 }, stop := { byteIdx := 473 } }
                              { dialect := "Core", name := "map_get" })
                            (ArgF.type
                              (TypeExprF.fvar { start := { byteIdx := 428 }, stop := { byteIdx := 429 } } 0
                                (Array.mkEmpty 0))))
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 430 }, stop := { byteIdx := 431 } } 1
                              (Array.mkEmpty 0))))
                        (ArgF.expr
                          (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 468 } }
                            (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 468 } }
                              (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 468 } }
                                (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 468 } }
                                  (ExprF.app { start := { byteIdx := 457 }, stop := { byteIdx := 468 } }
                                    (ExprF.fn { start := { byteIdx := 457 }, stop := { byteIdx := 468 } }
                                      { dialect := "Core", name := "map_set" })
                                    (ArgF.type
                                      (TypeExprF.fvar { start := { byteIdx := 428 }, stop := { byteIdx := 429 } } 0
                                        (Array.mkEmpty 0))))
                                  (ArgF.type
                                    (TypeExprF.fvar { start := { byteIdx := 430 }, stop := { byteIdx := 431 } } 1
                                      (Array.mkEmpty 0))))
                                (ArgF.expr (ExprF.bvar { start := { byteIdx := 457 }, stop := { byteIdx := 458 } } 3)))
                              (ArgF.expr (ExprF.bvar { start := { byteIdx := 459 }, stop := { byteIdx := 461 } } 1)))
                            (ArgF.expr (ExprF.bvar { start := { byteIdx := 465 }, stop := { byteIdx := 467 } } 0)))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 469 }, stop := { byteIdx := 472 } } 2)))))
                (ArgF.expr
                  (ExprF.app { start := { byteIdx := 477 }, stop := { byteIdx := 483 } }
                    (ExprF.app { start := { byteIdx := 477 }, stop := { byteIdx := 483 } }
                      (ExprF.app { start := { byteIdx := 477 }, stop := { byteIdx := 483 } }
                        (ExprF.app { start := { byteIdx := 477 }, stop := { byteIdx := 483 } }
                          (ExprF.fn { start := { byteIdx := 477 }, stop := { byteIdx := 483 } }
                            { dialect := "Core", name := "map_get" })
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 428 }, stop := { byteIdx := 429 } } 0
                              (Array.mkEmpty 0))))
                        (ArgF.type
                          (TypeExprF.fvar { start := { byteIdx := 430 }, stop := { byteIdx := 431 } } 1
                            (Array.mkEmpty 0))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 477 }, stop := { byteIdx := 478 } } 3)))
                    (ArgF.expr (ExprF.bvar { start := { byteIdx := 479 }, stop := { byteIdx := 482 } } 2)))))))) }]
-/
#guard_msgs in
#eval examplePgm.commands

/--
info: [LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.tcons
   "Map"
   [Lambda.LMonoTy.ftvar "k",
    Lambda.LMonoTy.ftvar
      "v"]) (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.ftvar
   "k") (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.ftvar
   "v") (LExpr.bvar () 0) (LExpr.eq () (LExpr.app () (LExpr.app () (LExpr.op () { name := "select",
   metadata := Core.Visibility.unres } (some Lambda.LMonoTy.tcons
   "arrow"
   [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
    Lambda.LMonoTy.tcons
      "arrow"
      [Lambda.LMonoTy.ftvar "k",
       Lambda.LMonoTy.ftvar
         "v"]])) (LExpr.app () (LExpr.app () (LExpr.app () (LExpr.op () { name := "update",
   metadata := Core.Visibility.unres } (some Lambda.LMonoTy.tcons
   "arrow"
   [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
    Lambda.LMonoTy.tcons
      "arrow"
      [Lambda.LMonoTy.ftvar "k",
       Lambda.LMonoTy.tcons
         "arrow"
         [Lambda.LMonoTy.ftvar "v",
          Lambda.LMonoTy.tcons
            "Map"
            [Lambda.LMonoTy.ftvar "k",
             Lambda.LMonoTy.ftvar
               "v"]]]])) (LExpr.bvar () 2)) (LExpr.bvar () 1)) (LExpr.bvar () 0))) (LExpr.bvar () 1)) (LExpr.bvar () 0)))),
 LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.tcons
   "Map"
   [Lambda.LMonoTy.ftvar "k",
    Lambda.LMonoTy.ftvar
      "v"]) (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.ftvar
   "k") (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.ftvar
   "k") (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.ftvar
   "v") (LExpr.bvar () 0) (LExpr.eq () (LExpr.app () (LExpr.app () (LExpr.op () { name := "select",
   metadata := Core.Visibility.unres } (some Lambda.LMonoTy.tcons
   "arrow"
   [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
    Lambda.LMonoTy.tcons
      "arrow"
      [Lambda.LMonoTy.ftvar "k",
       Lambda.LMonoTy.ftvar
         "v"]])) (LExpr.app () (LExpr.app () (LExpr.app () (LExpr.op () { name := "update",
   metadata := Core.Visibility.unres } (some Lambda.LMonoTy.tcons
   "arrow"
   [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
    Lambda.LMonoTy.tcons
      "arrow"
      [Lambda.LMonoTy.ftvar "k",
       Lambda.LMonoTy.tcons
         "arrow"
         [Lambda.LMonoTy.ftvar "v",
          Lambda.LMonoTy.tcons
            "Map"
            [Lambda.LMonoTy.ftvar "k",
             Lambda.LMonoTy.ftvar
               "v"]]]])) (LExpr.bvar () 3)) (LExpr.bvar () 1)) (LExpr.bvar () 0))) (LExpr.bvar () 2)) (LExpr.app () (LExpr.app () (LExpr.op () { name := "select",
   metadata := Core.Visibility.unres } (some Lambda.LMonoTy.tcons
   "arrow"
   [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
    Lambda.LMonoTy.tcons
      "arrow"
      [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"]])) (LExpr.bvar () 3)) (LExpr.bvar () 2))))))]
-/
#guard_msgs in
#eval
  extractAxiomsWithFreeTypeVars examplePgm ["k", "v"]
