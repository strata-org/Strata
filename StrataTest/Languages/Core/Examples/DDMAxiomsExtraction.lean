/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

-- Example Strata Core program with axioms
def examplePgm :=
#strata
program Core;
type k;
type v;
axiom [updateSelect]: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv;
axiom [updatePreserves]: forall m: Map k v, okk: k, kk: k, vv: v :: m[kk := vv][okk] == m[okk];
#end

/--
  This function extracts the Core.Decl in the given program that are axiom declarations
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
  Extract all axioms from the given environment by first translating it into a Strata Core Program.
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
axiom [updateSelect]:forall((m:(Map v k)),(kk:k)),(vv:v)::(m[kk:=vv])[kk]==vv;
axiom [updatePreserves]:forall(((m:(Map v k)),(okk:k)),(kk:k)),(vv:v)::(m[kk:=vv])[okk]==m[okk];
-/
#guard_msgs in
#eval IO.println examplePgm

/--
info: #[{ ann := { start := { byteIdx := 296 }, stop := { byteIdx := 303 } },
    name := { dialect := "Core", name := "command_typedecl" },
    args :=
      ((Array.mkEmpty 2).push (ArgF.ident { start := { byteIdx := 301 }, stop := { byteIdx := 302 } } "k")).push
        (ArgF.option { start := { byteIdx := 302 }, stop := { byteIdx := 302 } } none) },
  { ann := { start := { byteIdx := 304 }, stop := { byteIdx := 311 } },
    name := { dialect := "Core", name := "command_typedecl" },
    args :=
      ((Array.mkEmpty 2).push (ArgF.ident { start := { byteIdx := 309 }, stop := { byteIdx := 310 } } "v")).push
        (ArgF.option { start := { byteIdx := 310 }, stop := { byteIdx := 310 } } none) },
  { ann := { start := { byteIdx := 312 }, stop := { byteIdx := 391 } },
    name := { dialect := "Core", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (ArgF.option { start := { byteIdx := 318 }, stop := { byteIdx := 333 } }
              (some
                (ArgF.op
                  { ann := { start := { byteIdx := 318 }, stop := { byteIdx := 333 } },
                    name := { dialect := "Core", name := "label" },
                    args :=
                      (Array.mkEmpty 1).push
                        (ArgF.ident { start := { byteIdx := 319 }, stop := { byteIdx := 331 } }
                          "updateSelect") })))).push
        (ArgF.expr
          (ExprF.app { start := { byteIdx := 334 }, stop := { byteIdx := 390 } }
            (ExprF.app { start := { byteIdx := 334 }, stop := { byteIdx := 390 } }
              (ExprF.fn { start := { byteIdx := 334 }, stop := { byteIdx := 390 } }
                { dialect := "Core", name := "forall" })
              (ArgF.op
                { ann := { start := { byteIdx := 341 }, stop := { byteIdx := 365 } },
                  name := { dialect := "Core", name := "declPush" },
                  args :=
                    ((Array.mkEmpty 2).push
                          (ArgF.op
                            { ann := { start := { byteIdx := 341 }, stop := { byteIdx := 358 } },
                              name := { dialect := "Core", name := "declPush" },
                              args :=
                                ((Array.mkEmpty 2).push
                                      (ArgF.op
                                        { ann := { start := { byteIdx := 341 }, stop := { byteIdx := 351 } },
                                          name := { dialect := "Core", name := "declAtom" },
                                          args :=
                                            (Array.mkEmpty 1).push
                                              (ArgF.op
                                                { ann := { start := { byteIdx := 341 }, stop := { byteIdx := 351 } },
                                                  name := { dialect := "Core", name := "bind_mk" },
                                                  args :=
                                                    (((Array.mkEmpty 3).push
                                                              (ArgF.ident
                                                                { start := { byteIdx := 341 },
                                                                  stop := { byteIdx := 342 } }
                                                                "m")).push
                                                          (ArgF.option
                                                            { start := { byteIdx := 344 }, stop := { byteIdx := 344 } }
                                                            none)).push
                                                      (ArgF.type
                                                        (TypeExprF.ident
                                                          { start := { byteIdx := 344 }, stop := { byteIdx := 347 } }
                                                          { dialect := "Core", name := "Map" }
                                                          (((Array.mkEmpty 2).push
                                                                (TypeExprF.fvar
                                                                  { start := { byteIdx := 350 },
                                                                    stop := { byteIdx := 351 } }
                                                                  1 (Array.mkEmpty 0))).push
                                                            (TypeExprF.fvar
                                                              { start := { byteIdx := 348 },
                                                                stop := { byteIdx := 349 } }
                                                              0 (Array.mkEmpty 0))))) }) })).push
                                  (ArgF.op
                                    { ann := { start := { byteIdx := 353 }, stop := { byteIdx := 358 } },
                                      name := { dialect := "Core", name := "bind_mk" },
                                      args :=
                                        (((Array.mkEmpty 3).push
                                                  (ArgF.ident
                                                    { start := { byteIdx := 353 }, stop := { byteIdx := 355 } }
                                                    "kk")).push
                                              (ArgF.option { start := { byteIdx := 357 }, stop := { byteIdx := 357 } }
                                                none)).push
                                          (ArgF.type
                                            (TypeExprF.fvar { start := { byteIdx := 357 }, stop := { byteIdx := 358 } }
                                              0 (Array.mkEmpty 0))) }) })).push
                      (ArgF.op
                        { ann := { start := { byteIdx := 360 }, stop := { byteIdx := 365 } },
                          name := { dialect := "Core", name := "bind_mk" },
                          args :=
                            (((Array.mkEmpty 3).push
                                      (ArgF.ident { start := { byteIdx := 360 }, stop := { byteIdx := 362 } }
                                        "vv")).push
                                  (ArgF.option { start := { byteIdx := 364 }, stop := { byteIdx := 364 } } none)).push
                              (ArgF.type
                                (TypeExprF.fvar { start := { byteIdx := 364 }, stop := { byteIdx := 365 } } 1
                                  (Array.mkEmpty 0))) }) }))
            (ArgF.expr
              (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 390 } }
                (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 390 } }
                  (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 390 } }
                    (ExprF.fn { start := { byteIdx := 369 }, stop := { byteIdx := 390 } }
                      { dialect := "Core", name := "equal" })
                    (ArgF.type
                      (TypeExprF.fvar { start := { byteIdx := 350 }, stop := { byteIdx := 351 } } 1 (Array.mkEmpty 0))))
                  (ArgF.expr
                    (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 384 } }
                      (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 384 } }
                        (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 384 } }
                          (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 384 } }
                            (ExprF.fn { start := { byteIdx := 369 }, stop := { byteIdx := 384 } }
                              { dialect := "Core", name := "map_get" })
                            (ArgF.type
                              (TypeExprF.fvar { start := { byteIdx := 348 }, stop := { byteIdx := 349 } } 0
                                (Array.mkEmpty 0))))
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 350 }, stop := { byteIdx := 351 } } 1
                              (Array.mkEmpty 0))))
                        (ArgF.expr
                          (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 380 } }
                            (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 380 } }
                              (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 380 } }
                                (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 380 } }
                                  (ExprF.app { start := { byteIdx := 369 }, stop := { byteIdx := 380 } }
                                    (ExprF.fn { start := { byteIdx := 369 }, stop := { byteIdx := 380 } }
                                      { dialect := "Core", name := "map_set" })
                                    (ArgF.type
                                      (TypeExprF.fvar { start := { byteIdx := 348 }, stop := { byteIdx := 349 } } 0
                                        (Array.mkEmpty 0))))
                                  (ArgF.type
                                    (TypeExprF.fvar { start := { byteIdx := 350 }, stop := { byteIdx := 351 } } 1
                                      (Array.mkEmpty 0))))
                                (ArgF.expr (ExprF.bvar { start := { byteIdx := 369 }, stop := { byteIdx := 370 } } 2)))
                              (ArgF.expr (ExprF.bvar { start := { byteIdx := 371 }, stop := { byteIdx := 373 } } 1)))
                            (ArgF.expr (ExprF.bvar { start := { byteIdx := 377 }, stop := { byteIdx := 379 } } 0)))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 381 }, stop := { byteIdx := 383 } } 1)))))
                (ArgF.expr (ExprF.bvar { start := { byteIdx := 388 }, stop := { byteIdx := 390 } } 0)))))) },
  { ann := { start := { byteIdx := 392 }, stop := { byteIdx := 487 } },
    name := { dialect := "Core", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (ArgF.option { start := { byteIdx := 398 }, stop := { byteIdx := 416 } }
              (some
                (ArgF.op
                  { ann := { start := { byteIdx := 398 }, stop := { byteIdx := 416 } },
                    name := { dialect := "Core", name := "label" },
                    args :=
                      (Array.mkEmpty 1).push
                        (ArgF.ident { start := { byteIdx := 399 }, stop := { byteIdx := 414 } }
                          "updatePreserves") })))).push
        (ArgF.expr
          (ExprF.app { start := { byteIdx := 417 }, stop := { byteIdx := 486 } }
            (ExprF.app { start := { byteIdx := 417 }, stop := { byteIdx := 486 } }
              (ExprF.fn { start := { byteIdx := 417 }, stop := { byteIdx := 486 } }
                { dialect := "Core", name := "forall" })
              (ArgF.op
                { ann := { start := { byteIdx := 424 }, stop := { byteIdx := 456 } },
                  name := { dialect := "Core", name := "declPush" },
                  args :=
                    ((Array.mkEmpty 2).push
                          (ArgF.op
                            { ann := { start := { byteIdx := 424 }, stop := { byteIdx := 449 } },
                              name := { dialect := "Core", name := "declPush" },
                              args :=
                                ((Array.mkEmpty 2).push
                                      (ArgF.op
                                        { ann := { start := { byteIdx := 424 }, stop := { byteIdx := 442 } },
                                          name := { dialect := "Core", name := "declPush" },
                                          args :=
                                            ((Array.mkEmpty 2).push
                                                  (ArgF.op
                                                    {
                                                      ann :=
                                                        { start := { byteIdx := 424 }, stop := { byteIdx := 434 } },
                                                      name := { dialect := "Core", name := "declAtom" },
                                                      args :=
                                                        (Array.mkEmpty 1).push
                                                          (ArgF.op
                                                            {
                                                              ann :=
                                                                { start := { byteIdx := 424 },
                                                                  stop := { byteIdx := 434 } },
                                                              name := { dialect := "Core", name := "bind_mk" },
                                                              args :=
                                                                (((Array.mkEmpty 3).push
                                                                          (ArgF.ident
                                                                            { start := { byteIdx := 424 },
                                                                              stop := { byteIdx := 425 } }
                                                                            "m")).push
                                                                      (ArgF.option
                                                                        { start := { byteIdx := 427 },
                                                                          stop := { byteIdx := 427 } }
                                                                        none)).push
                                                                  (ArgF.type
                                                                    (TypeExprF.ident
                                                                      { start := { byteIdx := 427 },
                                                                        stop := { byteIdx := 430 } }
                                                                      { dialect := "Core", name := "Map" }
                                                                      (((Array.mkEmpty 2).push
                                                                            (TypeExprF.fvar
                                                                              { start := { byteIdx := 433 },
                                                                                stop := { byteIdx := 434 } }
                                                                              1 (Array.mkEmpty 0))).push
                                                                        (TypeExprF.fvar
                                                                          { start := { byteIdx := 431 },
                                                                            stop := { byteIdx := 432 } }
                                                                          0 (Array.mkEmpty 0))))) }) })).push
                                              (ArgF.op
                                                { ann := { start := { byteIdx := 436 }, stop := { byteIdx := 442 } },
                                                  name := { dialect := "Core", name := "bind_mk" },
                                                  args :=
                                                    (((Array.mkEmpty 3).push
                                                              (ArgF.ident
                                                                { start := { byteIdx := 436 },
                                                                  stop := { byteIdx := 439 } }
                                                                "okk")).push
                                                          (ArgF.option
                                                            { start := { byteIdx := 441 }, stop := { byteIdx := 441 } }
                                                            none)).push
                                                      (ArgF.type
                                                        (TypeExprF.fvar
                                                          { start := { byteIdx := 441 }, stop := { byteIdx := 442 } } 0
                                                          (Array.mkEmpty 0))) }) })).push
                                  (ArgF.op
                                    { ann := { start := { byteIdx := 444 }, stop := { byteIdx := 449 } },
                                      name := { dialect := "Core", name := "bind_mk" },
                                      args :=
                                        (((Array.mkEmpty 3).push
                                                  (ArgF.ident
                                                    { start := { byteIdx := 444 }, stop := { byteIdx := 446 } }
                                                    "kk")).push
                                              (ArgF.option { start := { byteIdx := 448 }, stop := { byteIdx := 448 } }
                                                none)).push
                                          (ArgF.type
                                            (TypeExprF.fvar { start := { byteIdx := 448 }, stop := { byteIdx := 449 } }
                                              0 (Array.mkEmpty 0))) }) })).push
                      (ArgF.op
                        { ann := { start := { byteIdx := 451 }, stop := { byteIdx := 456 } },
                          name := { dialect := "Core", name := "bind_mk" },
                          args :=
                            (((Array.mkEmpty 3).push
                                      (ArgF.ident { start := { byteIdx := 451 }, stop := { byteIdx := 453 } }
                                        "vv")).push
                                  (ArgF.option { start := { byteIdx := 455 }, stop := { byteIdx := 455 } } none)).push
                              (ArgF.type
                                (TypeExprF.fvar { start := { byteIdx := 455 }, stop := { byteIdx := 456 } } 1
                                  (Array.mkEmpty 0))) }) }))
            (ArgF.expr
              (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 486 } }
                (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 486 } }
                  (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 486 } }
                    (ExprF.fn { start := { byteIdx := 460 }, stop := { byteIdx := 486 } }
                      { dialect := "Core", name := "equal" })
                    (ArgF.type
                      (TypeExprF.fvar { start := { byteIdx := 433 }, stop := { byteIdx := 434 } } 1 (Array.mkEmpty 0))))
                  (ArgF.expr
                    (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 476 } }
                      (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 476 } }
                        (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 476 } }
                          (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 476 } }
                            (ExprF.fn { start := { byteIdx := 460 }, stop := { byteIdx := 476 } }
                              { dialect := "Core", name := "map_get" })
                            (ArgF.type
                              (TypeExprF.fvar { start := { byteIdx := 431 }, stop := { byteIdx := 432 } } 0
                                (Array.mkEmpty 0))))
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 433 }, stop := { byteIdx := 434 } } 1
                              (Array.mkEmpty 0))))
                        (ArgF.expr
                          (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 471 } }
                            (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 471 } }
                              (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 471 } }
                                (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 471 } }
                                  (ExprF.app { start := { byteIdx := 460 }, stop := { byteIdx := 471 } }
                                    (ExprF.fn { start := { byteIdx := 460 }, stop := { byteIdx := 471 } }
                                      { dialect := "Core", name := "map_set" })
                                    (ArgF.type
                                      (TypeExprF.fvar { start := { byteIdx := 431 }, stop := { byteIdx := 432 } } 0
                                        (Array.mkEmpty 0))))
                                  (ArgF.type
                                    (TypeExprF.fvar { start := { byteIdx := 433 }, stop := { byteIdx := 434 } } 1
                                      (Array.mkEmpty 0))))
                                (ArgF.expr (ExprF.bvar { start := { byteIdx := 460 }, stop := { byteIdx := 461 } } 3)))
                              (ArgF.expr (ExprF.bvar { start := { byteIdx := 462 }, stop := { byteIdx := 464 } } 1)))
                            (ArgF.expr (ExprF.bvar { start := { byteIdx := 468 }, stop := { byteIdx := 470 } } 0)))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 472 }, stop := { byteIdx := 475 } } 2)))))
                (ArgF.expr
                  (ExprF.app { start := { byteIdx := 480 }, stop := { byteIdx := 486 } }
                    (ExprF.app { start := { byteIdx := 480 }, stop := { byteIdx := 486 } }
                      (ExprF.app { start := { byteIdx := 480 }, stop := { byteIdx := 486 } }
                        (ExprF.app { start := { byteIdx := 480 }, stop := { byteIdx := 486 } }
                          (ExprF.fn { start := { byteIdx := 480 }, stop := { byteIdx := 486 } }
                            { dialect := "Core", name := "map_get" })
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 431 }, stop := { byteIdx := 432 } } 0
                              (Array.mkEmpty 0))))
                        (ArgF.type
                          (TypeExprF.fvar { start := { byteIdx := 433 }, stop := { byteIdx := 434 } } 1
                            (Array.mkEmpty 0))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 480 }, stop := { byteIdx := 481 } } 3)))
                    (ArgF.expr (ExprF.bvar { start := { byteIdx := 482 }, stop := { byteIdx := 485 } } 2)))))))) }]
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
