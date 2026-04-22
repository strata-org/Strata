/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


module
meta import Strata.Languages.Core.Verifier


meta section

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
    | .abs m name oty e => .abs m name (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace)) (replaceTypesByFTV e to_replace)
    | .quant m k name oty tr e => .quant m k name (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace)) (replaceTypesByFTV tr to_replace) (replaceTypesByFTV e to_replace)
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
axiom [updateSelect]: forall m : (Map v k), kk : k, vv : v :: (m[kk:=vv])[kk] == vv;
axiom [updatePreserves]: forall m : (Map v k), okk : k, kk : k, vv : v :: (m[kk:=vv])[okk] == m[okk];
-/
#guard_msgs in
#eval IO.println examplePgm

/--
info: #[{ ann := { start := { byteIdx := 323 }, stop := { byteIdx := 330 } },
    name := { dialect := "Core", name := "command_typedecl" },
    args :=
      ((Array.mkEmpty 2).push (ArgF.ident { start := { byteIdx := 328 }, stop := { byteIdx := 329 } } "k")).push
        (ArgF.option { start := { byteIdx := 329 }, stop := { byteIdx := 329 } } none) },
  { ann := { start := { byteIdx := 331 }, stop := { byteIdx := 338 } },
    name := { dialect := "Core", name := "command_typedecl" },
    args :=
      ((Array.mkEmpty 2).push (ArgF.ident { start := { byteIdx := 336 }, stop := { byteIdx := 337 } } "v")).push
        (ArgF.option { start := { byteIdx := 337 }, stop := { byteIdx := 337 } } none) },
  { ann := { start := { byteIdx := 339 }, stop := { byteIdx := 418 } },
    name := { dialect := "Core", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (ArgF.option { start := { byteIdx := 345 }, stop := { byteIdx := 360 } }
              (some
                (ArgF.op
                  { ann := { start := { byteIdx := 345 }, stop := { byteIdx := 360 } },
                    name := { dialect := "Core", name := "label" },
                    args :=
                      (Array.mkEmpty 1).push
                        (ArgF.ident { start := { byteIdx := 346 }, stop := { byteIdx := 358 } }
                          "updateSelect") })))).push
        (ArgF.expr
          (ExprF.app { start := { byteIdx := 361 }, stop := { byteIdx := 417 } }
            (ExprF.app { start := { byteIdx := 361 }, stop := { byteIdx := 417 } }
              (ExprF.fn { start := { byteIdx := 361 }, stop := { byteIdx := 417 } }
                { dialect := "Core", name := "forall" })
              (ArgF.op
                { ann := { start := { byteIdx := 368 }, stop := { byteIdx := 392 } },
                  name := { dialect := "Core", name := "declPush" },
                  args :=
                    ((Array.mkEmpty 2).push
                          (ArgF.op
                            { ann := { start := { byteIdx := 368 }, stop := { byteIdx := 385 } },
                              name := { dialect := "Core", name := "declPush" },
                              args :=
                                ((Array.mkEmpty 2).push
                                      (ArgF.op
                                        { ann := { start := { byteIdx := 368 }, stop := { byteIdx := 378 } },
                                          name := { dialect := "Core", name := "declAtom" },
                                          args :=
                                            (Array.mkEmpty 1).push
                                              (ArgF.op
                                                { ann := { start := { byteIdx := 368 }, stop := { byteIdx := 378 } },
                                                  name := { dialect := "Core", name := "bind_mk" },
                                                  args :=
                                                    (((Array.mkEmpty 3).push
                                                              (ArgF.ident
                                                                { start := { byteIdx := 368 },
                                                                  stop := { byteIdx := 369 } }
                                                                "m")).push
                                                          (ArgF.option
                                                            { start := { byteIdx := 371 }, stop := { byteIdx := 371 } }
                                                            none)).push
                                                      (ArgF.type
                                                        (TypeExprF.ident
                                                          { start := { byteIdx := 371 }, stop := { byteIdx := 374 } }
                                                          { dialect := "Core", name := "Map" }
                                                          (((Array.mkEmpty 2).push
                                                                (TypeExprF.fvar
                                                                  { start := { byteIdx := 377 },
                                                                    stop := { byteIdx := 378 } }
                                                                  1 (Array.mkEmpty 0))).push
                                                            (TypeExprF.fvar
                                                              { start := { byteIdx := 375 },
                                                                stop := { byteIdx := 376 } }
                                                              0 (Array.mkEmpty 0))))) }) })).push
                                  (ArgF.op
                                    { ann := { start := { byteIdx := 380 }, stop := { byteIdx := 385 } },
                                      name := { dialect := "Core", name := "bind_mk" },
                                      args :=
                                        (((Array.mkEmpty 3).push
                                                  (ArgF.ident
                                                    { start := { byteIdx := 380 }, stop := { byteIdx := 382 } }
                                                    "kk")).push
                                              (ArgF.option { start := { byteIdx := 384 }, stop := { byteIdx := 384 } }
                                                none)).push
                                          (ArgF.type
                                            (TypeExprF.fvar { start := { byteIdx := 384 }, stop := { byteIdx := 385 } }
                                              0 (Array.mkEmpty 0))) }) })).push
                      (ArgF.op
                        { ann := { start := { byteIdx := 387 }, stop := { byteIdx := 392 } },
                          name := { dialect := "Core", name := "bind_mk" },
                          args :=
                            (((Array.mkEmpty 3).push
                                      (ArgF.ident { start := { byteIdx := 387 }, stop := { byteIdx := 389 } }
                                        "vv")).push
                                  (ArgF.option { start := { byteIdx := 391 }, stop := { byteIdx := 391 } } none)).push
                              (ArgF.type
                                (TypeExprF.fvar { start := { byteIdx := 391 }, stop := { byteIdx := 392 } } 1
                                  (Array.mkEmpty 0))) }) }))
            (ArgF.expr
              (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 417 } }
                (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 417 } }
                  (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 417 } }
                    (ExprF.fn { start := { byteIdx := 396 }, stop := { byteIdx := 417 } }
                      { dialect := "Core", name := "equal" })
                    (ArgF.type
                      (TypeExprF.fvar { start := { byteIdx := 377 }, stop := { byteIdx := 378 } } 1 (Array.mkEmpty 0))))
                  (ArgF.expr
                    (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 411 } }
                      (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 411 } }
                        (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 411 } }
                          (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 411 } }
                            (ExprF.fn { start := { byteIdx := 396 }, stop := { byteIdx := 411 } }
                              { dialect := "Core", name := "map_get" })
                            (ArgF.type
                              (TypeExprF.fvar { start := { byteIdx := 375 }, stop := { byteIdx := 376 } } 0
                                (Array.mkEmpty 0))))
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 377 }, stop := { byteIdx := 378 } } 1
                              (Array.mkEmpty 0))))
                        (ArgF.expr
                          (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 407 } }
                            (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 407 } }
                              (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 407 } }
                                (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 407 } }
                                  (ExprF.app { start := { byteIdx := 396 }, stop := { byteIdx := 407 } }
                                    (ExprF.fn { start := { byteIdx := 396 }, stop := { byteIdx := 407 } }
                                      { dialect := "Core", name := "map_set" })
                                    (ArgF.type
                                      (TypeExprF.fvar { start := { byteIdx := 375 }, stop := { byteIdx := 376 } } 0
                                        (Array.mkEmpty 0))))
                                  (ArgF.type
                                    (TypeExprF.fvar { start := { byteIdx := 377 }, stop := { byteIdx := 378 } } 1
                                      (Array.mkEmpty 0))))
                                (ArgF.expr (ExprF.bvar { start := { byteIdx := 396 }, stop := { byteIdx := 397 } } 2)))
                              (ArgF.expr (ExprF.bvar { start := { byteIdx := 398 }, stop := { byteIdx := 400 } } 1)))
                            (ArgF.expr (ExprF.bvar { start := { byteIdx := 404 }, stop := { byteIdx := 406 } } 0)))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 408 }, stop := { byteIdx := 410 } } 1)))))
                (ArgF.expr (ExprF.bvar { start := { byteIdx := 415 }, stop := { byteIdx := 417 } } 0)))))) },
  { ann := { start := { byteIdx := 419 }, stop := { byteIdx := 514 } },
    name := { dialect := "Core", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (ArgF.option { start := { byteIdx := 425 }, stop := { byteIdx := 443 } }
              (some
                (ArgF.op
                  { ann := { start := { byteIdx := 425 }, stop := { byteIdx := 443 } },
                    name := { dialect := "Core", name := "label" },
                    args :=
                      (Array.mkEmpty 1).push
                        (ArgF.ident { start := { byteIdx := 426 }, stop := { byteIdx := 441 } }
                          "updatePreserves") })))).push
        (ArgF.expr
          (ExprF.app { start := { byteIdx := 444 }, stop := { byteIdx := 513 } }
            (ExprF.app { start := { byteIdx := 444 }, stop := { byteIdx := 513 } }
              (ExprF.fn { start := { byteIdx := 444 }, stop := { byteIdx := 513 } }
                { dialect := "Core", name := "forall" })
              (ArgF.op
                { ann := { start := { byteIdx := 451 }, stop := { byteIdx := 483 } },
                  name := { dialect := "Core", name := "declPush" },
                  args :=
                    ((Array.mkEmpty 2).push
                          (ArgF.op
                            { ann := { start := { byteIdx := 451 }, stop := { byteIdx := 476 } },
                              name := { dialect := "Core", name := "declPush" },
                              args :=
                                ((Array.mkEmpty 2).push
                                      (ArgF.op
                                        { ann := { start := { byteIdx := 451 }, stop := { byteIdx := 469 } },
                                          name := { dialect := "Core", name := "declPush" },
                                          args :=
                                            ((Array.mkEmpty 2).push
                                                  (ArgF.op
                                                    {
                                                      ann :=
                                                        { start := { byteIdx := 451 }, stop := { byteIdx := 461 } },
                                                      name := { dialect := "Core", name := "declAtom" },
                                                      args :=
                                                        (Array.mkEmpty 1).push
                                                          (ArgF.op
                                                            {
                                                              ann :=
                                                                { start := { byteIdx := 451 },
                                                                  stop := { byteIdx := 461 } },
                                                              name := { dialect := "Core", name := "bind_mk" },
                                                              args :=
                                                                (((Array.mkEmpty 3).push
                                                                          (ArgF.ident
                                                                            { start := { byteIdx := 451 },
                                                                              stop := { byteIdx := 452 } }
                                                                            "m")).push
                                                                      (ArgF.option
                                                                        { start := { byteIdx := 454 },
                                                                          stop := { byteIdx := 454 } }
                                                                        none)).push
                                                                  (ArgF.type
                                                                    (TypeExprF.ident
                                                                      { start := { byteIdx := 454 },
                                                                        stop := { byteIdx := 457 } }
                                                                      { dialect := "Core", name := "Map" }
                                                                      (((Array.mkEmpty 2).push
                                                                            (TypeExprF.fvar
                                                                              { start := { byteIdx := 460 },
                                                                                stop := { byteIdx := 461 } }
                                                                              1 (Array.mkEmpty 0))).push
                                                                        (TypeExprF.fvar
                                                                          { start := { byteIdx := 458 },
                                                                            stop := { byteIdx := 459 } }
                                                                          0 (Array.mkEmpty 0))))) }) })).push
                                              (ArgF.op
                                                { ann := { start := { byteIdx := 463 }, stop := { byteIdx := 469 } },
                                                  name := { dialect := "Core", name := "bind_mk" },
                                                  args :=
                                                    (((Array.mkEmpty 3).push
                                                              (ArgF.ident
                                                                { start := { byteIdx := 463 },
                                                                  stop := { byteIdx := 466 } }
                                                                "okk")).push
                                                          (ArgF.option
                                                            { start := { byteIdx := 468 }, stop := { byteIdx := 468 } }
                                                            none)).push
                                                      (ArgF.type
                                                        (TypeExprF.fvar
                                                          { start := { byteIdx := 468 }, stop := { byteIdx := 469 } } 0
                                                          (Array.mkEmpty 0))) }) })).push
                                  (ArgF.op
                                    { ann := { start := { byteIdx := 471 }, stop := { byteIdx := 476 } },
                                      name := { dialect := "Core", name := "bind_mk" },
                                      args :=
                                        (((Array.mkEmpty 3).push
                                                  (ArgF.ident
                                                    { start := { byteIdx := 471 }, stop := { byteIdx := 473 } }
                                                    "kk")).push
                                              (ArgF.option { start := { byteIdx := 475 }, stop := { byteIdx := 475 } }
                                                none)).push
                                          (ArgF.type
                                            (TypeExprF.fvar { start := { byteIdx := 475 }, stop := { byteIdx := 476 } }
                                              0 (Array.mkEmpty 0))) }) })).push
                      (ArgF.op
                        { ann := { start := { byteIdx := 478 }, stop := { byteIdx := 483 } },
                          name := { dialect := "Core", name := "bind_mk" },
                          args :=
                            (((Array.mkEmpty 3).push
                                      (ArgF.ident { start := { byteIdx := 478 }, stop := { byteIdx := 480 } }
                                        "vv")).push
                                  (ArgF.option { start := { byteIdx := 482 }, stop := { byteIdx := 482 } } none)).push
                              (ArgF.type
                                (TypeExprF.fvar { start := { byteIdx := 482 }, stop := { byteIdx := 483 } } 1
                                  (Array.mkEmpty 0))) }) }))
            (ArgF.expr
              (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 513 } }
                (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 513 } }
                  (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 513 } }
                    (ExprF.fn { start := { byteIdx := 487 }, stop := { byteIdx := 513 } }
                      { dialect := "Core", name := "equal" })
                    (ArgF.type
                      (TypeExprF.fvar { start := { byteIdx := 460 }, stop := { byteIdx := 461 } } 1 (Array.mkEmpty 0))))
                  (ArgF.expr
                    (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 503 } }
                      (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 503 } }
                        (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 503 } }
                          (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 503 } }
                            (ExprF.fn { start := { byteIdx := 487 }, stop := { byteIdx := 503 } }
                              { dialect := "Core", name := "map_get" })
                            (ArgF.type
                              (TypeExprF.fvar { start := { byteIdx := 458 }, stop := { byteIdx := 459 } } 0
                                (Array.mkEmpty 0))))
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 460 }, stop := { byteIdx := 461 } } 1
                              (Array.mkEmpty 0))))
                        (ArgF.expr
                          (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 498 } }
                            (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 498 } }
                              (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 498 } }
                                (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 498 } }
                                  (ExprF.app { start := { byteIdx := 487 }, stop := { byteIdx := 498 } }
                                    (ExprF.fn { start := { byteIdx := 487 }, stop := { byteIdx := 498 } }
                                      { dialect := "Core", name := "map_set" })
                                    (ArgF.type
                                      (TypeExprF.fvar { start := { byteIdx := 458 }, stop := { byteIdx := 459 } } 0
                                        (Array.mkEmpty 0))))
                                  (ArgF.type
                                    (TypeExprF.fvar { start := { byteIdx := 460 }, stop := { byteIdx := 461 } } 1
                                      (Array.mkEmpty 0))))
                                (ArgF.expr (ExprF.bvar { start := { byteIdx := 487 }, stop := { byteIdx := 488 } } 3)))
                              (ArgF.expr (ExprF.bvar { start := { byteIdx := 489 }, stop := { byteIdx := 491 } } 1)))
                            (ArgF.expr (ExprF.bvar { start := { byteIdx := 495 }, stop := { byteIdx := 497 } } 0)))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 499 }, stop := { byteIdx := 502 } } 2)))))
                (ArgF.expr
                  (ExprF.app { start := { byteIdx := 507 }, stop := { byteIdx := 513 } }
                    (ExprF.app { start := { byteIdx := 507 }, stop := { byteIdx := 513 } }
                      (ExprF.app { start := { byteIdx := 507 }, stop := { byteIdx := 513 } }
                        (ExprF.app { start := { byteIdx := 507 }, stop := { byteIdx := 513 } }
                          (ExprF.fn { start := { byteIdx := 507 }, stop := { byteIdx := 513 } }
                            { dialect := "Core", name := "map_get" })
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 458 }, stop := { byteIdx := 459 } } 0
                              (Array.mkEmpty 0))))
                        (ArgF.type
                          (TypeExprF.fvar { start := { byteIdx := 460 }, stop := { byteIdx := 461 } } 1
                            (Array.mkEmpty 0))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 507 }, stop := { byteIdx := 508 } } 3)))
                    (ArgF.expr (ExprF.bvar { start := { byteIdx := 509 }, stop := { byteIdx := 512 } } 2)))))))) }]
-/
#guard_msgs in
#eval examplePgm.commands

/--
info: [LExpr.quant () QuantifierKind.all "m" (some Lambda.LMonoTy.tcons
   "Map"
   [Lambda.LMonoTy.ftvar "k",
    Lambda.LMonoTy.ftvar
      "v"]) (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all "kk" (some Lambda.LMonoTy.ftvar
   "k") (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all "vv" (some Lambda.LMonoTy.ftvar
   "v") (LExpr.bvar () 0) (LExpr.eq () (LExpr.app () (LExpr.app () (LExpr.op () { name := "select",
   metadata := () } (some Lambda.LMonoTy.tcons
   "arrow"
   [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
    Lambda.LMonoTy.tcons
      "arrow"
      [Lambda.LMonoTy.ftvar "k",
       Lambda.LMonoTy.ftvar
         "v"]])) (LExpr.app () (LExpr.app () (LExpr.app () (LExpr.op () { name := "update",
   metadata := () } (some Lambda.LMonoTy.tcons
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
 LExpr.quant () QuantifierKind.all "m" (some Lambda.LMonoTy.tcons
   "Map"
   [Lambda.LMonoTy.ftvar "k",
    Lambda.LMonoTy.ftvar
      "v"]) (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all "okk" (some Lambda.LMonoTy.ftvar
   "k") (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all "kk" (some Lambda.LMonoTy.ftvar
   "k") (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all "vv" (some Lambda.LMonoTy.ftvar
   "v") (LExpr.bvar () 0) (LExpr.eq () (LExpr.app () (LExpr.app () (LExpr.op () { name := "select",
   metadata := () } (some Lambda.LMonoTy.tcons
   "arrow"
   [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
    Lambda.LMonoTy.tcons
      "arrow"
      [Lambda.LMonoTy.ftvar "k",
       Lambda.LMonoTy.ftvar
         "v"]])) (LExpr.app () (LExpr.app () (LExpr.app () (LExpr.op () { name := "update",
   metadata := () } (some Lambda.LMonoTy.tcons
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
   metadata := () } (some Lambda.LMonoTy.tcons
   "arrow"
   [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
    Lambda.LMonoTy.tcons
      "arrow"
      [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"]])) (LExpr.bvar () 3)) (LExpr.bvar () 2))))))]
-/
#guard_msgs in
#eval
  extractAxiomsWithFreeTypeVars examplePgm ["k", "v"]
