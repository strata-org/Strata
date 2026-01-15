/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier

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
info: #[{ ann := { start := { byteIdx := 291 }, stop := { byteIdx := 298 } },
    name := { dialect := "Core", name := "command_typedecl" },
    args :=
      ((Array.mkEmpty 2).push (ArgF.ident { start := { byteIdx := 296 }, stop := { byteIdx := 297 } } "k")).push
        (ArgF.option { start := { byteIdx := 297 }, stop := { byteIdx := 297 } } none) },
  { ann := { start := { byteIdx := 299 }, stop := { byteIdx := 306 } },
    name := { dialect := "Core", name := "command_typedecl" },
    args :=
      ((Array.mkEmpty 2).push (ArgF.ident { start := { byteIdx := 304 }, stop := { byteIdx := 305 } } "v")).push
        (ArgF.option { start := { byteIdx := 305 }, stop := { byteIdx := 305 } } none) },
  { ann := { start := { byteIdx := 307 }, stop := { byteIdx := 386 } },
    name := { dialect := "Core", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (ArgF.option { start := { byteIdx := 313 }, stop := { byteIdx := 328 } }
              (some
                (ArgF.op
                  { ann := { start := { byteIdx := 313 }, stop := { byteIdx := 328 } },
                    name := { dialect := "Core", name := "label" },
                    args :=
                      (Array.mkEmpty 1).push
                        (ArgF.ident { start := { byteIdx := 314 }, stop := { byteIdx := 326 } }
                          "updateSelect") })))).push
        (ArgF.expr
          (ExprF.app { start := { byteIdx := 329 }, stop := { byteIdx := 385 } }
            (ExprF.app { start := { byteIdx := 329 }, stop := { byteIdx := 385 } }
              (ExprF.fn { start := { byteIdx := 329 }, stop := { byteIdx := 385 } }
                { dialect := "Core", name := "forall" })
              (ArgF.op
                { ann := { start := { byteIdx := 336 }, stop := { byteIdx := 360 } },
                  name := { dialect := "Core", name := "declPush" },
                  args :=
                    ((Array.mkEmpty 2).push
                          (ArgF.op
                            { ann := { start := { byteIdx := 336 }, stop := { byteIdx := 353 } },
                              name := { dialect := "Core", name := "declPush" },
                              args :=
                                ((Array.mkEmpty 2).push
                                      (ArgF.op
                                        { ann := { start := { byteIdx := 336 }, stop := { byteIdx := 346 } },
                                          name := { dialect := "Core", name := "declAtom" },
                                          args :=
                                            (Array.mkEmpty 1).push
                                              (ArgF.op
                                                { ann := { start := { byteIdx := 336 }, stop := { byteIdx := 346 } },
                                                  name := { dialect := "Core", name := "bind_mk" },
                                                  args :=
                                                    (((Array.mkEmpty 3).push
                                                              (ArgF.ident
                                                                { start := { byteIdx := 336 },
                                                                  stop := { byteIdx := 337 } }
                                                                "m")).push
                                                          (ArgF.option
                                                            { start := { byteIdx := 339 }, stop := { byteIdx := 339 } }
                                                            none)).push
                                                      (ArgF.type
                                                        (TypeExprF.ident
                                                          { start := { byteIdx := 339 }, stop := { byteIdx := 342 } }
                                                          { dialect := "Core", name := "Map" }
                                                          (((Array.mkEmpty 2).push
                                                                (TypeExprF.fvar
                                                                  { start := { byteIdx := 345 },
                                                                    stop := { byteIdx := 346 } }
                                                                  1 (Array.mkEmpty 0))).push
                                                            (TypeExprF.fvar
                                                              { start := { byteIdx := 343 },
                                                                stop := { byteIdx := 344 } }
                                                              0 (Array.mkEmpty 0))))) }) })).push
                                  (ArgF.op
                                    { ann := { start := { byteIdx := 348 }, stop := { byteIdx := 353 } },
                                      name := { dialect := "Core", name := "bind_mk" },
                                      args :=
                                        (((Array.mkEmpty 3).push
                                                  (ArgF.ident
                                                    { start := { byteIdx := 348 }, stop := { byteIdx := 350 } }
                                                    "kk")).push
                                              (ArgF.option { start := { byteIdx := 352 }, stop := { byteIdx := 352 } }
                                                none)).push
                                          (ArgF.type
                                            (TypeExprF.fvar { start := { byteIdx := 352 }, stop := { byteIdx := 353 } }
                                              0 (Array.mkEmpty 0))) }) })).push
                      (ArgF.op
                        { ann := { start := { byteIdx := 355 }, stop := { byteIdx := 360 } },
                          name := { dialect := "Core", name := "bind_mk" },
                          args :=
                            (((Array.mkEmpty 3).push
                                      (ArgF.ident { start := { byteIdx := 355 }, stop := { byteIdx := 357 } }
                                        "vv")).push
                                  (ArgF.option { start := { byteIdx := 359 }, stop := { byteIdx := 359 } } none)).push
                              (ArgF.type
                                (TypeExprF.fvar { start := { byteIdx := 359 }, stop := { byteIdx := 360 } } 1
                                  (Array.mkEmpty 0))) }) }))
            (ArgF.expr
              (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 385 } }
                (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 385 } }
                  (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 385 } }
                    (ExprF.fn { start := { byteIdx := 364 }, stop := { byteIdx := 385 } }
                      { dialect := "Core", name := "equal" })
                    (ArgF.type
                      (TypeExprF.fvar { start := { byteIdx := 345 }, stop := { byteIdx := 346 } } 1 (Array.mkEmpty 0))))
                  (ArgF.expr
                    (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 379 } }
                      (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 379 } }
                        (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 379 } }
                          (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 379 } }
                            (ExprF.fn { start := { byteIdx := 364 }, stop := { byteIdx := 379 } }
                              { dialect := "Core", name := "map_get" })
                            (ArgF.type
                              (TypeExprF.fvar { start := { byteIdx := 343 }, stop := { byteIdx := 344 } } 0
                                (Array.mkEmpty 0))))
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 345 }, stop := { byteIdx := 346 } } 1
                              (Array.mkEmpty 0))))
                        (ArgF.expr
                          (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 375 } }
                            (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 375 } }
                              (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 375 } }
                                (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 375 } }
                                  (ExprF.app { start := { byteIdx := 364 }, stop := { byteIdx := 375 } }
                                    (ExprF.fn { start := { byteIdx := 364 }, stop := { byteIdx := 375 } }
                                      { dialect := "Core", name := "map_set" })
                                    (ArgF.type
                                      (TypeExprF.fvar { start := { byteIdx := 343 }, stop := { byteIdx := 344 } } 0
                                        (Array.mkEmpty 0))))
                                  (ArgF.type
                                    (TypeExprF.fvar { start := { byteIdx := 345 }, stop := { byteIdx := 346 } } 1
                                      (Array.mkEmpty 0))))
                                (ArgF.expr (ExprF.bvar { start := { byteIdx := 364 }, stop := { byteIdx := 365 } } 2)))
                              (ArgF.expr (ExprF.bvar { start := { byteIdx := 366 }, stop := { byteIdx := 368 } } 1)))
                            (ArgF.expr (ExprF.bvar { start := { byteIdx := 372 }, stop := { byteIdx := 374 } } 0)))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 376 }, stop := { byteIdx := 378 } } 1)))))
                (ArgF.expr (ExprF.bvar { start := { byteIdx := 383 }, stop := { byteIdx := 385 } } 0)))))) },
  { ann := { start := { byteIdx := 387 }, stop := { byteIdx := 482 } },
    name := { dialect := "Core", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (ArgF.option { start := { byteIdx := 393 }, stop := { byteIdx := 411 } }
              (some
                (ArgF.op
                  { ann := { start := { byteIdx := 393 }, stop := { byteIdx := 411 } },
                    name := { dialect := "Core", name := "label" },
                    args :=
                      (Array.mkEmpty 1).push
                        (ArgF.ident { start := { byteIdx := 394 }, stop := { byteIdx := 409 } }
                          "updatePreserves") })))).push
        (ArgF.expr
          (ExprF.app { start := { byteIdx := 412 }, stop := { byteIdx := 481 } }
            (ExprF.app { start := { byteIdx := 412 }, stop := { byteIdx := 481 } }
              (ExprF.fn { start := { byteIdx := 412 }, stop := { byteIdx := 481 } }
                { dialect := "Core", name := "forall" })
              (ArgF.op
                { ann := { start := { byteIdx := 419 }, stop := { byteIdx := 451 } },
                  name := { dialect := "Core", name := "declPush" },
                  args :=
                    ((Array.mkEmpty 2).push
                          (ArgF.op
                            { ann := { start := { byteIdx := 419 }, stop := { byteIdx := 444 } },
                              name := { dialect := "Core", name := "declPush" },
                              args :=
                                ((Array.mkEmpty 2).push
                                      (ArgF.op
                                        { ann := { start := { byteIdx := 419 }, stop := { byteIdx := 437 } },
                                          name := { dialect := "Core", name := "declPush" },
                                          args :=
                                            ((Array.mkEmpty 2).push
                                                  (ArgF.op
                                                    {
                                                      ann :=
                                                        { start := { byteIdx := 419 }, stop := { byteIdx := 429 } },
                                                      name := { dialect := "Core", name := "declAtom" },
                                                      args :=
                                                        (Array.mkEmpty 1).push
                                                          (ArgF.op
                                                            {
                                                              ann :=
                                                                { start := { byteIdx := 419 },
                                                                  stop := { byteIdx := 429 } },
                                                              name := { dialect := "Core", name := "bind_mk" },
                                                              args :=
                                                                (((Array.mkEmpty 3).push
                                                                          (ArgF.ident
                                                                            { start := { byteIdx := 419 },
                                                                              stop := { byteIdx := 420 } }
                                                                            "m")).push
                                                                      (ArgF.option
                                                                        { start := { byteIdx := 422 },
                                                                          stop := { byteIdx := 422 } }
                                                                        none)).push
                                                                  (ArgF.type
                                                                    (TypeExprF.ident
                                                                      { start := { byteIdx := 422 },
                                                                        stop := { byteIdx := 425 } }
                                                                      { dialect := "Core", name := "Map" }
                                                                      (((Array.mkEmpty 2).push
                                                                            (TypeExprF.fvar
                                                                              { start := { byteIdx := 428 },
                                                                                stop := { byteIdx := 429 } }
                                                                              1 (Array.mkEmpty 0))).push
                                                                        (TypeExprF.fvar
                                                                          { start := { byteIdx := 426 },
                                                                            stop := { byteIdx := 427 } }
                                                                          0 (Array.mkEmpty 0))))) }) })).push
                                              (ArgF.op
                                                { ann := { start := { byteIdx := 431 }, stop := { byteIdx := 437 } },
                                                  name := { dialect := "Core", name := "bind_mk" },
                                                  args :=
                                                    (((Array.mkEmpty 3).push
                                                              (ArgF.ident
                                                                { start := { byteIdx := 431 },
                                                                  stop := { byteIdx := 434 } }
                                                                "okk")).push
                                                          (ArgF.option
                                                            { start := { byteIdx := 436 }, stop := { byteIdx := 436 } }
                                                            none)).push
                                                      (ArgF.type
                                                        (TypeExprF.fvar
                                                          { start := { byteIdx := 436 }, stop := { byteIdx := 437 } } 0
                                                          (Array.mkEmpty 0))) }) })).push
                                  (ArgF.op
                                    { ann := { start := { byteIdx := 439 }, stop := { byteIdx := 444 } },
                                      name := { dialect := "Core", name := "bind_mk" },
                                      args :=
                                        (((Array.mkEmpty 3).push
                                                  (ArgF.ident
                                                    { start := { byteIdx := 439 }, stop := { byteIdx := 441 } }
                                                    "kk")).push
                                              (ArgF.option { start := { byteIdx := 443 }, stop := { byteIdx := 443 } }
                                                none)).push
                                          (ArgF.type
                                            (TypeExprF.fvar { start := { byteIdx := 443 }, stop := { byteIdx := 444 } }
                                              0 (Array.mkEmpty 0))) }) })).push
                      (ArgF.op
                        { ann := { start := { byteIdx := 446 }, stop := { byteIdx := 451 } },
                          name := { dialect := "Core", name := "bind_mk" },
                          args :=
                            (((Array.mkEmpty 3).push
                                      (ArgF.ident { start := { byteIdx := 446 }, stop := { byteIdx := 448 } }
                                        "vv")).push
                                  (ArgF.option { start := { byteIdx := 450 }, stop := { byteIdx := 450 } } none)).push
                              (ArgF.type
                                (TypeExprF.fvar { start := { byteIdx := 450 }, stop := { byteIdx := 451 } } 1
                                  (Array.mkEmpty 0))) }) }))
            (ArgF.expr
              (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 481 } }
                (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 481 } }
                  (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 481 } }
                    (ExprF.fn { start := { byteIdx := 455 }, stop := { byteIdx := 481 } }
                      { dialect := "Core", name := "equal" })
                    (ArgF.type
                      (TypeExprF.fvar { start := { byteIdx := 428 }, stop := { byteIdx := 429 } } 1 (Array.mkEmpty 0))))
                  (ArgF.expr
                    (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 471 } }
                      (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 471 } }
                        (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 471 } }
                          (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 471 } }
                            (ExprF.fn { start := { byteIdx := 455 }, stop := { byteIdx := 471 } }
                              { dialect := "Core", name := "map_get" })
                            (ArgF.type
                              (TypeExprF.fvar { start := { byteIdx := 426 }, stop := { byteIdx := 427 } } 0
                                (Array.mkEmpty 0))))
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 428 }, stop := { byteIdx := 429 } } 1
                              (Array.mkEmpty 0))))
                        (ArgF.expr
                          (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 466 } }
                            (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 466 } }
                              (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 466 } }
                                (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 466 } }
                                  (ExprF.app { start := { byteIdx := 455 }, stop := { byteIdx := 466 } }
                                    (ExprF.fn { start := { byteIdx := 455 }, stop := { byteIdx := 466 } }
                                      { dialect := "Core", name := "map_set" })
                                    (ArgF.type
                                      (TypeExprF.fvar { start := { byteIdx := 426 }, stop := { byteIdx := 427 } } 0
                                        (Array.mkEmpty 0))))
                                  (ArgF.type
                                    (TypeExprF.fvar { start := { byteIdx := 428 }, stop := { byteIdx := 429 } } 1
                                      (Array.mkEmpty 0))))
                                (ArgF.expr (ExprF.bvar { start := { byteIdx := 455 }, stop := { byteIdx := 456 } } 3)))
                              (ArgF.expr (ExprF.bvar { start := { byteIdx := 457 }, stop := { byteIdx := 459 } } 1)))
                            (ArgF.expr (ExprF.bvar { start := { byteIdx := 463 }, stop := { byteIdx := 465 } } 0)))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 467 }, stop := { byteIdx := 470 } } 2)))))
                (ArgF.expr
                  (ExprF.app { start := { byteIdx := 475 }, stop := { byteIdx := 481 } }
                    (ExprF.app { start := { byteIdx := 475 }, stop := { byteIdx := 481 } }
                      (ExprF.app { start := { byteIdx := 475 }, stop := { byteIdx := 481 } }
                        (ExprF.app { start := { byteIdx := 475 }, stop := { byteIdx := 481 } }
                          (ExprF.fn { start := { byteIdx := 475 }, stop := { byteIdx := 481 } }
                            { dialect := "Core", name := "map_get" })
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 426 }, stop := { byteIdx := 427 } } 0
                              (Array.mkEmpty 0))))
                        (ArgF.type
                          (TypeExprF.fvar { start := { byteIdx := 428 }, stop := { byteIdx := 429 } } 1
                            (Array.mkEmpty 0))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 475 }, stop := { byteIdx := 476 } } 3)))
                    (ArgF.expr (ExprF.bvar { start := { byteIdx := 477 }, stop := { byteIdx := 480 } } 2)))))))) }]
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
