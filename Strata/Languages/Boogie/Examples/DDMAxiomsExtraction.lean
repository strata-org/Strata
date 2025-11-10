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
program Boogie;
type k;
type v;
axiom [updateSelect]: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv;
axiom [updatePreserves]: forall m: Map k v, okk: k, kk: k, vv: v :: m[kk := vv][okk] == m[okk];
#end

/--
  This function extracts the Boogie.Decl in the given program that are axiom declarations
-/
def extractAxiomsDecl (prg: Boogie.Program) : (List Boogie.Decl) :=
  let rec loop (acc: List Boogie.Decl) (l: List Boogie.Decl): List Boogie.Decl :=
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
def extractExpr (axDecl: Boogie.Decl): (Lambda.LExpr Lambda.LMonoTy Boogie.Visibility) :=
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
def replaceTypesByFTV (expr: Lambda.LExpr Lambda.LMonoTy Boogie.Visibility) (to_replace: List String): Lambda.LExpr Lambda.LMonoTy Boogie.Visibility :=
  match expr with
    | .const c => .const c
    | .op o oty => .op o (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace))
    | .fvar name oty => .fvar name (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace))
    | .mdata info e => .mdata info (replaceTypesByFTV e to_replace)
    | .abs oty e => .abs (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace)) (replaceTypesByFTV e to_replace)
    | .quant k oty tr e => .quant k (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace)) (replaceTypesByFTV tr to_replace) (replaceTypesByFTV e to_replace)
    | .app fn e => .app (replaceTypesByFTV fn to_replace) (replaceTypesByFTV e to_replace)
    | .ite c t e => .ite (replaceTypesByFTV c to_replace) (replaceTypesByFTV t to_replace) (replaceTypesByFTV e to_replace)
    | .eq e1 e2 => .eq (replaceTypesByFTV e1 to_replace) (replaceTypesByFTV e2 to_replace)
    | _ => expr

/--
  Extract all axioms from the given environment by first translating it into a Boogie Program.
  It then extracts LExpr body from the axioms, and replace all occurences of the typeArgs by a ftvar with the same name
-/
def extractAxiomsWithFreeTypeVars (pgm: Program) (typeArgs: List String): (List (Lambda.LExpr Lambda.LMonoTy Boogie.Visibility)) :=
  let prg: Boogie.Program := (TransM.run (translateProgram pgm)).fst
  let axiomsDecls := extractAxiomsDecl prg
  let axioms := axiomsDecls.map extractExpr
  axioms.map (fun a => replaceTypesByFTV a typeArgs)

/--
info: program Boogie;
type k;
type v;
axiom [updateSelect]:forall(((m):(Map v k)),((kk):(k))),((vv):(v))::((m)[kk:=vv])[kk]==vv;
axiom [updatePreserves]:forall((((m):(Map v k)),((okk):(k))),((kk):(k))),((vv):(v))::((m)[kk:=vv])[okk]==(m)[okk];
-/
#guard_msgs in
#eval IO.println examplePgm.format.render

/--
info: #[{ ann := { start := { byteIdx := 295 }, stop := { byteIdx := 302 } },
    name := { dialect := "Boogie", name := "command_typedecl" },
    args :=
      ((Array.mkEmpty 2).push (ArgF.ident { start := { byteIdx := 300 }, stop := { byteIdx := 301 } } "k")).push
        (ArgF.option { start := { byteIdx := 301 }, stop := { byteIdx := 301 } } none) },
  { ann := { start := { byteIdx := 303 }, stop := { byteIdx := 310 } },
    name := { dialect := "Boogie", name := "command_typedecl" },
    args :=
      ((Array.mkEmpty 2).push (ArgF.ident { start := { byteIdx := 308 }, stop := { byteIdx := 309 } } "v")).push
        (ArgF.option { start := { byteIdx := 309 }, stop := { byteIdx := 309 } } none) },
  { ann := { start := { byteIdx := 311 }, stop := { byteIdx := 390 } },
    name := { dialect := "Boogie", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (ArgF.option { start := { byteIdx := 317 }, stop := { byteIdx := 332 } }
              (some
                (ArgF.op
                  { ann := { start := { byteIdx := 317 }, stop := { byteIdx := 332 } },
                    name := { dialect := "Boogie", name := "label" },
                    args :=
                      (Array.mkEmpty 1).push
                        (ArgF.ident { start := { byteIdx := 318 }, stop := { byteIdx := 330 } }
                          "updateSelect") })))).push
        (ArgF.expr
          (ExprF.app { start := { byteIdx := 333 }, stop := { byteIdx := 389 } }
            (ExprF.app { start := { byteIdx := 333 }, stop := { byteIdx := 389 } }
              (ExprF.fn { start := { byteIdx := 333 }, stop := { byteIdx := 389 } }
                { dialect := "Boogie", name := "forall" })
              (ArgF.op
                { ann := { start := { byteIdx := 340 }, stop := { byteIdx := 364 } },
                  name := { dialect := "Boogie", name := "declPush" },
                  args :=
                    ((Array.mkEmpty 2).push
                          (ArgF.op
                            { ann := { start := { byteIdx := 340 }, stop := { byteIdx := 357 } },
                              name := { dialect := "Boogie", name := "declPush" },
                              args :=
                                ((Array.mkEmpty 2).push
                                      (ArgF.op
                                        { ann := { start := { byteIdx := 340 }, stop := { byteIdx := 350 } },
                                          name := { dialect := "Boogie", name := "declAtom" },
                                          args :=
                                            (Array.mkEmpty 1).push
                                              (ArgF.op
                                                { ann := { start := { byteIdx := 340 }, stop := { byteIdx := 350 } },
                                                  name := { dialect := "Boogie", name := "bind_mk" },
                                                  args :=
                                                    (((Array.mkEmpty 3).push
                                                              (ArgF.ident
                                                                { start := { byteIdx := 340 },
                                                                  stop := { byteIdx := 341 } }
                                                                "m")).push
                                                          (ArgF.option
                                                            { start := { byteIdx := 343 }, stop := { byteIdx := 343 } }
                                                            none)).push
                                                      (ArgF.type
                                                        (TypeExprF.ident
                                                          { start := { byteIdx := 343 }, stop := { byteIdx := 346 } }
                                                          { dialect := "Boogie", name := "Map" }
                                                          (((Array.mkEmpty 2).push
                                                                (TypeExprF.fvar
                                                                  { start := { byteIdx := 349 },
                                                                    stop := { byteIdx := 350 } }
                                                                  1 (Array.mkEmpty 0))).push
                                                            (TypeExprF.fvar
                                                              { start := { byteIdx := 347 },
                                                                stop := { byteIdx := 348 } }
                                                              0 (Array.mkEmpty 0))))) }) })).push
                                  (ArgF.op
                                    { ann := { start := { byteIdx := 352 }, stop := { byteIdx := 357 } },
                                      name := { dialect := "Boogie", name := "bind_mk" },
                                      args :=
                                        (((Array.mkEmpty 3).push
                                                  (ArgF.ident
                                                    { start := { byteIdx := 352 }, stop := { byteIdx := 354 } }
                                                    "kk")).push
                                              (ArgF.option { start := { byteIdx := 356 }, stop := { byteIdx := 356 } }
                                                none)).push
                                          (ArgF.type
                                            (TypeExprF.fvar { start := { byteIdx := 356 }, stop := { byteIdx := 357 } }
                                              0 (Array.mkEmpty 0))) }) })).push
                      (ArgF.op
                        { ann := { start := { byteIdx := 359 }, stop := { byteIdx := 364 } },
                          name := { dialect := "Boogie", name := "bind_mk" },
                          args :=
                            (((Array.mkEmpty 3).push
                                      (ArgF.ident { start := { byteIdx := 359 }, stop := { byteIdx := 361 } }
                                        "vv")).push
                                  (ArgF.option { start := { byteIdx := 363 }, stop := { byteIdx := 363 } } none)).push
                              (ArgF.type
                                (TypeExprF.fvar { start := { byteIdx := 363 }, stop := { byteIdx := 364 } } 1
                                  (Array.mkEmpty 0))) }) }))
            (ArgF.expr
              (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 389 } }
                (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 389 } }
                  (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 389 } }
                    (ExprF.fn { start := { byteIdx := 368 }, stop := { byteIdx := 389 } }
                      { dialect := "Boogie", name := "equal" })
                    (ArgF.type
                      (TypeExprF.fvar { start := { byteIdx := 349 }, stop := { byteIdx := 350 } } 1 (Array.mkEmpty 0))))
                  (ArgF.expr
                    (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 383 } }
                      (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 383 } }
                        (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 383 } }
                          (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 383 } }
                            (ExprF.fn { start := { byteIdx := 368 }, stop := { byteIdx := 383 } }
                              { dialect := "Boogie", name := "map_get" })
                            (ArgF.type
                              (TypeExprF.fvar { start := { byteIdx := 347 }, stop := { byteIdx := 348 } } 0
                                (Array.mkEmpty 0))))
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 349 }, stop := { byteIdx := 350 } } 1
                              (Array.mkEmpty 0))))
                        (ArgF.expr
                          (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 379 } }
                            (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 379 } }
                              (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 379 } }
                                (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 379 } }
                                  (ExprF.app { start := { byteIdx := 368 }, stop := { byteIdx := 379 } }
                                    (ExprF.fn { start := { byteIdx := 368 }, stop := { byteIdx := 379 } }
                                      { dialect := "Boogie", name := "map_set" })
                                    (ArgF.type
                                      (TypeExprF.fvar { start := { byteIdx := 347 }, stop := { byteIdx := 348 } } 0
                                        (Array.mkEmpty 0))))
                                  (ArgF.type
                                    (TypeExprF.fvar { start := { byteIdx := 349 }, stop := { byteIdx := 350 } } 1
                                      (Array.mkEmpty 0))))
                                (ArgF.expr (ExprF.bvar { start := { byteIdx := 368 }, stop := { byteIdx := 369 } } 2)))
                              (ArgF.expr (ExprF.bvar { start := { byteIdx := 370 }, stop := { byteIdx := 372 } } 1)))
                            (ArgF.expr (ExprF.bvar { start := { byteIdx := 376 }, stop := { byteIdx := 378 } } 0)))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 380 }, stop := { byteIdx := 382 } } 1)))))
                (ArgF.expr (ExprF.bvar { start := { byteIdx := 387 }, stop := { byteIdx := 389 } } 0)))))) },
  { ann := { start := { byteIdx := 391 }, stop := { byteIdx := 486 } },
    name := { dialect := "Boogie", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (ArgF.option { start := { byteIdx := 397 }, stop := { byteIdx := 415 } }
              (some
                (ArgF.op
                  { ann := { start := { byteIdx := 397 }, stop := { byteIdx := 415 } },
                    name := { dialect := "Boogie", name := "label" },
                    args :=
                      (Array.mkEmpty 1).push
                        (ArgF.ident { start := { byteIdx := 398 }, stop := { byteIdx := 413 } }
                          "updatePreserves") })))).push
        (ArgF.expr
          (ExprF.app { start := { byteIdx := 416 }, stop := { byteIdx := 485 } }
            (ExprF.app { start := { byteIdx := 416 }, stop := { byteIdx := 485 } }
              (ExprF.fn { start := { byteIdx := 416 }, stop := { byteIdx := 485 } }
                { dialect := "Boogie", name := "forall" })
              (ArgF.op
                { ann := { start := { byteIdx := 423 }, stop := { byteIdx := 455 } },
                  name := { dialect := "Boogie", name := "declPush" },
                  args :=
                    ((Array.mkEmpty 2).push
                          (ArgF.op
                            { ann := { start := { byteIdx := 423 }, stop := { byteIdx := 448 } },
                              name := { dialect := "Boogie", name := "declPush" },
                              args :=
                                ((Array.mkEmpty 2).push
                                      (ArgF.op
                                        { ann := { start := { byteIdx := 423 }, stop := { byteIdx := 441 } },
                                          name := { dialect := "Boogie", name := "declPush" },
                                          args :=
                                            ((Array.mkEmpty 2).push
                                                  (ArgF.op
                                                    {
                                                      ann :=
                                                        { start := { byteIdx := 423 }, stop := { byteIdx := 433 } },
                                                      name := { dialect := "Boogie", name := "declAtom" },
                                                      args :=
                                                        (Array.mkEmpty 1).push
                                                          (ArgF.op
                                                            {
                                                              ann :=
                                                                { start := { byteIdx := 423 },
                                                                  stop := { byteIdx := 433 } },
                                                              name := { dialect := "Boogie", name := "bind_mk" },
                                                              args :=
                                                                (((Array.mkEmpty 3).push
                                                                          (ArgF.ident
                                                                            { start := { byteIdx := 423 },
                                                                              stop := { byteIdx := 424 } }
                                                                            "m")).push
                                                                      (ArgF.option
                                                                        { start := { byteIdx := 426 },
                                                                          stop := { byteIdx := 426 } }
                                                                        none)).push
                                                                  (ArgF.type
                                                                    (TypeExprF.ident
                                                                      { start := { byteIdx := 426 },
                                                                        stop := { byteIdx := 429 } }
                                                                      { dialect := "Boogie", name := "Map" }
                                                                      (((Array.mkEmpty 2).push
                                                                            (TypeExprF.fvar
                                                                              { start := { byteIdx := 432 },
                                                                                stop := { byteIdx := 433 } }
                                                                              1 (Array.mkEmpty 0))).push
                                                                        (TypeExprF.fvar
                                                                          { start := { byteIdx := 430 },
                                                                            stop := { byteIdx := 431 } }
                                                                          0 (Array.mkEmpty 0))))) }) })).push
                                              (ArgF.op
                                                { ann := { start := { byteIdx := 435 }, stop := { byteIdx := 441 } },
                                                  name := { dialect := "Boogie", name := "bind_mk" },
                                                  args :=
                                                    (((Array.mkEmpty 3).push
                                                              (ArgF.ident
                                                                { start := { byteIdx := 435 },
                                                                  stop := { byteIdx := 438 } }
                                                                "okk")).push
                                                          (ArgF.option
                                                            { start := { byteIdx := 440 }, stop := { byteIdx := 440 } }
                                                            none)).push
                                                      (ArgF.type
                                                        (TypeExprF.fvar
                                                          { start := { byteIdx := 440 }, stop := { byteIdx := 441 } } 0
                                                          (Array.mkEmpty 0))) }) })).push
                                  (ArgF.op
                                    { ann := { start := { byteIdx := 443 }, stop := { byteIdx := 448 } },
                                      name := { dialect := "Boogie", name := "bind_mk" },
                                      args :=
                                        (((Array.mkEmpty 3).push
                                                  (ArgF.ident
                                                    { start := { byteIdx := 443 }, stop := { byteIdx := 445 } }
                                                    "kk")).push
                                              (ArgF.option { start := { byteIdx := 447 }, stop := { byteIdx := 447 } }
                                                none)).push
                                          (ArgF.type
                                            (TypeExprF.fvar { start := { byteIdx := 447 }, stop := { byteIdx := 448 } }
                                              0 (Array.mkEmpty 0))) }) })).push
                      (ArgF.op
                        { ann := { start := { byteIdx := 450 }, stop := { byteIdx := 455 } },
                          name := { dialect := "Boogie", name := "bind_mk" },
                          args :=
                            (((Array.mkEmpty 3).push
                                      (ArgF.ident { start := { byteIdx := 450 }, stop := { byteIdx := 452 } }
                                        "vv")).push
                                  (ArgF.option { start := { byteIdx := 454 }, stop := { byteIdx := 454 } } none)).push
                              (ArgF.type
                                (TypeExprF.fvar { start := { byteIdx := 454 }, stop := { byteIdx := 455 } } 1
                                  (Array.mkEmpty 0))) }) }))
            (ArgF.expr
              (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 485 } }
                (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 485 } }
                  (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 485 } }
                    (ExprF.fn { start := { byteIdx := 459 }, stop := { byteIdx := 485 } }
                      { dialect := "Boogie", name := "equal" })
                    (ArgF.type
                      (TypeExprF.fvar { start := { byteIdx := 432 }, stop := { byteIdx := 433 } } 1 (Array.mkEmpty 0))))
                  (ArgF.expr
                    (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 475 } }
                      (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 475 } }
                        (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 475 } }
                          (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 475 } }
                            (ExprF.fn { start := { byteIdx := 459 }, stop := { byteIdx := 475 } }
                              { dialect := "Boogie", name := "map_get" })
                            (ArgF.type
                              (TypeExprF.fvar { start := { byteIdx := 430 }, stop := { byteIdx := 431 } } 0
                                (Array.mkEmpty 0))))
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 432 }, stop := { byteIdx := 433 } } 1
                              (Array.mkEmpty 0))))
                        (ArgF.expr
                          (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 470 } }
                            (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 470 } }
                              (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 470 } }
                                (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 470 } }
                                  (ExprF.app { start := { byteIdx := 459 }, stop := { byteIdx := 470 } }
                                    (ExprF.fn { start := { byteIdx := 459 }, stop := { byteIdx := 470 } }
                                      { dialect := "Boogie", name := "map_set" })
                                    (ArgF.type
                                      (TypeExprF.fvar { start := { byteIdx := 430 }, stop := { byteIdx := 431 } } 0
                                        (Array.mkEmpty 0))))
                                  (ArgF.type
                                    (TypeExprF.fvar { start := { byteIdx := 432 }, stop := { byteIdx := 433 } } 1
                                      (Array.mkEmpty 0))))
                                (ArgF.expr (ExprF.bvar { start := { byteIdx := 459 }, stop := { byteIdx := 460 } } 3)))
                              (ArgF.expr (ExprF.bvar { start := { byteIdx := 461 }, stop := { byteIdx := 463 } } 1)))
                            (ArgF.expr (ExprF.bvar { start := { byteIdx := 467 }, stop := { byteIdx := 469 } } 0)))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 471 }, stop := { byteIdx := 474 } } 2)))))
                (ArgF.expr
                  (ExprF.app { start := { byteIdx := 479 }, stop := { byteIdx := 485 } }
                    (ExprF.app { start := { byteIdx := 479 }, stop := { byteIdx := 485 } }
                      (ExprF.app { start := { byteIdx := 479 }, stop := { byteIdx := 485 } }
                        (ExprF.app { start := { byteIdx := 479 }, stop := { byteIdx := 485 } }
                          (ExprF.fn { start := { byteIdx := 479 }, stop := { byteIdx := 485 } }
                            { dialect := "Boogie", name := "map_get" })
                          (ArgF.type
                            (TypeExprF.fvar { start := { byteIdx := 430 }, stop := { byteIdx := 431 } } 0
                              (Array.mkEmpty 0))))
                        (ArgF.type
                          (TypeExprF.fvar { start := { byteIdx := 432 }, stop := { byteIdx := 433 } } 1
                            (Array.mkEmpty 0))))
                      (ArgF.expr (ExprF.bvar { start := { byteIdx := 479 }, stop := { byteIdx := 480 } } 3)))
                    (ArgF.expr (ExprF.bvar { start := { byteIdx := 481 }, stop := { byteIdx := 484 } } 2)))))))) }]
-/
#guard_msgs in
#eval examplePgm.commands

/--
info: [Lambda.LExpr.quant
   (Lambda.QuantifierKind.all)
   (some (Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"]))
   (Lambda.LExpr.bvar 0)
   (Lambda.LExpr.quant
     (Lambda.QuantifierKind.all)
     (some (Lambda.LMonoTy.ftvar "k"))
     (Lambda.LExpr.bvar 0)
     (Lambda.LExpr.quant
       (Lambda.QuantifierKind.all)
       (some (Lambda.LMonoTy.ftvar "v"))
       (Lambda.LExpr.bvar 0)
       (Lambda.LExpr.eq
         (Lambda.LExpr.app
           (Lambda.LExpr.app
             (Lambda.LExpr.op
               { name := "select", metadata := Boogie.Visibility.unres }
               (some (Lambda.LMonoTy.tcons
                  "arrow"
                  [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
                   Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"]])))
             (Lambda.LExpr.app
               (Lambda.LExpr.app
                 (Lambda.LExpr.app
                   (Lambda.LExpr.op
                     { name := "update", metadata := Boogie.Visibility.unres }
                     (some (Lambda.LMonoTy.tcons
                        "arrow"
                        [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
                         Lambda.LMonoTy.tcons
                           "arrow"
                           [Lambda.LMonoTy.ftvar "k",
                            Lambda.LMonoTy.tcons
                              "arrow"
                              [Lambda.LMonoTy.ftvar "v",
                               Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"]]]])))
                   (Lambda.LExpr.bvar 2))
                 (Lambda.LExpr.bvar 1))
               (Lambda.LExpr.bvar 0)))
           (Lambda.LExpr.bvar 1))
         (Lambda.LExpr.bvar 0)))),
 Lambda.LExpr.quant
   (Lambda.QuantifierKind.all)
   (some (Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"]))
   (Lambda.LExpr.bvar 0)
   (Lambda.LExpr.quant
     (Lambda.QuantifierKind.all)
     (some (Lambda.LMonoTy.ftvar "k"))
     (Lambda.LExpr.bvar 0)
     (Lambda.LExpr.quant
       (Lambda.QuantifierKind.all)
       (some (Lambda.LMonoTy.ftvar "k"))
       (Lambda.LExpr.bvar 0)
       (Lambda.LExpr.quant
         (Lambda.QuantifierKind.all)
         (some (Lambda.LMonoTy.ftvar "v"))
         (Lambda.LExpr.bvar 0)
         (Lambda.LExpr.eq
           (Lambda.LExpr.app
             (Lambda.LExpr.app
               (Lambda.LExpr.op
                 { name := "select", metadata := Boogie.Visibility.unres }
                 (some (Lambda.LMonoTy.tcons
                    "arrow"
                    [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
                     Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"]])))
               (Lambda.LExpr.app
                 (Lambda.LExpr.app
                   (Lambda.LExpr.app
                     (Lambda.LExpr.op
                       { name := "update", metadata := Boogie.Visibility.unres }
                       (some (Lambda.LMonoTy.tcons
                          "arrow"
                          [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
                           Lambda.LMonoTy.tcons
                             "arrow"
                             [Lambda.LMonoTy.ftvar "k",
                              Lambda.LMonoTy.tcons
                                "arrow"
                                [Lambda.LMonoTy.ftvar "v",
                                 Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"]]]])))
                     (Lambda.LExpr.bvar 3))
                   (Lambda.LExpr.bvar 1))
                 (Lambda.LExpr.bvar 0)))
             (Lambda.LExpr.bvar 2))
           (Lambda.LExpr.app
             (Lambda.LExpr.app
               (Lambda.LExpr.op
                 { name := "select", metadata := Boogie.Visibility.unres }
                 (some (Lambda.LMonoTy.tcons
                    "arrow"
                    [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
                     Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"]])))
               (Lambda.LExpr.bvar 3))
             (Lambda.LExpr.bvar 2))))))]
-/
#guard_msgs in
#eval
  extractAxiomsWithFreeTypeVars examplePgm ["k", "v"]
