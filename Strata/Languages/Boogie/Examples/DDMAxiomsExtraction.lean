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
def extractExpr (axDecl: Boogie.Decl): (Lambda.LExpr Lambda.LMonoTy Boogie.BoogieIdent) :=
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
def replaceTypesByFTV (expr: Lambda.LExpr Lambda.LMonoTy Boogie.BoogieIdent) (to_replace: List String): Lambda.LExpr Lambda.LMonoTy Boogie.BoogieIdent :=
  match expr with
    | .const c oty => .const c (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace))
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
def extractAxiomsWithFreeTypeVars (pgm: Program) (typeArgs: List String): (List (Lambda.LExpr Lambda.LMonoTy Boogie.BoogieIdent)) :=
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
info: #[{ name := { dialect := "Boogie", name := "command_typedecl" },
    args := ((Array.mkEmpty 2).push (Arg.ident "k")).push (Arg.option none) },
  { name := { dialect := "Boogie", name := "command_typedecl" },
    args := ((Array.mkEmpty 2).push (Arg.ident "v")).push (Arg.option none) },
  { name := { dialect := "Boogie", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (Arg.option
              (some
                (Arg.op
                  { name := { dialect := "Boogie", name := "label" },
                    args := (Array.mkEmpty 1).push (Arg.ident "updateSelect") })))).push
        (Arg.expr
          (((Expr.fn { dialect := "Boogie", name := "forall" }).app
                (Arg.op
                  { name := { dialect := "Boogie", name := "declPush" },
                    args :=
                      ((Array.mkEmpty 2).push
                            (Arg.op
                              { name := { dialect := "Boogie", name := "declPush" },
                                args :=
                                  ((Array.mkEmpty 2).push
                                        (Arg.op
                                          { name := { dialect := "Boogie", name := "declAtom" },
                                            args :=
                                              (Array.mkEmpty 1).push
                                                (Arg.op
                                                  { name := { dialect := "Boogie", name := "bind_mk" },
                                                    args :=
                                                      (((Array.mkEmpty 3).push (Arg.ident "m")).push
                                                            (Arg.option none)).push
                                                        (Arg.type
                                                          (TypeExpr.ident { dialect := "Boogie", name := "Map" }
                                                            (((Array.mkEmpty 2).push
                                                                  (TypeExpr.fvar 1 (Array.mkEmpty 0))).push
                                                              (TypeExpr.fvar 0 (Array.mkEmpty 0))))) }) })).push
                                    (Arg.op
                                      { name := { dialect := "Boogie", name := "bind_mk" },
                                        args :=
                                          (((Array.mkEmpty 3).push (Arg.ident "kk")).push (Arg.option none)).push
                                            (Arg.type (TypeExpr.fvar 0 (Array.mkEmpty 0))) }) })).push
                        (Arg.op
                          { name := { dialect := "Boogie", name := "bind_mk" },
                            args :=
                              (((Array.mkEmpty 3).push (Arg.ident "vv")).push (Arg.option none)).push
                                (Arg.type (TypeExpr.fvar 1 (Array.mkEmpty 0))) }) })).app
            (Arg.expr
              ((((Expr.fn { dialect := "Boogie", name := "equal" }).app
                        (Arg.type (TypeExpr.fvar 1 (Array.mkEmpty 0)))).app
                    (Arg.expr
                      (((((Expr.fn { dialect := "Boogie", name := "map_get" }).app
                                    (Arg.type (TypeExpr.fvar 0 (Array.mkEmpty 0)))).app
                                (Arg.type (TypeExpr.fvar 1 (Array.mkEmpty 0)))).app
                            (Arg.expr
                              ((((((Expr.fn { dialect := "Boogie", name := "map_set" }).app
                                                (Arg.type (TypeExpr.fvar 0 (Array.mkEmpty 0)))).app
                                            (Arg.type (TypeExpr.fvar 1 (Array.mkEmpty 0)))).app
                                        (Arg.expr (Expr.bvar 2))).app
                                    (Arg.expr (Expr.bvar 1))).app
                                (Arg.expr (Expr.bvar 0))))).app
                        (Arg.expr (Expr.bvar 1))))).app
                (Arg.expr (Expr.bvar 0)))))) },
  { name := { dialect := "Boogie", name := "command_axiom" },
    args :=
      ((Array.mkEmpty 2).push
            (Arg.option
              (some
                (Arg.op
                  { name := { dialect := "Boogie", name := "label" },
                    args := (Array.mkEmpty 1).push (Arg.ident "updatePreserves") })))).push
        (Arg.expr
          (((Expr.fn { dialect := "Boogie", name := "forall" }).app
                (Arg.op
                  { name := { dialect := "Boogie", name := "declPush" },
                    args :=
                      ((Array.mkEmpty 2).push
                            (Arg.op
                              { name := { dialect := "Boogie", name := "declPush" },
                                args :=
                                  ((Array.mkEmpty 2).push
                                        (Arg.op
                                          { name := { dialect := "Boogie", name := "declPush" },
                                            args :=
                                              ((Array.mkEmpty 2).push
                                                    (Arg.op
                                                      { name := { dialect := "Boogie", name := "declAtom" },
                                                        args :=
                                                          (Array.mkEmpty 1).push
                                                            (Arg.op
                                                              { name := { dialect := "Boogie", name := "bind_mk" },
                                                                args :=
                                                                  (((Array.mkEmpty 3).push (Arg.ident "m")).push
                                                                        (Arg.option none)).push
                                                                    (Arg.type
                                                                      (TypeExpr.ident
                                                                        { dialect := "Boogie", name := "Map" }
                                                                        (((Array.mkEmpty 2).push
                                                                              (TypeExpr.fvar 1 (Array.mkEmpty 0))).push
                                                                          (TypeExpr.fvar 0
                                                                            (Array.mkEmpty 0))))) }) })).push
                                                (Arg.op
                                                  { name := { dialect := "Boogie", name := "bind_mk" },
                                                    args :=
                                                      (((Array.mkEmpty 3).push (Arg.ident "okk")).push
                                                            (Arg.option none)).push
                                                        (Arg.type (TypeExpr.fvar 0 (Array.mkEmpty 0))) }) })).push
                                    (Arg.op
                                      { name := { dialect := "Boogie", name := "bind_mk" },
                                        args :=
                                          (((Array.mkEmpty 3).push (Arg.ident "kk")).push (Arg.option none)).push
                                            (Arg.type (TypeExpr.fvar 0 (Array.mkEmpty 0))) }) })).push
                        (Arg.op
                          { name := { dialect := "Boogie", name := "bind_mk" },
                            args :=
                              (((Array.mkEmpty 3).push (Arg.ident "vv")).push (Arg.option none)).push
                                (Arg.type (TypeExpr.fvar 1 (Array.mkEmpty 0))) }) })).app
            (Arg.expr
              ((((Expr.fn { dialect := "Boogie", name := "equal" }).app
                        (Arg.type (TypeExpr.fvar 1 (Array.mkEmpty 0)))).app
                    (Arg.expr
                      (((((Expr.fn { dialect := "Boogie", name := "map_get" }).app
                                    (Arg.type (TypeExpr.fvar 0 (Array.mkEmpty 0)))).app
                                (Arg.type (TypeExpr.fvar 1 (Array.mkEmpty 0)))).app
                            (Arg.expr
                              ((((((Expr.fn { dialect := "Boogie", name := "map_set" }).app
                                                (Arg.type (TypeExpr.fvar 0 (Array.mkEmpty 0)))).app
                                            (Arg.type (TypeExpr.fvar 1 (Array.mkEmpty 0)))).app
                                        (Arg.expr (Expr.bvar 3))).app
                                    (Arg.expr (Expr.bvar 1))).app
                                (Arg.expr (Expr.bvar 0))))).app
                        (Arg.expr (Expr.bvar 2))))).app
                (Arg.expr
                  (((((Expr.fn { dialect := "Boogie", name := "map_get" }).app
                                (Arg.type (TypeExpr.fvar 0 (Array.mkEmpty 0)))).app
                            (Arg.type (TypeExpr.fvar 1 (Array.mkEmpty 0)))).app
                        (Arg.expr (Expr.bvar 3))).app
                    (Arg.expr (Expr.bvar 2)))))))) }]
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
               u:select
               (some (Lambda.LMonoTy.tcons
                  "arrow"
                  [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
                   Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"]])))
             (Lambda.LExpr.app
               (Lambda.LExpr.app
                 (Lambda.LExpr.app
                   (Lambda.LExpr.op
                     u:update
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
                 u:select
                 (some (Lambda.LMonoTy.tcons
                    "arrow"
                    [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"],
                     Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.ftvar "k", Lambda.LMonoTy.ftvar "v"]])))
               (Lambda.LExpr.app
                 (Lambda.LExpr.app
                   (Lambda.LExpr.app
                     (Lambda.LExpr.op
                       u:update
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
                 u:select
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
