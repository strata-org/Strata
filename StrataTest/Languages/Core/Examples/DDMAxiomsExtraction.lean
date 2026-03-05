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
axiom [updateSelect]: forall ((m : (Map v k)), (kk : k)), (vv : v) :: (m[kk:=vv])[kk] == vv;
axiom [updatePreserves]: forall (((m : (Map v k)), (okk : k)), (kk : k)), (vv : v) :: (m[kk:=vv])[okk] == m[okk];
-/
#guard_msgs in
#eval IO.println examplePgm


/--
info: #["command_typedecl", "command_typedecl", "command_axiom", "command_axiom"]
-/
#guard_msgs in
#eval examplePgm.commands.map (fun c => c.name.name)

/--
info: [LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.tcons
   "Map"
   [Lambda.LMonoTy.ftvar "k",
    Lambda.LMonoTy.ftvar
      "v"]) (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.ftvar
   "k") (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.ftvar
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
 LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.tcons
   "Map"
   [Lambda.LMonoTy.ftvar "k",
    Lambda.LMonoTy.ftvar
      "v"]) (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.ftvar
   "k") (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.ftvar
   "k") (LExpr.bvar () 0) (LExpr.quant () QuantifierKind.all (some Lambda.LMonoTy.ftvar
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
