/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.Languages.Boogie.DDMTransform.Parse
import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

-- Example Boogie program with axioms
def exampleEnv : Environment :=
#strata
program Boogie;
type k;
type v;
axiom [updateSelect]: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv;
axiom [updatePreserves]: forall m: Map k v, okk: k, kk: k, vv: v :: m[kk := vv][okk] == m[okk];
#end

def extractAxiomsDecl (prg: Boogie.Program) : (List Boogie.Decl) :=
  let rec loop (acc: List Boogie.Decl) (l: List Boogie.Decl): List Boogie.Decl :=
    match l with
      | [] => acc
      | hd :: tl =>
          match hd with
          | .ax _ _ => loop (acc ++ [hd]) tl
          | _ => loop acc tl
  loop [] prg.decls

def extractExpr (axDecl: Boogie.Decl): (Lambda.LExpr Boogie.BoogieIdent) :=
  match axDecl with
    | .ax a _ => a.e
    | _ => panic "Can be called only on axiom declaration"

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

def replaceTypesByFTV (expr: Lambda.LExpr Boogie.BoogieIdent) (to_replace: List String): Lambda.LExpr Boogie.BoogieIdent :=
  match expr with
    | .const c oty => .const c (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace))
    | .op o oty => .op o (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace))
    | .fvar name oty => .fvar name (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace))
    | .mdata info e => .mdata info (replaceTypesByFTV e to_replace)
    | .abs oty e => .abs (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace)) (replaceTypesByFTV e to_replace)
    | .quant k oty e => .quant k (oty.map (fun t => transformSimpleTypeToFreeVariable t to_replace)) (replaceTypesByFTV e to_replace)
    | .app fn e => .app (replaceTypesByFTV fn to_replace) (replaceTypesByFTV e to_replace)
    | .ite c t e => .ite (replaceTypesByFTV c to_replace) (replaceTypesByFTV t to_replace) (replaceTypesByFTV e to_replace)
    | .eq e1 e2 => .eq (replaceTypesByFTV e1 to_replace) (replaceTypesByFTV e2 to_replace)
    | _ => expr

def extractAxiomsWithFreeTypeVars (env: Environment) (typeArgs: List String): (List (Lambda.LExpr Boogie.BoogieIdent)) :=
  let prg: Boogie.Program := (TransM.run (translateProgram (env.commands))).fst
  let axiomsDecls := extractAxiomsDecl prg
  let axioms := axiomsDecls.map extractExpr
  axioms.map (fun a => replaceTypesByFTV a typeArgs)

#eval IO.println exampleEnv.format.render
#eval exampleEnv.commands
#eval
  extractAxiomsWithFreeTypeVars exampleEnv ["k", "v"]
