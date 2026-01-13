/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.DefinitionAST

/-!
# Function-to-Axiom Transformation

Transforms B3 programs by splitting function definitions into declarations and axioms.
This is necessary because SMT solvers do not support mutually recursive function definitions
using the `define-fun` syntax. By converting function bodies to axioms with quantifiers,
we enable verification of programs with mutually recursive functions.

## Example: Simple Function

Input:
```
function abs(x : int) : int {
  if x >= 0 then x else -x
}
```

Output:
```
function abs(x : int) : int

axiom forall x : int pattern abs(x) abs(x) == (if x >= 0 then x else -x)
```

## Example: Mutually Recursive Functions

Input:
```
function isEven(n : int) : int {
  if n == 0 then 1 else isOdd(n - 1)
}
function isOdd(n : int) : int {
  if n == 0 then 0 else isEven(n - 1)
}
```

Output:
```
function isEven(n : int) : int
function isOdd(n : int) : int

axiom forall n : int pattern isEven(n) isEven(n) == (if n == 0 then 1 else isOdd(n - 1))
axiom forall n : int pattern isOdd(n) isOdd(n) == (if n == 0 then 0 else isEven(n - 1))
```

## Example: Function with Precondition

Input:
```
function sqrt(x : int) : int
  when x >= 0
{
  ...
}
```

Output:
```
function sqrt(x : int) : int

axiom forall x : int pattern sqrt(x) (x >= 0) ==> (sqrt(x) == ...)
```
-/

namespace Strata.B3.Transform

open Strata.B3AST

def transformFunctionDecl (decl : B3AST.Decl α) : List ( B3AST.Decl α) :=
  match decl with
  | .function _m name params resultType tag body =>
      match body.val with
      | some bodyAnn =>
          match bodyAnn with
          | FunctionBody.functionBody m whens bodyExpr =>
              let funcDecl := B3AST.Decl.function m name params resultType tag (Ann.mk body.ann none)
              let paramList := params.val.toList
              let funcCallArgs : Array (Expression α) :=
                params.val.mapIdx (fun i _param => Expression.id m i)
              let funcCall := Expression.functionCall m name ⟨m, funcCallArgs⟩
              let equality := Expression.binaryOp m (BinaryOp.eq m) funcCall bodyExpr
              let axiomBody :=
                if whens.val.isEmpty then
                  equality
                else
                  let whenExprs := whens.val.toList.filterMap (fun w =>
                    match w with | When.when _m cond => some cond)
                  let whenConj := match whenExprs with
                    | [] => Expression.literal whens.ann (Literal.boolLit whens.ann true)
                    | first :: rest => rest.foldl (fun acc e =>
                        Expression.binaryOp whens.ann (BinaryOp.and whens.ann) acc e
                      ) first
                  Expression.binaryOp whens.ann (BinaryOp.implies whens.ann) whenConj equality
              -- Create pattern with function call
              let pattern := Pattern.pattern m ⟨m, #[funcCall]⟩
              let axiomExpr := paramList.foldr (fun param body =>
                match param with
                | FParameter.fParameter _m _inj paramName paramTy =>
                    let varDecl := VarDecl.quantVarDecl m paramName paramTy
                    Expression.quantifierExpr m
                      (QuantifierKind.forall m)
                      ⟨m, #[varDecl]⟩ ⟨m, #[pattern]⟩ body
              ) axiomBody
              let axiomDecl := Decl.axiom m ⟨m, #[]⟩ axiomExpr
              [funcDecl, axiomDecl]
      | none => [decl]
  | decl => [decl]

def functionToAxiom (prog : B3AST.Program α) : B3AST.Program α :=
  match prog with
  | Program.program m decls =>
      Id.run do
        let mut typeDecls : List (B3AST.Decl α) := []
        let mut funcDecls : List (B3AST.Decl α) := []
        let mut funcAxioms : List (B3AST.Decl α) := []
        let mut otherDecls : List (B3AST.Decl α) := []

        for decl in decls.val.toList do
          match decl with
          | .typeDecl _ _ | .tagger _ _ _ =>
              typeDecls := typeDecls ++ [decl]
          | .function _ _ _ _ _ body =>
              match body.val with
              | some bodyAnn =>
                  match bodyAnn with
                  | FunctionBody.functionBody _ _ _ =>
                      let transformed := transformFunctionDecl decl
                      match transformed with
                      | [funcDecl, axiomDecl] =>
                          funcDecls := funcDecls ++ [funcDecl]
                          funcAxioms := funcAxioms ++ [axiomDecl]
                      | _ => otherDecls := otherDecls ++ [decl]
              | none =>
                  funcDecls := funcDecls ++ [decl]
          | .axiom _ _ _ =>
              funcAxioms := funcAxioms ++ [decl]
          | _ =>
              otherDecls := otherDecls ++ [decl]

        let finalDecls := typeDecls ++ funcDecls ++ funcAxioms ++ otherDecls
        return Program.program m ⟨decls.ann, finalDecls.toArray⟩

end Strata.B3.Transform
