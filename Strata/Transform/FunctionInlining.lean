/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Expressions

namespace Strata

/-! ## Function Inlining

Core-to-Core transforms that replace function calls with their bodies.
-/

public section

/--
Inline function bodies in an expression. For each fully-applied call `f(a₁, ..., aₙ)`
where `f` has a known body, replace it with `body[a₁/x₁, ..., aₙ/xₙ]`.
This avoids emitting uninterpreted `mathematical_function` symbols in GOTO.
-/
partial def inlineFuncDefs
    (defs : List (String × List Core.CoreIdent × Lambda.LExpr Core.CoreLParams.mono))
    (postProcess : Lambda.LExpr Core.CoreLParams.mono → Lambda.LExpr Core.CoreLParams.mono := id)
    (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
  let rec go (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
    let (head, args) := collectApp e
    match head with
    | .op _ o _ =>
      let args' := args.map go
      match defs.find? (fun (n, _, _) => n == (Lambda.Identifier.name o)) with
      | some (_, formals, body) =>
        if args'.length == formals.length then
          go (postProcess (Lambda.LExpr.substFvars body (formals.zip args')))
        else rebuildApp head args'
      | none => postProcess (rebuildApp head args')
    | _ =>
      match e with
      | .const .. | .op .. | .bvar .. | .fvar .. => e
      | .abs m n ty b => .abs m n ty (go b)
      | .quant m k n ty tr b => .quant m k n ty (go tr) (go b)
      | .app m f a => .app m (go f) (go a)
      | .ite m c t el => .ite m (go c) (go t) (go el)
      | .eq m l r => .eq m (go l) (go r)
  go e
where
  collectApp (e : Lambda.LExpr Core.CoreLParams.mono)
      : Lambda.LExpr Core.CoreLParams.mono × List (Lambda.LExpr Core.CoreLParams.mono) :=
    match e with
    | .app _ f a => let (h, as) := collectApp f; (h, as ++ [a])
    | other => (other, [])
  rebuildApp (head : Lambda.LExpr Core.CoreLParams.mono)
      (args : List (Lambda.LExpr Core.CoreLParams.mono))
      : Lambda.LExpr Core.CoreLParams.mono :=
    args.foldl (fun acc arg => .app default acc arg) head

/-- Build the function definition map from a program's declarations. -/
def collectFuncDefs (pgm : Core.Program)
    : List (String × List Core.CoreIdent × Lambda.LExpr Core.CoreLParams.mono) :=
  pgm.decls.filterMap fun d => do
    let f ← d.getFunc?
    let body ← f.body
    guard (!f.isRecursive)
    guard (f.typeArgs.toArray.isEmpty)
    some (f.name.name, f.inputs.keys, body)

/-- Inline recursive function calls with bounded unrolling.
    At depth 0, recursive calls are left as-is (uninterpreted). -/
partial def inlineRecFuncDefs
    (recDefs : List (String × List Core.CoreIdent × Lambda.LExpr Core.CoreLParams.mono))
    (maxDepth : Nat)
    (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
  go maxDepth e
where
  go (depth : Nat) (e : Lambda.LExpr Core.CoreLParams.mono)
      : Lambda.LExpr Core.CoreLParams.mono :=
    if depth == 0 then e
    else
      let (head, args) := collectApp e
      match head with
      | .op _ o _ =>
        let args' := args.map (go depth)
        match recDefs.find? (fun (n, _, _) => n == (Lambda.Identifier.name o)) with
        | some (_, formals, body) =>
          if args'.length == formals.length then
            go (depth - 1) (Lambda.LExpr.substFvars body (formals.zip args'))
          else rebuildApp head args'
        | none => rebuildApp head args'
      | _ =>
        match e with
        | .const .. | .op .. | .bvar .. | .fvar .. => e
        | .abs m n ty b => .abs m n ty (go depth b)
        | .quant m k n ty tr b => .quant m k n ty (go depth tr) (go depth b)
        | .app m f a => .app m (go depth f) (go depth a)
        | .ite m c t el => .ite m (go depth c) (go depth t) (go depth el)
        | .eq m l r => .eq m (go depth l) (go depth r)
  collectApp (e : Lambda.LExpr Core.CoreLParams.mono)
      : Lambda.LExpr Core.CoreLParams.mono × List (Lambda.LExpr Core.CoreLParams.mono) :=
    match e with
    | .app _ f a => let (h, as) := collectApp f; (h, as ++ [a])
    | other => (other, [])
  rebuildApp (head : Lambda.LExpr Core.CoreLParams.mono)
      (args : List (Lambda.LExpr Core.CoreLParams.mono))
      : Lambda.LExpr Core.CoreLParams.mono :=
    args.foldl (fun acc arg => .app default acc arg) head


end -- public section

end Strata
