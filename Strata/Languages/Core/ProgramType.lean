/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.FunctionType
public import Strata.Languages.Core.ProcedureType
public import Strata.DL.Lambda.LExprT
public import Strata.Languages.Core.Factory
public import Strata.DL.Lambda.LTyWF

public section

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)
open Lambda
open Strata (Message FileRange)

namespace Factory

def typeCheck (C : Expression.TyContext) (T : Expression.TyEnv)
    : Except Format Expression.TyEnv :=
  C.functions.toArray.foldlM (fun Env func => do
    match func.body with
    | none => .ok Env
    | some body =>
      if body.freeVars.idents.all (fun k => k ∈ func.inputs.keys) then
        -- Temporarily add formals in the context.
        let Env := Env.pushEmptyContext
        let Env := Env.addInNewestContext (Strata.Util.HMap.ofList func.inputPolyTypes)
        -- Type check the body and ensure that it unifies with the return type.
        -- let (bodyty, Env) ← infer Env body
        let (body_typed, Env) ← LExpr.resolve C Env body
        let bodyty := body_typed.toLMonoTy
        let (retty, Env) ← func.outputPolyType.instantiateWithCheck C Env
        let S ← Constraints.unify [(retty, bodyty)] Env.stateSubstInfo |>.mapError format
        let Env := Env.updateSubst S
        let Env := Env.popContext
        .ok Env
      else
        .error f!"Function body contains free variables!\n\
                  {func}") T

end Factory

namespace Program

/-- Type check the proposition of an axiom or a lemma, described by `what` in
the error message, and return it with its types resolved. -/
@[expose] def typeCheckProp (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (fileRange : FileRange) (what : String) (e : Expression.Expr) :
    Except Message (Expression.Expr × Core.Expression.TyEnv) := do
  let Env := Env.pushEmptySubstScope
  let (ae, Env) ← LExpr.resolve C Env e |>.mapError (fun e => Message.withRange fileRange e)
  let Env := Env.popSubstScope
  match ae.toLMonoTy with
  | .bool => .ok (ae.unresolved, Env)
  | _ => .error <| Message.withRange fileRange f!"{what} has non-boolean type."

/-- Type check a function declaration or a recursive function block, and add
its functions to the context. The caller must already have checked that the
declared names are unique and not yet declared, as `typeCheck.go` does. -/
@[expose] def typeCheckFuncDecl (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (fileRange : FileRange) :
    Decl → Except Message (Decl × Core.Expression.TyContext × Core.Expression.TyEnv)
  | .func func md => try
    if func.isRecursive then
      .error (Message.withRange fileRange <|
        f!"Decl.func does not allow recursive functions. Use recFuncBlock instead: '{func.name}'")
    if func.name.name ∈ C.functions then
      .error (Message.withRange fileRange <|
        f!"Error in function {func.name}: a function of this name already exists.")
    let Env := Env.pushEmptySubstScope
    let (func', Env) ← Function.typeCheck C Env func |>.mapError (fun e => Message.withRange fileRange e)
    let C := C.addFactoryFunction func'.toLFunc
    let Env := Env.popSubstScope
    .ok (Decl.func func' md, C, Env)
      catch e =>
        .error (e.withRangeIfUnknown fileRange)

  | .recFuncBlock funcs md => try
    let Env := Env.pushEmptySubstScope
    -- Validate: non-empty
    if funcs.isEmpty then
      .error (Message.withRange fileRange <|
        f!"recursive function block must contain at least one function")
    -- Validate: no inline functions in the block
    let _ ← funcs.foldlM (fun _ func => do
      if func.attr.any (· == .inline) then
        .error (Message.withRange fileRange <|
          f!"recursive function '{func.name}' cannot be marked inline")
      else pure ()) ()
    -- Validate: no function reuses a name already in the factory
    let _ ← funcs.foldlM (fun _ func => do
      if func.name.name ∈ C.functions then
        .error (Message.withRange fileRange <|
          f!"Error in function {func.name}: a function of this name already exists.")
      else pure ()) ()
    -- Phase 1: Add ALL function signatures as stubs so mutual calls resolve.
    -- The caller has already checked with `addListWithError` that the block's
    -- function names are unique.
    let C' := funcs.foldl (fun C func =>
      C.addFactoryFunction { name := func.name, typeArgs := func.typeArgs,
                             inputs := func.inputs, output := func.output }) C
    -- Phase 2: Type-check each function body against C'
    let (funcs', Env) ← funcs.foldlM (fun (acc, Env) func => do
      let (func', Env) ← Function.typeCheck C' Env func
        |>.mapError (fun e => Message.withRange fileRange e)
      pure (acc ++ [func'], Env)) ([], Env)
    -- Phase 3: Add all type-checked functions to the real context
    let C := funcs'.foldl (fun C func => C.addFactoryFunction func.toLFunc) C
    let Env := Env.popSubstScope
    .ok (Decl.recFuncBlock funcs' md, C, Env)
      catch e =>
        .error (e.withRangeIfUnknown fileRange)
  | d => .ok (d, C, Env)

/--
Type check the program. The function assumes that all functions registered to
C are already well-typed.
-/
@[expose] def typeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (program : Program) :
  Except Message (Program × Core.Expression.TyEnv) := do
    -- Push a type substitution scope to store global type variables.
    let Env := Env.updateSubst { subst := Subst.empty.push (Strata.Util.HMap.empty : SubstOne),
                                 isWF := SubstWF_of_pushEmptyScope _ SubstWF_of_empty }
    let (decls, Env) ← go C Env program.decls []
    .ok ({ decls }, Env)

  where go C Env remaining acc : Except Message (Decls × Core.Expression.TyEnv) :=
  match remaining with
  | [] => .ok (acc.reverse, Env)
  | decl :: drest => do
    let fileRange := Imperative.getFileRange decl.metadata |>.getD FileRange.unknown
    -- Add all names from the declaration (multiple for mutual datatypes)
    let idents ← C.idents.addListWithError decl.names (fun n =>
      (Message.withRange fileRange f!"Error in {decl.kind} {n}: a declaration of this name already exists."))
    let C := {C with idents}
    let (decl', C, Env) ←
      match decl with

      | .type td md => try
          match td with
          | .con tc =>
            let C ← C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } (Message.withRange fileRange f!"This type declaration's name is reserved!\n\
                      {td}\n\
                      KnownTypes' names:\n\
                      {C.knownTypes.keywords}")
            .ok (Decl.type td md, C, Env)
          | .syn ts =>
            let Env ← TEnv.addTypeAlias { typeArgs := ts.typeArgs, name := ts.name, type := ts.type } C Env
               |>.mapError (fun e => Message.withRange fileRange e)
            .ok (.type td md, C, Env)
          | .data block =>
            let (block, Env) ← MutualDatatype.resolveAliases block Env |>.mapError (fun e => Message.withRange fileRange e)
            let C ← C.addMutualBlock block
            .ok (.type (.data block) md, C, Env)
          catch e =>
            .error (e.withRangeIfUnknown fileRange)

      | .ax a md => try
        let (e, Env) ← typeCheckProp C Env fileRange s!"Axiom {a.name}" a.e
        .ok (Decl.ax { a with e } md, C, Env)
          catch e =>
            .error (e.withRangeIfUnknown fileRange)

      | .lemma l md => try
        -- A lemma must hold at every type, so its formula may not constrain a
        -- type parameter: it is first checked with each one replaced by a
        -- fresh opaque type.
        unless l.typeArgs.isEmpty do
          let rigid := l.typeArgs.map fun a => (a, s!"{skolemPrefix}{l.name}_{a}")
          let C' ← rigid.foldlM (init := C) fun C (_, n) =>
            C.addKnownTypeWithError { name := n, metadata := 0 }
              (Message.withRange fileRange f!"Error in lemma {l.name}: type {n} already exists.")
          let S := Strata.Util.HMaps.ofScopes [rigid.map fun (a, n) => (a, LMonoTy.tcons n [])]
          let _ ← typeCheckProp C' Env fileRange s!"Lemma {l.name}" (l.e.applyTypeSubst S)
        let (e, Env) ← typeCheckProp C Env fileRange s!"Lemma {l.name}" l.e
        .ok (Decl.lemma { l with e } md, C, Env)
          catch e =>
            -- A generated lemma precedes the function that lists it, and is
            -- ill-typed when that function is. Report the function's error,
            -- which says what to fix.
            let owner := drest.find? (·.lemmaNames.contains l.name)
            let ownerError := owner.bind fun d =>
              let range := Imperative.getFileRange d.metadata |>.getD FileRange.unknown
              match typeCheckFuncDecl C Env range d with
              | .error e => some e
              | .ok _ => none
            .error ((ownerError.getD e).withRangeIfUnknown fileRange)

      | .distinct l es md => try
        let Env := Env.pushEmptySubstScope
        let es' ← es.mapM (LExpr.resolve C Env) |>.mapError (fun e => Message.withRange fileRange e)
        let Env := Env.popSubstScope
        .ok (Decl.distinct l (es'.map (λ e => e.fst.unresolved)) md, C, Env)
        catch e =>
          .error (e.withRangeIfUnknown fileRange)

      | .proc proc md =>
        -- Already reports source locations.
        let Env := Env.pushEmptySubstScope
        let (proc', Env) ← Procedure.typeCheck C Env program proc md
        let Env := Env.popSubstScope
        .ok (Decl.proc proc' md, C, Env)

      | .func _ _ | .recFuncBlock _ _ => typeCheckFuncDecl C Env fileRange decl

    go C Env drest (decl' :: acc)

end Program
end Core

end -- public section
