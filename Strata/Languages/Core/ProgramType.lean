/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.AxiomType
public import Strata.Languages.Core.LemmaType
public import Strata.Languages.Core.DistinctType
public import Strata.Languages.Core.FunctionType
public import Strata.Languages.Core.RecFuncBlockType
public import Strata.Languages.Core.ProcedureType
public import Strata.DL.Lambda.LExprT
public import Strata.Languages.Core.Factory

public section

/-!
# Type checking Core programs

TODO: add the soundness theorem `Core.typeCheck_sound_output`: the program
the checker returns satisfies `ProgramWellTyped` and `ProgramNamesWF`.
-/

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)
open Lambda
open Strata (Message FileRange)

/-- The type context with the built-in functions and known types. -/
def initTyContext : Expression.TyContext :=
  { Lambda.LContext.default with
      functions := Core.Factory,
      knownTypes := Core.KnownTypes }

namespace Factory

/-- Check `func` against `C` at `Env`, with rigid constants that avoid the names of `scope`,
    returning the environment. -/
def checkFunction (scope : Thunk (Std.HashSet String)) (C : Expression.TyContext)
    (Env : Expression.TyEnv) (func : LFunc CoreLParams) : Except Format Expression.TyEnv := do
  let _ ← Function.typeCheckIn scope C Env func.toFunc
  .ok Env

/-- Check `func` of the factory of `C` against `C` at `Env`, with rigid constants that avoid
    the names of `scope`. The factory is used as given, so the type parameters of `func` must
    not start with a reserved prefix. -/
def checkFactoryFunction (scope : Thunk (Std.HashSet String)) (C : Expression.TyContext)
    (Env : Expression.TyEnv) (func : LFunc CoreLParams) : Except Format Expression.TyEnv := do
  checkTypeArgsAllowed s!"Factory function '{func.name.name}'" func.typeArgs
  checkFunction scope C Env func

/-- Check every function of `C` in order, threading the environment, with rigid constants that
    avoid the names of `scope`. -/
def typeCheckIn (scope : Thunk (Std.HashSet String)) (C : Expression.TyContext)
    (T : Expression.TyEnv) : Except Format Expression.TyEnv :=
  C.functions.toArray.foldlM (checkFactoryFunction scope C) T

/-- `typeCheckIn` against the set of the type names in scope in `C` and `T`, built at most once,
    when a function is polymorphic. -/
def typeCheck (C : Expression.TyContext) (T : Expression.TyEnv)
    : Except Format Expression.TyEnv :=
  typeCheckIn (scopeTyNameThunk C T) C T

/-- Check `func` against `C` at `Env`, with rigid constants that avoid the names of `S`, then
    add it to `C` with its reserved type parameters renamed, and add the type names of its
    signature to `S`. -/
def checkThenAddOne (Env : Expression.TyEnv)
    (acc : Expression.TyContext × Std.HashSet String) (func : LFunc CoreLParams) :
    Except Message (Expression.TyContext × Std.HashSet String) := do
  let (C, S) := acc
  let (renamed, _) ← Function.typeCheckIn (Thunk.pure S) C Env func.toFunc
    |>.mapError Message.fromFormat
  let func' := { func with toFunc := renamed }
  let functions ← C.functions.tryPush func'
  .ok ({ C with functions }, S.insertMany (funcSigTyNames func'))

/-- Check each function of `fns` in order at `Env` against `C` extended by the functions before
    it, adding each function once checked; `S` holds the type names in scope and grows with
    the signatures of the added functions. -/
def checkThenAddIn (S : Std.HashSet String) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (fns : Array (LFunc CoreLParams)) :
    Except Message (Expression.TyContext × Std.HashSet String) :=
  fns.foldlM (checkThenAddOne Env) (C, S)

/-- `checkThenAddIn` started from the set of the type names in scope in `C` and `Env`, returning
    only the context. -/
def checkThenAdd (C : Expression.TyContext) (Env : Expression.TyEnv)
    (fns : Array (LFunc CoreLParams)) : Except Message Expression.TyContext :=
  Prod.fst <$> checkThenAddIn (scopeTyNameThunk C Env).get C Env fns

/-- The number of functions in the factory of `C`. Kept out of line so the size is read before a
    later call extends `C`'s factory, which can then extend it in place rather than copy it. -/
@[noinline] def numFunctions (C : Expression.TyContext) : Nat :=
  C.functions.toArray.size

end Factory

/-- The proposition check of an axiom or a lemma declaration against a set of the type names
    in scope, returning the checked declaration (a lemma comes back with its reserved type
    parameters renamed); `none` for other declarations. -/
def Decl.propCheck? (d : Decl) (C : Expression.TyContext) :
    Option (Std.HashSet String → Expression.TyEnv → Except Format (Decl × Expression.TyEnv)) :=
  match d with
  | .ax a md => some fun _ Env => do
    let (e, Env') ← Axiom.typeCheckIn C Env a
    .ok (.ax { a with e } md, Env')
  | .lemma l md => some fun S Env => do
    let (l', Env') ← Lemma.typeCheckIn (Thunk.pure S) C Env l
    .ok (.lemma l' md, Env')
  | _ => none

/-- Check an axiom or a lemma declaration against the set `S` of the type names in scope,
    returning it with its checked proposition; `none` for other declarations. -/
def Decl.routePropBeforeRegistration (d : Decl) (S : Std.HashSet String)
    (C : Expression.TyContext) (Env : Expression.TyEnv) (fileRange : FileRange) :
    Except Message (Option Decl × Expression.TyEnv) :=
  match d.propCheck? C with
  | some check => do
    let (d', Env') ← check S Env.pushEmptySubstScope
      |>.mapError (fun e => Message.withRange fileRange e)
    .ok (some d', Env'.popSubstScope)
  | none => .ok (none, Env)

/-- Check a distinct declaration, returning its checked expressions; `none` for other
    declarations. -/
def Decl.routeDistinctBeforeRegistration (d : Decl) (C : Expression.TyContext)
    (Env : Expression.TyEnv) (fileRange : FileRange) :
    Except Message (Option (List Expression.Expr) × Expression.TyEnv) :=
  match d with
  | .distinct name es _ => do
    let Env0 := Env
    let Env := Env.pushEmptyContext.pushEmptySubstScope
    let (es, Env) ← Distinct.typeCheck C Env name es
      |>.mapError (fun e => Message.withRange fileRange
        (hideUnifierGeneratedNames C.knownTypes (toString e)))
    let Env := Env.popSubstScope.popContext
    .ok (some es, Env.updateContext Env0.context)
  | _ => .ok (none, Env)

namespace Program

/-- One iteration of `Program.typeCheck.goWith` on `decl`, continuing with `k` on its results
    and on the scope type-name set `S` extended with the type names `decl` adds to the scope;
    for a recursive function block, `k` receives the set its checker returns. The
    declaration checkers use `S` as the set of the type names in scope, and `PS` as the set
    of the type names of the procedure signatures. -/
def typeCheck.stepThen {α : Type} (program : Program) (PS : Thunk (Std.HashSet String))
    (S : Std.HashSet String) (C : Expression.TyContext) (Env : Expression.TyEnv) (decl : Decl)
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Message α) :
    Except Message α := do
  let fileRange := Imperative.getFileRange decl.metadata |>.getD FileRange.unknown
  let (checkedProp, Env) ← decl.routePropBeforeRegistration S C Env fileRange
  let (checkedDistinct, Env) ← decl.routeDistinctBeforeRegistration C Env fileRange
  let idents ← C.idents.addListWithError decl.names (fun n =>
    Message.withRange fileRange
      f!"Error in {decl.kind} {n}: a declaration of this name already exists.")
  let C := {C with idents}
  let (decl', C, Env, S) ←
    match decl with
    | .type td md => try
        match td with
        | .con tc =>
          let C ← TypeConstructor.typeCheck tc .program C Env
          .ok (Decl.type td md, C, Env, S)
        | .syn ts =>
          let (ts', Env) ← TypeSynonym.typeCheck ts C Env
             |>.mapError (fun e => Message.withRange fileRange e)
          .ok (.type (.syn ts') md, C, Env,
            S.insertMany (ts'.name :: getTypeRefs ts'.type))
        | .data block =>
          let n := Factory.numFunctions C
          let (block, C, Env) ← MutualDatatype.typeCheck block C Env
          .ok (.type (.data block) md, C, Env,
            S.insertMany (Factory.tyNamesFrom n C.functions))
        catch e =>
          .error (e.withRangeIfUnknown fileRange)
    | .ax .. | .lemma .. =>
      .ok (checkedProp.getD decl, C, Env, S)
    | .distinct l es md =>
      .ok (Decl.distinct l (checkedDistinct.getD es) md, C, Env, S)
    | .proc proc md => try
      let Env := Env.pushEmptySubstScope
      let (proc', Env) ← Procedure.typeCheckIn (Thunk.pure S) PS C Env program proc md
      let Env := Env.popSubstScope
      .ok (Decl.proc proc' md, C, Env, S)
        catch e =>
          .error (e.withRangeIfUnknown fileRange)
    | .func func md => try
      if func.isRecursive then
        throw (Message.fromFormat
          f!"Decl.func does not allow recursive functions. Use recFuncBlock instead: \
             '{func.name}'")
      (Function.checkNameFresh C func).mapError Message.fromFormat
      let Env := Env.pushEmptySubstScope
      let (_, func') ←
        Function.typeCheckIn (Thunk.pure S) C Env func
        |>.mapError (fun e => Message.withRange fileRange e)
      let lfunc := func'.toLFunc
      let C := C.addFactoryFunction lfunc
      let Env := Env.popSubstScope
      .ok (Decl.func func' md, C, Env, S.insertMany (funcSigTyNames lfunc))
        catch e =>
          .error (e.withRangeIfUnknown fileRange)
    | .recFuncBlock funcs md => try
      let Env := Env.pushEmptySubstScope
      let (funcs', C, Env, S) ← RecFuncBlock.typeCheckIn S C Env funcs
        |>.mapError (fun e => Message.withRange fileRange e)
      let Env := Env.popSubstScope
      .ok (Decl.recFuncBlock funcs' md, C, Env, S)
        catch e =>
          .error (e.withRangeIfUnknown fileRange)
  k decl' C Env S

/-- Check the declarations `remaining` in order with `stepThen`, threading the context, the
    environment and the scope type-name set `S`. Returns `acc` reversed, followed by the
    checked declarations of `remaining`, and the final environment. The thunk `PS` is the set
    of the type names of the procedure signatures. -/
def typeCheck.goWith (program : Program) (PS : Thunk (Std.HashSet String))
    (S : Std.HashSet String) (C : Expression.TyContext) (Env : Expression.TyEnv) :
    List Decl → Decls → Except Message (Decls × Expression.TyEnv)
  | [], acc => .ok (acc.reverse, Env)
  | decl :: drest, acc =>
    stepThen program PS S C Env decl fun decl' C Env S =>
      goWith program PS S C Env drest (decl' :: acc)

/-- `Env` with its type substitution replaced by one empty scope, which holds the global type
    variables. -/
def typeCheck.startEnv (Env : Expression.TyEnv) : Expression.TyEnv :=
  Env.updateSubst { subst := Subst.empty.push (Strata.Util.HMap.empty : SubstOne),
                    isWF := SubstWF_of_pushEmptyScope _ SubstWF_of_empty }

/-- Run the declaration walk `walk` from `Env` with a pushed global type substitution scope,
    and return the program of the checked declarations with the final environment. -/
def typeCheck.withStart (Env : Expression.TyEnv)
    (walk : Expression.TyEnv → Except Message (Decls × Expression.TyEnv)) :
    Except Message (Program × Expression.TyEnv) := do
  let (decls, Env) ← walk (typeCheck.startEnv Env)
  .ok ({ decls }, Env)

/--
Type check the program. The function assumes that all functions registered to
C are already type checked.
-/
@[expose] def typeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (program : Program) :
  Except Message (Program × Core.Expression.TyEnv) :=
    typeCheck.withStart Env fun Env => go C Env program.decls []

  where go C Env remaining acc : Except Message (Decls × Core.Expression.TyEnv) :=
    let PS := procSigTyNameThunk program
    typeCheck.goWith program PS (scopeTyNameThunk C Env).get C Env remaining acc

/-- `typeCheck` with `S` as the set of the type names in scope in `C` and `Env`. -/
def typeCheckIn (S : Std.HashSet String) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (program : Program) : Except Message (Program × Expression.TyEnv) :=
  typeCheck.withStart Env fun Env =>
    typeCheck.goWith program (procSigTyNameThunk program) S C Env program.decls []

end Program
end Core

end -- public section
